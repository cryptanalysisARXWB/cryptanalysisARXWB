# Requires a modified version of
# white_box_arx.c
# provided, just replace the original with it

# Simplified oracle generation which doesn't require to install other libraries but requires a precomputed header (white_box_backend.c)
# Use cleanOracle.py otherwise

import os
import subprocess
import random

from collections import namedtuple
from ctypes import *

from binteger import Bin  # pip install binteger


SpeckInstance = namedtuple('SpeckInstance', 'name, n, default_rounds, ws, m, alpha, beta')
speck_instances = {
	32: SpeckInstance("Speck_32_64", 16, 22, 16, 4, 7, 2),
	64: SpeckInstance("Speck_64_128", 32, 27, 32, 4, 8, 3),
	128: SpeckInstance("Speck_128_256", 64, 34, 64, 4, 8, 3),
}

# Currently only supports irf_degree 3 or 4 (to actually have quadratic encodings)
class WBOracle:
	def __init__(self, sharedLibFile="./white_box_arx.so", block_size=32):
		"""
		sharedLibFile:
			- If the file already exists, just use that one to create the encryption oracle
			If the file doesn't exist, go through the generation process
		"""

		speck_instance = speck_instances[block_size]
		self.n = speck_instance.n
		self.N = 2*self.n
		rounds = speck_instance.default_rounds
		wordsize = speck_instance.ws
		keym = speck_instance.m
		cfile_backend = "white_box_backend.c"

		if not os.path.isfile(sharedLibFile):

			print("No file " + sharedLibFile + ", compiling using precomputed header")

			#Compile into a shared C lib
			# cc -fPIC -shared -o white_box_arx.so white_box_arx.c -lm4ri > /dev/null 2>&1
			print("Compiling shared library")
			compileOutput = subprocess.check_output(["cc","-fPIC","-shared","-o",sharedLibFile,"white_box_arx.c","-lm4ri"],stderr=subprocess.STDOUT)

		else:
			print("Lib file " + sharedLibFile  +" already exists, loading it")

		#.so file has been generated, or already exists
		#Some globals
		self.ROUNDS = rounds-1 #One less because first round doesn't count
		self.sharedLibFile = sharedLibFile

		self.set_library(sharedLibFile)

		"""
		Precompute the index_coeff offset for each round
		Necessary for fast evaluation of partial rounds
		"""
		self.allIndex = [0 for _ in range(self.ROUNDS)]
		allIndex_c = (c_size_t * len(self.allIndex))(*self.allIndex)
		self.wbarx.getCoeffIndex(allIndex_c)
		for i in range(len(self.allIndex)):
			self.allIndex[i] = allIndex_c[i]

		self.rounds = [
			WhiteboxSpeckRound(n=self.n, round=round, wbo=self)
			for round in range(self.ROUNDS)
		]

	def set_library(self, sharedLibFile):
		self.wbarx = CDLL(sharedLibFile) #the magic
		#Declare arg types
		self.WORD_TYPE = c_uint16
		if self.n == 32:
			self.WORD_TYPE = c_uint32
		elif self.n == 64:
			self.WORD_TYPE = c_uint64
		#void enc(WORD_TYPE p[2], WORD_TYPE c[2])
		self.wbarx.enc.argtypes = [POINTER(self.WORD_TYPE), POINTER(self.WORD_TYPE)]
		#void getCoeffIndex(size_t allIndex[ROUNDS])
		self.wbarx.getCoeffIndex.argtypes = [POINTER(c_size_t)]
		#void partialRoundEnc(WORD_TYPE p[2],WORD_TYPE c[2],size_t allIndex[ROUNDS],size_t startingRound,size_t nbRound)
		self.wbarx.partialRoundEnc.argtypes = [POINTER(self.WORD_TYPE),POINTER(self.WORD_TYPE),POINTER(c_size_t),c_size_t,c_size_t]

	def encrypt(self,p):
		"""
		p is a list of size 2, containing each half of the plaintext
		return a list of size 2, containing each half of the ciphertext
		"""
		p_c = (self.WORD_TYPE * len(p))(*p)
		c = [0,0]
		c_c = (self.WORD_TYPE * len(c))(*c)
		self.wbarx.enc(p_c,c_c)
		c[0] = c_c[0]
		c[1] = c_c[1]
		return c

	def partialRoundEnc(self,p,startingRound,nbRound=1):
		"""
		Encrypt from round startingRound to startingRound+nbRound-1 (nbRound total)
		Starts from the first encoded round (so round 0 here is actually round 1 in Speck)
		Requires to have precompute allIndex to only evaluate the rounds we want
		"""
		p_c = (self.WORD_TYPE * len(p))(*p)
		c = [0,0]
		c_c = (self.WORD_TYPE * len(c))(*c)
		allIndex_c = (c_size_t * len(self.allIndex))(*self.allIndex)
		self.wbarx.partialRoundEnc(p_c,c_c,allIndex_c,startingRound,nbRound)
		c[0] = c_c[0]
		c[1] = c_c[1]
		return c

	# pickling fix
	def __getstate__(self):
		d = self.__dict__.copy()
		del d["wbarx"]
		return d

	def __setstate__(self, d):
		self.__dict__ = d.copy()
		self.set_library(d["sharedLibFile"])


class WhiteboxSpeckRound:
	def __init__(self, n, round, wbo):
		self.rno = int(round)
		self.n = int(n)
		self.N = self.n * 2
		self.wbo = wbo

	def query(self, x):
		l, r = map(int, Bin(x, self.N).split(2))
		c = self.wbo.partialRoundEnc([l, r], self.rno, 1)
		return Bin.concat(c[0], c[1], n=self.n)

"""
>>> General note : The default name for the shared lib file is white_box_arx.so, which can be changed when creating an oracle
>>> If the .so file already exists, the implementation will use it immediately.
>>>Since the generation can take a while, for now I chose to not add a functionality to delete the .so file and regenerate one if the file already exists, to avoid mistakes.
>>>Thus, if one wants to use the same filename for the .so, manually delete the file

This needs to have the white_box_backend.c already existing (which contains the raw data for the whitebox implementation)
If so, then one can simply compile and use the oracle with the following lines of code in Sage

from simplifiedOracle import *
oracle = WBOracle()
oracle.encrypt([0,0])

"""
