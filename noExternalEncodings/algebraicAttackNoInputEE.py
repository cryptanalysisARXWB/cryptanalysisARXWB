
from sage.all import *

# from cleanOracle import * #Used for full instance generation
from simplifiedOracle import * #Used when the white_box_backend.c is already provided

import time

SPECK_ALPHA = 7
SPECK_BETA = 2

def intToVector(x,n):
	v = [0 for _ in range(n)]
	for i in range(n):
		if (x & (1 << i)) != 0:
			v[i] = 1
	return vector(GF(2),v)

def intToDeg2Vector(x,n):
	'''
	From an integer over n bits, get the corresponding degree 2 vector
	This means a vector v = v1 + v2 where:
	- v1 is of length n, with v1[i] containing the value of the i-th bit of x (denoted xi in the following)
	- v2 is of length n*(n-1)/2, containing all values xi*xj with 0 <= i < j < n
	also add [1] at the end (constant term)
	'''
	v = [0 for _ in range(n)]
	for i in range(n):
		if (x & (1 << i)) != 0:
			v[i] = 1
	v2 = [0 for _ in range(n*(n-1)//2)]
	ctr = 0
	for i in range(n):
		for j in range(i+1,n):
			v2[ctr] = v[i]*v[j]
			ctr += 1
	return vector(GF(2),v+v2+[1])

def splitVectorToPairInt(v):
	'''
	Return (x,y) where x (resp. y) is the integer representing the lower (resp. upper) half bits of the binary vector v
	'''
	x = 0
	y = 0
	n = len(v)//2
	for i in range(n):
		if v[i] == 1:
			x |= (1 << i)
		if v[i+n] == 1:
			y |= (1 << i)
	return (x,y)

def mergePairIntToVector(x,y,nx,ny):
	'''
	Return the binary vector of length nx + ny (in GF(2)) representing the first nx bits of x followed by the first ny bits of y
	'''
	v = [0 for _ in range(nx+ny)]
	for i in range(nx):
		if (x & (1 << i)) != 0:
			v[i] = 1
	for i in range(ny):
		if (y & (1 << i)) != 0:
			v[i+nx] = 1
	return vector(GF(2),v)

def CSHL(x,n,s):
	"""
	Return the cyclic-shift of x by s position, with x over n significant bits
	"""
	if(s == 0):
		return (x & ((1 << n) - 1));
	return ((x << s) & ((1 << n) - 1)) | (x >> (n - s));

def CSHR(x,n,s):
	'''
	Return the cyclic-shift of x by s position to the right, with x over n bits
	'''

	if(s == 0):
		return (x & ((1 << n) - 1));
	return (x >> s) | ((x & ((1 << s)-1)) << (n-s));

def invSpeck(x,Lk):
	'''
	With r = len(Lk), apply the inverse of the Speck round function r times
	Keys are ordered in the same order as encryption, so Lk[0] is used last in the decryption
	'''

	if len(Lk) == 0:
		return splitVectorToPairInt(x)

	global SPECK_ALPHA,SPECK_BETA

	n = len(x)//2
	nbRound = len(Lk)
	modmask = (1 << n) - 1

	#Split the vector into 2 integers
	y0,y1 = splitVectorToPairInt(x)

	for r in range(nbRound):
		y1 = CSHR(y1 ^ y0,n,SPECK_BETA)
		tmp = (y0 ^ Lk[nbRound-1-r]) - y1
		while tmp < 0: #Get back to positive values
			tmp += (1 << n)
		y0 = CSHL(tmp&modmask,n,SPECK_ALPHA)

	#Return the two halves (still need the last partial round
	return y0,y1

def speck(x,Lk):
	"""
	With r = len(Lk), apply the Speck round function r times
	"""
	if len(Lk) == 0:
		return splitVectorToPairInt(x)
	global SPECK_ALPHA,SPECK_BETA

	n = len(x)//2
	nbRound = len(Lk)
	modmask = (1 << n) - 1

	#Split the vector into 2 integers
	y0,y1 = splitVectorToPairInt(x)

	for r in range(nbRound):
		y0 = ((CSHR(y0,n,SPECK_ALPHA) + y1)&modmask) ^ Lk[r]
		y1 = y0 ^ CSHL(y1,n,SPECK_BETA)

	return y0,y1



def mergePairIntToInt(x,n):
	"""
	x = [x0,x1] with xi over n bits
	return y = x1x0
	"""
	return x[0] | (x[1] << n)


globalTimeStart = time.time()
totalTimeInOracle = 0

n = 16
N = 2*n

#Number of rounds (starting from the end) on which to recover round keys
#In the case of Speck32/64, we need 4 rounds keys to recover the full master key
#However, this algorithm can be used to just recover all round keys anyway (i.e. it works if all round keys are independent)
#Recovering 5 consecutive round keys allows to uniquely determine the round keys for thee 4 last rounds (because we always get 2 candidates at each round, but one gets filtered out later).
nbRoundToRecover = 5

#Create/Load an oracle without external encodings

#Using cleanOracle to generated a full instance from scratch
# oracle = WBOracle(sharedLibFile=f"white_box_arx{N}_noEE.so",graph_auto_file=f"graph_autom_{N}.sobj", real_quad_encoding_file="quadEncodings.sobj",block_size=N,TRIVIAL_EE=True)

#Using simplifiedOracle to get the instance directly from the precomputed white_box_backend.c
oracle = WBOracle()
print("Oracle loaded")
nbRound = oracle.ROUNDS
modmask = (1 << n) - 1

#Generate a set of plaintexts
#Can be done only once overall
setPlain = set()
epsilon = 10
#We need to consider all deg2 monomials, of which there are N*(N-1)/2 + N
#So we need at least that many plaintexts, + a few more (epsilon) to be safe
while len(setPlain) < (N+((N*(N-1))//2)+epsilon):
	setPlain.add(randint(0,(1 << (2*n))-1))
print("Set generated")

#Convert to deg2 vectors
Lx = [intToVector(x,2*n) for x in setPlain]

#Also split plaintexts into pairs of length n bits
Lplain = []
for x in setPlain:
	Lplain.append([x&modmask, (x >> n)&modmask])


candidateRoundKeys = [[]]
for r in range(nbRound-1):
	#Recover possible keys on round r starting from the first

	#Encrypt over the first r+1 rounds
	tmpTimeStart = time.time()
	Ly = [None for _ in range(len(Lplain))]
	for i in range(len(Lplain)):
		tmp0,tmp1 = Lplain[i]
		tmp0 = (CSHR(tmp0,n,SPECK_ALPHA) + tmp1)&modmask
		y = oracle.partialRoundEnc([tmp0,tmp1],0,r+1)
		y = mergePairIntToInt(y,n)
		Ly[i] = intToDeg2Vector(y,2*n)
	tmpTimeEnd = time.time()
	totalTimeInOracle += (tmpTimeEnd - tmpTimeStart)
	Y = matrix(Ly)
	H = Y.left_kernel().matrix()

	#For each possible round keys candidate found for the (r-1) rounds before
	newCandidateRoundKeys = []
	for roundKeys in candidateRoundKeys:

		#Start with an empty key with no guesses
		currentCandidates = [0]
		#Guess bits two by two, from bits (0,7) up to (6,13)
		#Then only one by one for (7,14) and (8,15) (because 7 & 8 will be guessed already)
		for index in range(9):

			newCandidates = []
			for candidate in currentCandidates:

				#Prepare the key candidates
				#If index < 7, 4 candidates
				listck = []
				if index < 7:
					for guessBase in range(2):
						for guessShift in range(2):
							#Partial round key
							ck = candidate | (guessBase << index) | (guessShift << (index+SPECK_ALPHA))
							listck.append(ck)
				else: # 2 candidates
					for guessShift in range(2):
						ck = candidate | (guessShift << (index+SPECK_ALPHA))
						listck.append(ck)

				for ck in listck:

					Lz = []
					for x in Lx:
						#Apply r rounds
						z0,z1 = speck(x,roundKeys)

						#Apply one more round with the key guess
						z0 = ((CSHR(z0,n,SPECK_ALPHA) + z1)&modmask) ^ ck 
						z1 = z0 ^ CSHL(z1,n,SPECK_BETA)

						#Partially apply one more round to get some non-linearity from modAdd
						z0 = ((CSHR(z0,n,SPECK_ALPHA) + z1)&modmask)

						z0 = intToVector(z0 >> index, 1)
						Lz.append(z0)

					Z = matrix(Lz)
					HZ = H*Z 
					if HZ.is_zero():
						newCandidates.append(ck)

			currentCandidates = list(newCandidates)
			# print(f"len current candidates : {len(currentCandidates)}")

		# At this point, currentCandidates contains all candidate keys for this round
		# print("Round " + str(r) + " :")
		# print("Newly found for this round : " + str(currentCandidates))
		for ck in currentCandidates:
			newCandidateRoundKeys.append(roundKeys + [ck])

	candidateRoundKeys = list(newCandidateRoundKeys)
	print("End of round " + str(r) + ", all candidates")
	for tmp in candidateRoundKeys:
		print(tmp)
	if(len(candidateRoundKeys[0]) == nbRoundToRecover):
		break

globalTimeEnd = time.time()
globalDuration = int(round(globalTimeEnd - globalTimeStart))
totalTimeInOracle = int(round(totalTimeInOracle))
print(f"Total duration : {globalDuration} seconds")
print(f"Total time spent calling the oracle : {totalTimeInOracle} seconds")

#Recover the master key
lk = candidateRoundKeys[0][:4]

def reverseSpeckKS(lk,r):
	"""
	Reverse of Speck32/64 key schedule
	"""
	n = 16
	alpha = 7
	beta = 2
	modmask = (1 << n) - 1

	l = list(lk)
	#init
	def f(x,y,c):
		tmp = CSHL(x,n,beta) ^ y 
		z = tmp ^ c 
		z -= x 
		while z < 0:
			z += (1 << n)
		z &= modmask
		return CSHL(z,n,alpha)

	cst = r-1
	t2 = f(l[2],l[3],cst); cst -= 1
	t1 = f(l[1],l[2],cst); cst -= 1
	t0 = f(l[0],l[1],cst); cst -= 1
	ki = l[0]

	for i in range(r-3):
		ki = CSHR(t2^ki,n,beta)
		tmp = t0
		t0 = (t2^cst) - ki
		cst -= 1
		while t0 < 0:
			t0 += (1 << n)
		t0 &= modmask
		t0 = CSHL(t0,n,alpha)
		t2 = t1
		t1 = tmp
	
	return [ki,t0,t1,t2]

mk = reverseSpeckKS(lk,3)
masterkey = mk[0]
for i in range(1,4):
	masterkey |= (mk[i] << (i*n))

print(f"Recovered master key : {hex(masterkey)}")
