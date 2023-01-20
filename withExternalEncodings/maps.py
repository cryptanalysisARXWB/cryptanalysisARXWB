from sage.all import *
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix,
    GF, GL,
)
from random import choice
from itertools import product
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)


class AffineMap:
    @classmethod
    def id(cls, n):
        return cls(matrix=identity_matrix(GF(2), n))

    @classmethod
    def random(cls, n):
        return cls(matrix=GL(n, GF(2)).random_element().matrix(), const_in=random_vector(GF(2), n))

    def __init__(self, matrix=None, const_in=None, const_out=None):
        assert matrix or const_in or const_out
        if matrix is not None:
            self.n = matrix.nrows()
        if const_in is not None:
            self.n = len(const_in)
        if const_out is not None:
            self.n = len(const_out)

        if matrix is None:
            matrix = identity_matrix(GF(2), self.n)
        if const_in is None:
            const_in = vector(GF(2), self.n)
        if const_out is None:
            const_out = vector(GF(2), self.n)

        self.matrix = matrix
        self.imatrix = ~matrix
        self.full_const_out = const_out + matrix * const_in
        self.full_const_in = self.imatrix * const_out

    def __mul__(self, other):
        assert isinstance(other, AffineMap)
        return type(self)(
            matrix=self.matrix * other.matrix,
            const_out=self.full_const_out + self.matrix * other.full_const_out,
        )

    def query(self, vec):
        if isinstance(vec, (int, Bin)):
            vec = Bin(vec, self.n).vector
        else:
            vec = vector(GF(2), vec)

        y = self.matrix * vec + self.full_const_out
        return Bin(y)

    def iquery(self, vec):
        if isinstance(vec, (int, Bin)):
            vec = Bin(vec, self.n).vector
        else:
            vec = vector(GF(2), vec)

        y = self.imatrix * (vec + self.full_const_out)
        return Bin(y)

    def __invert__(self):
        return type(self)(matrix=self.imatrix, const_in=self.full_const_out)

    def fasten(self, **kwargs):
        return FastAffineMap(matrix=self.matrix, const_out=self.full_const_out, **kwargs)


class FastAffineMap(AffineMap):
    def __init__(self, *args, block_size=4, **kwargs):
        super().__init__(*args, **kwargs)
        self.block_size = int(block_size)
        self.mask = 2**self.block_size - 1
        self.n_blocks = int(self.n // self.block_size)
        assert self.n == self.n_blocks * self.block_size

        self._matrix_data = self._precompute_matrix(self.matrix)
        self._imatrix_data = self._precompute_matrix(self.imatrix)
        self._const_out = Bin(self.full_const_out, self.n)

    def query(self, x):
        # if not isinstance(x, Bin):
        #     x = Bin(x, self.n)
        x = int(x)
        return self._query_matrix(x, self._matrix_data) ^ self._const_out

    def iquery(self, y):
        # if not isinstance(y, Bin):
        #     y = Bin(y, self.n)
        y = int(y)
        return self._query_matrix(y ^ self._const_out.int, self._imatrix_data)

    def _precompute_matrix(self, mat):
        data = []
        if self.block_size > 8:
            matmap = FastAffineMap(matrix=mat, block_size=4)
            for i in range(self.n_blocks):
                cur = []
                for x in Bin.iter(self.block_size):
                    x = x.resize(self.n) << (i*self.block_size)
                    y = Bin(matmap.query(x))
                    cur.append(y.int)
                data.append(cur)
        else:
            for i in range(self.n_blocks):
                cur = []
                shift = i * self.block_size
                for x in range(2**self.block_size):
                    x <<= shift
                    y = Bin(mat * Bin(x, self.n).vector)
                # for x in Bin.iter(self.block_size):
                #     x = x.resize(self.n) << (i*self.block_size)
                #     y = Bin(mat * x.vector)
                    cur.append(y.int)
                data.append(cur)
        return data

    def _query_matrix(self, x, data):
        x = int(x)
        y = 0
        for row in data:
            y ^= row[x & self.mask]
            x >>= self.block_size
        return Bin(y, self.n)
