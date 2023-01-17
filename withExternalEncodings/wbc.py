from time import time
from sage.all import *
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix,
    GF, GL,
)
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)
from itertools import combinations, product
from collections import Counter, defaultdict
from maps import FastAffineMap


class SpeckWBC:
    def __init__(self, n, n_rounds):
        self.rounds = [SpeckRound(n)]
        for _ in range(1, n_rounds):
            self.rounds.append(SpeckRound(n, prev=self.rounds[-1]))

        self.n_queries = 0
        self.n = self.rounds[0].n
        self.N = self.rounds[0].N

    def query(self, x: Bin) -> Bin:
        self.n_queries += 1
        for r in self.rounds:
            x = r.query(x)
        return x

    def query_fast(self, x: Bin) -> Bin:
        self.n_queries += 1
        r0 = self.rounds[0]
        rR = self.rounds[-1]
        keys = [r.key for r in self.rounds]

        x = Bin(x, self.N)
        x = x ^ r0.cA
        x = Bin(r0.A * x.vector)
        l, r = x.split(2)

        for k in keys:
            l = l.ror(r0.alpha)
            l += r
            l ^= k
            r = r.rol(r0.beta)
            r ^= l

        y = Bin.concat(l, r)
        y = Bin(rR.B * y.vector) ^ rR.cB
        return y


class SpeckRound:
    def __init__(self, n, prev=None):
        n = self.n = int(n)
        N = self.N = int(2*n)

        if self.n <= 16:
            self.alpha, self.beta = 7, 2
        else:
            self.alpha, self.beta = 8, 3

        if prev is None:
            self.A = GL(2*n, GF(2)).random_element().matrix()
            self.cA = Bin.random(2*n)
        else:
            self.cA = prev.cB
            self.A = ~prev.B
        self.B = GL(2*n, GF(2)).random_element().matrix()
        self.cB = Bin.random(2*n)
        self.key = Bin.random(n)
        self.n_queries = 0

        # DEBUG
        #self.cA = self.cB = Bin(0, 2*n)
        #self.key = Bin(0, n)

        F = []
        for i in range(N):
            l, r = Bin.unit(i, N).split(2)
            r = r.rol(self.beta)
            r ^= l
            l = l.ror(self.alpha)
            F.append(Bin.concat(l, r).vector)
        self.matF = matrix(GF(2), F).transpose()
        self.SPECKLIN = FastAffineMap(matrix=self.matF)

        fullB = []
        for i in range(N):
            x = Bin.unit(i, N)
            l, r = x.split(2)
            r = r.rol(2)
            r ^= l
            y = Bin.concat(l, r)
            y = self.B * y.vector
            fullB.append(y)
        self.fullB = matrix(GF(2), fullB).transpose()

        fullA = []
        for i in range(N):
            x = Bin.unit(i, N)
            x = self.A * x.vector
            l, r = Bin(x).split(2)
            l = l.ror(7)
            y = Bin.concat(l, r)
            y = y.vector
            fullA.append(y)
        self.fullA = matrix(GF(2), fullA).transpose()

    def query(self, x: Bin) -> Bin:
        self.n_queries += 1
        x = Bin(x, self.N)
        x = x ^ self.cA
        x = Bin(self.A * x.vector)
        l, r = x.split(2)

        # speck part, equiv to "permuted add"
        l = l.ror(self.alpha)
        l = l + r
        r = r.rol(self.beta)
        l ^= self.key
        r ^= l

        x = Bin.concat(l, r)
        y = Bin(self.B * x.vector)
        return y ^ self.cB


def modadd(v):
    l, r = v.split(2)
    l += r
    return Bin.concat(l, r)


if __name__ == '__main__':
    n = 32
    WBC = SpeckWBC(n=n, n_rounds=10)
    for i in range(100):
        x = Bin.random(n*2)
        y1 = WBC.query(x)
        y2 = WBC.query_fast(x)
        assert y1 == y2
