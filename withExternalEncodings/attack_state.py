from sage.all import *
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix,
    GF, GL,
    BooleanPolynomialRing, copy,
)
from random import choice
from itertools import product, combinations
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)

from maps import AffineMap, FastAffineMap
from inversion import SystemInverse

class DecompositionFail(Exception):
    pass


class AttackState:
    """Abstraction for oracle with transparent affine encodings.
    Also useful query variants."""
    RANDOM_POOL = 777

    def __init__(
        self, n, oracle,
        ioracle=None,
        projX=None, cX=None,
        projY=None, cY=None,
        decomposed_mapX=None,
        decomposed_mapY=None,
    ):
        self.n = int(n)
        N = self.N = 2*self.n
        self.system = None

        if projX is None:
            projX = identity_matrix(GF(2), N)
        if projY is None:
            projY = identity_matrix(GF(2), N)
        if cX is None:
            cX = vector(GF(2), N)
        if cY is None:
            cY = vector(GF(2), N)

        self.oracle = oracle
        self.ioracle = ioracle

        # outer repr of constnats
        self.cX, self.cY = Bin(cX, N).vector, Bin(cY, N).vector

        self.projX, self.projY = projX, projY
        self.projXi = ~projX
        self.projYi = ~projY

        # inner repr of constnats
        self.cXin = self.projXi * self.cX
        self.cYin = self.projYi * self.cY

        self.mapX = FastAffineMap(matrix=self.projX, const_out=self.cX)
        self.mapY = FastAffineMap(matrix=self.projY, const_out=self.cY)

        self.pool = []
        self.decomposed_mapX = decomposed_mapX
        self.decomposed_mapY = decomposed_mapY
        if self.decomposed_mapX:
            self.decomposed_mapXi = ~decomposed_mapX
            self.decomposed_mapYi = ~decomposed_mapY
            self.check_decomposed()


    def check_decomposed(self):
        for _ in range(16):
            x = Bin.random(self.N)
            y = self.query_decomposed(x)
            yy = self.query(x)
            xx = self.iquery_decomposed(y)
            assert y == yy
            assert x == xx

    def query_decomposed(self, x):
        t = self.decomposed_mapX.iquery(x)
        l, r = t.split(2)
        l += r
        t = Bin.concat(l, r)
        y = self.decomposed_mapY.query(t)
        return y

    def iquery_decomposed(self, y):
        t = self.decomposed_mapY.iquery(y)
        l, r = t.split(2)
        l = Bin( (l.int - r.int) % 2**l.n, l.n)
        t = Bin.concat(l, r)
        x = self.decomposed_mapX.query(t)
        assert self.query(x) == y
        return x

    def mark_decomposed(self):
        self.decomposed_mapX = AffineMap.id(self.N)
        self.decomposed_mapY = AffineMap.id(self.N)
        self.check_decomposed()

    def modified(self, projX=None, cX=None, projY=None, cY=None, decomposed_mapX=None, decomposed_mapY=None):
        N = self.N
        if projX is None:
            projX = identity_matrix(GF(2), N)
        if projY is None:
            projY = identity_matrix(GF(2), N)
        if cX is None:
            cX = vector(GF(2), N)
        if cY is None:
            cY = vector(GF(2), N)

        if self.decomposed_mapX:
            dec_projX = AffineMap(projX, const_out=cX) * self.decomposed_mapX
            dec_projY = AffineMap(projY, const_out=cY) * self.decomposed_mapY
        else:
            dec_projX = None
            dec_projY = None

        # compose proj+const with current ones
        # AA(A+b)+bb = AA*A + (AA*b + bb)
        if self.system and self.system.can_query:
            return type(self)(
                n = self.n,
                oracle = self.system.fast_query,
                ioracle = self.system.fast_iquery,
                projX = projX,
                cX = Bin(cX).vector,
                projY = projY,
                cY = Bin(cY).vector,
            )
        else:
            return type(self)(
                n = self.n,
                oracle = self.oracle,
                projX = projX * self.projX,
                cX = projX * self.cX + Bin(cX).vector,
                projY = projY * self.projY,
                cY = projY * self.cY + Bin(cY).vector,
                decomposed_mapX = dec_projX,
                decomposed_mapY = dec_projY,
            )

    def sample(self, num=999999999):
        while num and len(self.pool) < self.RANDOM_POOL:
            x = Bin.random(self.N)
            y = self.query(x)
            self.pool.append((x, y))
            yield self.pool[-1]
            num -= 1
        while num:
            yield choice(self.pool)
            num -= 1

    def query(self, x):
        if self.system and self.system.can_query:
            return self.system.fast_query(x)
        v = Bin(x, self.N)

        v = self.mapX.iquery(v)
        v = self.oracle(v)
        v = self.mapY.query(v)
        return v

        # inverse of (projX*z + cX)
        x = self.projXi * (x.vector + self.cX)
        y = self.oracle(Bin(x))
        y = self.projY * y.vector + self.cY
        return Bin(y)

    def query_lr(self, l, r):
        n = self.n
        return self.query(Bin.concat(l, r, ns=(n-1,n+1))).split(ns=(n-1,n+1))

    def query_diff(self, dx):
        (x1, y1), = self.sample(1)
        # x1 = Bin.random(self.N)
        # y1 = self.query(x1)
        x2 = x1 ^ Bin(dx, self.N)
        y2 = self.query(x2)
        return y1 ^ y2

    def query_diff_lr(self, l, r):
        n = self.n
        return self.query_diff(Bin.concat(l, r, ns=(n-1,n+1))).split(ns=(n-1,n+1))

    def precompute_inverse(self, **kwargs):
        self.system = SystemInverse(n=self.n, oracle=self.query, **kwargs)

    def iquery(self, y, check=True, ensure_unique=True):
        if self.system and self.system.can_iquery:
            return self.system.fast_iquery(y)

        if self.ioracle:
            v = Bin(y, self.N)
            v = self.mapY.iquery(v)
            v = self.ioracle(v)
            v = self.mapX.query(v)
            return v

        if self.decomposed_mapX:
            return self.iquery_decomposed(y)

        if self.system:
            #y = self.projYi * (Bin(y, N).vector + self.cY)
            #x = self._iquery_using_equations(Bin(y), check=check)
            x = self.system.invert(Bin(y, self.N), ensure_unique=ensure_unique)
            if check:
                assert self.query(x) == y
            #x = self.projX * x.vector + self.cX
            return Bin(x)

        raise NotImplementedError()

    def randomized(self):
        assert self.decomposed_mapX is None
        return self.modified(
            projX=AffineMap.random(self.N).matrix,
            projY=AffineMap.random(self.N).matrix,
            cX=Bin.random(self.N).vector,
            cY=Bin.random(self.N).vector,
        )

    def fasten(self):
        if not self.system:
            self.precompute_inverse()
        if not self.system.can_query:
            self.system.precompute_fast_oracle(inverse=False)
        if not self.system.can_iquery:
            self.system.precompute_fast_oracle(inverse=True)


if __name__ == '__main__':
    def query(x):
        l, r = x.split(2)
        l += r
        return Bin.concat(l, r)


    n = 16
    N = 2*n
    st = AttackState(n=n, oracle=query)
    st.mark_decomposed()
    projX = GL(N, GF(2)).random_element().matrix()
    projY = GL(N, GF(2)).random_element().matrix()
    cX = random_vector(GF(2), N)
    cY = random_vector(GF(2), N)
    st2 = st.modified(projX=projX, cX=cX, projY=projY, cY=cY)
