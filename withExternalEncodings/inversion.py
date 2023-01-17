import sys
from random import choice, randrange
from itertools import product, combinations
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix,
    GF, GL, prod,
    BooleanPolynomialRing, copy,
    Combinations,
)

from ctypes import (
    CDLL, Structure, POINTER, pointer,
    c_int32,
    c_uint32,
    c_uint64,
)
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)

FIlib = CDLL("./fast_implicit.so")

# uint32_t solve32(uint32_t y, uint64_t* MS, int block_size, int n_rows)
FIlib.solve32.restype = c_uint32
FIlib.solve32.argtypes = (
    c_uint32,
    POINTER(c_uint64),
    POINTER(c_uint64),
    c_int32,
    c_int32,
)
MASK64 = 2**64-1

class c_uint128(Structure):
    _fields_ = [
        ("lo", c_uint64),
        ("hi", c_uint64)
    ]

    def __init__(self, x: int):
        super().__init__(lo=x & MASK64, hi=(x >> 64) & MASK64)

    def __int__(self):
        return int(self.lo) | (int(self.hi) << 64)

class c_uint256(Structure):
    _fields_ = [
        ("v0", c_uint64),
        ("v1", c_uint64),
        ("v2", c_uint64),
        ("v3", c_uint64),
    ]

    def __init__(self, x: int):
        super().__init__(
            v0=x & MASK64,
            v1=(x >> 64) & MASK64,
            v2=(x >> 128) & MASK64,
            v3=(x >> 192) & MASK64,
        )

    def __int__(self):
        return (
            int(self.v0)
            | (int(self.v1) << 64)
            | (int(self.v2) << 128)
            | (int(self.v3) << 192)
        )

FIlib.solve64.restype = c_uint64
FIlib.solve64.argtypes = (
    c_uint64,
    POINTER(c_uint128),
    POINTER(c_uint128),
    c_int32,
    c_int32,
)

FIlib.solve128.restype = c_uint128
FIlib.solve128.argtypes = (
    c_uint128,
    POINTER(c_uint256),
    POINTER(c_uint256),
    c_int32,
    c_int32,
)


class Monomial:
    def __init__(self, x=(), y=()):
        self.x = tuple(map(int, x))
        self.y = tuple(map(int, y))
        self.xy = self.x + self.y

    def __iter__(self):
        return iter(self.xy)

    def __str__(self):
        lst = ["x%d" % i for i in self.x]
        lst += ["y%d" % i for i in self.y]
        return "*".join(lst)

    __repr__ = __str__


class SystemInverse:
    def __init__(self, n, oracle, filter_x=None, quad_basis_indexes=(), nlin=0, xxy=True, extra_xmonos=()):
        quad_basis_indexes = sorted(quad_basis_indexes)
        n = self.n = int(n)
        N = self.N = self.n * 2
        self.oracle = oracle
        slin = N-nlin

        print("Precomputing inverse system... n =", n)

        monos = []
        monos += [Monomial()] # const 1
        monos += [Monomial(x=(i,)) for i in range(N)]  # linear X terms
        monos += [Monomial(y=(i,)) for i in range(N)]  # linear Y terms

        # normal cross terms
        for i in range(N):
            for j in range(N):
                # avoid relations xi yj = xj yi  when xi=yi (linear part)
                # if i >= slin and j >= slin:
                #     if j <= i:
                #         continue
                monos.append(
                    Monomial(x=(i,), y=(j,))
                )

        # xi xj yk
        if xxy:
            monos += [
                Monomial(x=(i, j), y=(k,))
                for i, j in combinations(quad_basis_indexes, 2)
                for k in range(N)
            ]

        # if quad_ext:
        #     # xi xj xk x...
        #     monos += [
        #         Monomial(x=mono)
        #         for mono in Combinations(quad_basis_indexes)
        #         if len(mono) >= 2
        #     ]
        # xi xj
        monos += [
            Monomial(x=(i, j))
            for i, j in combinations(quad_basis_indexes, 2)
        ]
        # extra xxx
        monos += [
            Monomial(x=mono)
            for mono in extra_xmonos
        ]

        self.monos = monos

        # stable uniq
        seen = set()
        self.xmonos = []
        for mono in self.monos:
            if mono.x not in seen:
                seen.add(mono.x)
                self.xmonos.append(mono.x)
        self.xmonos2i = {mono: i for i, mono in enumerate(self.xmonos)}
        print(f"  {len(monos)} monomials, {len(self.xmonos)} x-monomials")

        rows = []
        while len(rows) < len(monos) + 50:
            xo = x = Bin.random(self.N)
            if filter_x:
                xo = filter_x(x)
                if xo is True:
                    xo = x
                if xo is None or xo is False:
                    continue
            y = self.oracle(x)

            valx = xo
            valy = y

            row = []
            for mono in monos:
                res = 1
                for j in mono.x:
                    res &= valx[j]
                for j in mono.y:
                    res &= valy[j]
                row.append(res)
            rows.append(row)

        mat = matrix(GF(2), rows)
        rk = mat.right_kernel()
        # TODO: can sample a smaller subset of equations
        rkm = rk.matrix()

        self.system = list(rkm)
        print(f"  {len(self.system)} equations")

        self.can_query = False
        self.can_iquery = False

    def invert(self, y, ensure_unique=True):
        N = self.N
        rows = []
        for eq in self.system:
            row = vector(GF(2), len(self.xmonos))
            for mono, take in zip(self.monos, eq):
                if take:
                    row[self.xmonos2i[mono.x]] += prod(y[i] for i in mono.y)
            rows.append(row)

        mat = matrix(GF(2), rows)
        # for debugging
        self._inv_mat = mat
        self._target_y = y
        #print(mat.nrows(), mat.ncols(), mat.rank())
        assert mat.right_nullity() >= 1, \
            ("no solutions, rank %d / %d" % (mat.rank(), mat.ncols()))
        # if mat.right_nullity() > 1:
        #     print("warning: more solutions than expected? :( rank %d / %d" % (mat.rank(), mat.ncols()))
        #assert mat.rank() == N, \
        x = None
        for row in mat.right_kernel().matrix():
            if row[0] == 1:
                x2 = Bin([row[self.xmonos2i[(i,)]] for i in range(N)])
                if ensure_unique:
                    if x is not None and x != x2:
                        assert 0, "non-unique solution"
                    x = x2
                else:
                    x = x2
                    break
        if x is None:
            assert 0, ("no solution, rank %d / %d" % (mat.rank(), mat.ncols()))
        return x

    def precompute_fast_oracles(self, block_size=4, n_rows_max=None):
        print("PRECOMPUTE FAST ORACLES")
        pool = []
        for i in range(10):
            x = Bin.random(self.N)
            y = self.oracle(x)
            pool.append((x, y))
        self.precompute_fast_oracle(block_size=block_size, n_rows_max=n_rows_max, inverse=False)
        self.precompute_fast_oracle(block_size=block_size, n_rows_max=n_rows_max, inverse=True)
        for x, y in pool:
            xx = self.fast_iquery(y)
            yy = self.fast_query(x)
            assert y == yy
            assert x == xx

    def precompute_fast_oracle(self, block_size=4, n_rows_max=None, inverse=False):
        if n_rows_max is None:
            n_rows_max = self.N + 32
        n_rows = min(n_rows_max, len(self.system))
        mats = [[0] * n_rows for _ in range(self.N)]
        base_mat = [0] * n_rows
        assert self.N in (32, 64, 128)
        # each row is stored as N-bit row + N-bit reserved for 1 bit constant (for alignment..)
        while True:
            Q = random_matrix(GF(2), n_rows, len(self.system))
            if Q.rank() == n_rows:
                break

        for ieq, eq in enumerate(Q * matrix(self.system)):
            if ieq >= n_rows:
                break
            for mono, take in zip(self.monos, eq):
                if take:
                    if inverse:
                        mx, my = mono.x, mono.y
                    else:
                        my, mx = mono.x, mono.y

                    if mx and my:
                        xi, = mx
                        yi, = my
                        mats[yi][ieq] ^= 1 << (2*self.N-1 - xi)
                    elif mx and not my:
                        # xi
                        xi, = mx
                        base_mat[ieq] ^= 1 << (2*self.N-1 - xi)
                    elif my and not mx:
                        # yi
                        yi, = my
                        mats[yi][ieq] ^= 1
                    elif not mx and not my:
                        # const
                        base_mat[ieq] ^= 1
                    else:
                        raise ValueError(f"mono {mono}")

        MS = []
        for i in range(self.N//block_size):
            # batch = []
            sub = mats[-(i+1)*block_size:len(mats)-i*block_size]
            for y in Bin.iter(block_size):
                res = [0] * n_rows
                for mat, take in zip(sub, y):
                    if take:
                        res = [a ^ b for a, b in zip(res, mat)]
                #batch.append(res)
                MS.extend(res)
            # for v in res:
            #     print(Bin(v, 64).hex)
            # print()

        if self.N == 32:
            func = FIlib.solve32
            row_type = c_uint64
            int_type = c_uint32
            MSc = (row_type * len(MS))(*MS)
            base_matc = (row_type * len(base_mat))(*base_mat)
        elif self.N == 64:
            func = FIlib.solve64
            row_type = c_uint128
            int_type = c_uint64
            MSc = (row_type * len(MS))(*map(c_uint128, MS))
            base_matc = (row_type * len(MS))(*map(c_uint128, base_mat))
        elif self.N == 128:
            func = FIlib.solve128
            row_type = c_uint256
            int_type = c_uint128
            MSc = (row_type * len(MS))(*map(c_uint256, MS))
            base_matc = (row_type * len(MS))(*map(c_uint256, base_mat))
        else:
            raise

        if inverse:
            self.bk_n_rows = n_rows
            self.bk_block_size = block_size
            self.bk_MSc = MSc
            self.bk_base_mat = base_matc
            self.can_iquery = True
            y = 0x11223344aabbccdd % 2**self.N
            x = int(func(
                int_type(y),
                self.bk_base_mat,
                self.bk_MSc,
                self.bk_block_size,
                self.bk_n_rows,
            ))
            assert self.oracle(x) == y
        else:
            self.fw_n_rows = n_rows
            self.fw_block_size = block_size
            self.fw_MSc = MSc
            self.fw_base_mat = base_matc
            self.can_query = True
            x = 0x11223344aabbccdd % 2**self.N
            y = int(func(
                int_type(x),
                self.fw_base_mat,
                self.fw_MSc,
                self.fw_block_size,
                self.fw_n_rows,
            ))
            assert self.oracle(x) == y
        return

    def fast_iquery(self, y):
        if not self.bk_n_rows:
            self.can_query = False
            self.can_iquery = False
            self.precompute_fast_oracles()

        if self.N == 32:
            func = FIlib.solve32
            int_type = c_uint32
            row_type = c_uint64
        elif self.N == 64:
            func = FIlib.solve64
            int_type = c_uint64
            row_type = c_uint128
        elif self.N == 128:
            func = FIlib.solve128
            int_type = c_uint128
            row_type = c_uint256

        return Bin(int(func(
            int_type(int(y)),
            POINTER(row_type)(self.bk_base_mat),
            POINTER(row_type)(self.bk_MSc),
            self.bk_block_size,
            self.bk_n_rows,
        )), self.N)

    def fast_query(self, x):
        if not self.fw_n_rows:
            self.can_query = False
            self.can_iquery = False
            self.precompute_fast_oracles()

        if self.N == 32:
            func = FIlib.solve32
            int_type = c_uint32
            row_type = c_uint64
        elif self.N == 64:
            func = FIlib.solve64
            int_type = c_uint64
            row_type = c_uint128
        elif self.N == 128:
            func = FIlib.solve128
            int_type = c_uint128
            row_type = c_uint256

        return Bin(int(func(
            int_type(int(x)),
            POINTER(row_type)(self.fw_base_mat),
            POINTER(row_type)(self.fw_MSc),
            self.fw_block_size,
            self.fw_n_rows,
        )), self.N)

    def __getstate__(self):
        d = self.__dict__.copy()
        # words = "bk_base_mat bk_MSc bk_block_size bk_n_rows fw_base_mat fw_MSc fw_block_size fw_n_rows"
        words = "bk_base_mat bk_MSc fw_base_mat fw_MSc"
        for w in words.split():
            if w in d:
                d[w] = list(d[w])
        return d

    def __setstate__(self, d):
        self.__dict__ = d.copy()
        words = "bk_base_mat bk_MSc fw_base_mat fw_MSc"
        for w in words.split():
            if w in d:
                if self.N == 32:
                    self.__dict__[w] = (c_uint64 * len(d[w]))(*d[w])
                elif self.N == 64:
                    self.__dict__[w] = (c_uint128 * len(d[w]))(*d[w])
                elif self.N == 128:
                    self.__dict__[w] = (c_uint256 * len(d[w]))(*d[w])
                else:
                    raise NotImplementedError()

