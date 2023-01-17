from sage.all import *
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix,
    GF, GL,
)
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)
from itertools import combinations, product
from collections import Counter, defaultdict
from tqdm import tqdm
from time import time


from wbc import SpeckRound
from attack_state import AttackState
from decompose1 import RoundDecomposition


class TwoRoundDecomposition:
    def __init__(self, state_m2: AttackState, state_m1: AttackState, round: SpeckRound):
        self.Sm2 = state_m2
        self.Sm1 = state_m1

        self.M = self.Sm1.projX * self.Sm2.projYi
        self.Mi = ~self.M
        self.F = round.matF
        self.Fi = ~self.F
        self.alpha = round.alpha
        self.beta = round.beta

        self.n = self.Sm1.n
        self.N = self.Sm1.N
        # assert U * M * V == F
        # assert U * M == F * Vi # <<<
        # assert M * V == Ui * F
        # assert M == Ui * F * Vi

    def align_xors(self, Sm2, Sm1):
        n, N = self.n, self.N
        R = RoundDecomposition(n=self.n)
        sols1 = R.recover_constants(Sm1, n_bits=n-1)  # ignore the MSB
        sols2 = R.recover_constants(Sm2, n_bits=n-1)  # ignore the MSB

        # extend with possible MSB flip
        msb = Bin.unit(0, n)
        for a, b, c in list(sols1):
            sols1.add((a ^ msb, b, c ^ msb))
            sols1.add((a ^ msb, b ^ msb, c))
            sols1.add((a, b ^ msb, c ^ msb))
        for a, b, c in list(sols2):
            sols2.add((a ^ msb, b, c ^ msb))
            sols2.add((a ^ msb, b ^ msb, c))
            sols2.add((a, b ^ msb, c ^ msb))

        F = Sm1.projX * ~Sm2.projY
        Fi = ~F
        f1 = self.Fi * Sm1.cX
        for a1, b1, c1 in sols1:
            x1 = Bin.concat(a1, b1).vector
            f2 = self.Fi * x1
            for a2, b2, c2 in sols2:
                y2 = Bin.concat(c2, b2).vector
                #cdiff = (Sm2.cY + y2) + self.Fi * (Sm1.cX + x1)#
                # TODO: can do MitM here
                cdiff = (Sm2.cY + y2) + f1 + f2
                l, r = Bin(cdiff).split(2)
                if r == 0:
                    key = l
                    s2 = Sm2.modified(cY=y2)
                    s1 = Sm1.modified(cX=x1)
                    return s2, s1, key
        raise ValueError("Failed?")

    def recover_middle_linear(self):
        Sm1x = self.Sm1
        Sm2x = self.Sm2
        U, V = self.recover_UV()
        self.U = U
        self.V = V
        assert U * self.M * V == self.F == U * Sm1x.projX * Sm2x.projYi * V

        Sm2, imV = self.propagate_back(Sm2x, V)
        assert Sm2.projX == Sm2x.modified(projX=imV, projY=~V).projX
        assert Sm2.projY == Sm2x.modified(projX=imV, projY=~V).projY

        Sm1, imU = self.propagate_forward(Sm1x, U)
        assert Sm1.projX == Sm1x.modified(projX=U, projY=imU).projX
        assert Sm1.projY == Sm1x.modified(projX=U, projY=imU).projY
        return Sm2, Sm1

    def recover_UV(self):
        n, N = self.n, self.N
        self.init_vars()
        eqs = self.create_system()
        #print("UV system nullity:", eqs[:,:-1].right_nullity())
        sol = eqs[:,:-1].solve_right(eqs.column(-1))

        U = matrix(GF(2), N, N)
        Vi = matrix(GF(2), N, N)
        for i in range(N):
            for j in range(N):
                U[i,j] = self.evaluate(self.getu(i, j), sol)
                Vi[i,j] = self.evaluate(self.getv(i, j), sol)

        V = ~Vi
        assert U * self.M == self.F * Vi
        assert U * self.M * V == self.F
        return U, V

    def evaluate(self, vec, sol):
        if vec == 1:
            return 1
        if vec == 0:
            return 0
        i, = vec.support
        return sol[i]

    def init_vars(self):
        n, N = self.n, self.N

        # variables (unknown entries of the matrix)
        vs = set()
        vs.add((0, 1))
        for i in range(n):
            vs.add((0, n + i))
            vs.add((n, n + i))
        vs.add((n-1, n-1))
        vs.add((n-1, N-1))
        vs.add((N-1, n-1))
        vs.add((N-1, N-1))
        vs.add((0, n-1))
        vs.add((n, n-1))

        vs = {("u", i, j) for i, j in vs} | {("v", i, j) for i, j in vs}

        uvs = {}
        for ind, v in enumerate(vs):
            uvs[v] = ind
        ind = len(uvs)
        mids = list(range(1, n-1)) + list(range(n+1, N-1))

        # repeated variables
        for i in mids:
            uvs[("u", i, n-1)] = ind
        ind += 1
        for i in mids:
            uvs[("u", i, N-1)] = ind
        ind += 1
        for i in mids:
            uvs[("v", i, n-1)] = ind
        ind += 1
        for i in mids:
            uvs[("v", i, N-1)] = ind
        ind += 1

        order = [None] * len(set(uvs.values()))
        for v, i in uvs.items():
            order[i] = v

        vecs = []
        self.const0 = Bin([0] * len(order) + [0])
        self.const1 = Bin([0] * len(order) + [1])
        for i in range(len(order)):
            row = [0] * (len(order) + 1)
            row[i] = GF(2)(1)
            vecs.append(Bin(row))

        self.uvs = uvs
        self.order = order
        self.vecs = vecs

    def get(self, key):
        if key in self.uvs:
            return self.vecs[self.uvs[key]]

        name, i, j = key
        if i == j:
            return self.const1
        if i != j:
            return self.const0
        assert 0

    def show(self, key):
        if key in self.uvs:
            return self.N * 100 + self.uvs[key]
        name, i, j = key
        if i == j:
            return 1
        return 0

    def getu(self, i, j):
        return self.get(("u", i, j))

    def getv(self, i, j):
        return self.get(("v", i, j))

    def create_system(self):
        n, N = self.n, self.N
        eqs = []
        for itr in range(N):
            #  U * My = F * Vi * Mx
            #  U * My * ~Mx * V = F
            Mx = Bin.unit(itr, N)
            My = self.M * Mx.vector

            vcol = [self.getv(j, itr) for j in range(N)]
            l, r = vcol[:n], vcol[n:]

            # compute F on bits (each is represented by a vector)
            r = r[self.beta:] + r[:self.beta]  # rol(beta)
            r = [li ^ ri for li, ri in zip(l, r)]
            l = l[-self.alpha:] + l[:-self.alpha]  # ror(alpha
            Fout = l + r

            Uout = [Bin(0, len(self.order)+1) for i in range(N)]

            for i, My_val in enumerate(My):
                if My_val:
                    ucol = [self.getu(j, i) for j in range(N)]
                    Uout = [li ^ ri for li, ri in zip(Uout, ucol)]

            # Uout = Fout
            for a, b in zip(Fout, Uout):
                eq = a ^ b
                if eq:
                    eqs.append(eq)

        eqs = matrix(GF(2), eqs)
        assert eqs[:,:-1].rank() == eqs.ncols() - 1
        return eqs

    def propagate_back(self, state, V):
        n, N = self.n, self.N
        addlsb = identity_matrix(GF(2), N)
        addlsb[n-1,N-1] = 1
        assert addlsb**2 == 1

        pr = ~V

        stateB = state.modified(projY=pr)

        # step 0: invert the n+1 x n+1 right half map by observing it
        proj = identity_matrix(GF(2), N)

        x = Bin.empty(N)
        base = state.iquery(x)
        for i in range(n-1, N):
            dx = Bin.unit(i, N)
            dy = base ^ stateB.iquery(dx)
            proj[n-1:,i] = dy.vector[n-1:]

        proj = proj * ~addlsb
        proj.subdivide(n,n)
        state0 = stateB.modified(projX=~proj)

        # step 1: fix left lsb to left full word map
        # (separately to msb and to bits 1..n-1)
        proj = identity_matrix(GF(2), N)
        for itr in range(100):
            x = Bin.random(N)
            dx = Bin.concat(1, 0, n=n)
            l, r = (state0.iquery(x) ^ state0.iquery(x ^ dx)).split(2)
            if l.str[1:-1] == "1" * (n-2):
                # todo: can allow here patterns like 11110001
                # (optimization / stabilization, not important)
                proj[1:n-1,n-1] = vector(GF(2), [1]*(n-2))
                proj[0,n-1] = l[0]
                break
            if l.str[1:-1] == "0" * (n-2):
                proj[0,n-1] = l[0]
                break

            #print("skip", l.str)
        else:
            raise "failed, debug"

        state1 = state0.modified(projX=~proj)

        # step 1b: fix RIGHT lsb to left full word map
        # (separately to msb and to bits 1..n-1)
        proj = identity_matrix(GF(2), N)
        for itr in range(100):
            x = Bin.random(N)
            dx = Bin.concat(0, 1, n=n)
            l, r = (state1.iquery(x) ^ state1.iquery(x ^ dx)).split(2)
            if l.str[1:-1] == "1" * (n-2):
                # todo: can allow here patterns like 11110001
                # (optimization / stabilization, not important)
                proj[1:n-1,N-1] = vector(GF(2), [1]*(n-2))
                proj[0,N-1] = l[0]
                break
            if l.str[1:-1] == "0" * (n-2):
                proj[0,N-1] = l[0]
                break

            #print("skip", l.str)
        else:
            raise "failed, debug"

        state1b = state1.modified(projX=proj)

        # step2: fix right msb to left msb (except 2 right msb)
        # dunno: iquery fails, query is ok
        # (related to difference of [-] to [+]?)
        proj = identity_matrix(GF(2), N)
        x0 = Bin.empty(N)
        x1 = Bin.full(N)
        y0 = state1b.query(x0)
        y1 = state1b.query(x1)
        for i in range(2, n):
            l = Bin(0, n)
            r = Bin.unit(i, n)
            dx = Bin.concat(l, r)
            for x, y in [(x0, y0), (x1, y1)]:
                yy = state1b.query(x ^ dx)
                dy = y ^ yy
                l, r = dy.split(2)
                if l[i-1] == 0:
                    break
            else:
                raise
            proj[0,n + i] = l[0]
        state2 = state1b.modified(projX=proj)
        return state2, state2.projX * stateB.projXi

    def propagate_forward(self, state, U):
        n, N = self.n, self.N
        addlsb = identity_matrix(GF(2), N)
        addlsb[n-1,N-1] = 1
        assert addlsb**2 == 1

        pr = U
        stateB = state.modified(projX=pr)
        self.stateB = stateB

        # step 0: invert the n+1 x n+1 right half map by observing it
        proj = identity_matrix(GF(2), N)

        x = Bin.empty(N)
        base = state.query(x)
        for i in range(n-1, N):
            dx = Bin.unit(i, N)
            dy = base ^ stateB.query(dx)
            proj[n-1:,i] = dy.vector[n-1:]

        proj = proj * ~addlsb
        proj.subdivide(n,n)
        state0 = stateB.modified(projY=~proj)
        self.state0 = state0

        # step 1: fix left lsb to left full word map
        # (separately to msb and to bits 1..n-1)
        proj = identity_matrix(GF(2), N)
        for itr in range(100):
            x = Bin.random(N)
            dx = Bin.concat(1, 0, n=n)
            l, r = (state0.query(x) ^ state0.query(x ^ dx)).split(2)
            if l.str[1:-1] == "1" * (n-2):
                # todo: can allow here patterns like 11110001
                # (optimization / stabilization, not important)
                proj[1:n-1,n-1] = vector(GF(2), [1]*(n-2))
                proj[0,n-1] = l[0]
                break
            if l.str[1:-1] == "0" * (n-2):
                proj[0,n-1] = l[0]
                break

            #print("skip", l.str)
        else:
            raise "failed, debug"

        state1 = state0.modified(projY=proj)
        self.state1 = state1

        # step 1b: fix RIGHT lsb to left full word map
        # (separately to msb and to bits 1..n-1)
        proj = identity_matrix(GF(2), N)
        for itr in range(100):
            x = Bin.random(N)
            dx = Bin.concat(0, 1, n=n)
            l, r = (state1.query(x) ^ state1.query(x ^ dx)).split(2)
            if l.str[1:-1] == "1" * (n-2):
                # todo: can allow here patterns like 11110001
                # (optimization / stabilization, not important)
                proj[1:n-1,N-1] = vector(GF(2), [1]*(n-2))
                proj[0,N-1] = l[0]
                break
            if l.str[1:-1] == "0" * (n-2):
                proj[0,N-1] = l[0]
                break

            #print("skip", l.str)
        else:
            raise "failed, debug"

        state1b = state1.modified(projY=proj)
        self.state1b = state1b

        # step2: fix right msb to left msb (except 2 right msb)
        proj = identity_matrix(GF(2), N)
        x0 = Bin.empty(N)
        x1 = Bin.full(N)
        y0 = state1b.query(x0)
        y1 = state1b.query(x1)
        for i in range(2, n):
            l = Bin(0, n)
            r = Bin.unit(i, n)
            dx = Bin.concat(l, r)
            for x, y in [(x0, y0), (x1, y1)]:
                yy = state1b.query(x ^ dx)
                dy = y ^ yy
                l, r = dy.split(2)
                if l[i-1] == 0:
                    break
            else:
                raise
            proj[0,n + i] = l[0]
        state2 = state1b.modified(projY=proj)
        return state2, state2.projY * stateB.projYi
