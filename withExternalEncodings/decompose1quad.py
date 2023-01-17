from sage.all import (
    prod,
    vector, random_vector,
    random_matrix, identity_matrix, matrix, block_matrix,
    GF, GL, ZZ,
    copy, Combinations,
    BooleanPolynomialRing,
)
from copy import deepcopy
from random import choice, randrange, shuffle
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)
from itertools import combinations, product
from collections import Counter, defaultdict
from tqdm import tqdm
from time import time

from attack_state import AttackState, DecompositionFail
from maps import AffineMap
from decompose1 import RoundDecomposition


class QuadDecomposition:
    class UnsolvableError(DecompositionFail):
        pass

    class UnsolvableQ(UnsolvableError):
        pass

    class UnsolvableConst(UnsolvableError):
        pass

    class RefreshFailed(DecompositionFail):
        pass

    def __init__(self, n, state=None):
        self.n = int(n)
        self.N = 2*self.n

        self.state0 = self.state = state
        self.R = RoundDecomposition(self.n)

        self.quad_part = None
        self.preinverted_system = None
        self.affine_state = None
        self.quad_parts_seen = set()
        self.sQi = None

    def recover_all(self, state=None, n_consts=4):
        if state:
            self.state = state
        assert self.state, "state must be given"
        self.state = self.state.randomized()

        self.quad_part = None
        self.preinverted_system = None
        self.sQi = sQi = self.simplify_quadratics(state=self.state)

        try:
            self.prepare_inversion(state=sQi)
            self.recover_Q(state=sQi)
            self.invert_Q()
        except AssertionError as err:
            print("Q recovery failed:", err)
            raise self.UnsolvableQ("failed Q attempt")

        self.affine_state = self.make_affine_state()
        return self.affine_state

    def refresh_solution(self):
        sQi = self.sQi
        print("Refresh solution")
        self.prepare_inversion(state=sQi)
        self.recover_Q(state=sQi)
        self.invert_Q()

        self.affine_state = self.make_affine_state()
        return self.affine_state

    def simplify_quadratics(self, state=None):
        n, N = self.n, self.N
        if state:
            self.state = state

        self.s0 = self.state

        self.preinverted_system = None

        self.nlin, rels, self.s1 = self.R.recover_right_branch_space(state=self.s0)
        print("affine bits:", self.nlin)

        self.nquad, outrel, self.s2 = self.R.recover_outputs_by_degree(
            deg=2, state=self.s1, skip_last=self.nlin,
        )
        print("quadratic bits:", self.nquad)
        #print(outrel)
        print()

        names = (
            ["l%d"%i for i in range(N-self.nlin)][::-1]
            + ["r%d" % i for i in range(self.nlin)][::-1]
        )
        self.quad_indexes = list(range(N-self.nlin-self.nquad, N-self.nlin))
        self.anfs1 = anfs = self.recover_quadratic_ANF(self.quad_indexes, names, state=self.s2)
        print("quad ANFs:", end=" ")
        for i, a in anfs.items():
            print(len(a), "terms", end="; ")
        print()

        results1, results2 = self.recover_linear_structures_in_output_combinations(anfs)
        self.xrows, self.yrows = self.select_sparse_quadratics(results1, results2, nlin=self.nlin)
        print(len(self.xrows), "invoved input bits,", len(self.yrows), "output bits")
        print()

        proj = self.R.ext_matrix_extract_left(matrix(GF(2), self.yrows), self.nlin)
        self.s2m = self.s2.modified(projY=proj)

        pivots = matrix(GF(2), self.xrows).pivot_rows()
        pivot_xrows = [self.xrows[i] for i in pivots]

        ind_rows = matrix(GF(2), pivot_xrows).solve_left(matrix(GF(2), self.xrows))
        z1 = matrix(GF(2), ind_rows.nrows(), N-self.nlin-ind_rows.ncols())
        z2 = matrix(GF(2), ind_rows.nrows(), self.nlin)
        ind_rows = z1.augment(ind_rows).augment(z2)
        ind_rows = list(ind_rows)

        proj = self.R.ext_matrix_extract_left(matrix(GF(2), pivot_xrows), n_after=self.nlin)
        self.s3a = self.s2m.modified(projX=proj)

        pairs = []
        assert len(ind_rows) % 2 == 0, "pairs?"
        for i in range(0, len(ind_rows), 2):
            pairs.append((Bin(ind_rows[i]), Bin(ind_rows[i+1])))

        self.sQi = self.s3a.modified()
        if 0:
            # TODO: reuse previous ANF instead of queries
            names = (
                ["l%d"%i for i in range(N-self.nlin)][::-1]
                + ["r%d" % i for i in range(self.nlin)][::-1]
            )
            indexes = list(range(N-self.nlin-self.nquad, N-self.nlin))
            anfs3 = self.recover_quadratic_ANF(indexes, names, state=self.s3a)
            print("ANF3")
            for i, a in anfs3.items():
                print(a)
                print()


            state = self.s3a
            # B = list(anfs.values())[0].parent()
            indexes = list(anfs3)
            proj = lambda v: Bin([v[i] for i in indexes])
            zero = proj(state.query(Bin.empty(N)))
            rows = [[0] * N for i in indexes]
            cy = [0] * N
            for e in range(len(indexes)):
                if zero[e]:
                    cy[indexes[e]] = 1
            for i in range(N):
                v = proj(state.query(Bin.unit(i, N)))
                v ^= zero
                for e in range(len(indexes)):
                    if v[e]:
                        rows[e][i] = 1
            for row in rows:
                print(row)
            print()

            # proj = self.R.ext_matrix_extract_left(
            #     matrix(GF(2), rows), self.nlin + len(self.xrows)
            # )
            # self.s3 = self.s3a.modified(projX=proj, cY=Bin(cy))

            # names = (
            #     ["l%d"%i for i in range(N-self.nlin)][::-1]
            #     + ["r%d" % i for i in range(self.nlin)][::-1]
            # )
            # indexes = list(range(N-self.nlin-self.nquad, N-self.nlin))
            # just for showing / debug
            # anfs3new = self.recover_quadratic_ANF(indexes, names, state=self.s3)
            # print("ANF3 new")
            # for i, a in anfs3new.items():
            #     print(a)
            #     print()
            self.sQi = self.s3.modified()


        self.pairs = pairs
        print(len(pairs), "pairs of inputs (monomials)")
        for a, b in pairs:
            print(a.support, b.support)
        print()

        self.quad_basis = []
        for a, b in pairs:
            self.quad_basis.extend(a.support)
            self.quad_basis.extend(b.support)
        self.quad_basis = sorted(set(self.quad_basis))
        self.T = len(self.quad_basis)
        print(f"T={self.T}, quad_basis={self.quad_basis}")
        self.state = self.sQi
        return self.sQi

    def prepare_inversion(self, state=None):
        n, N = self.n, self.N
        if state:
            self.state = state

        def filter_quad_inactive(x):
            return sum(x[i] for i in self.quad_basis) <= 1
            # nonlocal self
            # for a, b in self.pairs:
            #     va = (x & a).parity
            #     vb = (x & b).parity
            #     vab = (x & (a & b)).parity
            #     if (va & vb) ^ vab == 1:
            #         return False
            # return True

        sQi = self.state

        if self.preinverted_system is None:
            sQi.precompute_inverse(filter_x=filter_quad_inactive)
            #print("made system", sQi.system)
            self.preinverted_system = copy(sQi.system), sQi.system.system[:]
        else:
            system, eqs = self.preinverted_system
            sQi.system = copy(system)
            sQi.system.oracle = sQi.query
            sQi.system.system = eqs
            sQi.system.can_iquery = False
            sQi.system.can_query = False
            #print("start with", len(eqs), "eqs")
            #print("sQi", sQi, "sys", sQi.system)

        for v in Bin.iter(self.T):
            if v.wt > 2:
                continue

            x = v.resize(N) << self.nlin
            try:
                sQi.iquery(sQi.query(x), check=False)
                #print("iquery", v, "ok")
                continue
            except AssertionError as err:
                print("value mismatch for", v, v.wt, "exception:", err)
                assert v.wt == 2, "v.wt != 2?"

            rows = []

            eqs = sQi.system.system

            is_ok = False
            for i in range(25):
                x = v.resize(N) << self.nlin
                x = x ^ Bin.random(self.nlin).resize(N)
                x = x ^ (Bin.random(N-self.nlin-self.T).resize(N) << (self.nlin+self.T))

                y = sQi.query(x)
                try:
                    sQi.iquery(y, check=False)
                    is_ok = True
                    break
                except AssertionError:
                    pass

                for ieq, eq in enumerate(eqs):
                    assert len(sQi.system.xmonos) == 1 + N, "xmonos len?"
                    row = vector(GF(2), len(sQi.system.xmonos) + len(eqs))
                    for mono, take in zip(sQi.system.monos, eq):
                        if not take:
                            continue
                        row[sQi.system.xmonos2i[mono.x]] += prod(y[i] for i in mono.y)
                    row[0] += row[1:1+N] * x.vector
                    row[N + 1 + ieq] = 1
                    rows.append(row)

            if is_ok:
                print(v, "is now ok")
                assert i == 0, "i != 0 is now ok"
                continue

            mat = matrix(GF(2), rows)
            print(v, mat.nrows(), mat.ncols(), mat.rank())
            if mat.right_nullity() <= 2:
                res = []
                for sol in sorted(mat.right_kernel()):
                    if not sol:
                        continue
                    if sol[0]:
                        print(sol[0], Bin(sol[1:1+N]), Bin(sol[N+1:]).support)
                        res.append(sol)

                        if sol[1:1+N] == 0:
                            print("empty sol is ok")
                            # always choose not to do anything if possible?
                            res = [sol]
                            break
                if res:
                    res = choice(res)
                    sol = Bin(res[N+1:]).support
                    print("GOOD, CORRECTING EQUATION", sol)
                    assert any(res[N+1:]), "should have been ok? nothing to correct"
                    eqs2 = list(sQi.system.system)
                    one = eqs[sol[0]]
                    for i in sol:
                        eqs2[i] += one
                    sQi.system.system = list(matrix(eqs2).row_space().matrix())
                    print(len(sQi.system.system), "rows (new number)")
                else:
                    #print("strange: no sols / one error equation")
                    raise self.UnsolvableQ("no sols")
            else:
                print("strange: too many sols / one error equation")
            print()

        if N == 32:
            assert len(sQi.system.system) == 187, len(sQi.system.system)
        if N == 64:
            assert len(sQi.system.system) == 627, len(sQi.system.system)

        # quick sanity test
        for i in range(30):
            xsec = Bin.random(N)
            x = sQi.iquery(sQi.query(xsec), check=False)

    def recover_Q(self, state=None):
        if state:
            self.state = state

        n, N = self.n, self.N
        sQi = state
        def qiq(x):
            nonlocal sQi
            return sQi.iquery(sQi.query(x), check=False)

        quad_part = []
        zero = qiq(Bin.empty(N))
        #print(zero, "zero")
        ones = {}
        for i in self.quad_basis:
            ones[i] = qiq(Bin.unit(i, N))
        #     print(ones[i], "one", i)
        # print()

        for i, j in combinations(self.quad_basis, 2):
            q = qiq(Bin({i,j}, N))
            qmask = ones[i] ^ ones[j] ^ zero ^ q
            if qmask:
                print(i, j, qmask)
                quad_part.append((i, j, qmask))
        print()
        quad_part = tuple(quad_part)
        if quad_part in self.quad_parts_seen:
            raise self.RefreshFailed("same quad")

        self.quad_parts_seen.add(quad_part)
        self.quad_part = tuple(quad_part)
        return quad_part[:]

    def invert_Q(self, quad_part=None, debug=False):
        if quad_part is not None:
            self.quad_part = quad_part
        n, N = self.n, self.N
        B = BooleanPolynomialRing(
            names=",".join(
                [f"x{i}" for i in reversed(range(N))]
                + [f"y{i}" for i in reversed(range(N))]
            ),
            order="lex",
        )
        XYS = B.gens()
        XS = B.gens()[:N]
        YS = B.gens()[N:]

        ys = list(XS)
        for i, j, add in self.quad_part:
            for k in Bin(add).support:
                ys[k] += XS[i] * XS[j]

        # if 1:
        #     for i, y in enumerate(ys):
        #         print(i, ":", y)
        #     print()

        I = B.ideal([YS[i] - ys[i] for i in range(N)])

        QEQS = [None] * N
        for eq in I.groebner_basis():
            xs = [mono for mono in eq if mono in XS]
            if len(xs) >= 1:
                vari = XS.index(xs[0])
                var = XS[vari]

                ys = [mono for mono in eq if mono != xs[0]]
                for mono in ys:
                    # ensure non divisible
                    # sage's .divides() not implemented..
                    assert mono / var == 0, "non-invertible Q"
                QEQS[XS.index(xs[0])] = [[XYS.index(t) for t in mono] for mono in ys]
                if debug:
                    print(xs[0], "=", sum(ys))
            else:
                if debug:
                    print("EQ", eq)
        assert None not in QEQS, "inversion failed"

        self.QI_eqs = QEQS

        self.query_affine_pool = []
        for i in range(40):
            x = Bin.random(N)
            y = self.query_affine(x)
            self.query_affine_pool.append((x, y))
            failed = []
            for irow, row in enumerate(self.state.system.system):
                res = 0
                for take, mono in zip(row, self.state.system.monos):
                    if take:
                        val = prod(x[i] for i in mono.x)
                        val &= prod(y[i] for i in mono.y)
                        res ^= val
                if res:
                    failed.append(irow)
            if failed:
                print(f"failed at eqs {len(failed)}/{len(self.state.system.system)}: ", failed)
                assert 0, "recovered system is incorrect"
                raise self.UnsolvableQ("recovered system is incorrect")
        return self.QI_eqs[:]

    def make_affine_state(self):
        state0 = AttackState(n=self.n, oracle=self.query_affine)

        for _ in range(8):
            v = x = Bin.random(self.N)
            y0 = self.query_affine(x)
            y1 = state0.oracle(x)

            v = state0.mapX.query(v)
            v = state0.query(v)
            v = state0.mapY.iquery(v)
            assert v == y0 == y1, f"failed why? bug: {(v.int, y0, y1)}"

        state0.system = copy(self.state.system)
        state0.system.oracle = self.query_affine
        state0.system.precompute_fast_oracles()
        # state0.fasten()

        for _ in range(8):
            v = x = Bin.random(self.N)
            y0 = self.query_affine(x)
            y1 = state0.oracle(x)

            v = state0.mapX.query(v)
            v = state0.query(v)
            v = state0.mapY.iquery(v)
            assert v == y0 == y1, f"bad Q system? bug: {(v.int, y0, y1)}"

        return state0.randomized()

    def query_Q(self, x):
        assert self.quad_part, "not ready"
        N = self.N
        x0 = x = Bin(x, N)
        for i, j, mask in self.quad_part:
            if x0[i] & x0[j]:
                x ^= mask
        return x

    def iquery_Q(self, y):
        assert self.QI_eqs, "not ready"
        N = self.N
        xy = [0] * N + list(y)
        for i, eq in enumerate(self.QI_eqs):
            for mono in eq:
                res = 1
                for t in mono:
                    res &= xy[t]
                xy[i] ^= res
        x = Bin(xy[:N], N)
        assert self.query_Q(x) == y, "iquery wrong"
        return x

    def query_affine(self, x):
        x = Bin(x, self.N)
        xx = self.iquery_Q(x)
        #assert self.query_Q(xx) == x
        return self.state.query(xx)

    def recover_quadratic_ANF(self, indexes=None, names=None, state=None):
        if state:
            self.state = state

        n, N = self.n, self.N
        if names is None:
            names = ["x%d" % i for i in range(self.N)]

        if indexes is None:
            indexes = list(range(N))

        B = BooleanPolynomialRing(N, names=names)
        xs = B.gens()

        tn = len(indexes)
        anfs = [0] * tn

        proj = lambda v: Bin([v[i] for i in indexes])

        zero = proj(state.query(Bin.empty(N)))
        for e in range(len(anfs)):
            anfs[e] += B(zero[e])

        vi = []
        for i in range(N):
            v = proj(state.query(Bin.unit(i, N)))
            vi.append(copy(v))
            v ^= zero
            for e in range(len(anfs)):
                anfs[e] += B(v[e]) * xs[i]

        for i in range(N):
            for j in range(i+1, N):
                v = proj(state.query(Bin.unit(i, N) + Bin.unit(j, N)))
                v ^= vi[i] ^ vi[j] ^ zero
                for e in range(len(anfs)):
                    anfs[e] += B(v[e]) * xs[i] * xs[j]
        return dict(zip(indexes, anfs))

    def recover_linear_structures_in_output_combinations(self, anfs: dict):
        n, N = self.n, self.N
        results1 = []
        results2 = []
        for ifs in Combinations(list(anfs)):
            if not ifs:
                continue

            mask = Bin(set(ifs), N)
            f = sum(anfs[i] for i in ifs)
            xs = f.parent().gens()
            has1, ls = find_linear_structures(f)
            print("output sum", ifs, ":", "LS dim", ls.nrows())
            if ls.nrows() < N-4:
                continue

            nonzero = [tuple(v) for v in ls.right_kernel() if v]
            nonzero = sorted(nonzero)  # important for dup removal below! (was bug)

            if ls.nrows() == N-2:
                results1.append((mask, nonzero))
                print("    candidate x1x2: 1")
            elif ls.nrows() == N-4:
                num = 0
                for p, q in Combinations(nonzero, 2):
                    for pp, qq in Combinations(nonzero, 2):
                        pq = tuple(vector(GF(2), p) + vector(GF(2), q))
                        ppqq = tuple(vector(GF(2), p) + vector(GF(2), q))
                        if p < q < pq and p < pp < qq < ppqq:
                            fp = sum(c*x for c, x in zip(p, xs))
                            fq = sum(c*x for c, x in zip(q, xs))
                            fpp = sum(c*x for c, x in zip(pp, xs))
                            fqq = sum(c*x for c, x in zip(qq, xs))
                            test = f - fp*fq - fpp*fqq
                            if test.degree() <= 1:
                                num += 1
                                if num == 1:
                                    results2.append((mask, [p, q, pp, qq]))
                print("   candidate pairs for x1x2 + x3x4:", num)
        print()
        return results1, results2

    def select_sparse_quadratics(self, results1, results2, nlin):
        n, N = self.n, self.N
        covered = matrix(GF(2), 0, N)
        cur_rank = 0

        self.config = dict(
            N=self.N,
            nlin=self.nlin,
            nquad=self.nquad,
            nquad_x=None,
            skip1=0,
            num1=0,
            skip2h=0,
        )
        skiplin = 0

        xrows = []
        yrows = []
        for mask, rs in results1:
            covered2 = covered.stack(vector(GF(2), mask))
            if covered2.rank() > cur_rank:
                covered = covered2
                cur_rank = covered.rank()
                assert len(rs) in (2, 3)
                # avoid linear bits inside quadratics
                # (ad-hoc, to avoid x0*y0 clear in the output - not part of the encoding)
                if not all(max(r[:-nlin]) for r in rs):
                    print("skip 1 output 1 mono lin*lin")
                    self.config.setdefault("skip1", 0)
                    self.config["skip1"] += 1
                    skiplin += 1
                    continue
                # rs = list(r for r in rs if max(r[:-nlin]))
                xrows.extend(rs[:2])
                yrows.append(mask)

                print("take 1 mono", mask, mask.support, matrix(GF(2), xrows).rank())
                # for row in rs[:2]:
                #     print("   ", row)
                self.config.setdefault("num1", 0)
                self.config["num1"] += 1
        print("indep. output bits with 1 monomial", cur_rank)
        print()

        for mask, rs in results2:
            covered2 = covered.stack(vector(GF(2), mask))
            if covered2.rank() > cur_rank:
                covered = covered2
                cur_rank = covered.rank()
                assert len(rs) == 4, len(rs)
                #rs = list(r for r in rs if max(r[:-nlin]))
                rs1 = rs[:2]
                rs2 = rs[2:]
                rs = []

                if all(max(r[:-nlin]) for r in rs1):
                    rs.extend(rs1)
                else:
                    print("skip 1 output 1/2 mono")
                    self.config.setdefault("skip2h", 0)
                    self.config["skip2h"] += 1

                if all(max(r[:-nlin]) for r in rs2):
                    rs.extend(rs2)
                else:
                    print("skip 1 output 1/2 mono")
                    self.config.setdefault("skip2h", 0)
                    self.config["skip2h"] += 1

                xrows.extend(rs)
                yrows.append(mask)

                print("take 2 mono", mask, mask.support, matrix(GF(2), xrows).rank())
                # for row in rs:
                #     print("   ", row)

                self.config.setdefault("num2_%d" % len(rs), 0)
                self.config["num2_%d" % len(rs)] += 1
            else:
                # print("skip dependent", mask, mask.support)
                pass

        print("indep. output bits with <=2 monomials", cur_rank)
        self.config["nquad_x"] = matrix(GF(2), xrows).rank()
        assert len(yrows) + skiplin == self.nquad, "failed, some bug"
        return xrows, yrows


def find_linear_structures(f: "BooleanPolynomialRing"):
    """Returns linear structure basis of a BPR function of degree <= 2.
    Returns:
        has_ls1(bool): is the first basis row 1-LS ? (i.e. differential mask1 -> 1 is prob. 1)
        basis(matrix): rows form LS basis (i.e. differentials mask -> 0 are prob. 1),
                       with all rows being 0-LS except possible the first one
    """
    assert f.degree() <= 2
    n = f.parent().n_variables()
    mat = matrix(GF(2), n, n)
    mono1i = {a: i for i, a in enumerate(f.parent().gens())}
    for mono in f:
        if mono.degree() == 2:
            a, b = mono
            ia = mono1i[a]
            ib = mono1i[b]
            mat[ia,ib] += 1
            mat[ib,ia] += 1
    rows = []
    row1 = None
    for row in mat.right_kernel().matrix():
        dy = f(*[0]*n) - f(*Bin(row).tuple)
        if dy == 1:
            if row1 is None:
                row1 = row
                continue
            else:
                row -= row1
        rows.append(row)
    mat = matrix(GF(2), rows).echelon_form()
    if row1 is not None:
        return True, matrix(row1).stack(mat)
    else:
        return False, mat
