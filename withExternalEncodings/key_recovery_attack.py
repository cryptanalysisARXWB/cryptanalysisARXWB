#!/usr/bin/env sage -python
# coding: utf-8

# Imports

from sage.all import *

from simplifiedOracle import WBOracle

from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)
from itertools import combinations, product
from collections import Counter, defaultdict
from tqdm import tqdm
from time import time
import datetime

from maps import AffineMap, FastAffineMap
from attack_state import AttackState

from decompose1 import RoundDecomposition
from decompose1quad import QuadDecomposition
from decompose2speck import TwoRoundDecomposition

from wbc import SpeckWBC, SpeckRound, modadd
from utils import Time, TimeReport

# Global parameters:
n = 16  # Speck-32
#n = 32  # Speck-64
N = 2*n

# Setup / benchmarks

# Load white-box instance from shared library:
WBO = WBOracle(
    # hardcoded filename since in .c file it is hardcoded
    sharedLibFile="./white_box_arx.so",
    block_size=N,
)


NR = WBO.ROUNDS
NR = 8  # sufficient for ~3 master key suggestions

WBID = WBO.rounds[1].query(0xabcd1234)
SpeckTest = SpeckRound(n=n)
print(NR, "rounds")
print("White-box ID (used for caching):", hex(WBID))


R = WBO.rounds[1]

with Time("wbc-round-query", 10):
    for _ in range(10):
        R.query(Bin.random(N))

TimeReport()

configs = {}
for RNO in range(1, NR):
    print("\n\n")
    print("========================")
    print("ROUND", RNO)
    print("========================")
    SECRET = WBO.rounds[RNO]

    unsolvableQ = 0
    refreshes = 0
    scratches = 0
    while True:
        s0 = AttackState(n=n, oracle=SECRET.query).randomized()

        fnameQ = "cache/wbid%08X_round%02d_Q" % (WBID, RNO)
        fnameS = "cache/wbid%08X_round%02d_ASA" % (WBID, RNO)
        print(fnameQ)
        sys.stdout.flush()
        sys.stderr.flush()

        try:
            stateF = load(fnameS)
            Q = load(fnameQ)
            break
        except:
            print(f"Date (quad stage):", datetime.datetime.now())
            Q = QuadDecomposition(n)
            with Time("quad-prepare"):
                Q.recover_prepare(state=s0)

            print("Date (affine stage):", datetime.datetime.now())
            print(fnameS)
            # loop to retry different candidates for Q
            stateF = None
            for itr in range(8):
                print(f"Date (itr={itr}):", datetime.datetime.now())

                try:
                    with Time("quad-refresh-sol"):
                        s1 = Q.refresh_solution()
                except Q.RefreshFailed as err:
                    print("refresh failed #", itr, ":", err)
                    continue
                except Q.UnsolvableError as err:
                    print("unsolvable Q #", itr, ":", err)
                    unsolvableQ += 1
                    break

                R = RoundDecomposition(n)
                try:
                    with Time("affine-fastened-recover"):
                        stateF = R.recover_all(state=s1, num_tries=1)
                    break
                except R.UnsolvableA as err:
                    print("MSB FAIL #", itr, "refresh Q solution", err)
                    refreshes += 1
                    continue

            if not stateF or not stateF.decomposed_mapX:
                print("retrying Q from scratch")
                scratches += 1
                continue

            assert Q.quad_part
            save(Q, fnameQ)
            save(stateF, fnameS)
            break

    configs[RNO] = Q.config.copy()
    configs[RNO]["unsolvableQ_tries"] = unsolvableQ
    configs[RNO]["refreshes"] = refreshes
    configs[RNO]["retries_from_scratch"] = scratches
    print("RNO:", *[f"{k}={v}" for k, v in configs[RNO].items()])

print()

for RNO in configs:
    print(f"ROUND {RNO:2d}: ", *[f"{k}={v}" for k, v in configs[RNO].items()])
TimeReport()

# Load decompositions
QFS = [None]
for RNO in range(1, NR):
    SECRET = WBO.rounds[RNO]
    fnameQ = "cache/wbid%08X_round%02d_Q" % (WBID, RNO)
    Q = load(fnameQ)

    fnameS = "cache/wbid%08X_round%02d_ASA" % (WBID, RNO)
    stateF = load(fnameS)

    QFS.append((SECRET, Q, stateF))
    print("RNO %02d:  " % RNO, *[f"{k}={v}" for k, v in Q.config.items()])


# Analyze 2-round mix
MAPS = [None]
rno = 1
for SECRET, Q, S in QFS[1:]:
    mapX = Q.state.mapX
    Q = Q
    mapM = S.mapX
    mapY = (~Q.state.mapY) * (~S.mapY)
    MAPS.append((mapX, Q, mapM, mapY))


# Propagates Qs back (affine decomposition fast)
def makefunc(my1, mx2, q2):
    def func(x):
        nonlocal my1, mx2, q2
        x = Bin(x, N)
        l, r = x.split(2)
        l += r
        x = Bin.concat(l, r)

        v = x
        v = my1.query(v)
        v = mx2.query(v)
        v = q2.query_Q(v)
        y = v
        return y
    return func

ASA2 = [None]
FUNCS = [None]
for RNO in range(1, NR-1):
    SECRET1, Q1, S1 = QFS[RNO]
    SECRET2, Q2, S2 = QFS[RNO+1]
    mapX1, Q1, mapM1, mapY1 = MAPS[RNO]
    mapX2, Q2, mapM2, mapY2 = MAPS[RNO+1]

    func = makefunc(mapY1, mapX2, Q2)
    FUNCS.append(func)

    fnameASA2 = "cache/wbid%08X_round%02d_ASA2" % (WBID, RNO)
    print(fnameASA2)
    state0 = AttackState(n=n, oracle=func)

    try:
        stateF = load(fnameASA2)
        stateF.oracle = func
    except:
        state0 = AttackState(n=n, oracle=func)
        R = RoundDecomposition(n=n, state=state0)
        stateF = R.recover_all()
        stateF.oracle = NotImplemented
        save(stateF, fnameASA2)
        stateF.oracle = func

    x = t = Bin.random(N)
    t = modadd(t)
    t = mapY1.query(t)
    t = mapX2.query(t)
    t = Q2.query_Q(t)
    assert t == func(x) == stateF.mapY.iquery(stateF.query(stateF.mapX.query(x)))

    assert len(ASA2) == RNO
    ASA2.append(stateF)


STATES = [None,]
for RNO in tqdm(range(1, NR-1)):
    SECRET1, Q1, S1 = QFS[RNO]
    mapX1, Q1, mapM1, mapY1 = MAPS[RNO]
    SS1 = ASA2[RNO]

    mapX = SS1.mapX * mapM1
    mapY = SS1.mapY

    def make():
        # closures...
        mx = mapX
        my = mapY
        def func(x):
            nonlocal mx, my
            v = Bin(x, N)
            v = mx.query(v)
            v = modadd(v)
            v = my.iquery(v)
            return v
        return func

    state1 = AttackState(n=n, oracle=make())
    state1 = state1.modified(
        projX = mapX.matrix,
        cX = mapX.full_const_out,
        projY = mapY.matrix,
        cY = mapY.full_const_out,
    )
    state1.mark_decomposed()
    STATES.append(state1)


# Recover subkeys (up to 2 MSBs)
keys = []
for RNO in range(1, NR-2):
    s1, s2 = STATES[RNO:RNO+2]
    TR = TwoRoundDecomposition(
        state_m2=s1,
        state_m1=s2,
        round=SpeckTest,
    )
    Sm2, Sm1 = TR.recover_middle_linear()

    s2, s1, key = TR.align_xors(Sm2, Sm1)
    keys.append(key)
    print(f"{RNO:2d}: ", key.hex)


# Employ Key Schedule

def RoundEnc(x, y, k):
    x = Bin(x, n)
    y = Bin(y, n)
    x = x.ror(SpeckTest.alpha)
    x += y
    x ^= k
    y = y.rol(SpeckTest.beta)
    y ^= x
    return x, y

def RoundDec(x, y, k):
    x0, y0 = x, y
    x = Bin(x, n)
    y = Bin(y, n)
    y ^= x
    y = y.ror(SpeckTest.beta)
    x ^= k
    x -= y
    x = x.rol(SpeckTest.alpha)
    assert RoundEnc(x, y, k) == (x0, y0)
    return x, y

def INOUT(k1, k2, i):
    out = k1.rol(SpeckTest.beta) ^ k2
    inp = out
    inp ^= i
    inp -= k1
    inp = inp.rol(SpeckTest.alpha)
    assert RoundEnc(inp, k1, i) == (out, k2)
    return inp, out

def KeySchedule(master_key, rounds=20):
    A = master_key[0]
    BCD = list(master_key[1:])
    rk = []
    i = j = 0
    while len(rk) < rounds:
        rk.append(A)
        BCD[j], A = RoundEnc(BCD[j], A, i)
        i += 1
        j = (j + 1) % len(BCD)
    return rk


for bits in Bin.iter(8):
    t1, t2, t3, t4 = [b.resize(n) << (n-2) for b in bits.split(4)]
    k1, k2, k3, k4 = keys[:4]
    k1 ^= t1
    k2 ^= t2
    k3 ^= t3
    k4 ^= t4

    i0 = 2
    A = k1
    B, BB = INOUT(k1, k2, i0)
    C, CC = INOUT(k2, k3, i0+1)
    D, DD = INOUT(k3, k4, i0+2)

    ABCD = A, B, C, D

    BCD = [B, C, D]

    rk = []
    i = i0
    j = 0

    while len(rk) < 20:
        rk.append(A)
        BCD[j], A = RoundEnc(BCD[j], A, i)
        i += 1
        j = (j + 1) % len(BCD)

    if (rk[4] ^ keys[4]) << 2 == 0:

        diff = []
        for ka, kb in zip(keys, rk):
            diff.append((ka ^ kb) << 2)

        if not any(diff):
            print("=================")
            print("suggested subkeys")
            for k in rk[:10]:
                print(k.hex, end=" ")
            print()
            print()

            print("differences excl. 2 MSBs")
            print(*[d.hex for d in diff])
            print()

            A, B, C, D = ABCD
            B, C, D = [C, D, B]

            C, A = RoundDec(C, A, 1)
            B, A = RoundDec(B, A, 0)

            master_key = A, B, C, D
            print("master_key =", ", ".join("0x%04x" % v for v in master_key))
            fullrk = KeySchedule(master_key)
            print(*[d.hex for d in fullrk[:2]], "...")
            print(*[d.hex for d in fullrk[2:]])
        print()

for RNO in configs:
    print(f"ROUND {RNO:2d}: ", *[f"{k}={v}" for k, v in configs[RNO].items()])
TimeReport()
