# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Arithmetic half of the divider proof (README 4.4).

div/divfv.sv proves multdiv32 equal to f_rdiv, which wraps f_udiv (a plain
restoring divider) in the RISC-V special cases. This script proves, with z3,
that f_rdiv is the RISC-V M DIV/DIVU/REM/REMU function:

  U  f_udiv(n, d) == (n udiv d, n urem d) for d != 0, by induction over the
     32 loop iterations: one generic iteration lemma (S1, integers), the
     agreement of the bit-vector iteration with it (S2), the start (S3) and
     uniqueness of quotient/remainder at the end (S4);
  W  f_rdiv == RISC-V spec (bvsdiv/bvsrem truncate toward zero, as SV / and
     %), with f_udiv replaced by udiv/urem (lemma U);
  X  optional cross-checks: the unrolled f_udiv against udiv/urem directly,
     exhaustively at 8 bits and by z3 at 32 bits (--direct).

Usage: venv/bin/python udiv_z3.py [--direct SECONDS]
"""

import sys
import z3

W = 32
ok = True


def prove(name, claim, timeout_ms=600000):
    global ok
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(z3.Not(claim))
    r = s.check()
    status = "PROVED" if r == z3.unsat else "FAILED" if r == z3.sat else "UNKNOWN"
    print(f"{status:8s} {name}", flush=True)
    if r == z3.sat:
        print("  cex:", s.model())
    if r != z3.unsat:
        ok = False


# ---- f_udiv, transcribed from div/divfv.sv (f_pref + last step) ----
def step_bv(r33, d, n, i, q):
    """One loop iteration at quotient bit i on 33-bit r; returns (r33, q)."""
    d33 = z3.ZeroExt(1, d)
    ge = z3.UGE(r33, d33)
    r33 = z3.If(ge, r33 - d33, r33)
    q = z3.If(ge, q | z3.BitVecVal(1 << i, W), q)
    return r33, q


def f_udiv(n, d):
    r = z3.Concat(z3.BitVecVal(0, 32), z3.Extract(31, 31, n))
    q = z3.BitVecVal(0, W)
    for i in range(31, 0, -1):
        r, q = step_bv(r, d, n, i, q)
        r = z3.Concat(z3.Extract(31, 0, r), z3.Extract(i - 1, i - 1, n))
    r, q = step_bv(r, d, n, 0, q)
    return q, z3.Extract(31, 0, r)


# ---- U: induction over iterations ----
# Invariant after iterations 31..i (integers): x_i = n >> i = d*Q_i + r_i,
# 0 <= r_i < d, with Q_i = q >> i (q's low i bits still 0).
x, b, d, Q, r = z3.Ints("x b d Q r")
R = 2 * r + b
ge = R >= d
r1 = z3.If(ge, R - d, R)
Q1 = 2 * Q + z3.If(ge, 1, 0)
prove("S1 iteration keeps x = d*Q + r, 0 <= r < d",
      z3.Implies(z3.And(d > 0, z3.Or(b == 0, b == 1), x == d * Q + r, r >= 0, r < d),
                 z3.And(2 * x + b == d * Q1 + r1, r1 >= 0, r1 < d)))

# Bridge lemmas S2/S2b/S2c are stated on bit-vectors with a 40-bit
# "integer" side: every value involved is below 2^34, so 40-bit +, *2, <, -
# never wrap and coincide with integer arithmetic (z3's BV2Int encoding of the
# same claims does not terminate).
def E(v):
    return z3.ZeroExt(40 - v.size(), v)


# S2: the 33-bit iteration of f_udiv computes the integer one. Before the
# compare, the 33-bit r holds R = 2*r_prev + bit with r_prev < d < 2^32, so it
# is exact; after it, r < d < 2^32, so dropping bit 32 when shifting in the
# next numerator bit loses nothing, and the next iteration again starts from
# r_prev < d (f_pref's initial r = {0, n[31]} is the case r_prev = 0, d != 0).
dv = z3.BitVec("dv", W)
rp = z3.BitVec("rp", W)
bit = z3.BitVec("bit", 1)
r33n, _ = step_bv(z3.Concat(rp, bit), dv, z3.BitVecVal(0, W), 0, z3.BitVecVal(0, W))
RI = 2 * E(rp) + E(bit)
r1I = z3.If(z3.UGE(RI, E(dv)), RI - E(dv), RI)
prove("S2 33-bit iteration == integer iteration, result < d",
      z3.Implies(z3.ULT(rp, dv),
                 z3.And(E(r33n) == r1I, z3.Extract(32, 32, r33n) == 0,
                        z3.ULT(z3.Extract(31, 0, r33n), dv))))
# S2b: setting quotient bit i (ge) in a q whose bits i..0 are 0 is
# Q_i = 2*Q_{i+1} + ge on the shifted view Q_i = q >> i.
# S2c: x_i = n >> i = 2*x_{i+1} + n[i].
for i in range(W):
    qv = z3.BitVec("qv", W)
    g = z3.BitVec("g", 1)
    qn = qv | (z3.ZeroExt(W - 1, g) << i)
    prove(f"S2b quotient bit {i:2d}",
          z3.Implies(z3.Extract(i, 0, qv) == 0,
                     E(z3.LShR(qn, i)) == 2 * E(z3.LShR(qv, i + 1)) + E(g)), 60000)
    nv = z3.BitVec("nv", W)
    prove(f"S2c n >> {i:2d} == 2*(n >> {i + 1:2d}) + n[{i}]",
          E(z3.LShR(nv, i)) == 2 * E(z3.LShR(nv, i + 1)) + E(z3.Extract(i, i, nv)), 60000)
# S3: start: x_32 = 0 = d*0 + 0 with r = 0 < d.
# S4: at the end x_0 = n = d*Q_0 + r_0, 0 <= r_0 < d determines Q_0 and r_0,
# which by the SMT-LIB definition of bvudiv/bvurem are n udiv d, n urem d.
n_, d_, Q_, r_ = z3.Ints("n_ d_ Q_ r_")
prove("S4 uniqueness: n = d*Q + r, 0 <= r < d  =>  Q = n div d, r = n mod d",
      z3.Implies(z3.And(n_ >= 0, d_ > 0, Q_ >= 0, n_ == d_ * Q_ + r_, r_ >= 0, r_ < d_),
                 z3.And(Q_ == n_ / d_, r_ == n_ % d_)))
nb, db = z3.BitVecs("nb db", W)


# ---- W: the RISC-V wrapper ----
def f_abs(v, neg):
    return z3.If(neg, -v, v)


def f_rdiv_core(a, b_, is_rem, sgn):
    sa = z3.And(sgn, z3.Extract(31, 31, a) == 1)
    sb = z3.And(sgn, z3.Extract(31, 31, b_) == 1)
    n, dd = f_abs(a, sa), f_abs(b_, sb)
    q, rr = z3.UDiv(n, dd), z3.URem(n, dd)          # lemma U
    return z3.If(b_ == 0, z3.If(is_rem, a, z3.BitVecVal(-1, W)),
                 z3.If(is_rem, f_abs(rr, sa), f_abs(q, z3.Xor(sa, sb))))


def riscv(a, b_, is_rem, sgn):
    # RISC-V M; signed / and % truncate toward zero (= SMT-LIB bvsdiv/bvsrem),
    # INT_MIN / -1 = INT_MIN, INT_MIN % -1 = 0 (two's-complement wrap).
    div = z3.If(sgn, a / b_, z3.UDiv(a, b_))
    rem = z3.If(sgn, z3.SRem(a, b_), z3.URem(a, b_))
    return z3.If(b_ == 0, z3.If(is_rem, a, z3.BitVecVal(-1, W)), z3.If(is_rem, rem, div))


# Split on the operand signs, signed mode and operator (16 cases), so both
# sides simplify to the same udiv/urem terms instead of two bit-blasted
# dividers.
al, bl = z3.BitVecs("al bl", W - 1)
for sa_ in (0, 1):
    for sb_ in (0, 1):
        for sg_ in (False, True):
            for isr_ in (False, True):
                a = z3.Concat(z3.BitVecVal(sa_, 1), al)
                bb = z3.Concat(z3.BitVecVal(sb_, 1), bl)
                prove(f"W  f_rdiv == RISC-V ({'REM' if isr_ else 'DIV'}{'' if sg_ else 'U'}, "
                      f"a[31]={sa_}, b[31]={sb_})",
                      f_rdiv_core(a, bb, z3.BoolVal(isr_), z3.BoolVal(sg_))
                      == riscv(a, bb, z3.BoolVal(isr_), z3.BoolVal(sg_)), 120000)


# ---- X: cross-checks of the unrolled f_udiv ----
def py_udiv(n, d, w):
    r, q = n >> (w - 1), 0
    for i in range(w - 1, -1, -1):
        if r >= d:
            r -= d
            q |= 1 << i
        if i:
            r = ((r & ((1 << w) - 1)) << 1) | ((n >> (i - 1)) & 1)
    return q, r


bad = sum(1 for n in range(256) for dd in range(1, 256) if py_udiv(n, dd, 8) != (n // dd, n % dd))
print(f"{'PROVED' if bad == 0 else 'FAILED':8s} X8 8-bit restoring loop exhaustive ({bad} bad)")
ok &= bad == 0

if "--direct" in sys.argv:
    t = int(sys.argv[sys.argv.index("--direct") + 1])
    qz, rz = f_udiv(nb, db)
    prove("X32 unrolled f_udiv == udiv/urem (32-bit, direct)",
          z3.Implies(db != 0, z3.And(qz == z3.UDiv(nb, db), rz == z3.URem(nb, db))), t * 1000)

print("ALL PROVED" if ok else "NOT ALL PROVED")
sys.exit(0 if ok else 1)
