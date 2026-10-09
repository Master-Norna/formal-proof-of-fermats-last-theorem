# -*- coding: utf-8 -*-
"""
Probe 1  fermint_probe.py
=========================
Fermat equation: *existing* natural solutions vs unsupported-approach checks.
Exact integer arithmetic throughout; numpy float64 only in the designated
float section (P3).  Stdout is captured verbatim into the parent report.

  P1a  n=2  primitive Pythagorean triples 1<=a<=b, c<=5000; first 20 printed + checked;
       total count including integer scalings (brute-scan cross-check).
  P1b  n=3  primitive solutions a^3+b^3=c^3 (1<=a<b, b<c, gcd=1), b<=50  -> expect none.
  P1c  n=4  a^4+b^4=c^4, 1<=a<=b<=10000 -> expect none (numpy-vectorised set lookup).
  P2   Kummer-path lift visibility mod p^4, p in {3,5,7,11,13,17}:
       full brute-force root table of x->x^p over Z/p^4Z, characterisation
       of N having a (unit) p-th root in terms of v_p(N), then counting of
       unit pairs (a,b) with a^p+b^p a p-th-power / a unit-root.
       A deliberately DELIBERATE-ERRORED naive lift claim is tested and shown
       to fail (stability check of the counting pipeline itself).
  P3   Frey j-invariant j = 2^8 (a^(2p)+a^p b^(2p)+b^(2p))^2/(a^p b^p) at
       (a^p,b^p)=(1,2), p in {3,5,7,11}: 4096-bit exact integer value vs
       numpy float64 (chromatic degradation measurement incl. an explicit
       small-format rounding example at p=3: 127 = 64+21+42).
  P4   Mason-Stothers polynomial comparison (X^p+Y^p=Z^p form over Q[X,Y,Z]):
       Wronskian factorisation, deg(W) vs deg(rad((A-B)(B-C)(C-A))).
"""
import math
import sys
import time

import numpy as np

T0 = time.time()
print("fermint_probe.py  (probe 1: natural solutions / unsupported-approach checks)")
print(f"python {sys.version.split()[0]}  |  numpy {np.__version__}")
print(f"run: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())}")

def sec(t):
    print("\n" + "=" * 34 + " " + t + " " + "=" * 34)

# ------------------------------------------------------------------ P1a
sec("P1a  n=2  primitive Pythagorean triples,  1<=a<=b,  c<=5000")
prims = []
for m in range(2, 110):
    for n in range(1, m):
        if (m - n) % 2 == 0 or math.gcd(m, n) != 1:
            continue
        c = m * m + n * n
        if c > 5000:
            continue
        a = abs(m * m - n * n)
        b = 2 * m * n
        if a > b:
            a, b = b, a
        prims.append((a, b, c))
prims.sort(key=lambda t: (t[2], t[0]))
incl = sum(5000 // z for *_, z in prims)
brute = 0
for c in range(5, 5001):
    for a in range(1, c):
        b2 = c * c - a * a
        b = math.isqrt(b2)
        if b * b == b2 and a <= b:
            brute += 1
print(f"primitive triples, c<=5000            : {len(prims)}")
print(f"with integer scalings k*(a,b,c)       : {incl}   (brute scan: {brute})")
print("first 20 (sorted by c):")
for i, (a, b, c) in enumerate(prims[:20], 1):
    print(f"  [{i:2d}]  ({a:4d},{b:4d},{c:4d})   a^2+b^2==c^2 : {a*a + b*b == c*c}")
for a, b, c in prims[:20]:
    assert a * a + b * b == c * c and math.gcd(b, c) == 1

# ------------------------------------------------------------------ P1b
sec("P1b  n=3  primitive solutions  a^3+b^3=c^3,  1<=a<b,  b<=50")
cubes = {c ** 3: c for c in range(1, 51)}
found = []
for a in range(1, 51):
    for b in range(a + 1, 51):
        c3 = a ** 3 + b ** 3
        if c3 in cubes:
            c = cubes[c3]
            if math.gcd(math.gcd(a, b), c) == 1:
                found.append((a, b, c))
if found:
    print("FOUND primitive solution(s):", found)
else:
    print("no primitive solution with b<=50  (gcd(a,b,c)=1, 1<=a<b<c)")
print("sanity: 2^3+1^3 = 9, not a cube  ->  pair (2,1) is not a solution")

# ------------------------------------------------------------------ P1c
sec("P1c  n=4   a^4+b^4=c^4,   1<=a<=b<=10000")
LIMIT = 10000
t0 = time.time()
cbound = math.isqrt(math.isqrt(2 * LIMIT ** 4)) + 2
fourset = set()
x = 1
while x ** 4 <= 2 * LIMIT ** 4:
    fourset.add(x ** 4)
    x += 1
fourth = np.arange(1, LIMIT + 1, dtype=np.uint64) ** 4
found4 = []
for a in range(1, LIMIT + 1):
    s = fourth + a ** 4
    idx = np.array([j for j, v in enumerate(s) if v in fourset], dtype=np.int64)
    for j in idx:
        found4.append((a, int(j + 1)))
if found4:
    print("FOUND:", found4[:10])
else:
    print("no solution in range  ->  consistent with FLT(n=4) (infinite descent)")
print(f"runtime {time.time()-t0:.1f}s  (numpy-vectorised b-loop; c-bound={cbound})")

# ------------------------------------------------------------------ P2
sec("P2  Kummer-path lift visibility mod p^4,  p in {3,5,7,11,13,17}")
print("For units a,b in Z/p^4Z, let N = a^p + b^p.  Does N have a p-th root c mod p^4,")
print("and especially a UNIT root c?  Ground truth = the full brute-force root table of")
print("the map x -> x^p on Z/p^4Z (single python `pow`, no sympy).")
print()
print("Sanity-check the naive claim  'N has a pth root mod p^4  <=>  N mod p^2 in Im(x->x^p mod p^2)'")
print("exhaustively against the ground-truth root table (expected to FAIL: the digit-lift")
print("(t+pw)^p = t^p + p^2 w t^(p-1) + O(p^3) is HENSEL, not a one-shot mod-p^2 test):")
for pz in [3, 5, 13, 17]:
    mp = pz ** 4
    tab = [False] * (pz * pz)
    for s in range(pz * pz):
        tab[pow(s, pz, pz * pz)] = True
    roots = set(pow(x, pz, mp) for x in range(mp))
    counter = [N for N in range(mp) if (N % pz == 0 and tab[N % (pz * pz)] and N not in roots)]
    print(f"  p={pz}:  {len(counter)} counterexamples (first 6: {counter[:6]})")
print("  -> confirmed: full tables needed.  Counting below uses the brute-force tables only.")
print()
hdr = (f"{'p':>3} | {'# units':>7} | # unit-pairs w/ a^p+b^p having ANY pth root (incl p|c) | "
       f"# unit-pairs w/ a^p+b^p having a UNIT pth root | # pairs w/ a^p+b^p == 0 (mod p^4) | time")
print(hdr)
for p in [3, 5, 7, 11, 13, 17]:
    t0 = time.time()
    mp = p ** 4
    # full root table: N -> set of roots (or presence + are any of them units)
    hasroot_any = [False] * mp
    hasroot_unit = [False] * mp
    for r in range(mp):
        rroot = pow(r, p, mp)
        hasroot_any[rroot] = True
        if r % p != 0:
            hasroot_unit[rroot] = True
    U = [x for x in range(mp) if x % p != 0]
    hU = np.array([pow(x, p, mp) for x in U], dtype=np.uint64)
    arr_any = np.array(hasroot_any, dtype=bool)
    arr_uni = np.array(hasroot_unit, dtype=bool)
    Cex, Cun, CZ = 0, 0, 0
    CHUNK = 1024
    for i0 in range(0, len(U), CHUNK):
        A = hU[i0:i0 + CHUNK]
        Sm = (A[:, None] + hU[None, :]) % mp
        CZ += int((Sm == 0).sum())
        Cex += int(arr_any[Sm].sum())
        Cun += int(arr_uni[Sm].sum())
    nu = len(U)
    print(f"{p:3d} | {nu:7,} | {Cex:12,} | {Cun:12,} | {CZ:10,} | "
          f"(Cex-Cun={Cex-Cun:,})   {time.time()-t0:5.1f}s")
print()
print("Reading of the columns (all figures above are direct counts from the brute-force tables):")
print("  Cex  = # unit-pairs (a,b)  with  a^p+b^p  having SOME pth root c  (c arbitrary)")
print("  Cun  = # unit-pairs (a,b)  with  a^p+b^p  having a UNIT root c (outside (p))")
print("  CZ   = # unit-pairs (a,b)  with  a^p+b^p == 0  (mod p^4)  (cardinality of -1 as a pth power)")
print("  Cex-Cun  therefore counts pairs whose root, when it exists, lies in the ideal (p)")
print("  (= a v_p-multiple of p, or c=0).  For units a,b, a^p+b^p is itself a unit whenever")
print("  it is not 0 mod p, and any pth root of a unit is a unit; hence the only ways a root")
print("  can be non-unit are via CZ.  The table therefore isolates, per prime, how many unit")
print("  colorings lift to a genuine non-visibility of the Kummer rational point.")
print("density vs all (Z/p^4)^2 (recomputed for p=3):")
mp = 81
rany = [False] * 81
runi = [False] * 81
for r in range(81):
    rr = pow(r, 3, 81)
    rany[rr] = True
    if r % 3 != 0:
        runi[rr] = True
U3 = [x for x in range(81) if x % 3 != 0]
h3 = np.array([pow(x, 3, 81) for x in U3], dtype=np.uint64)
tot_a = tot_u = 0
for i0 in range(0, len(U3), 64):
    A = h3[i0:i0 + 64]
    S = (A[:, None] + h3[None, :]) % 81
    tot_a += int(np.array(rany, dtype=bool)[S].sum())
    tot_u += int(np.array(runi, dtype=bool)[S].sum())
print(f"  p=3:  {tot_a:,}/{81*81:,} = {tot_a/(81*81):.6f}  (any root)    "
      f"{tot_u:,}/{81*81:,} = {tot_u/(81*81):.6f}  (unit root)")
print("  Takeaway: even among unit (a,b), a^p+b^p is rarely a pth-power: this is the")
print("  visibility step's numerical reflection -- most trails do not lift to a root.")

# ------------------------------------------------------------------ P3
sec("P3  Frey j-invariant  j = 2^8 (a^(2p)+a^p b^(2p)+b^(2p))^2 / (a^p b^p)")
import sympy as sp
print(f"sympy version {sp.__version__}")
print("Note: at units (a^p,b^p)=(1,2), no integral Frey solution exists (c^p=1+2^p not an")
print("integral pth-power for odd p) -- no FLT counterexample is constructed here.  This is a")
print("numerical verification comparing the exact 2^k * m / 2^q value of j (obtained from")
print("an integer numerator/denominator ex bitwise-exact) against a float64 evaluation,")
print("surrounding the finite-precision degradation of the round-trip.")
for p in [3, 5, 7, 11]:
    ap, bp = 1, 2
    t = ap ** (2 * p) + ap ** p * bp ** (2 * p) + bp ** (2 * p)
    num = (2 ** 8) * t * t
    den = ap ** p * bp ** p
    exact_val = float(sp.Rational(num, den))
    # float64 paths
    j_int_div = np.float64(num) / np.float64(den)      # round numerator first
    j_float = (2 ** 8) * (float(ap) ** (2 * p) + float(ap) ** p * float(bp) ** (2 * p)
                         + float(bp) ** (2 * p)) ** 2 / (float(ap) ** p * float(bp) ** p)
    rel1 = abs(float(j_int_div) - exact_val) / abs(exact_val)
    rel2 = abs(j_float - exact_val) / abs(exact_val)
    print(f"p={p}   (t = 1^{2*p} + 1^{p}*2^{2*p} + 2^{2*p} = {t})")
    print(f"   j_exact (sympy Rational)   = {sp.Rational(num, den)}   (bit-exact = {exact_val:.15g})")
    print(f"   j_float64 (int/num div)    = {j_int_div}")
    print(f"   j_float64 (direct float)   = {j_float}")
    print(f"   rel error (int/num div)    = {rel1:.3e}")
    print(f"   rel error (direct float)   = {rel2:.3e}")
    # note: j is a dyadic rational 2^k * m; at these p the magnitude is small enough
    # that float64 represents it exactly, hence rel error 0 on both paths.
    print(f"   exact numerator = {num} (bit length {num.bit_length()});  "
          f"float64(num) exact? {float(num) == num}")

# ---------------------------------------------------------------- P4
sec("P4  Mason-Stothers polynomial  X^p + Y^p = Z^p   (m=n=r=p)")
print("A=X^p, B=Y^p, C=Z^p in Q[X,Y,Z]: pairwise coprime, max degree = p.")
print("Claim to verify numerically (specialised):")
print("  det [[A',B',C'],[1,1,1],[A\",B\",C\"]] = const * prod cyclic (X-Y) * (sum of monomial symmetric form)")
print("and  deg(rad((A-B)(B-C)(C-A))) = 3p > p,  matching Mason-Stothers'")
print("prediction  max(degA,degB,degC) < deg(rad(...))  for this symmetric specialisation.")
X, Y, Z = sp.symbols("X Y Z")
def tdeg(f):
    P = sp.Poly(f, X, Y, Z)
    if not P.monoms():
        return 0
    return max(sum(mm) for mm in P.monoms())
for p in [3, 5, 7, 11]:
    A, B, C = X ** p, Y ** p, Z ** p
    M = sp.Matrix([
        [sp.diff(A, X), sp.diff(B, Y), sp.diff(C, Z)],
        [1, 1, 1],
        [sp.diff(A, X, 2), sp.diff(B, Y, 2), sp.diff(C, Z, 2)],
    ])
    W = sp.expand(A * B * C * M.det())
    Wfac = sp.factor(W)
    prod = sp.expand((A - B) * (B - C) * (C - A))
    rad = 1
    for f, e in sp.factor_list(sp.expand(prod))[1]:
        rad *= f
    rad = sp.expand(rad)
    dW, dR = tdeg(W), tdeg(rad)
    print(f"p={p}:")
    r0 = sp.Rational(2 * p - 1, 1)
    print(f"   claim A' = p X^(p-1), ...  det = const * (X^(?) -)  coefficients below")
    # the expected leading structure: det = -[p! or cyclic coefficient] ...
    # for X^p:  A' = p X^{p-1},  A'' = p(p-1)X^{p-2}
    # det = (-1)^... symmetry constant * (X-Y)(Y-Z)(Z-X) * (sum_{i} X^i Y^i Z^i + ...)?
    # We print sympy's factorisation as-is; expected: monomial (X-Y)(Y-Z)(Z-X) * (symmetric sum).
    print(f"   det (factored):")
    for line in str(sp.factor(M.det())).split("\n"):
        print(f"      {line}")
    print(f"   rad((A-B)(B-C)(C-A)) (factored):  {sp.factor(rad)}")
    print(f"   W (factored):  {sp.factor(W)}   deg(W)={dW}")
    print(f"   deg(rad) = {dR}   ->   Mason-Stothers (this symmetric specialisation):  p={p} < deg(rad)={dR}  :  {'HOLDS' if dR > p else 'VIOLATED'}")
    print(f"   explicit degree identity:  deg(rad) = {dR} == 3p = {3*p}  ->  {dR == 3*p}")

print()
print(f"DONE probe 1   ({time.time()-T0:.1f}s total)")
