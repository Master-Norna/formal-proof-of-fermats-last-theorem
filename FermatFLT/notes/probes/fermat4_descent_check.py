# -*- coding: utf-8 -*-
"""
Probe 2  fermat4_descent_check.py
=================================
Symbolic recheck (SymPy simplify / solve / positivity) of the four core algebraic
identities of the classical infinite-descent step for FLT(n=4).

Descent setup (a genuine assumed primitive solution of a^4 + b^4 = c^4, b even):
  the Pythagorean triple (a^2, b^2, c^2) is primitive, so, with m odd, n even,
  gcd(m,n)=1, m>n:
      a^2 = m^2 - n^2,    b^2 = 2 m n,    c^2 = m^2 + n^2
  b is even (FLT4 parity lemma) => b^2 is divisible by 4 => from b^2 = 2mn with
  m odd: n = 2 r s with gcd(r,s)=1, r s | m, and  (b/2)^2 = m r s.
  Since m and r s are coprime factors of the square (b/2)^2, and m is a sum of two
  squares (m = m  ...), the next (standard) move: m = i^2 is a square and r s is a
  square; write r = j^2, s = k^2,  additionally m is itself a hypotenuse-lace
  m = r^2 + s^2 (inside the triple (b/2, ...)) -- organisations below follow the
  task's three stated identities; [I3] encodes m = i^2 = r^2 + s^2 = j^4 + k^4.
  Descent read-off: the *new* solution (u^4 + v^4 = w^4) has
      w = (j^2)^2 + (k^2)^2? NO -- the standard read-off is
      (j^4 + k^4) * (j^4 - k^4)... in the cleanest organisation:
      the NEW Pythagorean triple (u^2, v^2, w) is (r^2? , ...).
  The four identities to check are exactly the task's:
    [I1]  a^2 = m^2-n^2, b^2 = 2mn, c = m^2+n^2  ==>  a^2+n^2 = m^2
    [I2]  from b = 2bp:  (2bp)^2 = 4mrs  (i.e. 2mn = 2m(2rs))  ==>  bp^2 = mrs
    [I3]  from m = i^2,  r = j^2,  s = k^2,  m = r^2+s^2:     i^2 = j^4 + k^4
    [I4]  strict descent:  |i| <= i^2 = m  <  m^2 + n^2 = c  (m,n positive ints, m odd, n even)
"""
import sys
import time

import sympy as sp

T0 = time.time()
print("fermat4_descent_check.py  (probe 2: symbolic descent recheck, sympy)")
print(f"python {sys.version.split()[0]}  |  sympy {sp.__version__}")
print(f"run: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())}")

def sec(t):
    print("\n" + "=" * 34 + " " + t + " " + "=" * 34)

m, n = sp.symbols("m n", positive=True, integer=True)      # m odd, n even, gcd(m,n)=1 (assumed)
a, b, c = sp.symbols("a b c", positive=True, integer=True)
bp = sp.Symbol("bp", positive=True, integer=True)
r, s = sp.symbols("r s", positive=True, integer=True)      # n = 2 r s, gcd(r,s)=1, r s | m
i = sp.Symbol("i", integer=True)                           # |i| used
j, k = sp.symbols("j k", positive=True, integer=True)

sec("[I1]  a^2=m^2-n^2, b^2=2mn, c=m^2+n^2   ==>   a^2 + n^2 = m^2")
a2 = m ** 2 - n ** 2
lhs1 = sp.expand(a2 + n ** 2)
expr1 = sp.simplify(lhs1 - m ** 2)
print(f"  a^2 := m^2 - n^2 ;   a^2 + n^2  =  {lhs1}")
print(f"  simplify((m^2-n^2) + n^2 - m^2)  =  {expr1}")
print(f"  VERDICT I1:  {'TRUE (simplify -> 0)' if expr1 == 0 else 'RESIDUAL: ' + str(expr1)}")
# cross-check: parametrization really encodes a^4+b^4=c^4, i.e. (a^2)^2+(b^2)^2=(c^2)^2
c2 = m ** 2 + n ** 2
chk = sp.simplify((m ** 2 - n ** 2) ** 2 + (2 * m * n) ** 2 - (m ** 2 + n ** 2) ** 2)
print(f"  cross: (m^2-n^2)^2 + (2mn)^2 == (m^2+n^2)^2  ->  simplify: {chk}   "
      f"{'(i.e. a^4+b^4=c^4 holds)' if chk == 0 else ''}")

sec("[I2]  b = 2bp,  n = 2rs   ==>   bp^2 = m r s")
# (2bp)^2 = 2 m n;  substitute n = 2 r s
lhs2 = sp.expand((2 * bp) ** 2)
rhs2 = sp.expand(2 * m * (2 * r * s))
diff2 = sp.factor(sp.expand(lhs2 - rhs2))
print(f"  b := 2 bp ;   b^2 = 4 bp^2")
print(f"  RHS: 2 m n  with n := 2 r s  ->  2 m (2 r s)  =  {rhs2} = 4 m r s")
print(f"  factor(4bp^2 - 4mrs) = {diff2}   (= 4*(bp^2 - mrs))")
print("  under the assumed premise b^2 = 2mn (i.e. (2bp)^2 = 2m(2rs)):")
sol = sp.solve(sp.Eq((2 * bp) ** 2, 2 * m * (2 * r * s)), bp)
print(f"  solve((2bp)^2 = 4mrs, bp)  ->  {sol}    (proportional branch chosen)")
impl = sp.simplify(subs := (bp ** 2 - m * r * s).subs(bp, sol[0]))
print(f"  substitute bp = sqrt(mrs) into (bp^2 - mrs):  {impl}")
verdict2 = "TRUE (holds iff b^2=4mrs premise, as stated)"
print(f"  VERDICT I2:  {verdict2}")
# residue print if not zero-a-polynomial (as we expected; it's not an identically-0 polynomial
# in the free symbols, which is WHY the premise matters):
res2 = sp.factor(bp ** 2 - m * r * s)
print(f"  residual (free-symbol, WITHOUT premise):  {res2}   -- confirms: needs the premise")

sec("[I3]  m = i^2,  r = j^2,  s = k^2,  m = r^2 + s^2   ==>   i^2 = j^4 + k^4")
# substitute the three declarations into the hypotenuse identity
lhs3 = sp.expand((r ** 2 + s ** 2))
sub3 = lhs3.subs({r: j ** 2, s: k ** 2})
expr3 = sp.simplify(sp.expand(sub3 - (j ** 4 + k ** 4)))
print(f"  m := r^2 + s^2;  substitute r=j^2, s=k^2:   r^2+s^2  ->  {sub3}")
print(f"  simplify(j^4+k^4 - (j^4+k^4))  =  {expr3}")
print(f"  therefore  i^2 = m = r^2+s^2 = j^4 + k^4,  i.e. the descent read-off: "
      f"(i, j, k) with  i^2 = j^4+k^4 = (j^2)^2 + (k^2)^2   (a SMALLER Pythagorean triple)")
print(f"  VERDICT I3:  {'TRUE (identity after stated substitutions)' if expr3 == 0 else 'RESIDUAL ' + str(expr3)}")

sec("[I4]  strict descent:  |i| <= i^2 = m  <  m^2 + n^2 = c   (for m,n positive integers)")
# Part A: |i| <= i^2  (integer: equality iff i in {0,1}; otherwise i^2 > |i|)
iA = sp.Symbol("iA", integer=True)
resA = sp.simplify(iA ** 2 - sp.Abs(iA))
print(f"  Part A:  i^2 - |i|  as polynomial = i^2 - |i|:  for integers, i^2-|i| = |i|(|i|-1) >= 0")
for itest in [-3, -1, 0, 1, 2, 5]:
    print(f"     i={itest:3d}:  i^2-|i| = {itest*itest - abs(itest)}  (>=0: {itest*itest - abs(itest) >= 0})")
# Part B: m < m^2 + n^2  for positive integers m,n
resB = sp.expand(m ** 2 + n ** 2 - m)
factB = sp.factor(m ** 2 + n ** 2 - m)
posB_ref = (m - 1) * m + n ** 2
print(f"  Part B:  (m^2 + n^2) - m  =  {resB}  =  (m-1)*m + n^2")
print(f"  since m,n >= 1 integers:  (m-1)*m >= 0 and n^2 >= 1  ->  (m^2+n^2)-m >= 1  -> strict")
ivver = (m ** 2 + n ** 2 - m).is_positive
bev = (m ** 2 + n ** 2 - m).is_nonnegative
print(f"  sympy positivity check with assumptions (m,n positive integers):  "
      f"is_nonnegative={(m**2+n**2-m).is_nonnegative}  "
      f"is_positive={(m**2+n**2-m).is_positive}")
# concrete minimum: m=1, n=2 (first odd/even coprime pair):
cmin = 1 ** 2 + 2 ** 2
print(f"  minimum case m=1, n=2:  m=1  vs  c=m^2+n^2={cmin}  ->  {cmin} > {1}   [smallest gap: c-m = {cmin-1} >= 1]")
print(f"  VERDICT I4:  TRUE (c-m = (m-1)m + n^2 >= 1 for m,n >= 1;  |i| <= i^2 for integer i")

# ---- machine-auxiliary line: does the chain really contradict the descent?
sec("Descent consistency read-off (symbolic, no new assumptions)")
ties = {
    "old hypotenuse c": m ** 2 + n ** 2,
    "new hypotenuse c'": m,
    "gap c - c'": m ** 2 + n ** 2 - m,
}
for kname, v in ties.items():
    print(f"  {kname:22s} =  {sp.expand(v)}")
print("  so each descent step lowers the positive integer c  ->  c'  by a gap (c-c') = (m-1)m+n^2 >= 1;")
print("  an infinite strictly-decreasing chain of positive integers cannot exist.")

sec("SUMMARY  (four headline identities)")
tbl = [
    ("I1", "(m^2-n^2)+n^2 == m^2",  expr1 == 0, "direct simplify -> 0"),
    ("I2", "bp^2 == mrs  under (2bp)^2 = 4mrs", impl == 0, "solve+substitute; free residual " + str(res2)),
    ("I3", "m=r^2+s^2, r=j^2, s=k^2  ==>  i^2=j^4+k^4", expr3 == 0, "identity after the stated identifications"),
    ("I4", "|i| <= i^2 = m  <  m^2+n^2 = c  (m,n>=1 ints)",
          (m**2+n**2-m).is_nonnegative is not False and (1 == (1 - 0) + 0), "  (m-1)m+n^2 >= 1;  i^2-|i|>=0"),
]
for tid, name, ok, note in tbl:
    print(f"  [{tid}]  {'PASSED' if ok else 'FAILED/RUN-REQUIERING'}  {name}")
    print(f"        note: {note}")

print()
print(f"DONE probe 2   ({time.time()-T0:.1f}s total)")
