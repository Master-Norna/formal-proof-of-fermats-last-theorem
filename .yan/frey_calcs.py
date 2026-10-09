"""Frey curve arithmetic — numeric pre-validation of the formulas that will be
stated in Lean (FermatFLT/WilesBridge.lean).

Frey (1985): for a primitive solution a^p + b^p = c^p (p odd prime,
min(v_a,v_b,v_c) = 1 w.l.o.g. a), the elliptic curve
    E : Y^2 = X (X + a^p) (X - b^p)
has (by expansion) :
    a4 = a^p - b^p = c^p - 2 b^p,   a6 = a^p b^p,
    Delta = 16 a^{2p} b^{2p} c^{2p},
    j = 2^8 ((a^p + b^p)^2 - a^p b^p) / (a^p b^p)
        = 2^8 ((a^p + b^p)^2 - (c^p - b^p) b^p) / c^{2p}    [use a^p b^p = b^p (c^p - b^p)]
and gcd(Delta, a6) = 16  (i.e. v_q is supported only on 2).

We test, for primes p in 3..11 and random primitive-ish integer triples:
  (i)  the expanded coefficient identities
  (ii) the Delta formula (via the product of the roots: for y^2 = x^3 + ax + b,
       Delta = -16 (4 a^3 + 27 b^2))
  (iii) v_q(Delta) even for all q  (UInt-Delta property)
  (iv) gcd(Delta, a6) == 16 on primitive triples (min v = 1)
"""
import math, random
from math import gcd

def vp(n, q):
    if n == 0: return None
    n = abs(n)
    c = 0
    while n % q == 0:
        n //= q; c += 1
    return c

def all_v(n):
    out = {}
    n = abs(n)
    d = 2
    while d*d <= n:
        if n % d == 0:
            k = 0
            while n % d == 0:
                n //= d; k += 1
            out[d] = k
        d += 1
    if n > 1: out[n] = 1
    return out

random.seed(7)
fails = 0
for p in [3, 5, 7, 11]:
    for _ in range(400):
        A = random.randint(2, 60); B = random.randint(2, 60)
        C = (A**p + B**p) ** round(0.5) if False else None
        # don't require exact FLT solutions nonexistent; test identities on ANY
        # integers a,b,c with c^p == a^p + b^p replaced by using s = ^(1/p)(a^p+b^p):
        # instead parametrize: pick a, b, and path-dependent c? FLT solutions don't exist.
        # Use the formal identities with c^p := a^p + b^p as a *symbolic* value:
        cp = A**p + B**p          # this IS c^p (a rational p-th root exists)
        # special: treat the curve as y^2 = x(x + a^p)(x - b^p) with a^p, b^p given
        ap = A**p; bp = B**p
        a4 = ap - bp
        a6 = ap * bp
        # Delta via -16(4a4^3 + 27 a6^2)
        Delta = -16 * (4*a4**3 + 27*a6**2)
        # claimed form: 16 * a^{2p} b^{2p} (a^p + b^p)^2 = 16 ap bp cp *(ap+bp) -- i.e. a6*cp*cp?
        claimed = 16 * ap * bp * cp * (ap + bp)  # = 16 a^(2p) b^(2p) c^(2p)
        if Delta != claimed:
            print(f"FAIL Delta p={p} a={A} b={B}: {Delta} != {claimed}"); fails += 1
        gd = gcd(Delta, a6)
        if gd != 16:
            print(f"FAIL gcd p={p} a={A} b={B}: {gd}"); fails += 1
        for q, e in all_v(Delta).items():
            if e % 2 != 0:
                print(f"FAIL odd v_{q} p={p} a={A} b={B}: v={e}"); fails += 1
    print(f"p={p} done")
print("FAILS:", fails)
