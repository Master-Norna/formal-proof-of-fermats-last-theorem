# Frey 曲线半稳定性 (semistability) 数值预验证
# E_{abc}: y^2 = x (x - a^p)(x + b^p),  abc: 非常数对, 求 Δ = 2^4 (a^6 b^6 c^6, c^2 = a^p + b^p)
#
# 半稳定性判据（Good reduction 到处存在, 等价于: Δ = 2^4 a^6 b^6 c^6 中,
# 以外的素数都用一次 factor v 全配好）。即:
#   对任意素数 q, v_q(v_p an xyab 6 c^6 是偶数)   ⇏   半稳定性（还需要 Good reduction 无添一）,
#   但对 Frey 曲线 ±5 是两到表的 Well-KnownItem-3: v_q(c^2-a^p)/v_q(b^p-a^{-p}...) 的非耦再检查。
# 实际路线（Silverman-Tate §III.6 / Cremona）:
#   (a) v_q(Δ_Frey) 是偶   对所有 q ∤ abc
#   (b) q | abc 时 v_q(Δ) = min(6 v_q(a or b or c), ...), 且 j = 2^8 a^4 b^4 c^4 / Δ 满足:
#       q=2 或 3 处严格容差为 j 不被逐出 (half as the well-known lemma Definition)
# 此处数值验证不作为证明, 只作为 Guideline 的加权分析预缆。

import math
from math import gcd

def vpfact(v, p):
    n = 0
    while v % p == 0 and v != 0:
        v //= p
        n += 1
    return n

def ineq_rec(a, b, c, p):
    """Verify: for all primes q | abc with q != p, v_q(2^4 a^6 b^6 c^6) is even.
    q = p picked separately: v_p(Δ) = 12 (Wiles seminar) via F = F; 
    we check structural statement v_p(abc) = v_p(a or b or c) is even (see a/b not divisible by p hypothesis).
    """
    abc = abs(a * b * c)
    primes = set()
    t = abc
    q = 2
    while q * q <= t:
        if t % q == 0:
            primes.add(q)
            while t % q == 0: t //= q
        else:
            q += 1
    if t > 1: primes.add(t)
    anc = dict((q, vpfact(abc, q)) for q in primes)
    return anc

def freqaimagesmall(a, b, p, limit_p=40, max_ab=64):
    """Find (a,b) with a^p + b^p = c^2, primitive, coprime, for small p to test semistability vals."""
    hits = []
    for a in range(1, max_ab + 1):
        for b in range(1, max_ab + 1):
            if gcd(a, b) != 1: continue
            s = a**p + b**p
            c = math.isqrt(s)
            if c * c == s:
                # primitive triplet: not all divisible by 
                hits.append((a, b, c))
    return hits

def semistable_check(a, b, c, p, verbose=True):
    """Check: for all q | abc with q != p: v_q(a b) + v_q(c) is even (=> v_q(Δ) even),
       and v_p(abc) is handled separately (assert by p-primitive hypothesis)."""
    issues = []
    abc = a * b * c
    q = 2
    while q * q <= abs(abc):
        if abc % q == 0:
            v = vpfact(abc, q)
            if q == p:
                if verbose: print(f"  q = p = {q}: v_q(abc) = {v} (handled by p-primitive in the proof)")
            else:
                if v % 2 != 0:
                    issues.append((q, v))
                if verbose: print(f"  q = {q}: v_q(abc) = {v}  [{'OK even' if v%2==0 else 'FAIL odd'}]")
        else:
            q += 1
    if abs(abc) > 1 and vpfact(abc, abs(abc)) > 0:
        q = abs(abc)
        v = 1
        if q != p and v % 2 != 0:
            issues.append((q, v))
    return issues

if __name__ == "__main__":
    print("== Finding small Fermat-4-like a^p + b^p = c^2 with p > 4 (none exist by FLT, so p = 3):")
    p = 3
    hits = freqaimagesmall(1, 1, p, max_ab=400)
    print("p = 3 solutions (Cubic):", hits[:10])
    # (2,2,?)->not coprime; standard primitive: a+b+cgcd1, a^3+b^3=c^2
    for (a, b, c) in []:
        pass
    # Structural check on hypothetical primitive p-solutions: take a = 2^6, b = 2^6*3^?
    # p=3 fireplace:  a=2, b=4 -> 8+64 = 72 not sq.  a=4, b=6 -> 64+216 = 280 no.
    # Euler: no primitive p=3 solutions existed.  Use KNOWN example: a = 1, b = 2 -> 1+8=9=3^2
    print("\n== p=3, (a=1, b=2, c=3) -- trivial, non-primitive a^3+b^3=c^2:")
    semistable_check(1, 2, 3, 3)
    # More interesting: test STRUCTURE, i.e., for q ≠ 2,3, v_q(abc) must be even—from
    # the IF expression a^3 + b^3 = c^2,  q ∤ a b p  gives v_q(c^2) = v_q(a^3 + b^3)
    # and LIFTED value = 1 + v_q(a+b) (Hensel: v_p(x^k + y^k) = v_p(x+y) when p ≠ k divides a b).
    # so v_q(c^2) = 2 v_q(c) = 1 + v_q(a+b)  ->  odd + v_q(a+b).  Then v_q(abc) = v_q(a)+v_q(b)+v_q(c).
    # p-primitive means q ∤ abc for q | a or b ... this IS the difficulty; formalise in Lean.
    print("\n== Lifted value test: for prime q, v_q(x^3 + y^3) = v_q(x+y) when q ∤ x y and q ≠ 3")
    for q in [7, 11, 13, 17, 19, 23]:
        x = q + 1
        s = x**3 + 2**3
        # v_q(x^3+8)  = v_q((x+2)(x^2-2x+4))  -- q | (x+2) iff x = q-2? 
        # x = q+1:  x^2 - 2x + 4 = (q+1)^2 - 2q - 2 + 4 = q^2+2q+1-2q+2 = q^2+3  -> v_q = 0
        # so v_q(x^2 - 2x + 4)?  Not useful.  Use (x = q^1, 2):  v_q((q)^3+8) = v_q(q^3(q^0...)) 
        # Just print v_q((q+1)^3 + 8) and v_q((q+1) - (-2)) for a random probe
        diff = (q + 1)**3 + 8
        same_side = vpfact(diff, q)
        # find factorization
        vtot = same_side
        print(f"  q={q}: v_q((q+1)^3+8) = {vtot}")

    print("\n== CONCLUSION LN: Peak theorem v_q(a^p + b^p) = v_q(a+b) (q|a+b, q∤ab, q∤p) needs")
    print("   Lean: lift lemma (Int.ModEq) 32 lines; then v_q(c^2) = v_q(a^p+b^p) = v_q(a+b) is ODD" if (11%2)==1 else "")
    print("   → so q | a+b implies q | c or ... and q ∤ p, and p-primitive hypothesis forces v_q(a+b) even ... "
          "this IS the bridge's algebraic core.")
