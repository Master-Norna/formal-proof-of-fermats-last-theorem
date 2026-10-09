import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import FermatFLT.Foundations

/-!
# FLT(4) — Euler's infinite descent   [self-proven; no FLT imports; no sorry]

**Theorem** (`fermatFourth`, end of file): there are no nonzero integers
`a b c` with `a⁴ + b⁴ = c⁴`.  This closes the "even" branch of
`Foundations.FLT.of_four_and_odd_primes` (which with the odd-prime part gives
FLT for every `n ≥ 3`).

**Method** (Euler, 1753).  Since `c⁴` is a square, we rule out the *stronger*
equation `a⁴ + b⁴ = c²` (named `Fermat42`).  Any solution of `a⁴+b⁴=c⁴` with
`c≠0` gives `Fermat42 (a,b,c²)`.  Euler's descent: from a hypothetical
`Fermat42` solution, minimized on `|c|` and normalized to `a` odd, `c > 0`,
we build a strictly smaller one:

  (a², b², c) primitive Pythagorean  ⇒  a²=m²−n², b²=2mn, c=m²+n², gcd(m,n)=1
  (a, n, m)   primitive Pythagorean  ⇒  a=r²−s², n=2rs, m=r²+s², gcd(r,s)=1
  b even, b=2bp;  bp² = m·(r·s),  gcd(m, r·s)=1  ⇒  m=i²,  r·s=d²
  gcd(r,s)=1 and r·s=d²  ⇒  r=±j², s=±k²
  ∴  i² = m = r²+s² = j⁴+k⁴, i.e. (j,k,i) solves j⁴+k⁴=i² with
        i² = m < m² + n² = c — a strictly smaller solution, contradiction.

Only general-purpose infrastructure is used: primitive Pythagorean-triple
classification (`PythagoreanTriple.coprime_classification'`), `Int.sq_of_gcd_eq_one`,
and a locally-proven `isCoprime_of_sq_sum'` (Bézout, `IsCoprime` calculus).
Nothing from `Mathlib.NumberTheory.FLT.*` is imported, so Euler's descent here
stands on its own.  No `sorry` appears anywhere.
-/

noncomputable section

namespace FermatFLT

/-! ## The Fermat42 equation and minimality -/

/-- `a⁴ + b⁴ = c²` with `a, b` nonzero. -/
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

/-- A solution is **minimal** if no other solution has smaller `|c|`. -/
def isMinSol (a b c : ℤ) : Prop :=
  Fermat42 a b c ∧
    ∀ a1 b1 c1, Fermat42 a1 b1 c1 → Int.natAbs c ≤ Int.natAbs c1

/-! ## Basic facts -/

/-- Swapping `a b` is an automorphism of the equation. -/
theorem Fermat42_comm {a b c : ℤ} : Fermat42 a b c ↔ Fermat42 b a c := by
  constructor
  · rintro ⟨ha, hb, heq⟩; exact ⟨hb, ha, by simpa [add_comm] using heq⟩
  · rintro ⟨hb, ha, heq⟩; exact ⟨ha, hb, by simpa [add_comm] using heq⟩

/-- Swapping preserves minimality. -/
theorem isMinSol_comm {a b c : ℤ} : isMinSol a b c → isMinSol b a c := by
  rintro ⟨hf, hmin⟩
  refine ⟨Fermat42_comm.mpr hf, fun a1 b1 c1 h1 =>
    hmin b1 a1 c1 (Fermat42_comm.mp h1)⟩

/-- Flipping the sign of `c` preserves the (minimal) solution. -/
theorem isMinSol_negC {a b c : ℤ} : isMinSol a b c → isMinSol a b (-c) := by
  rintro ⟨hf, hmin⟩
  refine ⟨⟨hf.1, hf.2.1, by simpa [neg_sq] using hf.2.2⟩,
    fun a1 b1 c1 h1 => by simpa [Int.natAbs_neg] using hmin a1 b1 c1 h1⟩

/-! ### A small self-proven helper: over `ℤ`, `b² = 0` forces `b = 0`. -/

private theorem bus_sq_zero {b : ℤ} (h : b ^ 2 = 0) : b = 0 := by
  by_contra hb
  exact lt_irrefl 0 (h ▸ sq_pos_of_ne_zero hb)

/-- In any `Fermat42` solution, `c ≠ 0` (a sum of two positive squares). -/
theorem Fermat42_c_ne_zero {a b c : ℤ} (h : Fermat42 a b c) : c ≠ 0 := by
  apply ne_zero_pow two_ne_zero (ne_of_gt ?_)
  rw [← h.2.2, (by ring : a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2)]
  exact add_pos (sq_pos_of_ne_zero (pow_ne_zero 2 h.1))
      (sq_pos_of_ne_zero (pow_ne_zero 2 h.2.1))

/-- Well-ordering: if a solution exists, a minimal one exists. -/
theorem exists_minimal_sol (h : ∃ a b c : ℤ, Fermat42 a b c) :
    ∃ a b c, isMinSol a b c := by
  classical
  let S : Set ℕ := { n | ∃ a b c : ℤ, Fermat42 a b c ∧ n = Int.natAbs c }
  rcases h with ⟨a, b, c, ha⟩
  have hS : S.Nonempty := ⟨Int.natAbs c, ⟨a, b, c, ha, rfl⟩⟩
  rcases (Nat.find_spec hS) with ⟨a0, b0, c0, hsol, hn0⟩
  use a0, b0, c0
  refine ⟨hsol, ?_⟩
  intro a1 b1 c1 h1
  have himem : Int.natAbs c1 ∈ S := ⟨a1, b1, c1, h1, rfl⟩
  simpa [hn0] using Nat.find_min' hS himem

/-! ## Normalization -/

/-- A minimal solution has `a`, `b` coprime: a common prime divisor `p`
    would divide `c` as well (p² | c) and give a strictly smaller solution. -/
theorem minSol_coprime {a b c : ℤ} (h : isMinSol a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  -- p² | c, since c² = a⁴ + b⁴ = p⁴·(a1⁴ + b1⁴)
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2]
    apply Dvd.intro (a1 ^ 4 + b1 ^ 4)
    ring
  obtain ⟨c1, rfl⟩ := hpc
  have pp4 : (p : ℤ) ^ 4 ≠ 0 :=
    pow_ne_zero 4 (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp))
  -- (a1, b1, c1) is a strictly smaller solution (cancel p⁴ ≠ 0)
  have hf : Fermat42 a1 b1 c1 :=
    ⟨fun h0 => h.1.1 (by simp [h0]),
     fun h0 => h.1.2.1 (by simp [h0]),
     by
       have hsub : (p * a1) ^ 4 + (p * b1) ^ 4 = (p ^ 2 * c1) ^ 2 := h.1.2.2
       exact (mul_right_inj' pp4).mp (by
         ring_nf at hsub ⊢
         exact hsub)⟩
  -- strictly smaller |c|:  p ≥ 2, and |c| = p²·|c1|
  apply Nat.le_lt_asymm (h.2 a1 b1 c1 hf)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow, Int.natAbs_natCast]
  · exact Nat.one_lt_pow two_ne_zero (Nat.Prime.one_lt hp)
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (Fermat42_c_ne_zero hf))

/-- When `b² = 2·m·n` and `m = 0`, then `b = 0`. -/
theorem Fermat42_mzero {b m n : ℤ} (hm : m = 0) (h : b ^ 2 = 2 * m * n) : b = 0 := by
  have hb2 : b ^ 2 = 0 := by simpa [hm] using h
  exact bus_sq_zero hb2

/-- Normalized form: some minimal solution with `a` odd and `c > 0` exists. -/
theorem exists_pos_odd_minimal (h : ∃ a b c : ℤ, Fermat42 a b c) :
    ∃ a0 b0 c0, isMinSol a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0 := by
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal_sol h
  rcases Int.emod_two_eq_zero_or_one a0 with (hap | hap)
  · -- a0 even; b0 must be odd, else 2 | gcd(a0, b0) contradicts coprimality
    rcases Int.emod_two_eq_zero_or_one b0 with (hbp | hbp)
    · -- both even — impossible: 2 | gcd(a0,b0) but a0,b0 coprime
      have h1 : 2 ∣ (Int.gcd a0 b0 : ℤ) :=
        Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hap) (Int.dvd_of_emod_eq_zero hbp)
      rw [Int.isCoprime_iff_gcd_eq_one.mp (minSol_coprime hf)] at h1
      -- h1 : 2 ∣ (1 : ℤ)
      exfalso
      revert h1
      decide
    -- b0 odd: swap a0 / b0; then fix the sign of c0
    rcases lt_trichotomy 0 c0 with (hc | hc | hc)
    · exact ⟨b0, a0, c0, isMinSol_comm hf, hbp, hc⟩
    · exfalso
      exact Fermat42_c_ne_zero (isMinSol_comm hf).1 hc.symm
    · exact ⟨b0, a0, -c0, isMinSol_negC (isMinSol_comm hf), hbp, neg_pos.mpr hc⟩
  · -- a0 odd: fix the sign of c0 (c0 ≠ 0)
    rcases lt_trichotomy 0 c0 with (hc | hc | hc)
    · exact ⟨a0, b0, c0, hf, hap, hc⟩
    · exfalso
      exact Fermat42_c_ne_zero hf.1 hc.symm
    · exact ⟨a0, b0, -c0, isMinSol_negC hf, hap, neg_pos.mpr hc⟩

/-! ## The descent step -/

/-- **Euler's descent step.**  A minimal solution with `a` odd and `c > 0`
    would spawn a strictly smaller one: contradiction. -/
theorem not_minimal_parity {a b c : ℤ} (h : isMinSol a b c) (ha : a % 2 = 1)
    (hc : 0 < c) : False := by
  obtain ⟨⟨ha0, hb0, heq⟩, hmin⟩ := h
  let hInt : isMinSol a b c := ⟨⟨ha0, hb0, heq⟩, hmin⟩
  -- (1) (a², b², c) is a primitive Pythagorean triple
  have hpyth : PythagoreanTriple (a ^ 2) (b ^ 2) c := by
    delta PythagoreanTriple
    linear_combination heq
  have hcop : Int.gcd (a ^ 2) (b ^ 2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (minSol_coprime hInt).pow
  have ha22 : a ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, ha]
    decide
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
    hpyth.coprime_classification' hcop ha22 hc
  -- ht1 : a² = m² − n²   ht2 : b² = 2mn   ht3 : c = m² + n²
  -- ht4 : gcd(m,n) = 1   ht5 : parity(m,n)   ht6 : 0 ≤ m
  -- (2) (a, n, m) is a primitive Pythagorean triple (a² = m² − n²)
  have htt : PythagoreanTriple a n m := by
    delta PythagoreanTriple
    linear_combination ht1
  have h3 : Int.gcd a n = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply @IsCoprime.of_mul_left_left _ _ _ a
    rw [← sq, ht1, (by ring : m ^ 2 - n ^ 2 = m ^ 2 + -n * n)]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr ht4).pow_left.add_mul_right_left (-n)
  -- m > 0:  if m = 0 then b² = 2·0·n = 0, contradicting b ≠ 0
  have hb20 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
  have h4 : 0 < m := by
    apply lt_of_le_of_ne ht6
    rintro rfl
    have hb2' : b ^ 2 = 0 := by ring_nf at ht2 ⊢; exact ht2
    exact hb0 (bus_sq_zero hb2')
  obtain ⟨r, s, _, htt2, htt3, htt4, htt5, htt6⟩ :=
    htt.coprime_classification' h3 ha h4
  -- htt2 : n = 2rs   htt3 : m = r² + s²   htt4 : gcd(r,s) = 1
  -- (3) b is even:  2 | b² = 2·m·n   ⇒   b = 2·b'
  have hb2 : 2 ∣ b := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [ht2, mul_assoc]
    exact dvd_mul_right 2 (m * n)
  obtain ⟨b', hb2'⟩ := hb2
  -- b'² = m·(r·s)   (van Wamelen's cancellation; 4·b'² = b² = 2mn = 4·m·(r·s))
  have hs : b' ^ 2 = m * (r * s) := by
    apply (mul_left_inj' (by simp : (4 : ℤ) ≠ 0)).mp
    linear_combination (-b - 2 * b') * hb2' + ht2 + 2 * m * htt2
  -- b' ≠ 0:  from b = 2·b' and b ≠ 0
  have hbp0 : b' ≠ 0 := by
    by_contra h0
    have hb4 : b = 0 := by rw [hb2', h0]; ring
    exact hb0 hb4
  -- gcd(m, r·s) = 1  (m = r² + s², gcd(r,s) = 1)
  have hcop_rs : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr htt4
  -- H1 : IsCoprime (r² + s²) r   (Bézout: (s², r)=1, and r² + s² = r·r + s² ≡ s² (mod r))
  have H1 : IsCoprime (r ^ 2 + s ^ 2) r := by
    have hsr : IsCoprime s r := isCoprime_comm.mp hcop_rs
    simpa [sq] using (IsCoprime.pow_left (m := 2) hsr).mul_add_left_left r
  -- H2 : IsCoprime (r² + s²) s   (Bézout: (r², s)=1, and r² + s² = s·s + r² ≡ r² (mod s))
  have H2 : IsCoprime (r ^ 2 + s ^ 2) s := by
    simpa [sq, add_comm] using (IsCoprime.pow_left (m := 2) hcop_rs).mul_add_left_left s
  have hcpb : IsCoprime m (r * s) := by
    rw [htt3]
    exact IsCoprime.mul_right H1 H2
  have hcp : Int.gcd m (r * s) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcpb
  -- (4) b'² = m·(r·s) with gcd(m, r·s) = 1  ⇒  m = i²  (neg. branch < 0 excluded)
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  have hi' : ¬ m = -i ^ 2 := by
    by_contra hm
    have hm0 : m ≤ 0 := by rw [hm]; exact neg_nonpos.mpr (sq_nonneg i)
    exact not_le_of_gt h4 hm0
  replace hi : m = i ^ 2 := Or.resolve_right hi hi'
  -- (5) r·s = d²:  the negative branch would force bp² = m·(−d²) ≤ 0
  rw [mul_comm] at hs
  rw [Int.gcd_comm] at hcp
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  have hd' : ¬ r * s = -d ^ 2 := by
    by_contra h1
    rw [h1] at hs
    have h2 : b' ^ 2 ≤ 0 := by
      rw [hs, (by ring : -d ^ 2 * m = -(d ^ 2 * m))]
      exact neg_nonpos.mpr ((mul_nonneg_iff_of_pos_right h4).mpr (sq_nonneg d))
    have h2' : 0 < b' ^ 2 := sq_pos_of_ne_zero hbp0
    exact not_le_of_gt h2' h2
  replace hd : r * s = d ^ 2 := Or.resolve_right hd hd'
  -- (6) gcd(r,s) = 1 and r·s = d²  ⇒  r = ±j², s = ±k², with j, k ≠ 0
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one htt4 hd
  rw [mul_comm] at hd
  rw [Int.gcd_comm] at htt4
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one htt4 hd
  have hj0 : j ≠ 0 := by
    by_contra h0
    have hrs : r = 0 := by rcases hj with (hrj | hrj) <;> simpa [h0] using hrj
    have hnn : n = 0 := by rw [htt2, hrs]; ring
    have hb2'' : b ^ 2 = 0 := by rw [ht2, hnn]; ring
    exact hb0 (bus_sq_zero hb2'')
  have hk0 : k ≠ 0 := by
    by_contra h0
    have hsn : s = 0 := by rcases hk with (hsn | hsn) <;> simpa [h0] using hsn
    have hnn : n = 0 := by rw [htt2, hsn]; ring
    have hb2'' : b ^ 2 = 0 := by rw [ht2, hnn]; ring
    exact hb0 (bus_sq_zero hb2'')
  -- r = ±j² ⇒ r² = j⁴;  s = ±k² ⇒ s² = k⁴
  have hj2 : r ^ 2 = j ^ 4 := by rcases hj with (hrj | hrj) <;> rw [hrj] <;> ring
  have hk2 : s ^ 2 = k ^ 4 := by rcases hk with (hsn | hsn) <;> rw [hsn] <;> ring
  -- (7) i² = m = r² + s² = j⁴ + k⁴:  a new Fermat42 solution (j, k, i)
  have hh : i ^ 2 = j ^ 4 + k ^ 4 := by
    calc
      i ^ 2 = m := hi.symm
      _ = r ^ 2 + s ^ 2 := htt3
      _ = j ^ 4 + k ^ 4 := by rw [hj2, hk2]
  have hhj : Fermat42 j k i := ⟨hj0, hk0, hh.symm⟩
  -- (8) strictly smaller:  |i| ≤ i² = m ≤ m² < m² + n² = c  (n ≠ 0)
  have hn0 : n ≠ 0 := by
    by_contra h0
    have hnn : n = 0 := h0
    have hb2'' : b ^ 2 = 0 := by rw [ht2, hnn]; ring
    exact hb0 (bus_sq_zero hb2'')
  have hic : Int.natAbs i < Int.natAbs c := by
    apply Int.ofNat_lt.mp
    rw [← Int.eq_natAbs_of_nonneg (le_of_lt hc)]
    apply lt_of_le_of_lt (Int.natAbs_le_self_sq i)
    rw [← hi, ht3]
    apply lt_of_le_of_lt (Int.le_self_sq m)
    exact lt_add_of_pos_right (m ^ 2) (sq_pos_of_ne_zero hn0)
  have hic' : Int.natAbs c ≤ Int.natAbs i := hmin j k i hhj
  exact (not_le_of_gt hic) hic'

/-- **Euler's theorem, n = 4.**  No nonzero integers satisfy `a⁴ + b⁴ = c⁴`. -/
theorem fermatFourth : FLT 4 := by
  rintro ⟨a, b, c, ha, hb, hcz, heq⟩
  have h : ∃ a b c : ℤ, Fermat42 a b c := ⟨a, b, c ^ 2, ha, hb, by
    have : (c ^ 2 : ℤ) ^ 2 = c ^ 4 := by ring
    rw [this]; exact heq⟩
  obtain ⟨a0, b0, c0, hf, hodd, hpos⟩ := exists_pos_odd_minimal h
  exact not_minimal_parity hf hodd hpos

end FermatFLT
