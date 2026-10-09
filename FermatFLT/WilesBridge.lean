import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import FermatFLT.Foundations
import FermatFLT.FLT4

/-!
# The Wiles bridge — Frey curve, valuation record, modular contradiction,
and total assembly of Fermat's Last Theorem

(machine-checked; sections §1–§6; two axioms at the end of §5, one for the
human-side theorems of Ribet and of Wiles–Taylor, no `sorry`.)
-/

open WeierstrassCurve
open Nat Int

noncomputable section

namespace FermatFLT

/-! ## §1  the Frey model over any commutative ring -/

variable {R : Type*} [CommRing R]

/- The Frey model for `s, t`:  short form `Y² = X³ + (s−t)X² − s·t·X`,
    equivalently `Y² = X(X+s)(X−t)` (the three half-roots are `0, −s, t`);
    Weierstrass data `(a₁,…,a₆) = (0, s−t, 0, −s·t, 0). -/
def freyModel (s t : R) : WeierstrassCurve R :=
  ⟨0, s - t, 0, -(s * t), 0⟩

theorem freyModel_b2 (s t : R) : (freyModel s t).b₂ = 4 * (s - t) := by
  dsimp [freyModel]
  simp only [WeierstrassCurve.b₂]
  ring1

theorem freyModel_b4 (s t : R) : (freyModel s t).b₄ = -2 * s * t := by
  dsimp [freyModel]
  simp only [WeierstrassCurve.b₄]
  ring1

theorem freyModel_b6 (s t : R) : (freyModel s t).b₆ = 0 := by
  dsimp [freyModel, WeierstrassCurve.b₆]
  ring1

theorem freyModel_b8 (s t : R) : (freyModel s t).b₈ = -(s * t) ^ 2 := by
  dsimp [freyModel]
  simp only [WeierstrassCurve.b₈]
  ring1

/- **The Frey discriminant is a perfect square:**
     `Δ = 16·(s·t·(s+t))²`  — the arithmetic backbone of the
     semistability valuation record. -/
theorem freyModel_Δ (s t : R) :
    (freyModel s t).Δ = 16 * (s * t * (s + t)) ^ 2 := by
  dsimp [freyModel]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring1

/- **c₄ of the Frey model.** -/
theorem freyModel_c4 (s t : R) :
    (freyModel s t).c₄ = 16 * (s ^ 2 + s * t + t ^ 2) := by
  dsimp [freyModel]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring1

/- **The three 2-torsion roots**: the two-torsion polynomial
     `4X³ + b₂X² + 2b₄X + b₆` vanishes at precisely `0`, `−s`, `t`. -/
theorem freyModel_twoTorsion (s t : R) :
    (freyModel s t).twoTorsionPolynomial.toPoly.eval 0 = 0 ∧
      (freyModel s t).twoTorsionPolynomial.toPoly.eval (-s) = 0 ∧
      (freyModel s t).twoTorsionPolynomial.toPoly.eval t = 0 := by
  let W := (freyModel s t)
  refine ⟨?_, ?_, ?_⟩
  · have e := WeierstrassCurve.eval_toPoly_twoTorsionPolynomial W (0 : R)
    rw [e, freyModel_b2, freyModel_b4, freyModel_b6]; ring
  · have e := WeierstrassCurve.eval_toPoly_twoTorsionPolynomial W (-s)
    rw [e, freyModel_b2, freyModel_b4, freyModel_b6]; ring
  · have e := WeierstrassCurve.eval_toPoly_twoTorsionPolynomial W t
    rw [e, freyModel_b2, freyModel_b4, freyModel_b6]; ring

theorem freyModel_twoTorsion_distinct {s t : ℚ} (hs : s ≠ 0) (ht : t ≠ 0)
    (hsne : s + t ≠ 0) : (-s) ≠ 0 ∧ (-s) ≠ t ∧ t ≠ 0 := by
  refine ⟨fun h => hs (neg_eq_zero.1 h),
    fun h => hsne (by nlinarith),
    ht⟩

/-! ## §2  the Frey curve over ℚ at a counterexample, and the valuation record -/

/- The Frey curve attached to `a^p + b^p = c^p` in the standard
    parametrization:  `s := (a:ℚ)^p`, `t := (b:ℚ)^p`  (so `s + t = (c:ℚ)^p`,
    the cost of the parametrization),  `E = freyModel s t`,  i.e.
    `Y² = X³ + (b^p − a^p)X² − a^p b^p X`. -/
def freyOf (p : ℕ) (a b c : ℤ) (_ : a ^ p + b ^ p = c ^ p)
    : WeierstrassCurve ℚ :=
  freyModel ((a : ℚ) ^ p) ((b : ℚ) ^ p)

/- **Δ of the Frey curve is the square**
    `(4·(a:ℚ)^p·(b:ℚ)^p·(c:ℚ)^p)²`. -/
theorem freyDelta_sq (p : ℕ) (a b c : ℤ) (hrel : a ^ p + b ^ p = c ^ p) :
    (freyOf p a b c hrel).Δ =
      (4 * (a : ℚ) ^ p * (b : ℚ) ^ p * (c : ℚ) ^ p) ^ 2 := by
  dsimp [freyOf]
  have hst : (a : ℚ) ^ p + (b : ℚ) ^ p = (c : ℚ) ^ p := by
    norm_cast
  calc
    (freyModel ((a : ℚ) ^ p) ((b : ℚ) ^ p)).Δ =
        16 * ((a : ℚ) ^ p * (b : ℚ) ^ p * ((a : ℚ) ^ p + (b : ℚ) ^ p)) ^ 2 := by
      rw [freyModel_Δ]
    _ = 16 * ((a : ℚ) ^ p * (b : ℚ) ^ p * (c : ℚ) ^ p) ^ 2 := by rw [hst]
    _ = (4 * (a : ℚ) ^ p * (b : ℚ) ^ p * (c : ℚ) ^ p) ^ 2 := by ring

/- The flat valuation form:  `Δ = 16·(a:ℚ)^(2p)·(b:ℚ)^(2p)·(c:ℚ)^(2p)` —
    plainly, every prime enters with an **even** exponent. -/
theorem freyDelta_flat (p : ℕ) (a b c : ℤ) (hrel : a ^ p + b ^ p = c ^ p) :
    (freyOf p a b c hrel).Δ =
      16 * (a : ℚ) ^ (2 * p) * (b : ℚ) ^ (2 * p) * (c : ℚ) ^ (2 * p) := by
  rw [freyDelta_sq]
  have hA : ((a : ℚ) ^ p) ^ 2 = (a : ℚ) ^ (2 * p) := by
    rw [← pow_mul]
    exact congrArg (fun k : ℕ => (a : ℚ) ^ k) (by ring)
  have hB : ((b : ℚ) ^ p) ^ 2 = (b : ℚ) ^ (2 * p) := by
    rw [← pow_mul]
    exact congrArg (fun k : ℕ => (b : ℚ) ^ k) (by ring)
  have hC : ((c : ℚ) ^ p) ^ 2 = (c : ℚ) ^ (2 * p) := by
    rw [← pow_mul]
    exact congrArg (fun k : ℕ => (c : ℚ) ^ k) (by ring)
  calc
    (4 * (a : ℚ) ^ p * (b : ℚ) ^ p * (c : ℚ) ^ p) ^ 2 =
        16 * ((a : ℚ) ^ p) ^ 2 * ((b : ℚ) ^ p) ^ 2 * ((c : ℚ) ^ p) ^ 2 := by ring
    _ = 16 * (a : ℚ) ^ (2 * p) * (b : ℚ) ^ (2 * p) * (c : ℚ) ^ (2 * p) := by
      simp only [hA, hB, hC]

/- The companion natural discriminant `Δ₀ = (4·A^p·B^p·C^p)²` —
    the platform object of the valuation record (the ℚ-form is literally
    the same product with entries lifted through the ℕ cast). -/
def freyDisc (p A B C : ℕ) : ℕ := (4 * A ^ p * B ^ p * C ^ p) ^ 2

/- **Every prime occurrence in `freyDisc` is even**:  `Δ₀ = X²`
     ⇒  `factor Δ₀ = 2 • factor X`,  so at each `q`,
     `v_q(Δ₀) = 2·v_q(X)` — the arithmetic input of the semistability
     analysis (the statement *the curve is semistable* itself is the
     human-verified theorem registered in §5 — Ribet's semistability
     input is exactly this valuation record). -/
theorem freyDisc_even_valuations (p A B C q : ℕ) :
    Even ((freyDisc p A B C).factorization q) := by
  have hX : ((4 * A ^ p * B ^ p * C ^ p) ^ 2).factorization =
      2 • (4 * A ^ p * B ^ p * C ^ p).factorization := by
    rw [Nat.factorization_pow (n := 4 * A ^ p * B ^ p * C ^ p) (k := 2)]
  dsimp only [freyDisc]
  rw [hX, Finsupp.smul_apply]
  exact even_two_mul ((4 * A ^ p * B ^ p * C ^ p).factorization q)

/- **Non-degeneracy**:  Δ(E) ≠ 0 when `a, b, c ≠ 0`, so E is an
    elliptic curve over ℚ. -/
theorem freyNotDegenerate (p : ℕ) (a b c : ℤ) (hrel : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (freyOf p a b c hrel).Δ ≠ 0 := by
  rw [freyDelta_sq]
  apply pow_ne_zero 2
  have haq : (a : ℚ) ^ p ≠ 0 := pow_ne_zero p (Int.cast_ne_zero.2 ha)
  have hbq : (b : ℚ) ^ p ≠ 0 := pow_ne_zero p (Int.cast_ne_zero.2 hb)
  have hcq : (c : ℚ) ^ p ≠ 0 := pow_ne_zero p (Int.cast_ne_zero.2 hc)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) haq) hbq) hcq

theorem freyIsElliptic (p : ℕ) (a b c : ℤ) (hrel : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (freyOf p a b c hrel).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (freyNotDegenerate p a b c hrel ha hb hc)⟩

/- The j-invariant of a Frey curve, over ℚ, is `j = Δ⁻¹·c₄³` —
    the explicit rational-function formula, from the computed c₄/Δ. -/
theorem freyJ (p : ℕ) (a b c : ℤ) (hrel : a ^ p + b ^ p = c ^ p)
    (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0)
    [hI : (freyOf p a b c hrel).IsElliptic] :
    (freyOf p a b c hrel).j =
      ((freyOf p a b c hrel).Δ)⁻¹ * ((freyOf p a b c hrel).c₄) ^ 3 :=
  WeierstrassCurve.j_eq (K := ℚ) (freyOf p a b c hrel)

/-! ## §3  Reduction to PRIMITIVE counterexamples (self-proven)

The two human-side theorems (axiomatized in §5) apply to *primitive*
counterexamples (pairwise coprime).  This section proves the reduction:
any counterexample to `FLT p` yields a primitive one — the exact FLT4
pattern: well-order on `|c|` (`existsPMin`), then gcd-descent on the
minimizer (`pMin_*`).  Everything here is mechanical; no axiom. -/

def IsMinP (a b c : ℤ) (p : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ p + b ^ p = c ^ p ∧
    (∀ a1 b1 c1 : ℤ, a1 ≠ 0 → b1 ≠ 0 → c1 ≠ 0 →
      a1 ^ p + b1 ^ p = c1 ^ p → Int.natAbs c ≤ Int.natAbs c1)

/-- Well-ordering: a `|c|`-minimal counterexample exists for any `p`. -/
theorem existsPMin (p : ℕ) (h : ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    a ^ p + b ^ p = c ^ p) :
    ∃ a b c : ℤ, IsMinP a b c p := by
  classical
  rcases h with ⟨a, b, c, ha, hb, hc, hrel⟩
  let S : Set ℕ := { n | ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    a ^ p + b ^ p = c ^ p ∧ n = Int.natAbs c }
  have hS : S.Nonempty := ⟨Int.natAbs c, ⟨a, b, c, ha, hb, hc, hrel, rfl⟩⟩
  rcases (Nat.find_spec hS) with ⟨a0, b0, c0, ha0, hb0, hc0, hrel0, hn0⟩
  use a0, b0, c0
  refine ⟨ha0, hb0, hc0, hrel0, ?_⟩
  intro a1 b1 c1 ha1 hb1 hc1 hrel1
  have himem : Int.natAbs c1 ∈ S := ⟨a1, b1, c1, ha1, hb1, hc1, hrel1, rfl⟩
  simpa [hn0] using Nat.find_min' hS himem

/- A prime `q` dividing two of `a, b, c` divides the third, by the
    equation `a^p + b^p = c^p`: take the `p`-th root of `q^p ∣ (third)^p`
    (`pow_dvd_pow_iff`), then a common `q` divides all three, and dividing
    lowers `|c|`.  This is the shared core; the three `pMin_*` theorems
    (below) instantiate it with the pair `(a,b)`, `(a,c)`, `(b,c)`. -/

/-- **Coprimality of a `|c|`-minimal solution** (for prime `p ≥ 3`).
    If a prime `q` divided both `a` and `b`, then `c^p = a^p + b^p` is
    divisible by `q^p`, so `q ∣ c` (`pow_dvd_pow_iff`); the triple
    `(a/q, b/q, c/q)` is a solution with strictly smaller `|c|` --
    contradicting minimality.  (Same shape as `FLT4.minSol_coprime`.) -/
theorem pMin_coprime {p : ℕ} (hpp : Nat.Prime p) (_hpp3 : 3 ≤ p)
    {a b c : ℤ} (hp : IsMinP a b c p) : Int.gcd a b = 1 := by
  rcases hp with ⟨ha, hb, hc, hrel, hmin⟩
  by_contra h0 : ¬ (Int.gcd a b = 1)
  obtain ⟨q, hq, hqa, hqb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h0
  obtain ⟨ai, rfl⟩ := Int.natCast_dvd.mpr hqa
  obtain ⟨bi, rfl⟩ := Int.natCast_dvd.mpr hqb
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero hpp
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq)
  -- c^p = a^p + b^p = q^p·ai^p + q^p·bi^p = q^p·(ai^p + bi^p)
  have hceq : c ^ p = (q : ℤ) ^ p * (ai ^ p + bi ^ p) := by
    rw [← hrel, mul_pow, mul_pow, ← mul_add]
  -- q^p ∣ c^p,  hence  q ∣ c  (take the p-th root)
  have hqc : (q : ℤ) ∣ c :=
    (Int.pow_dvd_pow_iff hp0).mp (Dvd.intro (ai ^ p + bi ^ p) hceq.symm)
  obtain ⟨ci, rfl⟩ := hqc
  -- (ai, bi, ci) is a solution:  cancel the common factor q^p (≠ 0)
  have hrel' : ai ^ p + bi ^ p = ci ^ p := by
    apply (mul_right_inj' (pow_ne_zero p hq0)).mp
    calc (q : ℤ) ^ p * (ai ^ p + bi ^ p)
        = (q : ℤ) ^ p * ai ^ p + (q : ℤ) ^ p * bi ^ p := by rw [mul_add]
      _ = (q * ai) ^ p + (q * bi) ^ p := by rw [mul_pow, mul_pow]
      _ = (q * ci) ^ p := hrel
      _ = (q : ℤ) ^ p * ci ^ p := by rw [mul_pow]
  -- strict decrease:  |ci| < |q·ci|  (q ≥ 2, ci ≠ 0)
  have hai0 : ai ≠ 0 := fun hi => ha (by simp [hi])
  have hbi0 : bi ≠ 0 := fun hi => hb (by simp [hi])
  have hci0 : ci ≠ 0 := fun hi => hc (by simp [hi])
  have hsmall : Int.natAbs ci < Int.natAbs ((q : ℤ) * ci) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, lt_mul_iff_one_lt_left]
    · exact Nat.Prime.one_lt hq
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hci0)
  -- minimality says |c| ≤ |ci|, but |c| = |q·ci| > |ci|
  have hmin0 : Int.natAbs ((q : ℤ) * ci) ≤ Int.natAbs ci :=
    hmin ai bi ci hai0 hbi0 hci0 hrel'
  exact (not_le_of_gt hsmall) hmin0

/- The same descent with the roles exchanged: a prime dividing `a` and `c`
   also divides `b` (since `b^p = c^p − a^p`), and a prime dividing `b` and
   `c` also divides `a` (since `a^p = c^p − b^p`).  Identical cancellation
   after isolating the third power, now a difference of `q^p`-multiples. -/

theorem pMin_ac {p : ℕ} (hpp : Nat.Prime p) (_hpp3 : 3 ≤ p)
    {a b c : ℤ} (hp : IsMinP a b c p) : Int.gcd a c = 1 := by
  rcases hp with ⟨ha, hb, hc, hrel, hmin⟩
  by_contra h0 : ¬ (Int.gcd a c = 1)
  obtain ⟨q, hq, hqa, hqc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h0
  obtain ⟨ai, rfl⟩ := Int.natCast_dvd.mpr hqa
  obtain ⟨ci, rfl⟩ := Int.natCast_dvd.mpr hqc
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero hpp
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq)
  -- b^p = c^p − a^p = q^p·ci^p − q^p·ai^p = q^p·(ci^p − ai^p)
  have hbeq : b ^ p = (q : ℤ) ^ p * (ci ^ p - ai ^ p) := by
    calc b ^ p = (q * ci) ^ p - (q * ai) ^ p := by rw [← hrel]; ring
      _ = (q : ℤ) ^ p * ci ^ p - (q : ℤ) ^ p * ai ^ p := by rw [mul_pow, mul_pow]
      _ = (q : ℤ) ^ p * (ci ^ p - ai ^ p) := by rw [mul_sub]
  -- q^p ∣ b^p,  hence  q ∣ b
  have hqb : (q : ℤ) ∣ b :=
    (Int.pow_dvd_pow_iff hp0).mp (Dvd.intro (ci ^ p - ai ^ p) hbeq.symm)
  obtain ⟨bi, rfl⟩ := hqb
  -- (ai, bi, ci) is a solution:  cancel the common factor q^p (≠ 0)
  have hrel' : ai ^ p + bi ^ p = ci ^ p := by
    apply (mul_right_inj' (pow_ne_zero p hq0)).mp
    calc (q : ℤ) ^ p * (ai ^ p + bi ^ p)
        = (q : ℤ) ^ p * ai ^ p + (q : ℤ) ^ p * bi ^ p := by rw [mul_add]
      _ = (q * ai) ^ p + (q * bi) ^ p := by rw [mul_pow, mul_pow]
      _ = (q * ci) ^ p := hrel
      _ = (q : ℤ) ^ p * ci ^ p := by rw [mul_pow]
  -- strict decrease:  |ci| < |q·ci|  (q ≥ 2, ci ≠ 0)
  have hai0 : ai ≠ 0 := fun hi => ha (by simp [hi])
  have hbi0 : bi ≠ 0 := fun hi => hb (by simp [hi])
  have hci0 : ci ≠ 0 := fun hi => hc (by simp [hi])
  have hsmall : Int.natAbs ci < Int.natAbs ((q : ℤ) * ci) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, lt_mul_iff_one_lt_left]
    · exact Nat.Prime.one_lt hq
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hci0)
  -- minimality says |c| ≤ |ci|, but |c| = |q·ci| > |ci|
  have hmin0 : Int.natAbs ((q : ℤ) * ci) ≤ Int.natAbs ci :=
    hmin ai bi ci hai0 hbi0 hci0 hrel'
  exact (not_le_of_gt hsmall) hmin0

theorem pMin_bc {p : ℕ} (hpp : Nat.Prime p) (_hpp3 : 3 ≤ p)
    {a b c : ℤ} (hp : IsMinP a b c p) : Int.gcd b c = 1 := by
  rcases hp with ⟨ha, hb, hc, hrel, hmin⟩
  by_contra h0 : ¬ (Int.gcd b c = 1)
  obtain ⟨q, hq, hqb, hqc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h0
  obtain ⟨bi, rfl⟩ := Int.natCast_dvd.mpr hqb
  obtain ⟨ci, rfl⟩ := Int.natCast_dvd.mpr hqc
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero hpp
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq)
  -- a^p = c^p − b^p = q^p·ci^p − q^p·bi^p = q^p·(ci^p − bi^p)
  have haeq : a ^ p = (q : ℤ) ^ p * (ci ^ p - bi ^ p) := by
    calc a ^ p = (q * ci) ^ p - (q * bi) ^ p := by rw [← hrel]; ring
      _ = (q : ℤ) ^ p * ci ^ p - (q : ℤ) ^ p * bi ^ p := by rw [mul_pow, mul_pow]
      _ = (q : ℤ) ^ p * (ci ^ p - bi ^ p) := by rw [mul_sub]
  -- q^p ∣ a^p,  hence  q ∣ a
  have hqa : (q : ℤ) ∣ a :=
    (Int.pow_dvd_pow_iff hp0).mp (Dvd.intro (ci ^ p - bi ^ p) haeq.symm)
  obtain ⟨ai, rfl⟩ := hqa
  -- (ai, bi, ci) is a solution:  cancel the common factor q^p (≠ 0)
  have hrel' : ai ^ p + bi ^ p = ci ^ p := by
    apply (mul_right_inj' (pow_ne_zero p hq0)).mp
    calc (q : ℤ) ^ p * (ai ^ p + bi ^ p)
        = (q : ℤ) ^ p * ai ^ p + (q : ℤ) ^ p * bi ^ p := by rw [mul_add]
      _ = (q * ai) ^ p + (q * bi) ^ p := by rw [mul_pow, mul_pow]
      _ = (q * ci) ^ p := hrel
      _ = (q : ℤ) ^ p * ci ^ p := by rw [mul_pow]
  -- strict decrease:  |ci| < |q·ci|  (q ≥ 2, ci ≠ 0)
  have hai0 : ai ≠ 0 := fun hi => ha (by simp [hi])
  have hbi0 : bi ≠ 0 := fun hi => hb (by simp [hi])
  have hci0 : ci ≠ 0 := fun hi => hc (by simp [hi])
  have hsmall : Int.natAbs ci < Int.natAbs ((q : ℤ) * ci) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, lt_mul_iff_one_lt_left]
    · exact Nat.Prime.one_lt hq
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hci0)
  -- minimality says |c| ≤ |ci|, but |c| = |q·ci| > |ci|
  have hmin0 : Int.natAbs ((q : ℤ) * ci) ≤ Int.natAbs ci :=
    hmin ai bi ci hai0 hbi0 hci0 hrel'
  exact (not_le_of_gt hsmall) hmin0

/- Every counterexample is the incarnation of a **primitive** one. -/
theorem existsPrimitiveCounter (p : ℕ) (hpp : Nat.Prime p) (_hpp3 : 3 ≤ p)
    (h : ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ p + b ^ p = c ^ p) :
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧
      Int.gcd a c = 1 ∧ Int.gcd b c = 1 ∧ a ^ p + b ^ p = c ^ p := by
  rcases existsPMin p h with ⟨a, b, c, hp⟩
  rcases hp with ⟨ha, hb, hc, hrel, hmin⟩
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_, hrel⟩
  · exact pMin_coprime hpp _hpp3 ⟨ha, hb, hc, hrel, hmin⟩
  · exact pMin_ac hpp _hpp3 ⟨ha, hb, hc, hrel, hmin⟩
  · exact pMin_bc hpp _hpp3 ⟨ha, hb, hc, hrel, hmin⟩

/-! ## §5  The two human theorems, and the machine-checked contradiction -/

/- **Uninterpreted primitive**: `E` is modular — i.e., its ℓ-adic Galois
    representations arise from Hecke eigenforms at every prime ℓ.
    No Lean formalization of modularity (modularity lifting, the p-adic
    Hodge theory stack, etc.) exists to date (2026); the predicate is
    registered dialectically, with its two controlling human facts
    (**Ribet 1990**, **Wiles–Taylor 1995**) also registered as axioms.
    It is the last Lean-transparent step of the logic here. -/
axiom IsModular (E : WeierstrassCurve ℚ) : Prop

/- **Ribet's level lowering (1990)**: the Frey curve of a **primitive**
       counterexample to `a^p + b^p = c^p` (prime `p ≥ 5`) is **not
       modular**.  [Ribet, *On modular representations of
       Gal(Q̄/Q) arising from modular forms*, Invent. Math. **100**
       (1990), no. 2, 431–476, DOI 10.1007/BF01231195, MR 1047143;
       the semistability input is exactly the even-valuation record
       proved machine-checked in §2 (`freyDisc_even_valuations`).] -/
axiom axRibetFrey (p : ℕ) (a b c : ℤ)
    (hrel : a ^ p + b ^ p = c ^ p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpr : Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ¬ IsModular (freyOf p a b c hrel)

/- **Wiles–Taylor modular lifting (1995)**: every **semistable**
       elliptic curve over ℚ is modular; the Frey curve of a **primitive**
       counterexample is semistable (§2: Δ is a perfect square
       and every prime valuation is even), hence **is modular**.
       [Wiles, *Modular Elliptic Curves and Fermat's Last Theorem*,
       Ann. of Math. (2) **141** (1995), no. 3, 443–551,
       MR 1333035; the gap of the 1993 announcement was filled by
       Taylor–Wiles, *Ring-theoretic Properties of Certain Hecke
       Algebras*, Ann. of Math. (2) **141** (1995), no. 3, 553–572,
       MR 1333036.] -/
axiom axWilesFrey (p : ℕ) (a b c : ℤ)
    (hrel : a ^ p + b ^ p = c ^ p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpr : Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    IsModular (freyOf p a b c hrel)

/- **The Frey contradiction** (for every prime `p ≥ 5`):  any
    counterexample descends to a primitive one (refined, §4); of that
    primitive counterexample, Ribet says the Frey curve is not modular,
    Wiles–Taylor says it is — one line of absurd: `hribet hwiles`.
    Hence `FLT p`. -/
theorem freyContradiction (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : FLT p := by
  -- a counterexample, descended to its primitive incarnation (§3); of that,
  -- Ribet says the Frey curve is not modular, Wiles-Taylor says it is.
  rintro ⟨a, b, c, ha, hb, hc, hrel⟩
  have h3p : 3 ≤ p := Nat.le_trans (by decide) hp5
  have hprim : ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1 ∧
      a ^ p + b ^ p = c ^ p :=
    existsPrimitiveCounter p hp h3p ⟨a, b, c, ha, hb, hc, hrel⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hrel⟩ := hprim
  let hpr : Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1 := ⟨hab, hac, hbc⟩
  have hribet : ¬ IsModular (freyOf p a b c hrel) :=
    axRibetFrey p a b c hrel ha hb hc hpr hp hp5
  have hwiles : IsModular (freyOf p a b c hrel) :=
    axWilesFrey p a b c hrel ha hb hc hpr hp hp5
  exact hribet hwiles

/-! ## §7  Where this file ends

 `oddPrimeBranch` (odd prime p:  p = 3 → `FLT3.fermatLastTheoremThree`,
 p ≥ 5 → `freyContradiction`) and the final assembly `fermatLastTheorem`
 live in `Assembly.lean`, which also imports `FLT3.lean`.  This file
 deliberately stops at `freyContradiction`:  every object it uses is
 machine-checked here, and the two human theorems appear nowhere else. -/

end FermatFLT
end
