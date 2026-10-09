import Mathlib

/-!
# Fermat's Little Theorem — self-proven (group-order argument, Euler 1736)

No appeal to `Nat.Prime.pow_mod_self`, `ZMod.pow_card_sub_one_eq_one` or
`Int.ModEq.pow_card_sub_one_eq_one`.  Only general arithmetic is used:
the `ZMod p` quotient ring, the unit group `(ZMod p)ˣ` (its cardinality
via `card_units`), and the group fact "every element of a finite group,
raised to the group's order, is the identity" (`pow_card_eq_one`), plus
standard congruence/divisibility calculus.

  ① `0 < r < p` ⇒ `(r : ZMod p)` is a unit.
  ② **core**:   `r < p` ⇒ `(r : ZMod p) ^ p = (r : ZMod p)`.
       `r = 0` case:  `0 ^ p = 0` (`zero_pow`, `p > 0`).
       `0 < r < p`:   by ① a unit `u` with value `r`; `pow_card_eq_one`
       together with `card_units` (`|(ZMod p)ˣ| = p − 1`) gives `u^(p−1) = 1`,
       so `(r : ZMod p)^(p−1) = 1`; with `p = 1 + (p − 1)`:
       `(r : ZMod p)^p = (r : ZMod p)·1`.
  ③ Natural form:  from ②, `(r^p : ZMod p) = (r : ZMod p)`, apply
       `ZMod.natCast_eq_natCast_iff` to get `r^p ≡ r [MOD p]`, and
       `Nat.ModEq.dvd'` gives `p ∣ r^p − r`.
  ④ Integer form:  reduce `a` to the residue `q = a % p` (`0 ≤ q < p`,
       `q = ↑(q.natAbs)`);  use the core for `q.natAbs` to get
       `q^p ≡ q [ZMOD p]`; chain `a ≡ q`, `a^p ≡ q^p`, `q^p ≡ q`,
       `q ≡ a`.
-/

namespace FermatFLT

open ZMod

noncomputable section

/-! ### A unit→ring power bridge (used in ②; one-line induction) -/

/-- Coercing a unit into the ring commutes with taking powers. -/
theorem unitPowCoerce {R : Type*} [CommMonoid R] (u : Rˣ) (n : ℕ) :
    (u : R) ^ n = (u ^ n : R) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]

/-! ## ① Unit criterion -/

/-- Prime `p`, `0 < r < p` ⇒ `r : ZMod p` is a unit. -/
private theorem isUnit_of_pos_lt_prime {p r : ℕ} (hp : Nat.Prime p)
    (hpos : 0 < r) (hlt : r < p) : IsUnit (r : ZMod p) := by
  rw [isUnit_iff_coprime, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hle : p ≤ r := Nat.le_of_dvd hpos hdvd
  exact (not_lt_of_ge hle) hlt

/-! ## ② Core `(ZMod p)` identity -/

/-- **Core, the `(ZMod p)`-form.**  Prime `p`, `r < p`
    ⇒ `(r : ZMod p) ^ p = (r : ZMod p)`. -/
theorem zmodFermatPow {p r : ℕ} (hp : Nat.Prime p) (hlt : r < p) :
    (r : ZMod p) ^ p = (r : ZMod p) := by
  by_cases hz : r = 0
  · subst hz
    simpa using zero_pow (Nat.Prime.ne_zero hp)
  · have hpos : 0 < r := Nat.pos_of_ne_zero hz
    have hU : IsUnit (r : ZMod p) := isUnit_of_pos_lt_prime hp hpos hlt
    let u : (ZMod p)ˣ := hU.unit
    have hval : (u : ZMod p) = (r : ZMod p) := IsUnit.unit_spec hU
    have hFact : Fact (Nat.Prime p) := ⟨hp⟩
    have hcard : Fintype.card (ZMod p)ˣ = p - 1 := card_units p
    have hpm1 : u ^ (p - 1) = 1 := by simpa [hcard] using pow_card_eq_one (x := u)
    have hring : (r : ZMod p) ^ (p - 1) = 1 := by
      calc
        (r : ZMod p) ^ (p - 1) = (u : ZMod p) ^ (p - 1) := by rw [hval.symm]
        _ = (u ^ (p - 1) : ZMod p) := (unitPowCoerce u (p - 1)).symm
        _ = (1 : ZMod p) :=
          (congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hpm1)
    have hsem : 1 + (p - 1) = p := by omega
    calc
      (r : ZMod p) ^ p = (r : ZMod p) ^ (1 + (p - 1)) :=
        (congrArg (fun k : ℕ => (r : ZMod p) ^ k) hsem).symm
      _ = (r : ZMod p) * (r : ZMod p) ^ (p - 1) := by rw [pow_add, pow_one]
      _ = (r : ZMod p) * 1 := by rw [hring]
      _ = (r : ZMod p) := by simp

/-! ## ③ Natural-number form -/

/-- **Fermat's Little Theorem, natural form.**  Prime `p`, `r < p`
    ⇒ `p ∣ r ^ p − r`. -/
theorem fermatLittleNat (hp : Nat.Prime p) (r : ℕ) (hlt : r < p) : p ∣ r ^ p - r := by
  have hz : (r : ZMod p) ^ p = (r : ZMod p) := zmodFermatPow hp hlt
  -- `Nat.cast_pow` bridges the ZMod ring-power (LHS of `hz`) to the genuine
  -- `Nat.cast (r ^ p)` demanded by `natCast_eq_natCast_iff`.
  have hmod : r ^ p ≡ r [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
    rw [Nat.cast_pow]
    exact hz
  exact Nat.ModEq.dvd' hmod.symm

/-! ### The double-cast bridge (ℕ → ℤ → ZMod) -/

/-- Sending a natural into `ZMod p` through `ℤ` is the same as sending it
    directly: the `ℤ` cast is cast-neutral on naturals. -/
private theorem castNatThrough {p r : ℕ} : ((r : ℤ) : ZMod p) = (r : ZMod p) := by
  simp

/-! ## ④ Integer form -/

/-- **Fermat's Little Theorem.**  Prime `p`, any `a : ℤ`
    ⇒ `(p : ℤ) ∣ a ^ p − a`. -/
theorem fermatLittleInt (hp : Nat.Prime p) (a : ℤ) : (p : ℤ) ∣ a ^ p - a := by
  let q : ℤ := a % (p : ℤ)
  have hp0nz : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero hp)
  have hq0 : 0 ≤ q := Int.emod_nonneg a hp0nz
  have hql : q < (p : ℤ) := Int.emod_lt a hp0nz
  have hqe : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq0
  have hrpr : q.natAbs < p := (Int.ofNat_lt).mp (by
    rwa [hqe.symm] at hql)
  -- a ≡ q [ZMOD p], since q = a % p:
  have har : a ≡ q [ZMOD (p : ℤ)] := by
    unfold Int.ModEq
    simp [q]
  -- q^p ≡ q [ZMOD p]:  the core, lifted through the integer cast.
  -- `Int.cast_pow` converts `(q.natAbs : ℤ)^p` (the integer power) to
  -- `((q.natAbs : ℤ) : ZMod p)^p`, and `castNatThrough` identifies the
  -- double cast with the direct natCast: exactly the core equality.
  have hqmod : (q.natAbs : ℤ) ^ p ≡ (q.natAbs : ℤ) [ZMOD (p : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    rw [Int.cast_pow, castNatThrough]
    exact zmodFermatPow hp hrpr
  -- a^p ≡ q^p ≡ (q.natAbs : ℤ)^p ≡ (q.natAbs : ℤ) ≡ q ≡ a:
  have hfinal : a ^ p ≡ a [ZMOD (p : ℤ)] := by
    calc
      a ^ p ≡ q ^ p [ZMOD (p : ℤ)] := Int.ModEq.pow p har
      _ ≡ (q.natAbs : ℤ) ^ p [ZMOD (p : ℤ)] := by
        simp [hqe]
      _ ≡ (q.natAbs : ℤ) [ZMOD (p : ℤ)] := hqmod
      _ ≡ q [ZMOD (p : ℤ)] := by
        simp [hqe]
      _ ≡ a [ZMOD (p : ℤ)] := har.symm
  exact Int.ModEq.dvd hfinal.symm

end

end FermatFLT
