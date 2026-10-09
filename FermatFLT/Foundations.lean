import Mathlib.Tactic
import Mathlib.Data.Int.GCD

/-!
# Fermat's Last Theorem — statements and the reduction backbone   [machine-checked]

Proven here, from scratch:
  * `FLT n`  definition  /  primitive-triple shape
  * n = 1, 2 have solutions (so the theorem is for n ≥ 3)
  * monotonicity: `m ∣ n` and `FLT m` → `FLT n`
  * **structural split**: for n ≥ 3, FLT(n) follows from FLT(4) and
    FLT at every odd prime (via mathlib's `four_dvd_or_exists_odd_prime…`)
-/

namespace FermatFLT


open Nat Int

/-- FLT(n): no nonzero integer solution to `a^n + b^n = c^n`. -/
def FLT (n : ℕ) : Prop :=
  ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ n + b ^ n = c ^ n

/-- A primitive triple: pairwise coprime. -/
def IsPrimitive (a b c : ℤ) : Prop :=
  Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1

/-! ### Base: n = 1, 2 fail -/

theorem notFLT_one : ¬ FLT 1 := fun h =>
  h ⟨1, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem notFLT_two : ¬ FLT 2 := fun h =>
  h ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Monotonicity in the exponent -/

theorem FLT.mono {m n : ℕ} (hmn : m ∣ n) (hm : FLT m) : FLT n := by
  rintro ⟨a, b, c, ha, hb, hc, heq⟩
  obtain ⟨t, rfl⟩ := hmn
  exact hm ⟨a ^ t, b ^ t, c ^ t,
    pow_ne_zero t ha, pow_ne_zero t hb, pow_ne_zero t hc,
    (by ring_nf at heq ⊢; exact heq)⟩

/-! ### Structural split + the meta-theorem -/

theorem FLT.of_four_and_odd_primes
    (hfour : FLT 4)
    (hop : ∀ p : ℕ, Nat.Prime p → Odd p → FLT p) :
    ∀ n : ℕ, 3 ≤ n → FLT n := by
  intro n hn
  obtain hd | ⟨p, hpp, hdvd, hodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · exact FLT.mono hd hfour
  · exact FLT.mono hdvd (hop p hpp hodd)

/-- "No primitive solution" — the shape of the primitive claim. -/
def FLT_primitive (n : ℕ) : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → IsPrimitive a b c → a ^ n + b ^ n ≠ c ^ n

end FermatFLT
