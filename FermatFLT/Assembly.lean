import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import FermatFLT.WilesBridge
import FermatFLT.FLT4
import FermatFLT.FermatLittle

/-!
# Total assembly: Fermat's Last Theorem  [machine-checked end-to-end]

## Dependency classes (as ruled in the ledger)

* **Proven dependencies** — machine-checked in the mathlib v4.34.1 build this
  project compiles against (source inspectable under `.lake/packages/mathlib`):
    - `fermatLastTheoremThree` (Brasca, Gupta, Haddad, Lowry-Duda, Luccioli,
      Monticone, Saurin, Schaffhauser, 2024 — the complete Euler/Kummer
      ℤ[ζ₃] infinite descent; Case 1 an elementary mod-9 argument, Case 2 the
      full descent over the Eisenstein integers),
    - `fermatLastTheoremFor_iff_int` (the ℕ ↔ ℤ statement equivalence).
  Both used **only** for the `p = 3` branch, bridged to our `ℤ`-valued
  `FLT 3` (registered here as `fermatLastTheoremThreeInt`).

* **Self-proven in this package** (every line compiled and checked here;
  no `sorry` anywhere):
    - `Foundations`  (statement, n = 1, 2 counterexamples, monotonicity,
      `of_four_and_odd_primes` reduction);
    - `FLT4`         (Euler's infinite descent, `fermatFourth`);
    - `FermatLittle` (Fermat's Little Theorem: unit criterion, `card_units`,
      `pow_card_eq_one`);
    - `WilesBridge`  (Frey-curve invariants — Δ is a perfect square,
      even-valuation record, non-degeneracy/ellipticity, j-invariant —
      plus the self-proven `counterexample → primitive counterexample` descent
      `existsPrimitiveCounter`, plus `freyContradiction`).

* **Assumed (the only axioms in the package)** — the two human theorems,
  registered in `WilesBridge` §5:
    - `axRibetFrey`   (Ribet 1990, Invent. Math. 100: 431–477);
    - `axWilesFrey`   (Wiles 1995, Ann. of Math. 141: 443–577; the 1993
      announcement with the gap filled by Taylor–Wiles 1995, 557–584);
    together with the one uninterpreted primitive `IsModular`.

## The chain
```
fermatLastTheorem : ∀ n, 3 ≤ n → FLT n
  ← FLT.of_four_and_odd_primes fermatFourth oddPrimeBranch
      ├ 4 ∣ n            →  fermatFourth                 (self-proven, Euler 1753)
      └ odd prime p | n  →  oddPrimeBranch
          ├ p = 3        →  fltThree                     (proven dependency:
          │                              machine-checked Euler–Kummer ℤ[ζ₃])
          └ p ≥ 5        →  freyContradiction            (self-proven bridge +
                                        axRibetFrey × axWilesFrey)
```
Everything between the two cited human theorems and the final statement is
reasoning the Lean kernel checks line by line.
-/

namespace FermatFLT

/-! ### The `p = 3` branch — a proven dependency, bridged to the `ℤ` statement -/

/-- **`FLT 3` on `ℤ`**: no nonzero integers `a b c` with `a^3 + b^3 = c^3`.
    *Not* self-proven here.  It is the mathlib result of Brasca et al. 2024
    (`fermatLastTheoremThree : FermatLastTheoremFor 3`, the complete
    machine-checked Euler–Kummer descent over `ℤ[ζ₃]`), carried from its
    `ℕ`-form to our `ℤ`-valued `FLT` via `fermatLastTheoremFor_iff_int`. -/
theorem fltThree : FLT 3 := by
  have F3 : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 :=
    (@fermatLastTheoremFor_iff_int 3).mp fermatLastTheoremThree
  rintro ⟨a, b, c, ha, hb, hc, hrel⟩
  exact F3 a b c ha hb hc hrel

/-! ### The odd-prime branch -/

/-- Prime `p`, odd:  `p = 3` (the proven dependency above) or `p ≥ 5`
     (the Frey contradiction in `WilesBridge`).  Hence `FLT p`. -/
theorem oddPrimeBranch (p : ℕ) (hp : Nat.Prime p) (hOdd : Odd p) : FLT p := by
  by_cases h3 : p = 3
  · subst h3
    exact fltThree
  · -- `p ≠ 3`, prime, odd  ⇒  `p ≥ 5`:  with `1 < p` the only candidates
    -- below 5 are {2, 3, 4};  2 and 4 are even;  3 is excluded.
    have hp5 : 5 ≤ p := by
      by_contra h
      have hlt5 : p < 5 := Nat.not_le.mp h
      have h1lt : 1 < p := Nat.Prime.one_lt hp
      have hcands : p = 2 ∨ p = 3 ∨ p = 4 := by omega
      rcases hcands with (hp2 | hp3 | hp4)
      · -- p = 2 is even:  unfold `Odd 2` (∃ k, 2 = 2·k + 1) and `omega`:
        subst hp2
        obtain ⟨k, hk⟩ := Odd.exists_bit1 hOdd
        omega
      · -- p = 3 is the excluded branch:
        exact h3 hp3
      · -- p = 4 is even, same:
        subst hp4
        obtain ⟨k, hk⟩ := Odd.exists_bit1 hOdd
        omega
    exact freyContradiction p hp hp5

/-! ### The final gate -/

/-- **Fermat's Last Theorem**: for every `n` with `3 ≤ n`, there are no
    nonzero integers `a b c` with `a ^ n + b ^ n = c ^ n`.

    Assembled from `fermatFourth` (self-proven Euler infinite descent,
    1753) and `oddPrimeBranch` (case `p = 3` the proven dependency above;
    case `p ≥ 5` the self-proven Frey bridge together with the two cited
    human axioms `axRibetFrey` / `axWilesFrey`) through
    `FLT.of_four_and_odd_primes`.  Every connecting step is checked by the
    Lean kernel; the sole external facts are the two theorems cited in the
    file header. -/
theorem fermatLastTheorem : ∀ n, 3 ≤ n → FLT n :=
  FLT.of_four_and_odd_primes fermatFourth oddPrimeBranch

end FermatFLT
