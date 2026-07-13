import CentralBinomialLean.Reduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős #728 — the problem statement

This file is the reviewer's entry point: it records *only* the paper-facing
statement of Erdős Problem #728 (as in `../erdos728.tex`) and the two central
divisibility predicates used by the central specialization.

- `erdos728Triple` / `erdos728UnboundedTriples` / `erdos728Main` — the theorem
  as claimed in the paper (the unconditional proof `erdos728Main_proved` is in
  `CentralBinomialLean.Statement`).
- `centralBinomialDivides` / `centralFactorialDivides` — the central-pair
  divisibility conditions, with the elementary bridge between them.

No proof machinery lives here; see `CentralBinomialLean.Statement` for the
reduction to a central-pair supply and `CentralBinomialLean.Global` for the
number-theoretic engine.
-/

namespace CentralBinomialLean

namespace Erdos728

/-- The triple condition appearing in Erdős Problem #728.  The real parameters
`ε`, `C₁`, and `C₂` are kept explicit; `a + b - n` is natural-number
truncated subtraction, which agrees with the intended gap in the central
specialization proved below. -/
def erdos728Triple (ε C₁ C₂ : ℝ) (a b n : Nat) : Prop :=
  0 < a ∧
  0 < b ∧
  0 < n ∧
  ε * (n : ℝ) ≤ (a : ℝ) ∧
  ε * (n : ℝ) ≤ (b : ℝ) ∧
  (a : ℝ) ≤ (1 - ε) * (n : ℝ) ∧
  (b : ℝ) ≤ (1 - ε) * (n : ℝ) ∧
  a.factorial * b.factorial ∣ n.factorial * (a + b - n).factorial ∧
  C₁ * Real.log (n : ℝ) < ((a + b - n : Nat) : ℝ) ∧
  ((a + b - n : Nat) : ℝ) < C₂ * Real.log (n : ℝ)

/-- Lean-friendly form of "there are infinitely many triples": triples exist
with unbounded `n`. -/
def erdos728UnboundedTriples (ε C₁ C₂ : ℝ) : Prop :=
  ∀ M : Nat, ∃ a b n : Nat, M ≤ n ∧ erdos728Triple ε C₁ C₂ a b n

/-- The general Erdős #728 target in Lean-friendly unbounded form. -/
def erdos728Main : Prop :=
  ∀ C₁ C₂ ε : ℝ,
    0 < C₁ →
    C₁ < C₂ →
    0 < ε →
    ε < (1 / 2 : ℝ) →
    erdos728UnboundedTriples ε C₁ C₂

/-- A paper-facing central-binomial condition. -/
def centralBinomialDivides (A k : Nat) : Prop :=
  Nat.choose (A + k) k ∣ Nat.choose (2 * A) A

/-- The central factorial-divisibility condition equivalent to
`centralBinomialDivides`. -/
def centralFactorialDivides (A k : Nat) : Prop :=
  A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial

/-- Central binomial divisibility implies the central factorial divisibility
used by the triple reduction. -/
theorem centralFactorialDivides_of_centralBinomialDivides
    {A k : Nat} (h : centralBinomialDivides A k) :
    centralFactorialDivides A k := by
  unfold centralBinomialDivides centralFactorialDivides at *
  exact factorial_dvd_of_lower_choose_dvd_central_choose h

end Erdos728

end CentralBinomialLean
