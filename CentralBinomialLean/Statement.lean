import CentralBinomialLean.Global
import CentralBinomialLean.Problem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Erdős #728 — reduction to a central-pair supply

This file reduces Erdős #728 (stated in `CentralBinomialLean.Problem`) to the
existence of a suitable supply of central pairs `(A, k)` with
`A!·(A+k)! | (2A)!·k!` and the right logarithmic window.  It defines the two
bridge predicates `centralPairsForTriples` and `centralLogWindowPairsAt` and
proves the central specialization `a = A`, `b = A + k`, `n = 2A`.

The parameter-supply chain that *discharges* this supply — and hence the
unconditional final theorem `erdos728Main_proved` — lives in
`CentralBinomialLean.ParameterSupply`.
-/

namespace CentralBinomialLean

namespace Erdos728

/-- A finite, paper-facing central-pair supply sufficient for the final
Erdős #728 triple conclusion.  This is the theorem-shaped bridge supplied by
`thm:binom` in the paper after choosing a constant between `C₁` and `C₂`. -/
def centralPairsForTriples (ε C₁ C₂ : ℝ) : Prop :=
  ∀ M : Nat, ∃ A k : Nat,
    M ≤ 2 * A ∧
    0 < A ∧
    0 < k ∧
    centralFactorialDivides A k ∧
    (k : ℝ) ≤ (1 - 2 * ε) * (A : ℝ) ∧
    C₁ * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
    (k : ℝ) < C₂ * Real.log ((2 * A : Nat) : ℝ)

/-- A theorem-shaped version of the paper's central asymptotic supply
`k / log A -> lam`.  For every positive logarithmic tolerance `δ` and every
positive centrality slope `ρ`, it supplies unbounded central pairs with
`k <= ρ A` and with `k` in the window
`(lam - δ) log(2A) < k < (lam + δ) log(2A)`. -/
def centralLogWindowPairsAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ A k : Nat,
      M ≤ 2 * A ∧
      0 < A ∧
      0 < k ∧
      centralFactorialDivides A k ∧
      (k : ℝ) ≤ ρ * (A : ℝ) ∧
      (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
      (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ)

/-- The central log-window supply implies the finite central-pair supply needed
for the final Erdős-triple reduction, after choosing `lam` strictly between
`C₁` and `C₂`. -/
theorem centralPairsForTriples_of_centralLogWindowPairsAt
    {ε C₁ C₂ lam : ℝ}
    (hC₁lam : C₁ < lam)
    (hlamC₂ : lam < C₂)
    (hεlt : ε < (1 / 2 : ℝ))
    (hsupply : centralLogWindowPairsAt lam) :
    centralPairsForTriples ε C₁ C₂ := by
  intro M
  let δ : ℝ := min (lam - C₁) (C₂ - lam) / 2
  let ρ : ℝ := 1 - 2 * ε
  have hρpos : 0 < ρ := by
    unfold ρ
    linarith
  have hleftpos : 0 < lam - C₁ := by linarith
  have hrightpos : 0 < C₂ - lam := by linarith
  have hminpos : 0 < min (lam - C₁) (C₂ - lam) :=
    lt_min hleftpos hrightpos
  have hδpos : 0 < δ := by
    unfold δ
    linarith [hminpos]
  rcases hsupply δ ρ hδpos hρpos M with
    ⟨A, k, hM, hApos, hkpos, hdiv, hkCentralρ, hgapLowerWindow, hgapUpperWindow⟩
  have hδleleft : δ ≤ (lam - C₁) / 2 := by
    unfold δ
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
  have hδleright : δ ≤ (C₂ - lam) / 2 := by
    unfold δ
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
  have hC₁le : C₁ ≤ lam - δ := by linarith
  have hC₂le : lam + δ ≤ C₂ := by linarith
  have htwoApos : 0 < 2 * A := by omega
  have hlog_nonneg : 0 ≤ Real.log ((2 * A : Nat) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_le_of_lt htwoApos)
  have hgapLower : C₁ * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hC₁le hlog_nonneg) hgapLowerWindow
  have hgapUpper : (k : ℝ) < C₂ * Real.log ((2 * A : Nat) : ℝ) := by
    exact lt_of_lt_of_le hgapUpperWindow (mul_le_mul_of_nonneg_right hC₂le hlog_nonneg)
  refine ⟨A, k, hM, hApos, hkpos, hdiv, ?_, hgapLower, hgapUpper⟩
  simpa [ρ] using hkCentralρ

/-- The reduction used in the paper: from the central specialization
`a = A`, `b = A + k`, `n = 2A`, the central factorial divisibility and the
explicit centrality/gap inequalities give an Erdős #728 triple. -/
theorem erdos728Triple_of_central
    {ε C₁ C₂ : ℝ} {A k : Nat}
    (hε_lt_half : ε < (1 / 2 : ℝ))
    (hApos : 0 < A) (hkpos : 0 < k)
    (hdiv : centralFactorialDivides A k)
    (hkCentral : (k : ℝ) ≤ (1 - 2 * ε) * (A : ℝ))
    (hgapLower : C₁ * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ))
    (hgapUpper : (k : ℝ) < C₂ * Real.log ((2 * A : Nat) : ℝ)) :
    erdos728Triple ε C₁ C₂ A (A + k) (2 * A) := by
  have hgapNat : A + (A + k) - 2 * A = k := by omega
  have hA_nonneg : 0 ≤ (A : ℝ) := by positivity
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hε_le_half : ε ≤ (1 / 2 : ℝ) := le_of_lt hε_lt_half
  have hLowerA : ε * ((2 * A : Nat) : ℝ) ≤ (A : ℝ) := by
    norm_num at hε_le_half ⊢
    nlinarith
  have hLowerB : ε * ((2 * A : Nat) : ℝ) ≤ (A + k : ℝ) := by
    have hAleB : (A : ℝ) ≤ (A + k : ℝ) := by
      exact_mod_cast Nat.le_add_right A k
    exact hLowerA.trans hAleB
  have hUpperA : (A : ℝ) ≤ (1 - ε) * ((2 * A : Nat) : ℝ) := by
    norm_num at hε_le_half ⊢
    nlinarith
  have hUpperB : (A + k : ℝ) ≤ (1 - ε) * ((2 * A : Nat) : ℝ) := by
    norm_num at hkCentral ⊢
    nlinarith
  unfold erdos728Triple centralFactorialDivides at *
  refine ⟨hApos, Nat.add_pos_left hApos k, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hLowerA
  · simpa [Nat.cast_add] using hLowerB
  · exact hUpperA
  · simpa [Nat.cast_add] using hUpperB
  · simpa [hgapNat] using hdiv
  · simpa [hgapNat] using hgapLower
  · simpa [hgapNat] using hgapUpper

/-- The central-pair supply implies unbounded Erdős #728 triples via
`a = A`, `b = A + k`, and `n = 2A`. -/
theorem erdos728UnboundedTriples_of_centralPairsForTriples
    {ε C₁ C₂ : ℝ}
    (hε_lt_half : ε < (1 / 2 : ℝ))
    (hcentral : centralPairsForTriples ε C₁ C₂) :
    erdos728UnboundedTriples ε C₁ C₂ := by
  intro M
  rcases hcentral M with
    ⟨A, k, hM, hApos, hkpos, hdiv, hkCentral, hgapLower, hgapUpper⟩
  refine ⟨A, A + k, 2 * A, hM, ?_⟩
  exact erdos728Triple_of_central hε_lt_half hApos hkpos hdiv
    hkCentral hgapLower hgapUpper

/-- Conditional final theorem: once the central-pair supply has been proved
for every admissible parameter range, the paper's main theorem follows. -/
theorem erdos728Main_of_centralPairsForTriples
    (hcentral :
      ∀ C₁ C₂ ε : ℝ,
        0 < C₁ →
        C₁ < C₂ →
        0 < ε →
        ε < (1 / 2 : ℝ) →
        centralPairsForTriples ε C₁ C₂) :
    erdos728Main := by
  intro C₁ C₂ ε hC₁pos hC₁C₂ hεpos hεlt
  exact erdos728UnboundedTriples_of_centralPairsForTriples hεlt
    (hcentral C₁ C₂ ε hC₁pos hC₁C₂ hεpos hεlt)

/-- Conditional final theorem in the asymptotic form of the paper's
`thm:binom`: if central log-window pairs exist for every positive target
ratio `lam`, then Erdős #728 follows. -/
theorem erdos728Main_of_centralLogWindowPairsAt
    (hsupply : ∀ lam : ℝ, 0 < lam → centralLogWindowPairsAt lam) :
    erdos728Main := by
  apply erdos728Main_of_centralPairsForTriples
  intro C₁ C₂ ε hC₁pos hC₁C₂ hεpos hεlt
  let lam : ℝ := (C₁ + C₂) / 2
  have hC₁lam : C₁ < lam := by
    unfold lam
    linarith
  have hlamC₂ : lam < C₂ := by
    unfold lam
    linarith
  have hlampos : 0 < lam := by
    unfold lam
    linarith
  exact centralPairsForTriples_of_centralLogWindowPairsAt
    hC₁lam hlamC₂ hεlt (hsupply lam hlampos)

end Erdos728

end CentralBinomialLean
