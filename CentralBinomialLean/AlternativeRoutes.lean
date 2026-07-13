import CentralBinomialLean.ParameterSupply

/-!
# Erdős #728 — alternative routes (not on the critical path)

These `Effective` / `Numeric` / `Crude` endpoint-supply variants and their
wrappers are *not* used by `erdos728Main_proved`; they record alternative
conditional entry points and are kept here so the main development in
`CentralBinomialLean.Statement` / `ParameterSupply` stays focused.
-/

namespace CentralBinomialLean

namespace Erdos728

/-- Crude endpoint-window version of the shifted large-`k` target.  The
prime-indexed bad-residue sum is replaced by a single worst-case bound for the
canonical medium window. -/
def shiftedLargeKCrudeEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card *
        (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) * (N + 1)) < N ∧
      M ≤ 2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      0 < shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      (k : ℝ) ≤ ρ * (shiftedProgressionBase k (Nat.sqrt (2 * k)) T : ℝ) ∧
      (0 ≤ lam - δ →
        (lam - δ) *
          Real.log ((2 * shiftedProgressionTop k (Nat.sqrt (2 * k)) T N : Nat) : ℝ) <
            (k : ℝ)) ∧
      (k : ℝ) <
        (lam + δ) *
          Real.log ((2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T : Nat) : ℝ)

/-- Effective numeric endpoint-window version of the shifted large-`k` target.
The bad-residue condition has no prime-indexed sum and no Finset cardinality,
but it keeps the useful denominator `(sqrt (2*k) + 1)^J`. -/
def shiftedLargeKEffectiveEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1) *
        (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) *
          (N / ((Nat.sqrt (2 * k) + 1) ^ J) + 1)) < N ∧
      M ≤ 2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      0 < shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      (k : ℝ) ≤ ρ * (shiftedProgressionBase k (Nat.sqrt (2 * k)) T : ℝ) ∧
      (0 ≤ lam - δ →
        (lam - δ) *
          Real.log ((2 * shiftedProgressionTop k (Nat.sqrt (2 * k)) T N : Nat) : ℝ) <
            (k : ℝ)) ∧
      (k : ℝ) <
        (lam + δ) *
          Real.log ((2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T : Nat) : ℝ)

/-- Fully numeric crude endpoint-window version of the shifted large-`k` target.
The bad-residue condition has no prime-indexed sum and no Finset cardinality. -/
def shiftedLargeKNumericEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1) *
        (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) * (N + 1)) < N ∧
      M ≤ 2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      0 < shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      (k : ℝ) ≤ ρ * (shiftedProgressionBase k (Nat.sqrt (2 * k)) T : ℝ) ∧
      (0 ≤ lam - δ →
        (lam - δ) *
          Real.log ((2 * shiftedProgressionTop k (Nat.sqrt (2 * k)) T N : Nat) : ℝ) <
            (k : ℝ)) ∧
      (k : ℝ) <
        (lam + δ) *
          Real.log ((2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T : Nat) : ℝ)

/-- The effective numeric endpoint-window target implies the endpoint-window
target by the effective medium-window sum bound and the trivial cardinality
bound. -/
theorem shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKEffectiveEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKEffectiveEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, heffective, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  let C := ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) *
    (N / ((Nat.sqrt (2 * k) + 1) ^ J) + 1)
  have hsum_le_card :
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1))
        ≤ (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card * C := by
    simpa [C] using mediumPrimeWindow_badResidue_sum_le_effective
      (k := k) (Y := Nat.sqrt (2 * k)) (J := J) (N := N)
  have hcard_le :
      (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card * C
        ≤ (2 * k + 1) * C :=
    Nat.mul_le_mul_right C
      (mediumPrimeWindow_card_le_two_mul_add_one (k := k) (Y := Nat.sqrt (2 * k)))
  exact lt_of_le_of_lt (le_trans hsum_le_card hcard_le) (by simpa [C] using heffective)

/-- The fully numeric endpoint-window target implies the crude endpoint-window
target by the trivial canonical medium-window cardinality bound. -/
theorem shiftedLargeKCrudeEndpointWindowParameterSupplyAt_of_shiftedLargeKNumericEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKNumericEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKCrudeEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hnumeric, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right
      (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) * (N + 1))
      (mediumPrimeWindow_card_le_two_mul_add_one (k := k) (Y := Nat.sqrt (2 * k))))
    hnumeric

/-- The crude endpoint-window target implies the endpoint-window target by the
canonical medium-window worst-case sum bound. -/
theorem shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKCrudeEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKCrudeEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hcrude, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  exact lt_of_le_of_lt
    (mediumPrimeWindow_badResidue_sum_le_crude
      (k := k) (Y := Nat.sqrt (2 * k)) (J := J) (N := N))
    hcrude

/-- Conditional final theorem through the crude endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKCrudeEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKCrudeEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKCrudeEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the effective numeric endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKEffectiveEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKEffectiveEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKEffectiveEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the fully numeric endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKNumericEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKNumericEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKCrudeEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKCrudeEndpointWindowParameterSupplyAt_of_shiftedLargeKNumericEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

end Erdos728

end CentralBinomialLean
