import CentralBinomialLean.Statement

/-!
# Erdős #728 — the parameter-supply chain and final theorem

This file carries the asymptotic machinery: the tower of
`…ParameterSupplyAt` predicates, their reductions, the sublinear-growth
discharge `…_of_pos`, and the resulting unconditional main theorem
`erdos728Main_proved`.  The paper-facing statement is in
`CentralBinomialLean.Problem`; the reduction it invokes is in
`CentralBinomialLean.Statement`.
-/

namespace CentralBinomialLean

namespace Erdos728

theorem upper_log_window_of_exp_lt
    {c : ℝ} {A k : Nat} (hc : 0 < c)
    (hA : Real.exp ((k : ℝ) / c) < ((2 * A : Nat) : ℝ)) :
    (k : ℝ) < c * Real.log ((2 * A : Nat) : ℝ) := by
  have hpos : 0 < Real.exp ((k : ℝ) / c) := Real.exp_pos _
  have hlog :
      (k : ℝ) / c < Real.log ((2 * A : Nat) : ℝ) := by
    simpa [Real.log_exp] using Real.log_lt_log hpos hA
  rw [div_lt_iff₀ hc] at hlog
  nlinarith

theorem lower_log_window_of_lt_exp
    {c : ℝ} {A k : Nat} (hc : 0 < c)
    (hApos : 0 < A)
    (hA : ((2 * A : Nat) : ℝ) < Real.exp ((k : ℝ) / c)) :
    c * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) := by
  have htwoApos : 0 < ((2 * A : Nat) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * A)
  have hlog :
      Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) / c := by
    simpa [Real.log_exp] using Real.log_lt_log htwoApos hA
  rw [lt_div_iff₀ hc] at hlog
  nlinarith

theorem centralBinomialDivides_of_congruence_smallPrimePowerModulus
    {A k : Nat}
    (hR : A % smallPrimePowerModulus k = k % smallPrimePowerModulus k) :
    centralBinomialDivides A k :=
  lower_choose_dvd_central_choose_of_congruence_smallPrimePowerModulus hR

theorem centralFactorialDivides_of_congruence_smallPrimePowerModulus
    {A k : Nat}
    (hR : A % smallPrimePowerModulus k = k % smallPrimePowerModulus k) :
    centralFactorialDivides A k :=
  factorial_dvd_of_congruence_smallPrimePowerModulus hR

theorem centralBinomialDivides_of_prime_partition
    {A k Y J : Nat}
    (hR :
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y)
    (hJ : 2 ≤ J)
    (hpartition :
      ∀ p, p.Prime →
        p ≤ Y ∨
        (8 ≤ p ∧ 2 * k < p * p ∧
          A % (p ^ J) ∉ semanticBadResidues k p J) ∨
        2 * k < p) :
    centralBinomialDivides A k :=
  lower_choose_dvd_central_choose_of_prime_partition hR hJ hpartition

theorem centralFactorialDivides_of_prime_partition
    {A k Y J : Nat}
    (hR :
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y)
    (hJ : 2 ≤ J)
    (hpartition :
      ∀ p, p.Prime →
        p ≤ Y ∨
        (8 ≤ p ∧ 2 * k < p * p ∧
          A % (p ^ J) ∉ semanticBadResidues k p J) ∨
        2 * k < p) :
    centralFactorialDivides A k :=
  factorial_dvd_of_prime_partition hR hJ hpartition

/-- Paper-facing progression-count endpoint: a finite medium-prime cover and
bad-residue sum produce a central pair in the small-prime congruence class. -/
theorem exists_progression_centralFactorialDivides_of_prime_partition_sum
    (P : Finset Nat) {k Y J N : Nat}
    (hcop :
      ∀ p ∈ P, Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J))
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (hcover : ∀ p, p.Prime → Y < p → ¬ 2 * k < p → p ∈ P)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ A t : Nat,
      t ∈ Finset.range N ∧
      A = k + baseRestrictedPrimePowerModulus k Y * t ∧
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y ∧
      centralFactorialDivides A k := by
  rcases exists_progression_factorial_dvd_of_prime_partition_sum
      P hcop hp hJ hbig hcover hcard with
    ⟨A, t, htRange, hAeq, hR, hdiv⟩
  exact ⟨A, t, htRange, hAeq, hR, hdiv⟩

/-- Shifted paper-facing progression-count endpoint: a finite medium-prime cover
and bad-residue sum produce a central pair in the small-prime congruence class
along `A = k + R * T + R * y`, `y < N`. -/
theorem exists_shifted_progression_centralFactorialDivides_of_prime_partition_sum
    (P : Finset Nat) {k Y J T N : Nat}
    (hcop :
      ∀ p ∈ P, Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J))
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (hcover : ∀ p, p.Prime → Y < p → ¬ 2 * k < p → p ∈ P)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ A y : Nat,
      y ∈ Finset.range N ∧
      A = k + baseRestrictedPrimePowerModulus k Y * T +
        baseRestrictedPrimePowerModulus k Y * y ∧
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y ∧
      centralFactorialDivides A k := by
  rcases exists_shifted_progression_factorial_dvd_of_prime_partition_sum
      P hcop hp hJ hbig hcover hcard with
    ⟨A, y, hyRange, hAeq, hR, hdiv⟩
  exact ⟨A, y, hyRange, hAeq, hR, hdiv⟩

/-- Finite progression parameters sufficient to produce the central log-window
supply at target ratio `lam`.  This packages the remaining asymptotic work: for
each tolerance and lower bound, choose finite parameters so the progression
counting theorem applies, and every resulting `A = k + R t` lies in the desired
central and logarithmic window. -/
def progressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ P : Finset Nat, ∃ k Y J N : Nat,
      0 < k ∧
      (∀ p ∈ P, Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J)) ∧
      (∀ p ∈ P, 8 ≤ p) ∧
      2 ≤ J ∧
      (∀ p ∈ P, 2 * k < p * p) ∧
      (∀ p, p.Prime → Y < p → ¬ 2 * k < p → p ∈ P) ∧
      (∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A t : Nat,
        t ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k Y * t →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Canonical finite progression parameters for the paper's standard medium
window `(Y, 2k]`.  Compared with `progressionWindowParameterSupplyAt`, the
coprimality, medium-prime lower bounds, square condition, and prime cover are
all consequences of the cutoff hypotheses `2k < (Y+1)^2` and `7 <= Y`. -/
def canonicalProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k Y J N : Nat,
      0 < k ∧
      2 * k < (Y + 1) * (Y + 1) ∧
      7 ≤ Y ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A t : Nat,
        t ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k Y * t →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Sqrt-canonical finite progression parameters: the small-prime cutoff is fixed
to `sqrt (2*k)`, so the square cutoff condition is automatic.  The remaining
asymptotic work is to choose `k`, `J`, and `N` so that the cutoff is large
enough, the bad-residue sum is small, and the resulting progression has the
right size and logarithmic window. -/
def sqrtProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat,
      0 < k ∧
      7 ≤ Nat.sqrt (2 * k) ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A t : Nat,
        t ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * t →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Large-`k` sqrt-canonical finite progression parameters.  The fixed lower
bound `25 <= k` implies both `0 < k` and `7 <= sqrt (2*k)`, so this is the
next narrower target for the asymptotic parameter choice. -/
def largeKProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A t : Nat,
        t ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * t →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- The first `A` value in the shifted progression window. -/
noncomputable def shiftedProgressionBase (k Y T : Nat) : Nat :=
  k + baseRestrictedPrimePowerModulus k Y * T

/-- A convenient upper endpoint for the shifted progression window
`shiftedProgressionBase k Y T + R * y`, `y < N`.  This is one step past the
last possible index, which avoids a separate `N - 1` case. -/
noncomputable def shiftedProgressionTop (k Y T N : Nat) : Nat :=
  shiftedProgressionBase k Y T + baseRestrictedPrimePowerModulus k Y * N

/-- If a real interval is wider than the shifted progression step times
`N + 2`, then some shifted window of length `N` lies inside it.  This isolates
the archimedean choice of the offset `T` from the later asymptotic estimates. -/
theorem exists_shiftedProgression_window_in_interval
    (k Y N : Nat) {L U : ℝ}
    (hkL : (k : ℝ) ≤ L)
    (hwidth :
      L + (baseRestrictedPrimePowerModulus k Y : ℝ) * ((N : ℝ) + 2) < U) :
    ∃ T : Nat,
      L < (shiftedProgressionBase k Y T : ℝ) ∧
      (shiftedProgressionTop k Y T N : ℝ) < U := by
  let R := baseRestrictedPrimePowerModulus k Y
  let x : ℝ := (L - (k : ℝ)) / (R : ℝ)
  let T : Nat := Nat.ceil x + 1
  have hRposNat : 0 < R := baseRestrictedPrimePowerModulus_pos k Y
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast hRposNat
  have hx_nonneg : 0 ≤ x := by
    exact div_nonneg (sub_nonneg.mpr hkL) (le_of_lt hRpos)
  have hx_le_ceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
  have hx_lt_T : x < (T : ℝ) := by
    calc
      x ≤ (Nat.ceil x : ℝ) := hx_le_ceil
      _ < (Nat.ceil x : ℝ) + 1 := by linarith
      _ = (T : ℝ) := by simp [T]
  have hT_lt_x_add_two : (T : ℝ) < x + 2 := by
    have hT_cast : (T : ℝ) = (Nat.ceil x : ℝ) + 1 := by simp [T]
    linarith
  have hbase_cast :
      (shiftedProgressionBase k Y T : ℝ) =
        (k : ℝ) + (R : ℝ) * (T : ℝ) := by
    simp [shiftedProgressionBase, R]
  have htop_cast :
      (shiftedProgressionTop k Y T N : ℝ) =
        (k : ℝ) + (R : ℝ) * ((T : ℝ) + (N : ℝ)) := by
    simp [shiftedProgressionTop, shiftedProgressionBase, R]
    ring
  have hbase_lower : L < (shiftedProgressionBase k Y T : ℝ) := by
    rw [hbase_cast]
    have hmul : (R : ℝ) * x < (R : ℝ) * (T : ℝ) :=
      mul_lt_mul_of_pos_left hx_lt_T hRpos
    have hx_mul : (R : ℝ) * x = L - (k : ℝ) := by
      calc
        (R : ℝ) * x = (R : ℝ) * ((L - (k : ℝ)) / (R : ℝ)) := by rfl
        _ = L - (k : ℝ) := mul_div_cancel₀ _ (ne_of_gt hRpos)
    nlinarith
  have htop_upper :
      (shiftedProgressionTop k Y T N : ℝ) <
        L + (R : ℝ) * ((N : ℝ) + 2) := by
    rw [htop_cast]
    have hmul : (R : ℝ) * (T : ℝ) < (R : ℝ) * (x + 2) :=
      mul_lt_mul_of_pos_left hT_lt_x_add_two hRpos
    have hx_mul : (R : ℝ) * x = L - (k : ℝ) := by
      calc
        (R : ℝ) * x = (R : ℝ) * ((L - (k : ℝ)) / (R : ℝ)) := by rfl
        _ = L - (k : ℝ) := mul_div_cancel₀ _ (ne_of_gt hRpos)
    nlinarith
  exact ⟨T, hbase_lower, lt_trans htop_upper (by simpa [R] using hwidth)⟩

theorem exists_shiftedProgressionBase_large
    (k Y M : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T : Nat,
      M ≤ 2 * shiftedProgressionBase k Y T ∧
      0 < shiftedProgressionBase k Y T ∧
      (k : ℝ) ≤ ρ * (shiftedProgressionBase k Y T : ℝ) := by
  rcases exists_nat_gt (max (M : ℝ) ((k : ℝ) / ρ)) with ⟨T, hT⟩
  let R := baseRestrictedPrimePowerModulus k Y
  let ABase := shiftedProgressionBase k Y T
  have hMlt : (M : ℝ) < (T : ℝ) := lt_of_le_of_lt (le_max_left _ _) hT
  have hkdivlt : (k : ℝ) / ρ < (T : ℝ) := lt_of_le_of_lt (le_max_right _ _) hT
  have hMleT : M ≤ T := by exact_mod_cast le_of_lt hMlt
  have hTpos : 0 < T := by
    have : (0 : ℝ) < (T : ℝ) := by
      exact lt_of_le_of_lt (by positivity) hMlt
    exact_mod_cast this
  have hRone : 1 ≤ R := Nat.succ_le_of_lt (baseRestrictedPrimePowerModulus_pos k Y)
  have hTleRT : T ≤ R * T := by
    simpa using Nat.mul_le_mul_right T hRone
  have hTleBase : T ≤ ABase := by
    calc
      T ≤ R * T := hTleRT
      _ ≤ k + R * T := Nat.le_add_left _ _
      _ = ABase := by simp [ABase, shiftedProgressionBase, R]
  have hM : M ≤ 2 * ABase := by
    exact hMleT.trans (hTleBase.trans (by omega))
  have hbasePos : 0 < ABase := lt_of_lt_of_le hTpos hTleBase
  have hbaseReal : (T : ℝ) ≤ (ABase : ℝ) := by exact_mod_cast hTleBase
  have hkdivltBase : (k : ℝ) / ρ < (ABase : ℝ) := lt_of_lt_of_le hkdivlt hbaseReal
  have hklt : (k : ℝ) < ρ * (ABase : ℝ) := by
    rw [div_lt_iff₀ hρ] at hkdivltBase
    nlinarith
  exact ⟨T, hM, hbasePos, le_of_lt hklt⟩

/-- Shifted finite progression parameters.  Compared with
`progressionWindowParameterSupplyAt`, the arithmetic progression starts at
`k + R * T` and searches the next `N` indices. -/
def shiftedProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ P : Finset Nat, ∃ k Y J T N : Nat,
      0 < k ∧
      (∀ p ∈ P, Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J)) ∧
      (∀ p ∈ P, 8 ≤ p) ∧
      2 ≤ J ∧
      (∀ p ∈ P, 2 * k < p * p) ∧
      (∀ p, p.Prime → Y < p → ¬ 2 * k < p → p ∈ P) ∧
      (∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A y : Nat,
        y ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k Y * T +
          baseRestrictedPrimePowerModulus k Y * y →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Canonical shifted finite progression parameters for the paper's standard
medium window `(Y, 2k]`. -/
def shiftedCanonicalProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k Y J T N : Nat,
      0 < k ∧
      2 * k < (Y + 1) * (Y + 1) ∧
      7 ≤ Y ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A y : Nat,
        y ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k Y * T +
          baseRestrictedPrimePowerModulus k Y * y →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Sqrt-canonical shifted finite progression parameters. -/
def shiftedSqrtProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      0 < k ∧
      7 ≤ Nat.sqrt (2 * k) ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A y : Nat,
        y ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * T +
          baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * y →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- Large-`k` shifted sqrt-canonical finite progression parameters. -/
def shiftedLargeKProgressionWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
      (∀ A y : Nat,
        y ∈ Finset.range N →
        A = k + baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * T +
          baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) * y →
          M ≤ 2 * A ∧
          0 < A ∧
          (k : ℝ) ≤ ρ * (A : ℝ) ∧
          (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) ∧
          (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ))

/-- The integer bad-residue weight used in the medium-prime sum. -/
def badResidueWeight (p J : Nat) : Nat :=
  (p / 2) * p * ((3 * p) / 4) ^ (J - 2)

theorem natCast_div_le_real (n d : Nat) (hd : 0 < d) :
    ((n / d : Nat) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hmul : (n / d) * d ≤ n := Nat.div_mul_le_self n d
  have hmulR : (((n / d) * d : Nat) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmul
  rw [Nat.cast_mul] at hmulR
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hdR]
  simpa [mul_comm] using hmulR

theorem badResidueWeight_quotient_cast_le_geometric
    {p J N : Nat} (hp : 0 < p) (hJ : 2 ≤ J) :
    ((badResidueWeight p J * (N / (p ^ J)) : Nat) : ℝ) ≤
      (N : ℝ) * (1 / 2 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) := by
  have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpRne : (p : ℝ) ≠ 0 := ne_of_gt hpRpos
  have hpowpos : 0 < p ^ J := Nat.pow_pos hp
  have hdivN :
      ((N / (p ^ J) : Nat) : ℝ) ≤ (N : ℝ) / (((p ^ J : Nat) : ℝ)) :=
    natCast_div_le_real N (p ^ J) hpowpos
  have hpdiv :
      ((p / 2 : Nat) : ℝ) ≤ (p : ℝ) / 2 :=
    natCast_div_le_real p 2 (by norm_num)
  have h3pdiv :
      (((3 * p) / 4 : Nat) : ℝ) ≤ ((3 * p : Nat) : ℝ) / 4 :=
    natCast_div_le_real (3 * p) 4 (by norm_num)
  have h3pdiv' :
      (((3 * p) / 4 : Nat) : ℝ) ≤ (3 : ℝ) * (p : ℝ) / 4 := by
    simpa [Nat.cast_mul] using h3pdiv
  have h3pdiv'' :
      (((3 * p) / 4 : Nat) : ℝ) ≤ ((3 : Nat) : ℝ) * (p : ℝ) / 4 := by
    simpa using h3pdiv'
  have hdivN' :
      ((N / (p ^ J) : Nat) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ J := by
    simpa [Nat.cast_pow] using hdivN
  have hnonneg_left : 0 ≤ ((p / 2 : Nat) : ℝ) := by positivity
  have hnonneg_p : 0 ≤ (p : ℝ) := by positivity
  have hnonneg_pow : 0 ≤ (((3 * p) / 4 : Nat) : ℝ) ^ (J - 2) := by positivity
  have hbound :
      ((badResidueWeight p J * (N / (p ^ J)) : Nat) : ℝ) ≤
        ((p : ℝ) / 2) * (p : ℝ) *
            ((((3 * p : Nat) : ℝ) / 4) ^ (J - 2)) *
          ((N : ℝ) / (((p ^ J : Nat) : ℝ))) := by
    simp only [badResidueWeight, Nat.cast_mul, Nat.cast_pow]
    gcongr
  refine hbound.trans_eq ?_
  let m := J - 2
  have hJ' : J = m + 2 := by omega
  subst m
  rw [hJ']
  norm_num [Nat.cast_pow, pow_add, pow_two]
  field_simp [hpRne]
  ring

/-- The part of the canonical medium-prime bad-residue sum carrying the
quotients `N / p^J`. -/
noncomputable def canonicalMediumBadResidueQuotientSum (k J N : Nat) : Nat :=
  ∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
    badResidueWeight p J * (N / (p ^ J))

theorem canonicalMediumBadResidueQuotientSum_cast_le_geometric
    {k J N : Nat} (hJ : 2 ≤ J) :
    (canonicalMediumBadResidueQuotientSum k J N : ℝ) ≤
      ((mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card : ℝ) *
        (N : ℝ) * (1 / 2 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) := by
  let P := mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)
  let C : ℝ := (N : ℝ) * (1 / 2 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2))
  calc
    (canonicalMediumBadResidueQuotientSum k J N : ℝ)
        = ∑ p ∈ P, ((badResidueWeight p J * (N / (p ^ J)) : Nat) : ℝ) := by
          simp [canonicalMediumBadResidueQuotientSum, P]
    _ ≤ ∑ _p ∈ P, C := by
          apply Finset.sum_le_sum
          intro p hp
          have hp8 : 8 ≤ p := eight_le_of_mem_mediumPrimeWindow (by simpa [P] using hp)
          exact badResidueWeight_quotient_cast_le_geometric (p := p) (J := J) (N := N)
            (by omega) hJ
    _ = (P.card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card : ℝ) *
        (N : ℝ) * (1 / 2 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) := by
          simp [P, C, mul_assoc]

theorem canonicalMediumBadResidueQuotientSum_cast_le_crude_geometric
    {k J N : Nat} (hJ : 2 ≤ J) :
    (canonicalMediumBadResidueQuotientSum k J N : ℝ) ≤
      (2 * k + 1 : ℝ) * (N : ℝ) * (1 / 2 : ℝ) *
        ((3 / 4 : ℝ) ^ (J - 2)) := by
  have hgeom := canonicalMediumBadResidueQuotientSum_cast_le_geometric
    (k := k) (J := J) (N := N) hJ
  have hcardNat :
      (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card ≤ 2 * k + 1 :=
    mediumPrimeWindow_card_le_two_mul_add_one (k := k) (Y := Nat.sqrt (2 * k))
  have hcard :
      ((mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card : ℝ) ≤
        (2 * k + 1 : ℝ) := by
    exact_mod_cast hcardNat
  exact hgeom.trans (by gcongr)

theorem two_mul_canonicalMediumBadResidueQuotientSum_cast_lt_of_geometric
    {k J N : Nat} (hJ : 2 ≤ J) (hN : 0 < N)
    (hgeom : (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1) :
    (2 : ℝ) * (canonicalMediumBadResidueQuotientSum k J N : ℝ) < (N : ℝ) := by
  have hq := canonicalMediumBadResidueQuotientSum_cast_le_crude_geometric
    (k := k) (J := J) (N := N) hJ
  have hq2 :
      (2 : ℝ) * (canonicalMediumBadResidueQuotientSum k J N : ℝ) ≤
        (N : ℝ) * ((2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2))) := by
    calc
      (2 : ℝ) * (canonicalMediumBadResidueQuotientSum k J N : ℝ)
          ≤ 2 * ((2 * k + 1 : ℝ) * (N : ℝ) * (1 / 2 : ℝ) *
              ((3 / 4 : ℝ) ^ (J - 2))) := by
            gcongr
      _ = (N : ℝ) * ((2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2))) := by
            ring
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  exact hq2.trans_lt (by
    calc
      (N : ℝ) * ((2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)))
          < (N : ℝ) * 1 := by gcongr
      _ = (N : ℝ) := by ring)

/-- The `+1` tail part of the canonical medium-prime bad-residue sum. -/
noncomputable def canonicalMediumBadResidueTailSum (k J : Nat) : Nat :=
  ∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
    badResidueWeight p J

theorem canonicalMediumBadResidueTailSum_le_crude (k J : Nat) :
    canonicalMediumBadResidueTailSum k J ≤
      (2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) := by
  let C := (2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)
  have hsum_le :=
    mediumPrimeWindow_badResidue_sum_le_crude
      (k := k) (Y := Nat.sqrt (2 * k)) (J := J) (N := 0)
  have hraw_eq :
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2)) * (0 / (p ^ J) + 1)) =
        canonicalMediumBadResidueTailSum k J := by
    simp [canonicalMediumBadResidueTailSum, badResidueWeight]
  have htarget_eq :
      (2 * k + 1) * (C * (0 + 1)) = (2 * k + 1) * C := by
    simp
  have htail_le_card :
      canonicalMediumBadResidueTailSum k J ≤
        (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card * C := by
    simpa [hraw_eq, C] using hsum_le
  have hcard_le :
      (mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1)).card * C
        ≤ (2 * k + 1) * C :=
    Nat.mul_le_mul_right C
      (mediumPrimeWindow_card_le_two_mul_add_one (k := k) (Y := Nat.sqrt (2 * k)))
  exact htail_le_card.trans (by simpa [C] using hcard_le)

theorem two_mul_canonicalMediumBadResidueTailSum_cast_lt_of_crude
    {k J N : Nat}
    (htail :
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N) :
    (2 : ℝ) * (canonicalMediumBadResidueTailSum k J : ℝ) < (N : ℝ) := by
  have hle := canonicalMediumBadResidueTailSum_le_crude k J
  have htailNat : 2 * canonicalMediumBadResidueTailSum k J < N := by
    omega
  exact_mod_cast htailNat

theorem exists_geometric_decay_exponent (k : Nat) :
    ∃ J : Nat,
      2 ≤ J ∧ (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 := by
  let C : ℝ := 2 * k + 1
  have hCpos : 0 < C := by
    unfold C
    positivity
  have htarget : 0 < (1 / C : ℝ) := one_div_pos.mpr hCpos
  rcases exists_pow_lt_of_lt_one htarget (by norm_num : (3 / 4 : ℝ) < 1) with
    ⟨m, hm⟩
  refine ⟨m + 2, by omega, ?_⟩
  have hmul : C * ((3 / 4 : ℝ) ^ m) < C * (1 / C) :=
    mul_lt_mul_of_pos_left hm hCpos
  have hCmul : C * (1 / C) = 1 := by
    field_simp [ne_of_gt hCpos]
  exact (by simpa [C] using hmul.trans_eq hCmul)

theorem exists_progression_length_above_tail (k J : Nat) :
    ∃ N : Nat,
      0 < N ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N := by
  let B :=
    2 * ((2 * k + 1) *
      ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)))
  exact ⟨B + 1, by omega, by omega⟩

/-- The crude natural threshold used to dominate the tail part of the bad
residue count. -/
def crudeTailThreshold (k J : Nat) : Nat :=
  2 * ((2 * k + 1) *
    ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)))

/-- The crude tail threshold is bounded by a simple power of `2*k+3`.  This
turns its logarithm into an `O(J log k)` term in the final asymptotic target. -/
theorem crudeTailThreshold_add_three_le_pow {k J : Nat}
    (hk : 1 ≤ k) (hJ : 2 ≤ J) :
    crudeTailThreshold k J + 3 ≤ (2 * k + 3) ^ (J + 3) := by
  let X : Nat := 2 * k + 3
  have hXpos : 0 < X := by omega
  have hXge2 : 2 ≤ X := by omega
  have htwo_le : 2 ≤ X := hXge2
  have htwoKone_le : 2 * k + 1 ≤ X := by omega
  have htwoK_le : 2 * k ≤ X := by omega
  have hthree_le : (3 * (2 * k)) / 4 ≤ X := by
    have hraw : (3 * (2 * k)) / 4 ≤ 3 * (2 * k) := Nat.div_le_self _ _
    omega
  have hpow_le : ((3 * (2 * k)) / 4) ^ (J - 2) ≤ X ^ (J - 2) :=
    Nat.pow_le_pow_left hthree_le _
  have hmain :
      crudeTailThreshold k J ≤ X ^ (J + 2) := by
    have hmul :
        2 * ((2 * k + 1) *
          ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) ≤
          X * (X * ((X * X) * X ^ (J - 2))) := by
      exact Nat.mul_le_mul htwo_le
        (Nat.mul_le_mul htwoKone_le
          (Nat.mul_le_mul (Nat.mul_le_mul htwoK_le htwoK_le) hpow_le))
    have hpow_eq :
        X * (X * ((X * X) * X ^ (J - 2))) = X ^ (J + 2) := by
      calc
        X * (X * ((X * X) * X ^ (J - 2))) = X ^ 4 * X ^ (J - 2) := by
          ring
        _ = X ^ (4 + (J - 2)) := by rw [pow_add]
        _ = X ^ (J + 2) := by
          congr 1
          omega
    simpa [crudeTailThreshold, X, hpow_eq] using hmul
  have hthree_le_gap : 3 ≤ X ^ (J + 2) * (X - 1) := by
    have hgap : 1 ≤ X - 1 := by omega
    have hthree_le_pow : 3 ≤ X ^ (J + 2) := by
      have hX_le_pow : X ≤ X ^ (J + 2) := by
        have hExp : J + 2 ≠ 0 := by omega
        exact Nat.le_self_pow hExp X
      exact (by omega : 3 ≤ X).trans hX_le_pow
    exact le_trans hthree_le_pow (Nat.le_mul_of_pos_right (X ^ (J + 2)) hgap)
  have hgap_eq : X ^ (J + 3) = X ^ (J + 2) + X ^ (J + 2) * (X - 1) := by
    have hXge1 : 1 ≤ X := by omega
    have hx : 1 + (X - 1) = X := by omega
    calc
      X ^ (J + 3) = X ^ (J + 2) * X := by
        rw [show J + 3 = J + 2 + 1 by omega, pow_succ]
      _ = X ^ (J + 2) * (1 + (X - 1)) := by rw [hx]
      _ = X ^ (J + 2) + X ^ (J + 2) * (X - 1) := by ring
  calc
    crudeTailThreshold k J + 3 ≤ X ^ (J + 2) + 3 := by
      exact Nat.add_le_add_right hmain 3
    _ ≤ X ^ (J + 2) + X ^ (J + 2) * (X - 1) := by
      exact Nat.add_le_add_left hthree_le_gap _
    _ = X ^ (J + 3) := hgap_eq.symm
    _ = (2 * k + 3) ^ (J + 3) := by simp [X]

/-- Logarithmic form of `crudeTailThreshold_add_three_le_pow`. -/
theorem log_crudeTailThreshold_add_three_le {k J : Nat}
    (hk : 1 ≤ k) (hJ : 2 ≤ J) :
    Real.log ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤
      (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) := by
  have hpos : 0 < ((crudeTailThreshold k J + 3 : Nat) : ℝ) := by positivity
  have hleNat := crudeTailThreshold_add_three_le_pow (k := k) (J := J) hk hJ
  have hle :
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤
        (((2 * k + 3) ^ (J + 3) : Nat) : ℝ) := by
    exact_mod_cast hleNat
  have hlog_le :
      Real.log ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤
        Real.log ((((2 * k + 3) ^ (J + 3) : Nat) : ℝ)) :=
    Real.log_le_log hpos hle
  simpa [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using hlog_le

/-- Logarithmic form of the geometric decay condition. -/
theorem geometric_decay_of_log_lt {k J : Nat}
    (hlog :
      Real.log ((2 * k + 1 : Nat) : ℝ) <
        (J - 2 : Nat) * Real.log (4 / 3 : ℝ)) :
    (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 := by
  have hbasePos : 0 < (4 / 3 : ℝ) := by norm_num
  have hltPow : ((2 * k + 1 : Nat) : ℝ) < (4 / 3 : ℝ) ^ (J - 2) := by
    exact Real.pow_lt_of_lt_log hbasePos hlog
  have hpowPos : 0 < (3 / 4 : ℝ) ^ (J - 2) := by positivity
  have hmul := mul_lt_mul_of_pos_right hltPow hpowPos
  have hone : (4 / 3 : ℝ) ^ (J - 2) * (3 / 4 : ℝ) ^ (J - 2) = 1 := by
    rw [← mul_pow]
    norm_num
  simpa [hone] using hmul

/-- A bounded choice of progression length: taking `N = tail + 1` satisfies the
tail inequality, and the remaining upper bound is exactly `tail + 3`. -/
theorem exists_progression_length_above_tail_with_exp_bound
    {k J : Nat} {C : ℝ}
    (hC : ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C) :
    ∃ N : Nat,
      0 < N ∧
      crudeTailThreshold k J < N ∧
      (N : ℝ) + 2 ≤ Real.exp C := by
  refine ⟨crudeTailThreshold k J + 1, by omega, by omega, ?_⟩
  have hcast :
      ((crudeTailThreshold k J + 1 : Nat) : ℝ) + 2 =
        ((crudeTailThreshold k J + 3 : Nat) : ℝ) := by
    norm_num
    ring
  rw [hcast]
  exact hC

/-- The exact canonical medium-prime bad-residue sum splits into a quotient
part and a tail part. -/
theorem canonicalMediumBadResidueSum_eq_quotient_add_tail {k J N : Nat} :
    (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        badResidueWeight p J * (N / (p ^ J) + 1)) =
      canonicalMediumBadResidueQuotientSum k J N +
        canonicalMediumBadResidueTailSum k J := by
  unfold canonicalMediumBadResidueQuotientSum canonicalMediumBadResidueTailSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.mul_add]
  simp

/-- Endpoint version of the shifted large-`k` target.  It is enough to prove
the final size and centrality inequalities at the bottom of the shifted window,
the upper logarithmic inequality at the bottom, and the lower logarithmic
inequality at the top when `lam - δ` is nonnegative. -/
def shiftedLargeKEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) ∧
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

/-- Split endpoint-window version of the shifted large-`k` target.  It is
enough to make both the quotient part and the tail part of the bad-residue sum
smaller than half of the available progression length. -/
def shiftedLargeKSplitEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      2 * canonicalMediumBadResidueQuotientSum k J N < N ∧
      2 * canonicalMediumBadResidueTailSum k J < N ∧
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

/-- Real-valued split endpoint-window version of the shifted large-`k` target.
This is the analysis-facing form of the remaining bad-residue estimates. -/
def shiftedLargeKRealSplitEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 : ℝ) * (canonicalMediumBadResidueQuotientSum k J N : ℝ) < (N : ℝ) ∧
      (2 : ℝ) * (canonicalMediumBadResidueTailSum k J : ℝ) < (N : ℝ) ∧
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

/-- Geometric split endpoint-window target.  This is a cleaner remaining
asymptotic target than the raw real split sums: the quotient part is controlled
by the geometric decay `(3/4)^(J-2)`, while the tail part is controlled by a
single crude finite bound. -/
def shiftedLargeKGeometricEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
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

/-- Exponential endpoint-window target.  This is equivalent in spirit to the
geometric endpoint target, but the logarithmic endpoint inequalities are
replaced by the more convenient exponential interval bounds. -/
def shiftedLargeKExponentialEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J T N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
      M ≤ 2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      0 < shiftedProgressionBase k (Nat.sqrt (2 * k)) T ∧
      (k : ℝ) ≤ ρ * (shiftedProgressionBase k (Nat.sqrt (2 * k)) T : ℝ) ∧
      Real.exp ((k : ℝ) / (lam + δ)) <
        ((2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T : Nat) : ℝ) ∧
      (0 < lam - δ →
        ((2 * shiftedProgressionTop k (Nat.sqrt (2 * k)) T N : Nat) : ℝ) <
          Real.exp ((k : ℝ) / (lam - δ)))

/-- Interval-width endpoint target.  This is the bookkeeping-free form of the
remaining asymptotic construction: find a real interval `(L,U)` which is
large/central enough at its left endpoint, lies inside the desired exponential
window after multiplying by `2`, and has enough width to contain a shifted
progression window of length `N`. -/
def shiftedLargeKIntervalEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat, ∃ L U : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
      (k : ℝ) ≤ L ∧
      (M : ℝ) ≤ 2 * L ∧
      (k : ℝ) ≤ ρ * L ∧
      Real.exp ((k : ℝ) / (lam + δ)) < 2 * L ∧
      L + (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) < U ∧
      (0 < lam - δ → 2 * U < Real.exp ((k : ℝ) / (lam - δ)))

/-- The only hard interval-width case is `δ < lam`, where the upper
exponential endpoint is finite.  The complementary case `lam ≤ δ` has no upper
endpoint obligation in the logarithmic target. -/
def shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat, ∃ L U : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
      (k : ℝ) ≤ L ∧
      (M : ℝ) ≤ 2 * L ∧
      (k : ℝ) ≤ ρ * L ∧
      Real.exp ((k : ℝ) / (lam + δ)) < 2 * L ∧
      L + (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) < U ∧
      2 * U < Real.exp ((k : ℝ) / (lam - δ))

/-- Concrete left endpoint used in the subcritical exponential interval. -/
noncomputable def subcriticalEndpointLeft (lam δ : ℝ) (k : Nat) : ℝ :=
  Real.exp ((k : ℝ) / (lam + δ)) / 2 + 1

/-- Half of the concrete upper exponential endpoint in the subcritical case. -/
noncomputable def subcriticalEndpointUpperHalf (lam δ : ℝ) (k : Nat) : ℝ :=
  Real.exp ((k : ℝ) / (lam - δ)) / 2

/-- If the modulus and progression length are separately exponentially bounded,
then their endpoint-width cost is bounded by the exponential of the sum. -/
theorem shiftedProgression_cost_le_exp
    {k N : Nat} {B C : ℝ}
    (hR :
      (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) ≤ Real.exp B)
    (hN : (N : ℝ) + 2 ≤ Real.exp C) :
    (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) ≤
      Real.exp (B + C) := by
  calc
    (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2)
        ≤ Real.exp B * Real.exp C := by
          exact mul_le_mul hR hN (by positivity) (by positivity)
    _ = Real.exp (B + C) := by rw [Real.exp_add]

/-- Linearized exponential comparison: `log c + a <= b` is a convenient way
to prove `c * exp a <= exp b`. -/
theorem mul_exp_le_exp_of_log_add_le {c a b : ℝ}
    (hc : 0 < c) (h : Real.log c + a ≤ b) :
    c * Real.exp a ≤ Real.exp b := by
  have hExp : Real.exp (Real.log c + a) ≤ Real.exp b :=
    Real.exp_le_exp.mpr h
  simpa [Real.exp_add, Real.exp_log hc] using hExp

/-- In the subcritical case `0 < δ < lam`, the upper reciprocal exponent has
positive linear gap over the lower reciprocal exponent. -/
theorem subcritical_inverse_gap_pos {lam δ : ℝ}
    (hδ : 0 < δ) (hδlt : δ < lam) :
    0 < (lam - δ)⁻¹ - (lam + δ)⁻¹ := by
  have hlow : 0 < lam - δ := by linarith
  have hhigh : 0 < lam + δ := by linarith
  have hlt : lam - δ < lam + δ := by linarith
  have hinv : (lam + δ)⁻¹ < (lam - δ)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hlow hlt
  linarith

/-- Archimedean helper: a positive slope eventually dominates any fixed real
constant. -/
theorem exists_nat_mul_ge_of_pos {g x : ℝ} (hg : 0 < g) :
    ∃ k : Nat, x ≤ (k : ℝ) * g := by
  rcases exists_nat_gt (x / g) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hkg : x / g < (k : ℝ) := hk
  rw [div_lt_iff₀ hg] at hkg
  linarith

/-- The integer square root is bounded by the real square root. -/
theorem nat_sqrt_cast_le_real_sqrt (n : Nat) :
    ((Nat.sqrt n : Nat) : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hsquare :
      (((Nat.sqrt n : Nat) : ℝ) ^ 2) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le' n
  exact (Real.le_sqrt (by positivity) (by positivity)).2 hsquare

/-- A logarithm of a natural number is eventually below any positive linear
slope. -/
theorem eventually_log_natCast_le_mul_self {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in Filter.atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.bound hc
  have hnat :
      ∀ᶠ n : Nat in Filter.atTop,
        ‖Real.log ((n : Nat) : ℝ)‖ ≤ c * ‖id (((n : Nat) : ℝ))‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with n hn hn1
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hn1
  simpa [Real.norm_of_nonneg hlog_nonneg,
    Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] using hn

/-- The integer-sqrt modulus term is eventually below any positive linear
slope. -/
theorem eventually_nat_sqrt_mul_log_two_mul_le_mul_self {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : Nat in Filter.atTop,
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ c * (k : ℝ) := by
  let η : ℝ := c / 2
  have hηpos : 0 < η := by positivity
  have hreal :
      ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ η * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))).bound hηpos
  have htendsto :
      Filter.Tendsto (fun k : Nat => ((2 * k : Nat) : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.cast_mul] using
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun k : Nat => (2 : ℝ) * (k : ℝ)) Filter.atTop Filter.atTop)
  have hnat :
      ∀ᶠ k : Nat in Filter.atTop,
        ‖Real.log (((2 * k : Nat) : ℝ))‖ ≤
          η * ‖(((2 * k : Nat) : ℝ)) ^ (1 / 2 : ℝ)‖ :=
    htendsto.eventually hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with k hk hk1
  have htwopos : 0 < ((2 * k : Nat) : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log ((2 * k : Nat) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * k)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((2 * k : Nat) : ℝ) := Real.sqrt_nonneg _
  have hsqrt_bound :
      (Nat.sqrt (2 * k) : ℝ) ≤ Real.sqrt ((2 * k : Nat) : ℝ) :=
    nat_sqrt_cast_le_real_sqrt (2 * k)
  have hlog_bound :
      Real.log ((2 * k : Nat) : ℝ) ≤ η * Real.sqrt ((2 * k : Nat) : ℝ) := by
    have hrpow_nonneg :
        0 ≤ (((2 * k : Nat) : ℝ) ^ (1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have hk' := hk
    rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg] at hk'
    rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg] at hk'
    rw [← Real.sqrt_eq_rpow ((2 * k : Nat) : ℝ)] at hk'
    exact hk'
  calc
    (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ)
        ≤ Real.sqrt ((2 * k : Nat) : ℝ) * Real.log ((2 * k : Nat) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hsqrt_bound hlog_nonneg
    _ ≤ Real.sqrt ((2 * k : Nat) : ℝ) * (η * Real.sqrt ((2 * k : Nat) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlog_bound hsqrt_nonneg
    _ = η * ((2 * k : Nat) : ℝ) := by
          rw [show Real.sqrt ((2 * k : Nat) : ℝ) *
                (η * Real.sqrt ((2 * k : Nat) : ℝ)) =
                η * (Real.sqrt ((2 * k : Nat) : ℝ)) ^ 2 by ring]
          rw [Real.sq_sqrt (by positivity)]
    _ = c * (k : ℝ) := by
          simp [η]
          ring

/-- For the explicit ceiling choice of `J`, the power-tail logarithmic term is
eventually below any positive linear slope. -/
theorem eventually_ceil_log_tail_le_mul_self {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : Nat in Filter.atTop,
      let J : Nat :=
        Nat.ceil (Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)) + 3
      (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) ≤ c * (k : ℝ) := by
  let a : ℝ := Real.log (4 / 3 : ℝ)
  have hapos : 0 < a := by
    unfold a
    exact Real.log_pos (by norm_num)
  let εsq : ℝ := c * a / 6
  have hεsq : 0 < εsq := by positivity
  let εlog : ℝ := c / 42
  have hεlog : 0 < εlog := by positivity
  have htendsto :
      Filter.Tendsto (fun k : Nat => ((2 * k + 3 : Nat) : ℝ))
        Filter.atTop Filter.atTop := by
    have hmul : Filter.Tendsto (fun k : Nat => ((2 * k : Nat) : ℝ))
        Filter.atTop Filter.atTop := by
      simpa [Nat.cast_mul] using
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
          tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun k : Nat => (2 : ℝ) * (k : ℝ))
              Filter.atTop Filter.atTop)
    simpa [Nat.cast_add] using
      hmul.atTop_add (tendsto_const_nhds (x := (3 : ℝ)))
  have hsqReal :
      ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ 2‖ ≤ εsq * ‖id x‖ :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hεsq
  have hlogReal :
      ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ εlog * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.bound hεlog
  have hsqNat :
      ∀ᶠ k : Nat in Filter.atTop,
        ‖Real.log (((2 * k + 3 : Nat) : ℝ)) ^ 2‖ ≤
          εsq * ‖id (((2 * k + 3 : Nat) : ℝ))‖ :=
    htendsto.eventually hsqReal
  have hlogNat :
      ∀ᶠ k : Nat in Filter.atTop,
        ‖Real.log (((2 * k + 3 : Nat) : ℝ))‖ ≤
          εlog * ‖id (((2 * k + 3 : Nat) : ℝ))‖ :=
    htendsto.eventually hlogReal
  filter_upwards [hsqNat, hlogNat, Filter.eventually_ge_atTop 3] with k hsq hlog hk3
  let L : ℝ := Real.log ((2 * k + 3 : Nat) : ℝ)
  let x : ℝ := Real.log ((2 * k + 1 : Nat) : ℝ) / a
  let J : Nat := Nat.ceil x + 3
  have hLnonneg : 0 ≤ L := by
    unfold L
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * k + 3)
  have hXnonneg : 0 ≤ (((2 * k + 3 : Nat) : ℝ)) := by positivity
  have hXnonneg' : 0 ≤ (2 * (k : ℝ) + 3) := by positivity
  have hsq' : L ^ 2 ≤ εsq * ((2 * k + 3 : Nat) : ℝ) := by
    have hpow_nonneg : 0 ≤ L ^ 2 := by positivity
    have hsq' := hsq
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg] at hsq'
    simpa [id, Nat.cast_mul, Nat.cast_add, abs_of_nonneg hXnonneg'] using hsq'
  have hlog' : L ≤ εlog * ((2 * k + 3 : Nat) : ℝ) := by
    have hlog' := hlog
    rw [Real.norm_eq_abs, abs_of_nonneg hLnonneg] at hlog'
    simpa [id, Nat.cast_mul, Nat.cast_add, abs_of_nonneg hXnonneg'] using hlog'
  have htwo_three_le : ((2 * k + 3 : Nat) : ℝ) ≤ 3 * (k : ℝ) := by
    exact_mod_cast (by omega : 2 * k + 3 ≤ 3 * k)
  have hsq_scaled : a⁻¹ * L ^ 2 ≤ (c / 6) * ((2 * k + 3 : Nat) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsq' (le_of_lt (inv_pos.mpr hapos))
    have heq :
        a⁻¹ * (εsq * ((2 * k + 3 : Nat) : ℝ)) =
          (c / 6) * ((2 * k + 3 : Nat) : ℝ) := by
      field_simp [εsq, ne_of_gt hapos]
      ring
    rwa [heq] at hmul
  have hsq_budget : a⁻¹ * L ^ 2 ≤ (c / 2) * (k : ℝ) := by
    have hmul : (c / 6) * ((2 * k + 3 : Nat) : ℝ) ≤ (c / 6) * (3 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left htwo_three_le (by positivity)
    have heq : (c / 6) * (3 * (k : ℝ)) = (c / 2) * (k : ℝ) := by ring
    exact hsq_scaled.trans (by simpa [heq] using hmul)
  have hlog_scaled : 7 * L ≤ (c / 6) * ((2 * k + 3 : Nat) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog' (by norm_num : (0 : ℝ) ≤ 7)
    have heq :
        7 * (εlog * ((2 * k + 3 : Nat) : ℝ)) =
          (c / 6) * ((2 * k + 3 : Nat) : ℝ) := by
      simp [εlog]
      ring
    rwa [heq] at hmul
  have hlog_budget : 7 * L ≤ (c / 2) * (k : ℝ) := by
    have hmul : (c / 6) * ((2 * k + 3 : Nat) : ℝ) ≤ (c / 6) * (3 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left htwo_three_le (by positivity)
    have heq : (c / 6) * (3 * (k : ℝ)) = (c / 2) * (k : ℝ) := by ring
    exact hlog_scaled.trans (by simpa [heq] using hmul)
  have hlog_one_le : Real.log ((2 * k + 1 : Nat) : ℝ) ≤ L := by
    unfold L
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 3)
  have hx_nonneg : 0 ≤ x := by
    unfold x
    exact div_nonneg (by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ 2 * k + 1)) (le_of_lt hapos)
  have hceil_le : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx_nonneg).le
  have hx_le : x ≤ L / a := by
    unfold x
    exact div_le_div_of_nonneg_right hlog_one_le (le_of_lt hapos)
  have hJ_bound : ((J + 3 : Nat) : ℝ) ≤ L / a + 7 := by
    have hJ_cast : ((J + 3 : Nat) : ℝ) = (Nat.ceil x : ℝ) + 6 := by
      have hnat : J + 3 = Nat.ceil x + 6 := by
        simp [J]
      exact_mod_cast hnat
    rw [hJ_cast]
    nlinarith
  have htail_bound :
      ((J + 3 : Nat) : ℝ) * L ≤ (L / a + 7) * L :=
    mul_le_mul_of_nonneg_right hJ_bound hLnonneg
  have hsplit : (L / a + 7) * L = a⁻¹ * L ^ 2 + 7 * L := by
    field_simp [ne_of_gt hapos]
  have hbudget_sum : a⁻¹ * L ^ 2 + 7 * L ≤ c * (k : ℝ) := by
    nlinarith
  exact htail_bound.trans (by simpa [hsplit] using hbudget_sum)

/-- Explicit subcritical interval target.  The arbitrary interval witnesses are
removed: the left endpoint is just past the lower exponential endpoint, and the
right endpoint is obtained by taking a midpoint before the upper endpoint. -/
def shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
      (k : ℝ) ≤ subcriticalEndpointLeft lam δ k ∧
      (M : ℝ) ≤ 2 * subcriticalEndpointLeft lam δ k ∧
      (k : ℝ) ≤ ρ * subcriticalEndpointLeft lam δ k ∧
      subcriticalEndpointLeft lam δ k +
          (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) <
        subcriticalEndpointUpperHalf lam δ k

/-- Analytic subcritical target.  This replaces the raw modulus-width term by
two exponent estimates: one for the square-root small-prime modulus and one for
the chosen progression length. -/
def shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J N : Nat, ∃ B C : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      0 < N ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      2 * ((2 * k + 1) *
        ((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2))) < N ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (N : ℝ) + 2 ≤ Real.exp C ∧
      (k : ℝ) ≤ subcriticalEndpointLeft lam δ k ∧
      (M : ℝ) ≤ 2 * subcriticalEndpointLeft lam δ k ∧
      (k : ℝ) ≤ ρ * subcriticalEndpointLeft lam δ k ∧
      subcriticalEndpointLeft lam δ k + Real.exp (B + C) <
        subcriticalEndpointUpperHalf lam δ k

/-- Analytic subcritical target with the progression length eliminated.  The
length is chosen as `crudeTailThreshold k J + 1`; hence it is enough to prove
`tail + 3 <= exp C`. -/
def shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (k : ℝ) ≤ subcriticalEndpointLeft lam δ k ∧
      (M : ℝ) ≤ 2 * subcriticalEndpointLeft lam δ k ∧
      (k : ℝ) ≤ ρ * subcriticalEndpointLeft lam δ k ∧
      subcriticalEndpointLeft lam δ k + Real.exp (B + C) <
        subcriticalEndpointUpperHalf lam δ k

/-- Split-width version of the bounded-tail target.  The final interval-width
inequality is replaced by three simpler exponential comparisons: the lower
endpoint, the constant `1`, and the combined modulus/length cost each consume
at most one eighth of the upper exponential endpoint. -/
def shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (k : ℝ) ≤ subcriticalEndpointLeft lam δ k ∧
      (M : ℝ) ≤ 2 * subcriticalEndpointLeft lam δ k ∧
      (k : ℝ) ≤ ρ * subcriticalEndpointLeft lam δ k ∧
      4 * Real.exp ((k : ℝ) / (lam + δ)) ≤
        Real.exp ((k : ℝ) / (lam - δ)) ∧
      8 ≤ Real.exp ((k : ℝ) / (lam - δ)) ∧
      8 * Real.exp (B + C) ≤ Real.exp ((k : ℝ) / (lam - δ))

/-- Growth-form split-width target.  The lower-endpoint size and centrality
conditions are replaced by direct lower-exponential estimates. -/
def shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (2 : ℝ) * (k : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (M : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (2 : ℝ) * (k : ℝ) ≤ ρ * Real.exp ((k : ℝ) / (lam + δ)) ∧
      4 * Real.exp ((k : ℝ) / (lam + δ)) ≤
        Real.exp ((k : ℝ) / (lam - δ)) ∧
      8 ≤ Real.exp ((k : ℝ) / (lam - δ)) ∧
      8 * Real.exp (B + C) ≤ Real.exp ((k : ℝ) / (lam - δ))

/-- Linearized growth-form split-width target.  The three upper-exponential
share inequalities are expressed as additive inequalities among exponents. -/
def shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (2 : ℝ) * (k : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (M : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (2 : ℝ) * (k : ℝ) ≤ ρ * Real.exp ((k : ℝ) / (lam + δ)) ∧
      Real.log 4 + (k : ℝ) / (lam + δ) ≤ (k : ℝ) / (lam - δ) ∧
      Real.log 8 ≤ (k : ℝ) / (lam - δ) ∧
      Real.log 8 + (B + C) ≤ (k : ℝ) / (lam - δ)

/-- Linear growth target with the two fixed endpoint-gap inequalities removed.
It must produce arbitrarily large `k`; the wrapper chooses the lower bound
large enough to absorb the constants `log 4` and `log 8`. -/
def shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      K ≤ k ∧
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      (2 : ℝ) * (k : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (M : ℝ) ≤ Real.exp ((k : ℝ) / (lam + δ)) ∧
      (2 : ℝ) * (k : ℝ) ≤ ρ * Real.exp ((k : ℝ) / (lam + δ)) ∧
      Real.log 8 + (B + C) ≤ (k : ℝ) / (lam - δ)

/-- Logarithmic lower-growth version of the cost-linear target.  The lower
exponential domination conditions are expressed as logarithmic inequalities. -/
def shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      K ≤ k ∧
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log 8 + (B + C) ≤ (k : ℝ) / (lam - δ)

/-- Budgeted version of the logarithmic cost-linear target.  The combined
cost inequality is replaced by separate quarter-budget bounds for the modulus
and tail exponents. -/
def shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k J : Nat, ∃ B C : ℝ,
      K ≤ k ∧
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp C ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ) ∧
      B ≤ ((k : ℝ) / (lam - δ)) / 4 ∧
      C ≤ ((k : ℝ) / (lam - δ)) / 4

/-- Direct budgeted version of the logarithmic cost-linear target.  The
auxiliary exponents are eliminated: the tail term is controlled by its log,
and the modulus term is controlled directly by the same quarter budget. -/
def shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k J : Nat,
      K ≤ k ∧
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      Real.log ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ)

/-- Power-tail version of the direct budget target.  The opaque crude-tail
logarithm is replaced by the explicit upper bound `(J+3) log(2k+3)`. -/
def shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k J : Nat,
      K ≤ k ∧
      25 ≤ k ∧
      2 ≤ J ∧
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 ∧
      (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ)

/-- Ceiling-`J` version of the power-tail direct budget target.  Here `J` is
chosen explicitly from the geometric-decay lower bound. -/
def shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ ρ : ℝ,
    0 < δ →
    δ < lam →
    0 < ρ →
    ∀ M K : Nat, ∃ k : Nat,
      let J : Nat :=
        Nat.ceil (Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)) + 3
      K ≤ k ∧
      25 ≤ k ∧
      (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) ∧
      Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ)

/-- Core ceiling-`J` target.  The dependence on the fixed constants `M` and
`ρ` has been removed; those lower-growth bounds are recovered by making `k`
larger. -/
def shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (lam : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ →
    δ < lam →
    ∀ K : Nat, ∃ k : Nat,
      let J : Nat :=
        Nat.ceil (Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)) + 3
      K ≤ k ∧
      25 ≤ k ∧
      (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 ∧
      Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (2 * (lam + δ))

/-- The core ceiling target implies the full ceiling target after increasing
the lower bound for `k` to absorb the fixed constants `log M` and `-log ρ`. -/
theorem shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_core
    {lam : ℝ}
    (hsupply :
      shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  have hhigh : 0 < lam + δ := by linarith
  have hslope : 0 < (2 * (lam + δ))⁻¹ := by positivity
  rcases exists_nat_mul_ge_of_pos (g := (2 * (lam + δ))⁻¹)
      (x := Real.log (M : ℝ)) hslope with
    ⟨KM, hKM⟩
  rcases exists_nat_mul_ge_of_pos (g := (2 * (lam + δ))⁻¹)
      (x := -Real.log ρ) hslope with
    ⟨Kρ, hKρ⟩
  let K' : Nat := max K (max KM Kρ)
  rcases hsupply δ hδ hδlt K' with
    ⟨k, hK'le, hk25, htailPower, hmodBudget, hlogTwoHalf⟩
  have hKle : K ≤ k := (Nat.le_max_left K (max KM Kρ)).trans hK'le
  have hKMle : KM ≤ k := (Nat.le_max_left KM Kρ).trans
    ((Nat.le_max_right K (max KM Kρ)).trans hK'le)
  have hKρle : Kρ ≤ k := (Nat.le_max_right KM Kρ).trans
    ((Nat.le_max_right K (max KM Kρ)).trans hK'le)
  have hhalf_le_full : (k : ℝ) / (2 * (lam + δ)) ≤ (k : ℝ) / (lam + δ) := by
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    field_simp [ne_of_gt hhigh]
    nlinarith
  have hlogTwo : Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (lam + δ) :=
    hlogTwoHalf.trans hhalf_le_full
  have hlogM_half : Real.log (M : ℝ) ≤ (k : ℝ) / (2 * (lam + δ)) := by
    have hcast : (KM : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKMle
    have hmono :
        (KM : ℝ) * (2 * (lam + δ))⁻¹ ≤
          (k : ℝ) * (2 * (lam + δ))⁻¹ :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt hslope)
    have hraw : Real.log (M : ℝ) ≤ (k : ℝ) * (2 * (lam + δ))⁻¹ :=
      hKM.trans hmono
    have heq : (k : ℝ) * (2 * (lam + δ))⁻¹ = (k : ℝ) / (2 * (lam + δ)) := by
      rw [div_eq_mul_inv]
    rwa [heq] at hraw
  have hlogM : Real.log (M : ℝ) ≤ (k : ℝ) / (lam + δ) :=
    hlogM_half.trans hhalf_le_full
  have hnegLogρ_half : -Real.log ρ ≤ (k : ℝ) / (2 * (lam + δ)) := by
    have hcast : (Kρ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKρle
    have hmono :
        (Kρ : ℝ) * (2 * (lam + δ))⁻¹ ≤
          (k : ℝ) * (2 * (lam + δ))⁻¹ :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt hslope)
    have hraw : -Real.log ρ ≤ (k : ℝ) * (2 * (lam + δ))⁻¹ :=
      hKρ.trans hmono
    have heq : (k : ℝ) * (2 * (lam + δ))⁻¹ = (k : ℝ) / (2 * (lam + δ)) := by
      rw [div_eq_mul_inv]
    rwa [heq] at hraw
  have hlogCentral : Real.log (((2 * k : Nat) : ℝ) / ρ) ≤ (k : ℝ) / (lam + δ) := by
    have hkpos : 0 < k := by omega
    have htwoPos : (0 : ℝ) < ((2 * k : Nat) : ℝ) := by positivity
    have hdivLog :
        Real.log (((2 * k : Nat) : ℝ) / ρ) =
          Real.log ((2 * k : Nat) : ℝ) - Real.log ρ := by
      rw [Real.log_div (ne_of_gt htwoPos) (ne_of_gt hρ)]
    have hhalf_add :
        (k : ℝ) / (2 * (lam + δ)) + (k : ℝ) / (2 * (lam + δ)) =
          (k : ℝ) / (lam + δ) := by
      field_simp [ne_of_gt hhigh]
      ring
    rw [hdivLog]
    nlinarith
  exact ⟨k, hKle, hk25, htailPower, hmodBudget, hlogTwo, hlogM, hlogCentral⟩

/-- The core ceiling target follows from the standard sublinear growth of
`log`, `log^2`, and `sqrt(x) log x`. -/
theorem shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_pos
    {lam : ℝ} (hlam : 0 < lam) :
    shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ hδ hδlt K
  have hlow : 0 < lam - δ := by linarith
  have hhigh : 0 < lam + δ := by linarith
  let cUpper : ℝ := (4 * (lam - δ))⁻¹
  have hcUpper : 0 < cUpper := by
    unfold cUpper
    positivity
  let cLower : ℝ := (4 * (lam + δ))⁻¹
  have hcLower : 0 < cLower := by
    unfold cLower
    positivity
  have htailEv := eventually_ceil_log_tail_le_mul_self (c := cUpper) hcUpper
  have hsqrtEv := eventually_nat_sqrt_mul_log_two_mul_le_mul_self (c := cUpper) hcUpper
  have hlogAll := eventually_log_natCast_le_mul_self (c := cLower) hcLower
  have htendstoTwo :
      Filter.Tendsto (fun k : Nat => ((2 * k : Nat) : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.cast_mul] using
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun k : Nat => (2 : ℝ) * (k : ℝ)) Filter.atTop Filter.atTop)
  have htendstoTwoNat :
      Filter.Tendsto (fun k : Nat => 2 * k) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_atTop_of_monotone
      (fun a b h => Nat.mul_le_mul_left 2 h)
      (fun b => ⟨b, by omega⟩)
  have hlogTwoEv :
      ∀ᶠ k : Nat in Filter.atTop,
        Real.log ((2 * k : Nat) : ℝ) ≤ cLower * ((2 * k : Nat) : ℝ) :=
    htendstoTwoNat.eventually hlogAll
  have hEv :
      ∀ᶠ k : Nat in Filter.atTop,
        let J : Nat :=
          Nat.ceil (Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)) + 3
        K ≤ k ∧
        25 ≤ k ∧
        (J + 3 : Nat) * Real.log ((2 * k + 3 : Nat) : ℝ) ≤
          ((k : ℝ) / (lam - δ)) / 4 ∧
        (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤
          ((k : ℝ) / (lam - δ)) / 4 ∧
        Real.log ((2 * k : Nat) : ℝ) ≤ (k : ℝ) / (2 * (lam + δ)) := by
    filter_upwards [htailEv, hsqrtEv, hlogTwoEv, Filter.eventually_ge_atTop K,
      Filter.eventually_ge_atTop 25] with k htail hsqrt hlog hK hk25
    have hUpperEq : cUpper * (k : ℝ) = ((k : ℝ) / (lam - δ)) / 4 := by
      unfold cUpper
      field_simp [ne_of_gt hlow]
    have hLowerEq : cLower * (2 * (k : ℝ)) = (k : ℝ) / (2 * (lam + δ)) := by
      unfold cLower
      field_simp [ne_of_gt hhigh]
      ring_nf
    exact ⟨hK, hk25, by simpa [hUpperEq] using htail,
      by simpa [hUpperEq] using hsqrt,
      by simpa [hLowerEq, Nat.cast_mul] using hlog⟩
  rcases hEv.exists with ⟨k, hk⟩
  exact ⟨k, hk⟩

/-- The ceiling-`J` target implies the power-tail target: the extra `+1` above
the ceiling supplies the strict geometric decay. -/
theorem shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_ceil
    {lam : ℝ}
    (hsupply :
      shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  rcases hsupply δ ρ hδ hδlt hρ M K with
    ⟨k, hKle, hk25, htailPower, hmodBudget, hlogTwo, hlogM, hlogCentral⟩
  let x : ℝ := Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)
  let J : Nat := Nat.ceil x + 3
  have hJ : 2 ≤ J := by omega
  have hJsub : J - 2 = Nat.ceil x + 1 := by omega
  have hlog43pos : 0 < Real.log (4 / 3 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hlogNonneg : 0 ≤ Real.log ((2 * k + 1 : Nat) : ℝ) := by
    apply Real.log_nonneg
    norm_num
  have hx_nonneg : 0 ≤ x := by
    exact div_nonneg hlogNonneg (le_of_lt hlog43pos)
  have hx_lt : x < (Nat.ceil x : ℝ) + 1 := by
    have hx_le : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    linarith
  have hmul_lt :
      x * Real.log (4 / 3 : ℝ) <
        ((Nat.ceil x : ℝ) + 1) * Real.log (4 / 3 : ℝ) :=
    mul_lt_mul_of_pos_right hx_lt hlog43pos
  have hx_mul :
      x * Real.log (4 / 3 : ℝ) = Real.log ((2 * k + 1 : Nat) : ℝ) := by
    change
      (Real.log ((2 * k + 1 : Nat) : ℝ) / Real.log (4 / 3 : ℝ)) *
          Real.log (4 / 3 : ℝ) =
        Real.log ((2 * k + 1 : Nat) : ℝ)
    field_simp [ne_of_gt hlog43pos]
  have hJcast : ((J - 2 : Nat) : ℝ) = (Nat.ceil x : ℝ) + 1 := by
    rw [hJsub]
    norm_num
  have hgeomLog :
      Real.log ((2 * k + 1 : Nat) : ℝ) <
        (J - 2 : Nat) * Real.log (4 / 3 : ℝ) := by
    rw [← hx_mul]
    simpa [hJcast] using hmul_lt
  have hgeom :
      (2 * k + 1 : ℝ) * ((3 / 4 : ℝ) ^ (J - 2)) < 1 :=
    geometric_decay_of_log_lt (k := k) (J := J) hgeomLog
  exact ⟨k, J, hKle, hk25, hJ, hgeom, htailPower, hmodBudget, hlogTwo, hlogM,
    hlogCentral⟩

/-- The power-tail target implies the direct budget target by the elementary
crude-tail power bound. -/
theorem shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_powerTail
    {lam : ℝ}
    (hsupply :
      shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  rcases hsupply δ ρ hδ hδlt hρ M K with
    ⟨k, J, hKle, hk25, hJ, hgeom, htailPower, hmodBudget, hlogTwo, hlogM,
      hlogCentral⟩
  have hk1 : 1 ≤ k := by omega
  have htailLog :
      Real.log ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤
        ((k : ℝ) / (lam - δ)) / 4 :=
    (log_crudeTailThreshold_add_three_le (k := k) (J := J) hk1 hJ).trans
      htailPower
  exact ⟨k, J, hKle, hk25, hJ, hgeom, htailLog, hmodBudget, hlogTwo, hlogM,
    hlogCentral⟩

/-- The direct budgeted target implies the budgeted target by taking the two
auxiliary exponents to be the common quarter budget. -/
theorem shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt_of_directBudget
    {lam : ℝ}
    (hsupply : shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  rcases hsupply δ ρ hδ hδlt hρ M K with
    ⟨k, J, hKle, hk25, hJ, hgeom, htailLog, hmodBudget, hlogTwo, hlogM,
      hlogCentral⟩
  let E : ℝ := ((k : ℝ) / (lam - δ)) / 4
  have htailE : ((crudeTailThreshold k J + 3 : Nat) : ℝ) ≤ Real.exp E := by
    exact Real.le_exp_of_log_le (by simpa [E] using htailLog)
  exact ⟨k, J, E, E, hKle, hk25, hJ, hgeom, htailE, hmodBudget, hlogTwo,
    hlogM, hlogCentral, le_rfl, le_rfl⟩

/-- The budgeted target implies the log-cost target after choosing `k` large
enough that `log 8` fits in the remaining half of the upper exponent budget. -/
theorem shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt_of_budget
    {lam : ℝ}
    (hsupply : shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  have hlow : 0 < lam - δ := by linarith
  have hslope : 0 < (2 * (lam - δ))⁻¹ := by positivity
  rcases exists_nat_mul_ge_of_pos (g := (2 * (lam - δ))⁻¹)
      (x := Real.log 8) hslope with
    ⟨K₈, hK₈⟩
  let K' : Nat := max K K₈
  rcases hsupply δ ρ hδ hδlt hρ M K' with
    ⟨k, J, B, C, hK'le, hk25, hJ, hgeom, htailC, hB, hlogTwo, hlogM,
      hlogCentral, hBbudget, hCbudget⟩
  have hKle : K ≤ k := (Nat.le_max_left K K₈).trans hK'le
  have hK₈le : K₈ ≤ k := (Nat.le_max_right K K₈).trans hK'le
  have hlog8_half : Real.log 8 ≤ ((k : ℝ) / (lam - δ)) / 2 := by
    have hcast : (K₈ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK₈le
    have hmono :
        (K₈ : ℝ) * (2 * (lam - δ))⁻¹ ≤
          (k : ℝ) * (2 * (lam - δ))⁻¹ :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt hslope)
    have hraw : Real.log 8 ≤ (k : ℝ) * (2 * (lam - δ))⁻¹ := hK₈.trans hmono
    have heq :
        (k : ℝ) * (2 * (lam - δ))⁻¹ = ((k : ℝ) / (lam - δ)) / 2 := by
      field_simp [ne_of_gt hlow]
    rwa [heq] at hraw
  have hCostGap : Real.log 8 + (B + C) ≤ (k : ℝ) / (lam - δ) := by
    nlinarith
  exact ⟨k, J, B, C, hKle, hk25, hJ, hgeom, htailC, hB, hlogTwo, hlogM,
    hlogCentral, hCostGap⟩

/-- The logarithmic lower-growth target implies the cost-linear target by
exponentiating the three lower-growth inequalities. -/
theorem shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt_of_logCostLinear
    {lam : ℝ}
    (hsupply : shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M K
  rcases hsupply δ ρ hδ hδlt hρ M K with
    ⟨k, J, B, C, hKle, hk25, hJ, hgeom, htailC, hB, hlogTwo, hlogM,
      hlogCentral, hCostGap⟩
  let lower : ℝ := (k : ℝ) / (lam + δ)
  have htwoExp : (2 : ℝ) * (k : ℝ) ≤ Real.exp lower := by
    have hraw : (((2 * k : Nat) : ℝ)) ≤ Real.exp lower :=
      Real.le_exp_of_log_le (by simpa [lower] using hlogTwo)
    simpa using hraw
  have hMExp : (M : ℝ) ≤ Real.exp lower :=
    Real.le_exp_of_log_le (by simpa [lower] using hlogM)
  have hcentralExp : (2 : ℝ) * (k : ℝ) ≤ ρ * Real.exp lower := by
    have hdiv : (((2 * k : Nat) : ℝ) / ρ) ≤ Real.exp lower :=
      Real.le_exp_of_log_le (by simpa [lower] using hlogCentral)
    have hmul : ρ * ((((2 * k : Nat) : ℝ) / ρ)) ≤ ρ * Real.exp lower :=
      mul_le_mul_of_nonneg_left hdiv (le_of_lt hρ)
    have hleft' : ρ * ((2 * (k : ℝ)) / ρ) = 2 * (k : ℝ) := by
      field_simp [ne_of_gt hρ]
    have hmul' : 2 * (k : ℝ) ≤ ρ * Real.exp lower := by
      simpa [hleft'] using hmul
    nlinarith
  exact ⟨k, J, B, C, hKle, hk25, hJ, hgeom, htailC, hB,
    by simpa [lower] using htwoExp,
    by simpa [lower] using hMExp,
    by simpa [lower] using hcentralExp,
    hCostGap⟩

/-- Producing arbitrarily large `k` for the cost-linear target suffices for the
fully linearized target. -/
theorem shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt_of_costLinear
    {lam : ℝ}
    (hsupply : shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  let g : ℝ := (lam - δ)⁻¹ - (lam + δ)⁻¹
  have hgpos : 0 < g := by
    exact subcritical_inverse_gap_pos hδ hδlt
  have hlowPos : 0 < lam - δ := by linarith
  rcases exists_nat_mul_ge_of_pos (g := g) (x := Real.log 4) hgpos with
    ⟨K₁, hK₁⟩
  rcases exists_nat_mul_ge_of_pos (g := (lam - δ)⁻¹) (x := Real.log 8)
      (by positivity) with
    ⟨K₂, hK₂⟩
  let K : Nat := max K₁ K₂
  rcases hsupply δ ρ hδ hδlt hρ M K with
    ⟨k, J, B, C, hKle, hk25, hJ, hgeom, htailC, hB, hkExp, hMExp,
      hcentralExp, hCostGap⟩
  have hK₁k : K₁ ≤ k := by
    exact (Nat.le_max_left K₁ K₂).trans hKle
  have hK₂k : K₂ ≤ k := by
    exact (Nat.le_max_right K₁ K₂).trans hKle
  have hlog4_le : Real.log 4 ≤ (k : ℝ) * g := by
    have hcast : (K₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK₁k
    have hmono : (K₁ : ℝ) * g ≤ (k : ℝ) * g := by
      exact mul_le_mul_of_nonneg_right hcast (le_of_lt hgpos)
    exact hK₁.trans hmono
  have hlog8_le : Real.log 8 ≤ (k : ℝ) / (lam - δ) := by
    have hcast : (K₂ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK₂k
    have hmono : (K₂ : ℝ) * (lam - δ)⁻¹ ≤ (k : ℝ) * (lam - δ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hcast (le_of_lt (inv_pos.mpr hlowPos))
    have hK₂' : Real.log 8 ≤ (K₂ : ℝ) * (lam - δ)⁻¹ := hK₂
    have hk_eq : (k : ℝ) * (lam - δ)⁻¹ = (k : ℝ) / (lam - δ) := by
      rw [div_eq_mul_inv]
    exact hK₂'.trans (by simpa [hk_eq] using hmono)
  have hLowerGap : Real.log 4 + (k : ℝ) / (lam + δ) ≤ (k : ℝ) / (lam - δ) := by
    have hhighPos : 0 < lam + δ := by linarith
    have hdiff :
        (k : ℝ) / (lam - δ) - (k : ℝ) / (lam + δ) = (k : ℝ) * g := by
      simp [g, div_eq_mul_inv]
      ring
    nlinarith
  exact ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkExp, hMExp,
    hcentralExp, hLowerGap, hlog8_le, hCostGap⟩

/-- The linearized growth target implies the multiplicative growth target. -/
theorem shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt_of_linear
    {lam : ℝ}
    (hsupply : shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkExp, hMExp, hcentralExp,
      hLowerGap, hOneGap, hCostGap⟩
  refine ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkExp, hMExp,
    hcentralExp, ?_, ?_, ?_⟩
  · exact mul_exp_le_exp_of_log_add_le (by norm_num : (0 : ℝ) < 4) hLowerGap
  · have h := mul_exp_le_exp_of_log_add_le
      (by norm_num : (0 : ℝ) < 8) (a := 0) (b := (k : ℝ) / (lam - δ)) (by simpa using hOneGap)
    simpa using h
  · exact mul_exp_le_exp_of_log_add_le (by norm_num : (0 : ℝ) < 8) hCostGap

/-- Growth-form split-width supply implies the split-width target because the
chosen left endpoint is `exp(lower)/2 + 1`. -/
theorem shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt_of_growth
    {lam : ℝ}
    (hsupply : shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkExp, hMExp, hcentralExp,
      hlowerShare, honeShare, hcostShare⟩
  refine ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, ?_, ?_, ?_,
    hlowerShare, honeShare, hcostShare⟩
  · simp [subcriticalEndpointLeft]
    nlinarith
  · simp [subcriticalEndpointLeft]
    nlinarith
  · have hρnonneg : 0 ≤ ρ := le_of_lt hρ
    have hhalf_le :
        ρ * (Real.exp ((k : ℝ) / (lam + δ)) / 2) ≤
          ρ * (subcriticalEndpointLeft lam δ k) := by
      apply mul_le_mul_of_nonneg_left _ hρnonneg
      simp [subcriticalEndpointLeft]
    have hk_le_half : (k : ℝ) ≤ ρ * (Real.exp ((k : ℝ) / (lam + δ)) / 2) := by
      nlinarith
    exact le_trans hk_le_half hhalf_le

/-- The split-width target implies the bounded-tail target by summing the
three one-eighth contributions. -/
theorem shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt_of_splitWidth
    {lam : ℝ}
    (hsupply : shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkL, hML, hcentralL,
      hlowerShare, honeShare, hcostShare⟩
  refine ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkL, hML, hcentralL, ?_⟩
  let E := Real.exp ((k : ℝ) / (lam - δ))
  let A := Real.exp ((k : ℝ) / (lam + δ))
  let D := Real.exp (B + C)
  have hEpos : 0 < E := by
    unfold E
    positivity
  have hAshare : A / 2 ≤ E / 8 := by
    have h : 4 * A ≤ E := by simpa [A, E] using hlowerShare
    nlinarith
  have honeshare : (1 : ℝ) ≤ E / 8 := by
    have h : (8 : ℝ) ≤ E := by simpa [E] using honeShare
    nlinarith
  have hDshare : D ≤ E / 8 := by
    have h : 8 * D ≤ E := by simpa [D, E] using hcostShare
    nlinarith
  have hsum :
      A / 2 + 1 + D ≤ 3 * E / 8 := by
    nlinarith
  have hstrict : 3 * E / 8 < E / 2 := by
    nlinarith
  have hleft :
      subcriticalEndpointLeft lam δ k + Real.exp (B + C) =
        A / 2 + 1 + D := by
    simp [subcriticalEndpointLeft, A, D]
  have hupper :
      subcriticalEndpointUpperHalf lam δ k = E / 2 := by
    simp [subcriticalEndpointUpperHalf, E]
  rw [hleft, hupper]
  exact lt_of_le_of_lt hsum hstrict

/-- The bounded-tail target implies the analytic target by taking
`N = crudeTailThreshold k J + 1`. -/
theorem shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt_of_boundedTail
    {lam : ℝ}
    (hsupply : shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, B, C, hk25, hJ, hgeom, htailC, hB, hkL, hML, hcentralL, hfit⟩
  rcases exists_progression_length_above_tail_with_exp_bound
      (k := k) (J := J) (C := C) htailC with
    ⟨N, hNpos, htail, hNexp⟩
  refine ⟨k, J, N, B, C, hk25, hJ, hNpos, hgeom, ?_, hB, hNexp,
    hkL, hML, hcentralL, hfit⟩
  simpa [crudeTailThreshold] using htail

/-- The analytic subcritical target implies the explicit endpoint target by
exponentiating the modulus bound and multiplying the two exponential estimates. -/
theorem shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt_of_analytic
    {lam : ℝ}
    (hsupply : shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, N, B, C, hk25, hJ, hNpos, hgeom, htail, hB, hC, hkL, hML,
      hcentralL, hfit⟩
  have hkpos : 0 < k := by omega
  have hRexp :
      (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) ≤ Real.exp B :=
    baseRestrictedPrimePowerModulus_sqrt_cast_le_exp (k := k) hkpos hB
  have hcost :
      (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) ≤
        Real.exp (B + C) :=
    shiftedProgression_cost_le_exp hRexp hC
  refine ⟨k, J, N, hk25, hJ, hNpos, hgeom, htail, hkL, hML, hcentralL, ?_⟩
  nlinarith

/-- The explicit subcritical endpoint inequalities produce the interval-witness
form by placing `U` halfway between the consumed width and the upper endpoint. -/
theorem shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt_of_explicit
    {lam : ℝ}
    (hsupply :
      shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hδlt hρ M
  rcases hsupply δ ρ hδ hδlt hρ M with
    ⟨k, J, N, hk25, hJ, hNpos, hgeom, htail, hkL, hML, hcentralL, hfit⟩
  let L := subcriticalEndpointLeft lam δ k
  let H := subcriticalEndpointUpperHalf lam δ k
  let W := L + (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2)
  let U := (W + H) / 2
  have hLdef : L = subcriticalEndpointLeft lam δ k := rfl
  have hHdef : H = subcriticalEndpointUpperHalf lam δ k := rfl
  have hUdef : U = (W + H) / 2 := rfl
  have hfit' : W < H := by simpa [W, L, H] using hfit
  have hlowerL : Real.exp ((k : ℝ) / (lam + δ)) < 2 * L := by
    rw [hLdef, subcriticalEndpointLeft]
    nlinarith
  have hwidth : W < U := by
    rw [hUdef]
    nlinarith
  have hupper : 2 * U < Real.exp ((k : ℝ) / (lam - δ)) := by
    have hU : 2 * U = W + H := by
      rw [hUdef]
      ring
    have hH : Real.exp ((k : ℝ) / (lam - δ)) = 2 * H := by
      rw [hHdef, subcriticalEndpointUpperHalf]
      ring
    nlinarith
  exact ⟨k, J, N, L, U, hk25, hJ, hNpos, hgeom, htail,
    by simpa [L] using hkL,
    by simpa [L] using hML,
    by simpa [L] using hcentralL,
    hlowerL,
    by simpa [W] using hwidth,
    hupper⟩

/-- Subcritical interval supply suffices: when `δ >= lam`, the upper endpoint
condition is contradictory and one can choose an arbitrarily large interval
after satisfying the geometric and tail constraints. -/
theorem shiftedLargeKIntervalEndpointWindowParameterSupplyAt_of_subcritical
    {lam : ℝ}
    (hsupply : shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKIntervalEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  by_cases hδlt : δ < lam
  · rcases hsupply δ ρ hδ hδlt hρ M with
      ⟨k, J, N, L, U, hk25, hJ, hNpos, hgeom, htail, hkL, hML, hcentralL,
        hlowerL, hwidth, hupperU⟩
    exact ⟨k, J, N, L, U, hk25, hJ, hNpos, hgeom, htail, hkL, hML, hcentralL,
      hlowerL, hwidth, fun _ => hupperU⟩
  · let k : Nat := 25
    rcases exists_geometric_decay_exponent k with ⟨J, hJ, hgeom⟩
    rcases exists_progression_length_above_tail k J with ⟨N, hNpos, htail⟩
    let C : ℝ :=
      max (max (max (k : ℝ) ((M : ℝ) / 2)) ((k : ℝ) / ρ))
        (Real.exp ((k : ℝ) / (lam + δ)) / 2)
    rcases exists_nat_gt C with ⟨m, hm⟩
    let L : ℝ := m
    let U : ℝ :=
      L + (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) * ((N : ℝ) + 2) + 1
    have hC_lt_L : C < L := by simpa [L] using hm
    refine ⟨k, J, N, L, U, by omega, hJ, hNpos, hgeom, htail, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hk_lt : (k : ℝ) < L := by
        have hkC : (k : ℝ) ≤ C := by
          exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
        exact lt_of_le_of_lt hkC hC_lt_L
      exact le_of_lt hk_lt
    · have hM_lt : (M : ℝ) / 2 < L := by
        have hMC : (M : ℝ) / 2 ≤ C := by
          exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
        exact lt_of_le_of_lt hMC hC_lt_L
      nlinarith
    · have hkdiv_lt : (k : ℝ) / ρ < L := by
        have hkdivC : (k : ℝ) / ρ ≤ C := by
          exact le_trans (le_max_right _ _) (le_max_left _ _)
        exact lt_of_le_of_lt hkdivC hC_lt_L
      rw [div_lt_iff₀ hρ] at hkdiv_lt
      exact le_of_lt (by simpa [mul_comm] using hkdiv_lt)
    · have hexp_lt : Real.exp ((k : ℝ) / (lam + δ)) / 2 < L := by
        exact lt_of_le_of_lt (le_max_right _ _) hC_lt_L
      nlinarith
    · simp [U]
    · intro hpos
      have : δ < lam := by linarith
      exact False.elim (hδlt this)

/-- The large-`k` supply implies the sqrt-canonical supply. -/
theorem sqrtProgressionWindowParameterSupplyAt_of_largeKProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : largeKProgressionWindowParameterSupplyAt lam) :
    sqrtProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, N, hk25, hJ, hcard, hpost⟩
  refine ⟨k, J, N, ?_, ?_, hJ, hcard, hpost⟩
  · omega
  · exact seven_le_sqrt_two_mul_of_25_le hk25

/-- The sqrt-canonical finite progression supply implies the canonical finite
progression supply by taking `Y = sqrt (2*k)`. -/
theorem canonicalProgressionWindowParameterSupplyAt_of_sqrtProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : sqrtProgressionWindowParameterSupplyAt lam) :
    canonicalProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, N, hkpos, hY7, hJ, hcard, hpost⟩
  refine ⟨k, Nat.sqrt (2 * k), J, N, hkpos, ?_, hY7, hJ, hcard, hpost⟩
  exact two_mul_lt_succ_sqrt_two_mul_sq k

/-- The canonical finite progression supply implies the more explicit finite
parameter package by taking `P` to be the canonical medium-prime window. -/
theorem progressionWindowParameterSupplyAt_of_canonicalProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : canonicalProgressionWindowParameterSupplyAt lam) :
    progressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, Y, J, N, hkpos, hYsq, hY7, hJ, hcard, hpost⟩
  refine ⟨mediumPrimeWindow k (Y + 1) (2 * k + 1), k, Y, J, N, hkpos, ?_, ?_, hJ, ?_, ?_, hcard, hpost⟩
  · intro p hp
    exact baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff hp
  · intro p hp
    exact eight_le_of_mem_mediumPrimeWindow hp
  · intro p hp
    exact two_mul_lt_sq_of_mem_mediumPrimeWindow hp
  · intro p hpPrime hYp hnotLarge
    exact mem_canonical_mediumPrimeWindow_of_prime_gt_cutoff_not_large
      hYsq hY7 hpPrime hYp hnotLarge

/-- The finite progression-parameter supply closes the paper's central
log-window supply predicate. -/
theorem centralLogWindowPairsAt_of_progressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : progressionWindowParameterSupplyAt lam) :
    centralLogWindowPairsAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨P, k, Y, J, N, hkpos, hcop, hp, hJ, hbig, hcover, hcard, hpost⟩
  rcases exists_progression_centralFactorialDivides_of_prime_partition_sum
      P hcop hp hJ hbig hcover hcard with
    ⟨A, t, htRange, hAeq, hR, hdiv⟩
  rcases hpost A t htRange hAeq with
    ⟨hM, hApos, hkCentral, hgapLower, hgapUpper⟩
  exact ⟨A, k, hM, hApos, hkpos, hdiv, hkCentral, hgapLower, hgapUpper⟩

/-- The shifted large-`k` supply implies the shifted sqrt-canonical supply. -/
theorem shiftedSqrtProgressionWindowParameterSupplyAt_of_shiftedLargeKProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKProgressionWindowParameterSupplyAt lam) :
    shiftedSqrtProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hcard, hpost⟩
  refine ⟨k, J, T, N, ?_, ?_, hJ, hcard, hpost⟩
  · omega
  · exact seven_le_sqrt_two_mul_of_25_le hk25

/-- The shifted sqrt-canonical supply implies the shifted canonical supply. -/
theorem shiftedCanonicalProgressionWindowParameterSupplyAt_of_shiftedSqrtProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedSqrtProgressionWindowParameterSupplyAt lam) :
    shiftedCanonicalProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hkpos, hY7, hJ, hcard, hpost⟩
  refine ⟨k, Nat.sqrt (2 * k), J, T, N, hkpos, ?_, hY7, hJ, hcard, hpost⟩
  exact two_mul_lt_succ_sqrt_two_mul_sq k

/-- The shifted canonical finite progression supply implies the explicit finite
prime-set shifted package. -/
theorem shiftedProgressionWindowParameterSupplyAt_of_shiftedCanonicalProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedCanonicalProgressionWindowParameterSupplyAt lam) :
    shiftedProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, Y, J, T, N, hkpos, hYsq, hY7, hJ, hcard, hpost⟩
  refine ⟨mediumPrimeWindow k (Y + 1) (2 * k + 1), k, Y, J, T, N, hkpos, ?_, ?_, hJ, ?_, ?_, hcard, hpost⟩
  · intro p hp
    exact baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff hp
  · intro p hp
    exact eight_le_of_mem_mediumPrimeWindow hp
  · intro p hp
    exact two_mul_lt_sq_of_mem_mediumPrimeWindow hp
  · intro p hpPrime hYp hnotLarge
    exact mem_canonical_mediumPrimeWindow_of_prime_gt_cutoff_not_large
      hYsq hY7 hpPrime hYp hnotLarge

/-- The shifted finite progression-parameter supply closes the same central
log-window predicate, but allows the asymptotic layer to start the searched
window after an arbitrary progression shift. -/
theorem centralLogWindowPairsAt_of_shiftedProgressionWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedProgressionWindowParameterSupplyAt lam) :
    centralLogWindowPairsAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨P, k, Y, J, T, N, hkpos, hcop, hp, hJ, hbig, hcover, hcard, hpost⟩
  rcases exists_shifted_progression_centralFactorialDivides_of_prime_partition_sum
      P hcop hp hJ hbig hcover hcard with
    ⟨A, y, hyRange, hAeq, hR, hdiv⟩
  rcases hpost A y hyRange hAeq with
    ⟨hM, hApos, hkCentral, hgapLower, hgapUpper⟩
  exact ⟨A, k, hM, hApos, hkpos, hdiv, hkCentral, hgapLower, hgapUpper⟩

/-- Endpoint-window parameters imply the shifted large-`k` supply.  The proof
is only monotonicity: all searched values lie between the shifted base and top
endpoints. -/
theorem shiftedLargeKProgressionWindowParameterSupplyAt_of_shiftedLargeKEndpointWindowParameterSupplyAt
    {lam : ℝ} (hlam : 0 < lam)
    (hsupply : shiftedLargeKEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKProgressionWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hcard, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, hcard, ?_⟩
  intro A y hyRange hAeq
  let Y := Nat.sqrt (2 * k)
  let R := baseRestrictedPrimePowerModulus k Y
  let ABase := shiftedProgressionBase k Y T
  let ATop := shiftedProgressionTop k Y T N
  have hylt : y < N := by simpa using hyRange
  have hy_le : y ≤ N := Nat.le_of_lt hylt
  have hRy_le_RN : R * y ≤ R * N := Nat.mul_le_mul_left R hy_le
  have hbase_le_A : ABase ≤ A := by
    rw [hAeq]
    simp [ABase, shiftedProgressionBase, Y]
  have hA_le_top : A ≤ ATop := by
    rw [hAeq]
    simp [ATop, shiftedProgressionTop, shiftedProgressionBase, Y]
    exact hRy_le_RN
  have hM : M ≤ 2 * A := by
    have htwo : 2 * shiftedProgressionBase k (Nat.sqrt (2 * k)) T ≤ 2 * A :=
      Nat.mul_le_mul_left 2 (by simpa [ABase, Y] using hbase_le_A)
    exact le_trans hMbase htwo
  have hApos : 0 < A := lt_of_lt_of_le (by simpa [ABase, Y] using hbasePos) hbase_le_A
  have hkpos : 0 < k := by omega
  have hkCentral : (k : ℝ) ≤ ρ * (A : ℝ) := by
    have hcast : (ABase : ℝ) ≤ (A : ℝ) := by exact_mod_cast hbase_le_A
    have hρnonneg : 0 ≤ ρ := le_of_lt hρ
    calc
      (k : ℝ) ≤ ρ * (ABase : ℝ) := by simpa [ABase, Y] using hcentralBase
      _ ≤ ρ * (A : ℝ) := mul_le_mul_of_nonneg_left hcast hρnonneg
  have htwoApos : 0 < ((2 * A : Nat) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * A)
  have hlogA_nonneg : 0 ≤ Real.log ((2 * A : Nat) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * A)
  have hgapLower : (lam - δ) * Real.log ((2 * A : Nat) : ℝ) < (k : ℝ) := by
    by_cases hcoeff : 0 ≤ lam - δ
    · have htwo_le : ((2 * A : Nat) : ℝ) ≤ ((2 * ATop : Nat) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hA_le_top
      have hlog_le : Real.log ((2 * A : Nat) : ℝ) ≤ Real.log ((2 * ATop : Nat) : ℝ) :=
        Real.log_le_log htwoApos htwo_le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlog_le hcoeff)
        (by simpa [ATop, Y] using hlowerTop hcoeff)
    · have hcoeff_nonpos : lam - δ ≤ 0 := by linarith
      have hprod_nonpos : (lam - δ) * Real.log ((2 * A : Nat) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hlogA_nonneg
      have hkposReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      exact lt_of_le_of_lt hprod_nonpos hkposReal
  have hgapUpper : (k : ℝ) < (lam + δ) * Real.log ((2 * A : Nat) : ℝ) := by
    have hcoeff_nonneg : 0 ≤ lam + δ := by linarith
    have hbase_two_pos : 0 < ((2 * ABase : Nat) : ℝ) := by
      exact_mod_cast (by
        have hbp : 0 < ABase := by simpa [ABase, Y] using hbasePos
        omega : 0 < 2 * ABase)
    have htwo_le : ((2 * ABase : Nat) : ℝ) ≤ ((2 * A : Nat) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hbase_le_A
    have hlog_le : Real.log ((2 * ABase : Nat) : ℝ) ≤ Real.log ((2 * A : Nat) : ℝ) :=
      Real.log_le_log hbase_two_pos htwo_le
    exact lt_of_lt_of_le (by simpa [ABase, Y] using hupperBase)
      (mul_le_mul_of_nonneg_left hlog_le hcoeff_nonneg)
  exact ⟨hM, hApos, hkCentral, hgapLower, hgapUpper⟩

/-- Exponential endpoint placement implies logarithmic endpoint placement. -/
theorem shiftedLargeKGeometricEndpointWindowParameterSupplyAt_of_shiftedLargeKExponentialEndpointWindowParameterSupplyAt
    {lam : ℝ} (hlam : 0 < lam)
    (hsupply : shiftedLargeKExponentialEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKGeometricEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hNpos, hgeom, htail, hMbase, hbasePos,
      hcentralBase, hupperExp, hlowerExp⟩
  refine ⟨k, J, T, N, hk25, hJ, hNpos, hgeom, htail, hMbase, hbasePos,
    hcentralBase, ?_, ?_⟩
  · intro hcoeff
    by_cases hzero : lam - δ = 0
    · have hkposReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      simpa [hzero] using hkposReal
    · have hcoeff_pos : 0 < lam - δ := lt_of_le_of_ne hcoeff (Ne.symm hzero)
      have htopPos : 0 < shiftedProgressionTop k (Nat.sqrt (2 * k)) T N := by
        unfold shiftedProgressionTop
        omega
      exact lower_log_window_of_lt_exp hcoeff_pos htopPos (hlowerExp hcoeff_pos)
  · have hsum_pos : 0 < lam + δ := by linarith
    exact upper_log_window_of_exp_lt hsum_pos hupperExp

/-- A sufficiently wide real interval inside the exponential window supplies a
shifted arithmetic progression window inside the same exponential endpoints. -/
theorem shiftedLargeKExponentialEndpointWindowParameterSupplyAt_of_shiftedLargeKIntervalEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKIntervalEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKExponentialEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, N, L, U, hk25, hJ, hNpos, hgeom, htail, hkL, hML, hcentralL,
      hlowerL, hwidth, hupperU⟩
  rcases exists_shiftedProgression_window_in_interval
      (k := k) (Y := Nat.sqrt (2 * k)) (N := N) hkL hwidth with
    ⟨T, hLbase, htopU⟩
  let ABase := shiftedProgressionBase k (Nat.sqrt (2 * k)) T
  let ATop := shiftedProgressionTop k (Nat.sqrt (2 * k)) T N
  have hbase_cast : L < (ABase : ℝ) := by simpa [ABase] using hLbase
  have htop_cast : (ATop : ℝ) < U := by simpa [ATop] using htopU
  have hMbase : M ≤ 2 * ABase := by
    have hMlt : (M : ℝ) < (2 * ABase : Nat) := by
      have htwoLbase : 2 * L < 2 * (ABase : ℝ) := by nlinarith
      have hcast : ((2 * ABase : Nat) : ℝ) = 2 * (ABase : ℝ) := by norm_num
      rw [hcast]
      exact lt_of_le_of_lt hML htwoLbase
    exact le_of_lt (by exact_mod_cast hMlt)
  have hbasePos : 0 < ABase := by
    have hkpos : 0 < k := by omega
    unfold ABase shiftedProgressionBase
    omega
  have hcentralBase : (k : ℝ) ≤ ρ * (ABase : ℝ) := by
    have hρnonneg : 0 ≤ ρ := le_of_lt hρ
    have hρL_le : ρ * L ≤ ρ * (ABase : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hbase_cast) hρnonneg
    exact le_trans hcentralL hρL_le
  have hlowerBase :
      Real.exp ((k : ℝ) / (lam + δ)) <
        ((2 * ABase : Nat) : ℝ) := by
    have htwo : 2 * L < 2 * (ABase : ℝ) := by nlinarith
    have hcast : ((2 * ABase : Nat) : ℝ) = 2 * (ABase : ℝ) := by norm_num
    rw [hcast]
    exact lt_trans hlowerL htwo
  have hupperTop :
      0 < lam - δ →
        ((2 * ATop : Nat) : ℝ) < Real.exp ((k : ℝ) / (lam - δ)) := by
    intro hcoeff
    have htwoTopU : 2 * (ATop : ℝ) < 2 * U := by nlinarith
    have hcast : ((2 * ATop : Nat) : ℝ) = 2 * (ATop : ℝ) := by norm_num
    rw [hcast]
    exact lt_trans htwoTopU (hupperU hcoeff)
  exact ⟨k, J, T, N, hk25, hJ, hNpos, hgeom, htail, hMbase, hbasePos,
    hcentralBase, hlowerBase, hupperTop⟩

/-- The geometric split endpoint target implies the raw real-valued split
endpoint target. -/
theorem shiftedLargeKRealSplitEndpointWindowParameterSupplyAt_of_shiftedLargeKGeometricEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKGeometricEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKRealSplitEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hNpos, hquotGeom, htailCrude, hMbase, hbasePos,
      hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, ?_, hMbase, hbasePos,
    hcentralBase, hlowerTop, hupperBase⟩
  · exact two_mul_canonicalMediumBadResidueQuotientSum_cast_lt_of_geometric
      (k := k) (J := J) (N := N) hJ hNpos hquotGeom
  · exact two_mul_canonicalMediumBadResidueTailSum_cast_lt_of_crude
      (k := k) (J := J) (N := N) htailCrude

/-- The real-valued split endpoint-window target implies the natural-number
split endpoint target. -/
theorem shiftedLargeKSplitEndpointWindowParameterSupplyAt_of_shiftedLargeKRealSplitEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKRealSplitEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKSplitEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hquotReal, htailReal, hMbase, hbasePos,
      hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, ?_, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  · exact_mod_cast hquotReal
  · exact_mod_cast htailReal

/-- The split endpoint-window target implies the endpoint-window target by
recombining the quotient and tail parts of the bad-residue sum. -/
theorem shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKSplitEndpointWindowParameterSupplyAt
    {lam : ℝ}
    (hsupply : shiftedLargeKSplitEndpointWindowParameterSupplyAt lam) :
    shiftedLargeKEndpointWindowParameterSupplyAt lam := by
  intro δ ρ hδ hρ M
  rcases hsupply δ ρ hδ hρ M with
    ⟨k, J, T, N, hk25, hJ, hquot, htail, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  refine ⟨k, J, T, N, hk25, hJ, ?_, hMbase, hbasePos, hcentralBase, hlowerTop, hupperBase⟩
  have hsplit :
      canonicalMediumBadResidueQuotientSum k J N + canonicalMediumBadResidueTailSum k J < N := by
    omega
  have hraw_eq :
      (∑ p ∈ mediumPrimeWindow k (Nat.sqrt (2 * k) + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2)) * (N / (p ^ J) + 1)) =
        canonicalMediumBadResidueQuotientSum k J N +
          canonicalMediumBadResidueTailSum k J := by
    simpa [badResidueWeight] using
      (canonicalMediumBadResidueSum_eq_quotient_add_tail (k := k) (J := J) (N := N))
  simpa [hraw_eq] using hsplit

/-- Conditional final theorem in finite-parameter form: the remaining
asymptotic task is to prove the progression-parameter supply for every positive
target ratio. -/
theorem erdos728Main_of_progressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → progressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_centralLogWindowPairsAt
  intro lam hlampos
  exact centralLogWindowPairsAt_of_progressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem in canonical finite-parameter form.  This is now
the narrow remaining target for the paper's exponential-window estimates. -/
theorem erdos728Main_of_canonicalProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → canonicalProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_progressionWindowParameterSupplyAt
  intro lam hlampos
  exact progressionWindowParameterSupplyAt_of_canonicalProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem in sqrt-canonical finite-parameter form. -/
theorem erdos728Main_of_sqrtProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → sqrtProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_canonicalProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact canonicalProgressionWindowParameterSupplyAt_of_sqrtProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem in large-`k` finite-parameter form. -/
theorem erdos728Main_of_largeKProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → largeKProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_sqrtProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact sqrtProgressionWindowParameterSupplyAt_of_largeKProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the shifted finite-parameter route. -/
theorem erdos728Main_of_shiftedProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_centralLogWindowPairsAt
  intro lam hlampos
  exact centralLogWindowPairsAt_of_shiftedProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the shifted canonical finite-parameter route. -/
theorem erdos728Main_of_shiftedCanonicalProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedCanonicalProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedProgressionWindowParameterSupplyAt_of_shiftedCanonicalProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the shifted sqrt-canonical finite-parameter route. -/
theorem erdos728Main_of_shiftedSqrtProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedSqrtProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedCanonicalProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedCanonicalProgressionWindowParameterSupplyAt_of_shiftedSqrtProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the shifted large-`k` finite-parameter route. -/
theorem erdos728Main_of_shiftedLargeKProgressionWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKProgressionWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedSqrtProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedSqrtProgressionWindowParameterSupplyAt_of_shiftedLargeKProgressionWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKProgressionWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKProgressionWindowParameterSupplyAt_of_shiftedLargeKEndpointWindowParameterSupplyAt
    hlampos (hsupply lam hlampos)

/-- Conditional final theorem through the split endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKSplitEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKSplitEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKEndpointWindowParameterSupplyAt_of_shiftedLargeKSplitEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the real-valued split endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKRealSplitEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKRealSplitEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKSplitEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKSplitEndpointWindowParameterSupplyAt_of_shiftedLargeKRealSplitEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the geometric endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKGeometricEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKGeometricEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKRealSplitEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKRealSplitEndpointWindowParameterSupplyAt_of_shiftedLargeKGeometricEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the exponential endpoint-window shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKExponentialEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKExponentialEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKGeometricEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKGeometricEndpointWindowParameterSupplyAt_of_shiftedLargeKExponentialEndpointWindowParameterSupplyAt
    hlampos (hsupply lam hlampos)

/-- Conditional final theorem through the interval-width endpoint shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKIntervalEndpointWindowParameterSupplyAt
    (hsupply : ∀ lam : ℝ, 0 < lam → shiftedLargeKIntervalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKExponentialEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKExponentialEndpointWindowParameterSupplyAt_of_shiftedLargeKIntervalEndpointWindowParameterSupplyAt
    (hsupply lam hlampos)

/-- Conditional final theorem through the subcritical interval-width endpoint
shifted large-`k` route.  This is the current narrowest theorem-shaped target:
only the case `0 < δ < lam` remains. -/
theorem erdos728Main_of_shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam → shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKIntervalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKIntervalEndpointWindowParameterSupplyAt_of_subcritical
    (hsupply lam hlampos)

/-- Conditional final theorem through the explicit subcritical interval-width
endpoint shifted large-`k` route. -/
theorem erdos728Main_of_shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKSubcriticalIntervalEndpointWindowParameterSupplyAt_of_explicit
    (hsupply lam hlampos)

/-- Conditional final theorem through the analytic subcritical endpoint route.
This is now the narrowest theorem-shaped remaining target: choose `k`, `J`,
`N`, and exponents `B`, `C` so the combined cost `exp (B+C)` fits in the
subcritical exponential gap. -/
theorem erdos728Main_of_shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKExplicitSubcriticalIntervalEndpointWindowParameterSupplyAt_of_analytic
    (hsupply lam hlampos)

/-- Conditional final theorem through the bounded-tail analytic subcritical
endpoint route.  This removes the progression-length witness from the remaining
asymptotic target. -/
theorem erdos728Main_of_shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKAnalyticSubcriticalEndpointWindowParameterSupplyAt_of_boundedTail
    (hsupply lam hlampos)

/-- Conditional final theorem through the split-width bounded-tail endpoint
route. -/
theorem erdos728Main_of_shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKBoundedTailSubcriticalEndpointWindowParameterSupplyAt_of_splitWidth
    (hsupply lam hlampos)

/-- Conditional final theorem through the growth-form split-width endpoint
route. -/
theorem erdos728Main_of_shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKSplitWidthSubcriticalEndpointWindowParameterSupplyAt_of_growth
    (hsupply lam hlampos)

/-- Conditional final theorem through the linearized growth-form endpoint
route. -/
theorem erdos728Main_of_shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKGrowthSplitWidthSubcriticalEndpointWindowParameterSupplyAt_of_linear
    (hsupply lam hlampos)

/-- Conditional final theorem through the cost-linear endpoint route with
arbitrarily large `k`. -/
theorem erdos728Main_of_shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKLinearGrowthSubcriticalEndpointWindowParameterSupplyAt_of_costLinear
    (hsupply lam hlampos)

/-- Conditional final theorem through the logarithmic cost-linear endpoint
route. -/
theorem erdos728Main_of_shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKCostLinearSubcriticalEndpointWindowParameterSupplyAt_of_logCostLinear
    (hsupply lam hlampos)

/-- Conditional final theorem through the budgeted endpoint route. -/
theorem erdos728Main_of_shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKLogCostLinearSubcriticalEndpointWindowParameterSupplyAt_of_budget
    (hsupply lam hlampos)

/-- Conditional final theorem through the direct budgeted endpoint route. -/
theorem erdos728Main_of_shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKBudgetSubcriticalEndpointWindowParameterSupplyAt_of_directBudget
    (hsupply lam hlampos)

/-- Conditional final theorem through the power-tail direct budget route. -/
theorem erdos728Main_of_shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_powerTail
    (hsupply lam hlampos)

/-- Conditional final theorem through the ceiling-`J` power-tail route. -/
theorem erdos728Main_of_shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_ceil
    (hsupply lam hlampos)

/-- Conditional final theorem through the core ceiling-`J` route. -/
theorem erdos728Main_of_shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
    (hsupply :
      ∀ lam : ℝ, 0 < lam →
        shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt lam) :
    erdos728Main := by
  apply erdos728Main_of_shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_core
    (hsupply lam hlampos)

/-- Erdős #728 in the Lean-friendly unbounded form used in this file. -/
theorem erdos728Main_proved : erdos728Main := by
  apply erdos728Main_of_shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt
  intro lam hlampos
  exact shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_pos
    hlampos

end Erdos728

end CentralBinomialLean
