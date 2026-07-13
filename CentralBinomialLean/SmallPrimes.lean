import CentralBinomialLean.Kummer
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Chebyshev

/-!
# Small-prime congruence control

This file formalizes the deterministic small-prime mechanism from Section 5 of
`../erdos728.pdf`: if `A ≡ k (mod R)` and `R` contains every relevant prime
power `p^j ≤ 2k`, then lower carries are dominated by central carries at every
digit level.
-/

namespace CentralBinomialLean

namespace Erdos728

attribute [local instance] Classical.propDecidable

/-- `R` contains all powers of `p` up to `2k`. This abstracts the role of the
paper's modulus `R_k` for a fixed prime `p`. -/
def containsPrimePowersUpTo (k R p : Nat) : Prop :=
  ∀ j, p ^ j ≤ 2 * k → p ^ j ∣ R

/-- A concrete finite modulus that contains every positive integer up to `2k`.
It is stronger than the optimized product of prime powers used in the paper,
but serves the same congruence-control purpose. -/
def smallPrimePowerModulus (k : Nat) : Nat :=
  Nat.lcmUpto (2 * k)

/-- For a base at least `2`, the exponent is bounded by the corresponding
power. This finite-bound lemma lets us index all prime powers `p^j ≤ 2k` by
`j ≤ 2k`. -/
theorem exponent_le_pow_of_two_le {p j : Nat} (hp : 2 ≤ p) :
    j ≤ p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hp_pos : 0 < p := by omega
      have hpow_pos : 0 < p ^ j := Nat.pow_pos hp_pos
      have hstep : j + 1 ≤ p ^ j + p ^ j := by omega
      have hdouble : p ^ j + p ^ j ≤ p * p ^ j := by
        nlinarith
      calc
        j + 1 ≤ p ^ j + p ^ j := hstep
        _ ≤ p * p ^ j := hdouble
        _ = p ^ (j + 1) := by rw [Nat.pow_succ]; ring

/-- The paper's optimized small-prime modulus with a base cutoff `Y`: it
contains the powers `p^j ≤ 2k` only for bases `p ≤ Y`. -/
noncomputable def baseRestrictedPrimePowerModulus (k Y : Nat) : Nat :=
  ((Finset.Icc 1 Y ×ˢ Finset.range (2 * k + 1)).filter fun pj => pj.1 ^ pj.2 ≤ 2 * k).lcm
    fun pj => pj.1 ^ pj.2

/-- A compressed product controlling the base-restricted modulus: for each base
`p ≤ Y`, keep only the largest power of `p` bounded by `2k`. -/
noncomputable def baseRestrictedPrimePowerProductBound (k Y : Nat) : Nat :=
  ∏ p ∈ Finset.Icc 2 Y, p ^ Nat.log p (2 * k)

theorem baseRestrictedPrimePowerModulus_ne_zero (k Y : Nat) :
    baseRestrictedPrimePowerModulus k Y ≠ 0 := by
  unfold baseRestrictedPrimePowerModulus
  rw [Finset.lcm_ne_zero_iff]
  intro pj hpj
  rcases pj with ⟨p, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hpj
  exact pow_ne_zero j (by omega : p ≠ 0)

theorem baseRestrictedPrimePowerModulus_pos (k Y : Nat) :
    0 < baseRestrictedPrimePowerModulus k Y :=
  Nat.pos_of_ne_zero (baseRestrictedPrimePowerModulus_ne_zero k Y)

theorem baseRestrictedPrimePowerModulus_dvd_productBound (k Y : Nat) :
    baseRestrictedPrimePowerModulus k Y ∣
      baseRestrictedPrimePowerProductBound k Y := by
  unfold baseRestrictedPrimePowerModulus baseRestrictedPrimePowerProductBound
  apply Finset.lcm_dvd
  intro pj hpj
  rcases pj with ⟨p, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hpj
  rcases hpj with ⟨⟨⟨hp1, hpY⟩, _hj⟩, hpowle⟩
  by_cases hpone : p = 1
  · simp [hpone]
  · have hpgt : 1 < p := by omega
    have hjle : j ≤ Nat.log p (2 * k) :=
      Nat.le_log_of_pow_le hpgt hpowle
    have hpow_dvd : p ^ j ∣ p ^ Nat.log p (2 * k) :=
      Nat.pow_dvd_pow p hjle
    have hmem : p ∈ Finset.Icc 2 Y := by
      simp only [Finset.mem_Icc]
      exact ⟨by omega, hpY⟩
    exact hpow_dvd.trans (Finset.dvd_prod_of_mem _ hmem)

theorem baseRestrictedPrimePowerProductBound_le_pow {k Y : Nat} (hk : 0 < k) :
    baseRestrictedPrimePowerProductBound k Y ≤ (2 * k) ^ Y := by
  unfold baseRestrictedPrimePowerProductBound
  calc
    (∏ p ∈ Finset.Icc 2 Y, p ^ Nat.log p (2 * k))
        ≤ ∏ _p ∈ Finset.Icc 2 Y, 2 * k := by
          apply Finset.prod_le_prod
          · intro p hp
            exact Nat.zero_le _
          · intro p hp
            exact Nat.pow_log_le_self p (by omega : 2 * k ≠ 0)
    _ = (2 * k) ^ (Finset.Icc 2 Y).card := by
          rw [Finset.prod_const]
    _ ≤ (2 * k) ^ Y := by
          exact Nat.pow_le_pow_right (by omega : 1 ≤ 2 * k)
            (by
              have hcard : (Finset.Icc 2 Y).card ≤ Y := by
                rw [Nat.card_Icc]
                omega
              exact hcard)

theorem baseRestrictedPrimePowerModulus_le_pow {k Y : Nat} (hk : 0 < k) :
    baseRestrictedPrimePowerModulus k Y ≤ (2 * k) ^ Y := by
  have hbound := baseRestrictedPrimePowerModulus_dvd_productBound k Y
  exact (Nat.le_of_dvd
    (by
      have hprodpos : 0 < baseRestrictedPrimePowerProductBound k Y := by
        unfold baseRestrictedPrimePowerProductBound
        exact Finset.prod_pos fun p hp => Nat.pow_pos (by
          simp only [Finset.mem_Icc] at hp
          omega : 0 < p)
      exact hprodpos)
    hbound).trans (baseRestrictedPrimePowerProductBound_le_pow hk)

theorem log_baseRestrictedPrimePowerModulus_le {k Y : Nat} (hk : 0 < k) :
    Real.log (baseRestrictedPrimePowerModulus k Y : ℝ) ≤
      (Y : ℝ) * Real.log ((2 * k : Nat) : ℝ) := by
  have hleNat := baseRestrictedPrimePowerModulus_le_pow (k := k) (Y := Y) hk
  have hleReal :
      (baseRestrictedPrimePowerModulus k Y : ℝ) ≤ (((2 * k) ^ Y : Nat) : ℝ) := by
    exact_mod_cast hleNat
  have hpos : 0 < (baseRestrictedPrimePowerModulus k Y : ℝ) := by
    exact_mod_cast baseRestrictedPrimePowerModulus_pos k Y
  calc
    Real.log (baseRestrictedPrimePowerModulus k Y : ℝ)
        ≤ Real.log ((((2 * k) ^ Y : Nat) : ℝ)) :=
          Real.log_le_log hpos hleReal
    _ = Real.log ((((2 * k : Nat) : ℝ) ^ Y)) := by norm_num
    _ = (Y : ℝ) * Real.log ((2 * k : Nat) : ℝ) := by
          rw [Real.log_pow]

/-- Exponentiated form of the base-restricted modulus bound. -/
theorem baseRestrictedPrimePowerModulus_cast_le_exp
    {k Y : Nat} {B : ℝ} (hk : 0 < k)
    (hB : (Y : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B) :
    (baseRestrictedPrimePowerModulus k Y : ℝ) ≤ Real.exp B := by
  exact Real.le_exp_of_log_le ((log_baseRestrictedPrimePowerModulus_le
    (k := k) (Y := Y) hk).trans hB)

/-- Exponentiated form specialized to the paper's square-root cutoff. -/
theorem baseRestrictedPrimePowerModulus_sqrt_cast_le_exp
    {k : Nat} {B : ℝ} (hk : 0 < k)
    (hB : (Nat.sqrt (2 * k) : ℝ) * Real.log ((2 * k : Nat) : ℝ) ≤ B) :
    (baseRestrictedPrimePowerModulus k (Nat.sqrt (2 * k)) : ℝ) ≤ Real.exp B :=
  baseRestrictedPrimePowerModulus_cast_le_exp (k := k) (Y := Nat.sqrt (2 * k)) hk hB

theorem baseRestrictedPrimePowerModulus_containsPrimePowersUpTo
    {k Y p : Nat} (hp : 0 < p) (hpY : p ≤ Y) :
    containsPrimePowersUpTo k (baseRestrictedPrimePowerModulus k Y) p := by
  intro j hle
  by_cases hpone : p = 1
  · rw [hpone, one_pow]
    exact one_dvd _
  · have hp2 : 2 ≤ p := by omega
    have hjle : j ≤ 2 * k :=
      (exponent_le_pow_of_two_le (p := p) (j := j) hp2).trans hle
    unfold baseRestrictedPrimePowerModulus
    exact Finset.dvd_lcm
      (s := (Finset.Icc 1 Y ×ˢ Finset.range (2 * k + 1)).filter
        fun pj => pj.1 ^ pj.2 ≤ 2 * k)
      (f := fun pj : Nat × Nat => pj.1 ^ pj.2)
      (b := (p, j))
      (by
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
        exact ⟨⟨⟨by omega, hpY⟩, Nat.lt_succ_of_le hjle⟩, hle⟩)

/-- If a prime divides none of the entries in a finite lcm, it does not divide
the lcm. -/
theorem prime_not_dvd_finset_lcm {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → Nat} {p : Nat}
    (hp : p.Prime) (h : ∀ a ∈ s, ¬ p ∣ f a) :
    ¬ p ∣ s.lcm f := by
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | insert a s ha ih =>
      rw [Finset.lcm_insert]
      exact Nat.Prime.not_dvd_lcm hp
        (h a (by simp [ha]))
        (ih (by
          intro b hb
          exact h b (by simp [hb])))

/-- A prime above the base cutoff is coprime to the base-restricted modulus,
and hence to every power of itself. -/
theorem baseRestrictedPrimePowerModulus_coprime_prime_pow_of_lt
    {k Y p J : Nat} (hp : p.Prime) (hYp : Y < p) :
    Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J) := by
  apply hp.coprime_pow_of_not_dvd
  unfold baseRestrictedPrimePowerModulus
  exact prime_not_dvd_finset_lcm
    (s := (Finset.Icc 1 Y ×ˢ Finset.range (2 * k + 1)).filter
      fun pj => pj.1 ^ pj.2 ≤ 2 * k)
    (f := fun pj : Nat × Nat => pj.1 ^ pj.2) hp (by
      intro pj hpj hdiv
      rcases pj with ⟨q, j⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hpj
      have hp_dvd_q : p ∣ q := hp.dvd_of_dvd_pow hdiv
      have hqpos : 0 < q := by omega
      have hpleq : p ≤ q := Nat.le_of_dvd hqpos hp_dvd_q
      omega)

theorem smallPrimePowerModulus_containsPrimePowersUpTo
    {k p : Nat} (hp : 0 < p) :
    containsPrimePowersUpTo k (smallPrimePowerModulus k) p := by
  intro j hle
  unfold smallPrimePowerModulus
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (by
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_le_of_lt (Nat.pow_pos hp : 0 < p ^ j), hle⟩)

/-- Congruence modulo `R` descends to any divisor `q` of `R`, expressed as
equality of remainders. -/
theorem mod_eq_of_mod_eq_of_dvd
    {A k R q : Nat} (hR : A % R = k % R) (hq : q ∣ R) :
    A % q = k % q := by
  have hmodR : A ≡ k [MOD R] := by
    calc
      A ≡ A % R [MOD R] := (Nat.mod_modEq A R).symm
      _ = k % R := hR
      _ ≡ k [MOD R] := Nat.mod_modEq k R
  exact Nat.ModEq.of_dvd hq hmodR

/-- Central carry indicators are invariant under equality of residues. -/
theorem centralCarry_eq_of_modEq
    {A k q : Nat} (hA : A % q = k % q) :
    centralCarry A q ↔ centralCarry k q := by
  unfold centralCarry
  rw [hA]

/-- Under `A ≡ k (mod q)`, the lower carry at modulus `q` is exactly the
central carry for `A` at modulus `q`. -/
theorem lowerCarry_eq_centralCarry_self_of_modEq
    {A k q : Nat} (hA : A % q = k % q) :
    lowerCarry A k q ↔ centralCarry A q := by
  exact (lowerCarry_eq_centralCarry_of_modEq hA).trans
    (centralCarry_eq_of_modEq hA).symm

/-- The Section 5 small-prime dichotomy at one digit level: either `p^j ≤ 2k`
and the exact congruence makes the carry indicators equal, or `p^j > 2k` and
Lemma 5 gives domination. -/
theorem carry_domination_of_congruence_contains_or_large
    {A k R p j : Nat}
    (hR : A % R = k % R)
    (hcontains : containsPrimePowersUpTo k R p) :
    lowerCarry A k (p ^ j) → centralCarry A (p ^ j) := by
  by_cases hsmall : p ^ j ≤ 2 * k
  · have hdiv : p ^ j ∣ R := hcontains j hsmall
    have hmod : A % (p ^ j) = k % (p ^ j) :=
      mod_eq_of_mod_eq_of_dvd hR hdiv
    exact (lowerCarry_eq_centralCarry_self_of_modEq hmod).mp
  · have hlarge : 2 * k < p ^ j := by omega
    exact lowerCarry_le_centralCarry_of_two_mul_lt hlarge

/-- Small-prime congruence control on a finite Kummer window. -/
theorem bounded_carry_count_le_of_congruence_contains
    {A k R p b : Nat}
    (hR : A % R = k % R)
    (hcontains : containsPrimePowersUpTo k R p) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  exact bounded_carry_count_le_of_pointwise fun j _ =>
    carry_domination_of_congruence_contains_or_large hR hcontains

/-- Small-prime carry-count domination using the concrete `lcmUpto (2k)`
modulus. -/
theorem bounded_carry_count_le_of_congruence_smallPrimePowerModulus
    {A k p b : Nat} (hp : 0 < p)
    (hR : A % smallPrimePowerModulus k = k % smallPrimePowerModulus k) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  exact bounded_carry_count_le_of_congruence_contains hR
    (smallPrimePowerModulus_containsPrimePowersUpTo (k := k) (p := p) hp)

/-- Small-prime carry-count domination using the paper's base-restricted
modulus. This is the optimized congruence-control mechanism for bases
`p ≤ Y`. -/
theorem bounded_carry_count_le_of_congruence_baseRestrictedPrimePowerModulus
    {A k Y p b : Nat} (hp : 0 < p) (hpY : p ≤ Y)
    (hR :
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  exact bounded_carry_count_le_of_congruence_contains hR
    (baseRestrictedPrimePowerModulus_containsPrimePowersUpTo
      (k := k) (Y := Y) (p := p) hp hpY)

end Erdos728

end CentralBinomialLean
