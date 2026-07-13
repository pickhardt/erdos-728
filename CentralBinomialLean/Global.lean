import CentralBinomialLean.LargePrimes
import CentralBinomialLean.Reduction
import CentralBinomialLean.SmallPrimes
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.PrimeCounting

/-!
# Global central-specialization theorems

This file packages the local carry machinery into end-to-end divisibility
statements for the central specialization used throughout the project.
-/

namespace CentralBinomialLean

namespace Erdos728

attribute [local instance] Classical.propDecidable

/-- Primes in the half-open interval `[lo, hi)`. -/
noncomputable def primeWindow (lo hi : Nat) : Finset Nat :=
  (Finset.Ico lo hi).filter Nat.Prime

theorem mem_primeWindow {lo hi p : Nat} :
    p ∈ primeWindow lo hi ↔ lo ≤ p ∧ p < hi ∧ p.Prime := by
  unfold primeWindow
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem prime_of_mem_primeWindow {lo hi p : Nat}
    (hp : p ∈ primeWindow lo hi) : p.Prime :=
  (mem_primeWindow.mp hp).2.2

theorem lower_le_of_mem_primeWindow {lo hi p : Nat}
    (hp : p ∈ primeWindow lo hi) : lo ≤ p :=
  (mem_primeWindow.mp hp).1

theorem lt_upper_of_mem_primeWindow {lo hi p : Nat}
    (hp : p ∈ primeWindow lo hi) : p < hi :=
  (mem_primeWindow.mp hp).2.1

/-- Primes at most the base cutoff `Y`. -/
noncomputable def smallPrimeWindow (Y : Nat) : Finset Nat :=
  primeWindow 1 (Y + 1)

theorem mem_smallPrimeWindow {Y p : Nat} :
    p ∈ smallPrimeWindow Y ↔ 1 ≤ p ∧ p ≤ Y ∧ p.Prime := by
  unfold smallPrimeWindow
  rw [mem_primeWindow]
  constructor
  · intro h
    exact ⟨h.1, by omega, h.2.2⟩
  · intro h
    exact ⟨h.1, by omega, h.2.2⟩

theorem prime_of_mem_smallPrimeWindow {Y p : Nat}
    (hp : p ∈ smallPrimeWindow Y) : p.Prime :=
  (mem_smallPrimeWindow.mp hp).2.2

theorem le_cutoff_of_mem_smallPrimeWindow {Y p : Nat}
    (hp : p ∈ smallPrimeWindow Y) : p ≤ Y :=
  (mem_smallPrimeWindow.mp hp).2.1

theorem pos_of_mem_smallPrimeWindow {Y p : Nat}
    (hp : p ∈ smallPrimeWindow Y) : 0 < p := by
  have hp1 : 1 ≤ p := (mem_smallPrimeWindow.mp hp).1
  omega

/-- Carry-count domination for primes in the small-prime window, using the
paper's base-restricted modulus. -/
theorem bounded_carry_count_le_of_congruence_smallPrimeWindow
    {A k Y p b : Nat}
    (hpWin : p ∈ smallPrimeWindow Y)
    (hR :
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_of_congruence_baseRestrictedPrimePowerModulus
    (A := A) (k := k) (Y := Y) (p := p) (b := b)
    (pos_of_mem_smallPrimeWindow hpWin)
    (le_cutoff_of_mem_smallPrimeWindow hpWin)
    hR

/-- For primes above `2k`, every digit level is above `2k`, so Lemma 5 gives
carry-count domination without any congruence or compensation. -/
theorem bounded_carry_count_le_of_two_mul_lt_base
    {A k p b : Nat} (hp : 2 * k < p) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  apply bounded_carry_count_le_of_pointwise
  intro j hj hlow
  have hp_pos : 0 < p := by omega
  have hj1 : 1 ≤ j := by
    simp only [Finset.mem_Ico] at hj
    exact hj.1
  have hp_le_pow : p ≤ p ^ j := by
    have hpow : p ^ 1 ≤ p ^ j := Nat.pow_le_pow_right hp_pos hj1
    simpa using hpow
  exact lowerCarry_le_centralCarry_of_two_mul_lt
    (lt_of_lt_of_le hp hp_le_pow) hlow

/-- Medium primes in a finite interval, carrying the hypotheses needed by the
integer `3/4` bad-residue estimate. -/
noncomputable def mediumPrimeWindow (k lo hi : Nat) : Finset Nat :=
  (primeWindow lo hi).filter fun p => 8 ≤ p ∧ 2 * k < p * p

theorem mem_mediumPrimeWindow {k lo hi p : Nat} :
    p ∈ mediumPrimeWindow k lo hi ↔
      lo ≤ p ∧ p < hi ∧ p.Prime ∧ 8 ≤ p ∧ 2 * k < p * p := by
  unfold mediumPrimeWindow
  simp only [Finset.mem_filter, mem_primeWindow]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩

theorem prime_of_mem_mediumPrimeWindow {k lo hi p : Nat}
    (hp : p ∈ mediumPrimeWindow k lo hi) : p.Prime :=
  (mem_mediumPrimeWindow.mp hp).2.2.1

theorem eight_le_of_mem_mediumPrimeWindow {k lo hi p : Nat}
    (hp : p ∈ mediumPrimeWindow k lo hi) : 8 ≤ p :=
  (mem_mediumPrimeWindow.mp hp).2.2.2.1

theorem two_mul_lt_sq_of_mem_mediumPrimeWindow {k lo hi p : Nat}
    (hp : p ∈ mediumPrimeWindow k lo hi) : 2 * k < p * p :=
  (mem_mediumPrimeWindow.mp hp).2.2.2.2

theorem lower_le_of_mem_mediumPrimeWindow {k lo hi p : Nat}
    (hp : p ∈ mediumPrimeWindow k lo hi) : lo ≤ p :=
  (mem_mediumPrimeWindow.mp hp).1

theorem lt_upper_of_mem_mediumPrimeWindow {k lo hi p : Nat}
    (hp : p ∈ mediumPrimeWindow k lo hi) : p < hi :=
  (mem_mediumPrimeWindow.mp hp).2.1

/-- The canonical medium-prime window has at most the size of the ambient
initial segment ending at `2*k + 1`. -/
theorem mediumPrimeWindow_card_le_two_mul_add_one {k Y : Nat} :
    (mediumPrimeWindow k (Y + 1) (2 * k + 1)).card ≤ 2 * k + 1 := by
  calc
    (mediumPrimeWindow k (Y + 1) (2 * k + 1)).card ≤ (Finset.range (2 * k + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      have hlt : p < 2 * k + 1 := lt_upper_of_mem_mediumPrimeWindow hp
      simpa [Finset.mem_range] using hlt
    _ = 2 * k + 1 := by simp

/-- A crude deterministic upper bound for the canonical medium-window
bad-residue sum.  It replaces every prime-dependent summand by its worst-case
bound using only `p <= 2*k`. -/
theorem mediumPrimeWindow_badResidue_sum_le_crude {k Y J N : Nat} :
    (∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1))
      ≤ (mediumPrimeWindow k (Y + 1) (2 * k + 1)).card *
        (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) * (N + 1)) := by
  apply sum_le_card_mul
  intro p hp
  have hp_le : p ≤ 2 * k := by
    have hhi : p < 2 * k + 1 := lt_upper_of_mem_mediumPrimeWindow hp
    omega
  have hp_half_le : p / 2 ≤ 2 * k := le_trans (Nat.div_le_self p 2) hp_le
  have hthree_le : (3 * p) / 4 ≤ (3 * (2 * k)) / 4 := by
    exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 hp_le)
  have hpow_le : ((3 * p) / 4) ^ (J - 2) ≤ ((3 * (2 * k)) / 4) ^ (J - 2) := by
    exact Nat.pow_le_pow_left hthree_le (J - 2)
  have hdiv_le : N / (p ^ J) + 1 ≤ N + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_self N (p ^ J)) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp_half_le hp_le) hpow_le) hdiv_le

/-- A more effective deterministic upper bound for the canonical medium-window
bad-residue sum.  It uses `p <= 2*k` for the numerator and `Y + 1 <= p` for
the divisor `p^J`. -/
theorem mediumPrimeWindow_badResidue_sum_le_effective {k Y J N : Nat} :
    (∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1))
      ≤ (mediumPrimeWindow k (Y + 1) (2 * k + 1)).card *
        (((2 * k) * (2 * k) * ((3 * (2 * k)) / 4) ^ (J - 2)) *
          (N / ((Y + 1) ^ J) + 1)) := by
  apply sum_le_card_mul
  intro p hp
  have hp_le : p ≤ 2 * k := by
    have hhi : p < 2 * k + 1 := lt_upper_of_mem_mediumPrimeWindow hp
    omega
  have hp_lo : Y + 1 ≤ p := lower_le_of_mem_mediumPrimeWindow hp
  have hp_half_le : p / 2 ≤ 2 * k := le_trans (Nat.div_le_self p 2) hp_le
  have hthree_le : (3 * p) / 4 ≤ (3 * (2 * k)) / 4 := by
    exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 hp_le)
  have hpow_le : ((3 * p) / 4) ^ (J - 2) ≤ ((3 * (2 * k)) / 4) ^ (J - 2) := by
    exact Nat.pow_le_pow_left hthree_le (J - 2)
  have hden_le : (Y + 1) ^ J ≤ p ^ J := Nat.pow_le_pow_left hp_lo J
  have hlo_pos : 0 < (Y + 1) ^ J := Nat.pow_pos (by omega : 0 < Y + 1)
  have hdiv_le : N / (p ^ J) + 1 ≤ N / ((Y + 1) ^ J) + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_div_left hden_le hlo_pos) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp_half_le hp_le) hpow_le) hdiv_le

/-- Medium primes whose window starts above the small-prime cutoff are
automatically coprime to the base-restricted small-prime modulus. -/
theorem baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff
    {k Y hi p J : Nat}
    (hp : p ∈ mediumPrimeWindow k (Y + 1) hi) :
    Nat.Coprime (baseRestrictedPrimePowerModulus k Y) (p ^ J) := by
  have hpPrime : p.Prime := prime_of_mem_mediumPrimeWindow hp
  have hYp : Y < p := by
    have hlo : Y + 1 ≤ p := lower_le_of_mem_mediumPrimeWindow hp
    omega
  exact baseRestrictedPrimePowerModulus_coprime_prime_pow_of_lt hpPrime hYp

/-- The exact square-root cutoff automatically satisfies the square condition
used by the canonical medium-window cover. -/
theorem two_mul_lt_succ_sqrt_two_mul_sq (k : Nat) :
    2 * k < (Nat.sqrt (2 * k) + 1) * (Nat.sqrt (2 * k) + 1) := by
  simpa using Nat.lt_succ_sqrt (2 * k)

/-- A concrete lower bound on `k` makes the square-root cutoff at least `7`,
which is enough for the integer `3/4` bad-residue estimate. -/
theorem seven_le_sqrt_two_mul_of_25_le {k : Nat} (hk : 25 ≤ k) :
    7 ≤ Nat.sqrt (2 * k) := by
  rw [Nat.le_sqrt]
  omega

/-- Under the usual square-root cutoff assumptions, the canonical medium window
`(Y, 2k]` contains every prime above `Y` that is not already in the automatic
large-prime range `p > 2k`. -/
theorem mem_canonical_mediumPrimeWindow_of_prime_gt_cutoff_not_large
    {k Y p : Nat}
    (hYsq : 2 * k < (Y + 1) * (Y + 1))
    (hY7 : 7 ≤ Y)
    (hpPrime : p.Prime)
    (hYp : Y < p)
    (hnotLarge : ¬ 2 * k < p) :
    p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1) := by
  rw [mem_mediumPrimeWindow]
  have hlo : Y + 1 ≤ p := Nat.succ_le_of_lt hYp
  have hhi : p < 2 * k + 1 := by omega
  have hp8 : 8 ≤ p := by omega
  have hsq_le : (Y + 1) * (Y + 1) ≤ p * p := Nat.mul_le_mul hlo hlo
  have hbig : 2 * k < p * p := lt_of_lt_of_le hYsq hsq_le
  exact ⟨hlo, hhi, hpPrime, hp8, hbig⟩

/-- Medium-prime interval-count conclusion specialized to the named finite
medium-prime window. -/
theorem exists_mem_Ico_medium_carry_count_le_of_mediumPrimeWindow_sum
    {k pLo pHi ALo AHi J b : Nat}
    (hJ : 2 ≤ J)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hcard :
      ∑ p ∈ mediumPrimeWindow k pLo pHi,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * ((AHi - ALo) / (p ^ J) + 1) < AHi - ALo) :
    ∃ A ∈ Finset.Ico ALo AHi,
      ∀ p ∈ mediumPrimeWindow k pLo pHi,
        ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
          ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  exact exists_mem_Ico_medium_carry_count_le_of_three_quarters_sum
    (P := mediumPrimeWindow k pLo pHi)
    (lo := ALo) (hi := AHi) (k := k) (J := J) (b := b)
    (fun p hp => eight_le_of_mem_mediumPrimeWindow hp)
    hJ
    (fun p hp => two_mul_lt_sq_of_mem_mediumPrimeWindow hp)
    h1mem hwindow hcard

/-- Medium-prime progression-count conclusion specialized to the named finite
medium-prime window. -/
theorem exists_mem_range_progression_medium_carry_count_le_of_mediumPrimeWindow_sum
    {k pLo pHi offset scale N J b : Nat}
    (hcop : ∀ p ∈ mediumPrimeWindow k pLo pHi, Nat.Coprime scale (p ^ J))
    (hJ : 2 ≤ J)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hcard :
      ∑ p ∈ mediumPrimeWindow k pLo pHi,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ t ∈ Finset.range N,
      ∀ p ∈ mediumPrimeWindow k pLo pHi,
        ((Finset.Ico 1 b).filter fun j =>
            lowerCarry (offset + scale * t) k (p ^ j)).card
          ≤ ((Finset.Ico 1 b).filter fun j =>
            centralCarry (offset + scale * t) (p ^ j)).card := by
  exact exists_mem_range_progression_medium_carry_count_le_of_three_quarters_sum
    (P := mediumPrimeWindow k pLo pHi)
    (offset := offset) (scale := scale) (N := N) (k := k) (J := J) (b := b)
    hcop
    (fun p hp => eight_le_of_mem_mediumPrimeWindow hp)
    hJ
    (fun p hp => two_mul_lt_sq_of_mem_mediumPrimeWindow hp)
    h1mem hwindow hcard

/-- Progression medium-prime count for the paper's small-prime congruence
class.  Starting the medium window at `Y + 1` automatically supplies the
coprimality needed for the progression transfer. -/
theorem exists_mem_range_progression_medium_carry_count_le_of_baseRestricted_mediumPrimeWindow_sum
    {k Y pHi N J b : Nat}
    (hJ : 2 ≤ J)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hcard :
      ∑ p ∈ mediumPrimeWindow k (Y + 1) pHi,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ t ∈ Finset.range N,
      ∀ p ∈ mediumPrimeWindow k (Y + 1) pHi,
        ((Finset.Ico 1 b).filter fun j =>
            lowerCarry (k + baseRestrictedPrimePowerModulus k Y * t) k (p ^ j)).card
          ≤ ((Finset.Ico 1 b).filter fun j =>
            centralCarry (k + baseRestrictedPrimePowerModulus k Y * t) (p ^ j)).card := by
  exact exists_mem_range_progression_medium_carry_count_le_of_mediumPrimeWindow_sum
    (k := k) (pLo := Y + 1) (pHi := pHi)
    (offset := k) (scale := baseRestrictedPrimePowerModulus k Y)
    (N := N) (J := J) (b := b)
    (fun p hp =>
      baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff hp)
    hJ h1mem hwindow hcard

/-- Carry-count domination for all primes from an explicit small/medium/large
partition.  Small primes are controlled by the base-restricted congruence,
medium primes by semantic-bad-residue avoidance, and primes above `2k` by the
`q > 2k` domination lemma. -/
theorem bounded_carry_count_le_of_prime_partition
    {A k Y J b : Nat}
    (hR :
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y)
    (hJ : 2 ≤ J)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hpartition :
      ∀ p, p.Prime →
        p ≤ Y ∨
        (8 ≤ p ∧ 2 * k < p * p ∧
          A % (p ^ J) ∉ semanticBadResidues k p J) ∨
        2 * k < p) :
    ∀ p, p.Prime →
      ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
        ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  intro p hpPrime
  rcases hpartition p hpPrime with hsmall | hmedium | hlarge
  · have hpWin : p ∈ smallPrimeWindow Y := by
      rw [mem_smallPrimeWindow]
      exact ⟨hpPrime.one_le, hsmall, hpPrime⟩
    exact bounded_carry_count_le_of_congruence_smallPrimeWindow
      (A := A) (k := k) (Y := Y) (p := p) (b := b) hpWin hR
  · rcases hmedium with ⟨hp8, hp2, havoid⟩
    have hp2le : 2 ≤ p := by omega
    have hp2pow : 2 * k < p ^ 2 := by
      simpa [pow_two] using hp2
    exact bounded_carry_count_le_medium_of_not_mem_semanticBadResidues
      (A := A) (k := k) (p := p) (b := b) (J := J)
      hp2le hp2pow hJ h1mem hwindow havoid
  · exact bounded_carry_count_le_of_two_mul_lt_base
      (A := A) (k := k) (p := p) (b := b) hlarge

/-- Binomial divisibility from the explicit prime partition. -/
theorem lower_choose_dvd_central_choose_of_prime_partition
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
    Nat.choose (A + k) k ∣ Nat.choose (2 * A) A := by
  apply lower_choose_dvd_central_choose_of_bounded_carry_count_le
  intro p hp
  let b := max (Nat.log p (A + k)) (Nat.log p (2 * A)) + max 2 (J + 1)
  refine ⟨b, ?_, ?_, ?_⟩
  · unfold b
    omega
  · unfold b
    omega
  · have h1mem : 1 ∈ Finset.Ico 1 b := by
      simp only [Finset.mem_Ico]
      unfold b
      omega
    have hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_Ico]
      unfold b
      omega
    exact bounded_carry_count_le_of_prime_partition
      (A := A) (k := k) (Y := Y) (J := J) (b := b)
      hR hJ h1mem hwindow hpartition p hp

/-- Factorial divisibility from the explicit prime partition. -/
theorem factorial_dvd_of_prime_partition
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
    A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial :=
  factorial_dvd_of_lower_choose_dvd_central_choose
    (lower_choose_dvd_central_choose_of_prime_partition hR hJ hpartition)

/-- Progression-level global existence theorem.  If the finite medium-prime
set `P` covers every prime between the small cutoff `Y` and the automatic
large-prime range, and the summed bad-residue estimate is smaller than the
number of progression points, then some `A = k + R * t` in the small-prime
congruence class satisfies the central factorial divisibility. -/
theorem exists_progression_factorial_dvd_of_prime_partition_sum
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
      A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  let R := baseRestrictedPrimePowerModulus k Y
  rcases exists_mem_range_avoiding_semanticBadResidues_of_three_quarters_sum
      (P := P) (offset := k) (scale := R) (N := N) (k := k) (J := J)
      (by simpa [R] using hcop) hp hJ hbig hcard with
    ⟨t, htRange, havoid⟩
  let A := k + R * t
  have hR : A % R = k % R := by
    have hmod : A ≡ k [MOD R] := by
      unfold A
      unfold Nat.ModEq
      rw [Nat.add_mul_mod_self_left]
    exact hmod
  have hpartition :
      ∀ p, p.Prime →
        p ≤ Y ∨
        (8 ≤ p ∧ 2 * k < p * p ∧
          A % (p ^ J) ∉ semanticBadResidues k p J) ∨
        2 * k < p := by
    intro p hpPrime
    by_cases hpY : p ≤ Y
    · exact Or.inl hpY
    · right
      by_cases hlarge : 2 * k < p
      · exact Or.inr hlarge
      · left
        have hpYlt : Y < p := by omega
        have hpP : p ∈ P := hcover p hpPrime hpYlt hlarge
        exact ⟨hp p hpP, hbig p hpP, havoid p hpP⟩
  refine ⟨A, t, htRange, rfl, ?_, ?_⟩
  · simpa [R] using hR
  · exact factorial_dvd_of_prime_partition
      (A := A) (k := k) (Y := Y) (J := J) (by simpa [R] using hR) hJ hpartition

/-- Shifted progression-level global existence theorem.  This is the same
finite counting endpoint as `exists_progression_factorial_dvd_of_prime_partition_sum`,
but the searched progression is `A = k + R * T + R * y`, `y < N`.  The extra
shift lets the asymptotic layer search inside a later interval instead of
forcing the first progression point `A = k` to satisfy the final size and
log-window constraints. -/
theorem exists_shifted_progression_factorial_dvd_of_prime_partition_sum
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
      A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  let R := baseRestrictedPrimePowerModulus k Y
  rcases exists_mem_range_avoiding_semanticBadResidues_of_three_quarters_sum
      (P := P) (offset := k + R * T) (scale := R) (N := N) (k := k) (J := J)
      (by simpa [R] using hcop) hp hJ hbig hcard with
    ⟨y, hyRange, havoid⟩
  let A := k + R * T + R * y
  have hR : A % R = k % R := by
    have hsum : A = k + R * (T + y) := by
      unfold A
      ring
    have hmod : A ≡ k [MOD R] := by
      unfold Nat.ModEq
      rw [hsum]
      rw [Nat.add_mul_mod_self_left]
    exact hmod
  have hpartition :
      ∀ p, p.Prime →
        p ≤ Y ∨
        (8 ≤ p ∧ 2 * k < p * p ∧
          A % (p ^ J) ∉ semanticBadResidues k p J) ∨
        2 * k < p := by
    intro p hpPrime
    by_cases hpY : p ≤ Y
    · exact Or.inl hpY
    · right
      by_cases hlarge : 2 * k < p
      · exact Or.inr hlarge
      · left
        have hpYlt : Y < p := by omega
        have hpP : p ∈ P := hcover p hpPrime hpYlt hlarge
        exact ⟨hp p hpP, hbig p hpP, havoid p hpP⟩
  refine ⟨A, y, hyRange, rfl, ?_, ?_⟩
  · simpa [R] using hR
  · exact factorial_dvd_of_prime_partition
      (A := A) (k := k) (Y := Y) (J := J) (by simpa [R] using hR) hJ hpartition

/-- Canonical progression-level endpoint using the medium-prime window
`(Y, 2k]`.  The cutoff assumptions provide the prime cover, and the start at
`Y + 1` provides the coprimality needed for progression transfer. -/
theorem exists_progression_factorial_dvd_of_canonical_mediumPrimeWindow_sum
    {k Y J N : Nat}
    (hYsq : 2 * k < (Y + 1) * (Y + 1))
    (hY7 : 7 ≤ Y)
    (hJ : 2 ≤ J)
    (hcard :
      ∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ A t : Nat,
      t ∈ Finset.range N ∧
      A = k + baseRestrictedPrimePowerModulus k Y * t ∧
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y ∧
      A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  exact exists_progression_factorial_dvd_of_prime_partition_sum
    (P := mediumPrimeWindow k (Y + 1) (2 * k + 1))
    (k := k) (Y := Y) (J := J) (N := N)
    (fun p hp =>
      baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff hp)
    (fun p hp => eight_le_of_mem_mediumPrimeWindow hp)
    hJ
    (fun p hp => two_mul_lt_sq_of_mem_mediumPrimeWindow hp)
    (fun p hpPrime hYp hnotLarge =>
      mem_canonical_mediumPrimeWindow_of_prime_gt_cutoff_not_large
        hYsq hY7 hpPrime hYp hnotLarge)
    hcard

/-- Shifted canonical progression-level endpoint using the medium-prime window
`(Y, 2k]`. -/
theorem exists_shifted_progression_factorial_dvd_of_canonical_mediumPrimeWindow_sum
    {k Y J T N : Nat}
    (hYsq : 2 * k < (Y + 1) * (Y + 1))
    (hY7 : 7 ≤ Y)
    (hJ : 2 ≤ J)
    (hcard :
      ∑ p ∈ mediumPrimeWindow k (Y + 1) (2 * k + 1),
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ A y : Nat,
      y ∈ Finset.range N ∧
      A = k + baseRestrictedPrimePowerModulus k Y * T +
        baseRestrictedPrimePowerModulus k Y * y ∧
      A % baseRestrictedPrimePowerModulus k Y =
        k % baseRestrictedPrimePowerModulus k Y ∧
      A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  exact exists_shifted_progression_factorial_dvd_of_prime_partition_sum
    (P := mediumPrimeWindow k (Y + 1) (2 * k + 1))
    (k := k) (Y := Y) (J := J) (T := T) (N := N)
    (fun p hp =>
      baseRestrictedPrimePowerModulus_coprime_of_mem_mediumPrimeWindow_above_cutoff hp)
    (fun p hp => eight_le_of_mem_mediumPrimeWindow hp)
    hJ
    (fun p hp => two_mul_lt_sq_of_mem_mediumPrimeWindow hp)
    (fun p hpPrime hYp hnotLarge =>
      mem_canonical_mediumPrimeWindow_of_prime_gt_cutoff_not_large
        hYsq hY7 hpPrime hYp hnotLarge)
    hcard

/-- The concrete small-prime-power modulus is always positive. -/
theorem smallPrimePowerModulus_pos (k : Nat) :
    0 < smallPrimePowerModulus k := by
  unfold smallPrimePowerModulus
  exact Nat.lcmUpto_pos (2 * k)

/-- If `A ≡ k` modulo the concrete modulus containing all powers up to `2k`,
then the lower binomial coefficient divides the central one. -/
theorem lower_choose_dvd_central_choose_of_congruence_smallPrimePowerModulus
    {A k : Nat}
    (hR : A % smallPrimePowerModulus k = k % smallPrimePowerModulus k) :
    Nat.choose (A + k) k ∣ Nat.choose (2 * A) A := by
  apply lower_choose_dvd_central_choose_of_bounded_carry_count_le
  intro p hp
  let b := max (Nat.log p (A + k)) (Nat.log p (2 * A)) + 1
  refine ⟨b, ?_, ?_, ?_⟩
  · unfold b
    omega
  · unfold b
    omega
  · exact bounded_carry_count_le_of_congruence_smallPrimePowerModulus
      (A := A) (k := k) (p := p) (b := b) hp.pos hR

/-- If `A ≡ k` modulo the concrete modulus containing all powers up to `2k`,
then the central-specialized factorial divisibility follows. -/
theorem factorial_dvd_of_congruence_smallPrimePowerModulus
    {A k : Nat}
    (hR : A % smallPrimePowerModulus k = k % smallPrimePowerModulus k) :
    A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial :=
  factorial_dvd_of_lower_choose_dvd_central_choose
    (lower_choose_dvd_central_choose_of_congruence_smallPrimePowerModulus hR)

/-- For every lower bound `M`, there is an `A ≥ M` satisfying the concrete
small-prime-power congruence and hence the central-specialized factorial
divisibility. -/
theorem exists_ge_factorial_dvd_of_smallPrimePowerModulus
    (k M : Nat) :
    ∃ A,
      M ≤ A ∧
      A % smallPrimePowerModulus k = k % smallPrimePowerModulus k ∧
      A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  let R := smallPrimePowerModulus k
  let A := k + M * R
  have hRpos : 0 < R := by
    simpa [R] using smallPrimePowerModulus_pos k
  have hAge : M ≤ A := by
    have hRge : 1 ≤ R := hRpos
    unfold A
    nlinarith
  have hcong : A % R = k % R := by
    have hmod : A ≡ k [MOD R] := by
      unfold A
      exact (Nat.add_mul_modulus_modEq_iff (a := k) (b := M) (c := k) (n := R)).mpr
        Nat.ModEq.rfl
    exact hmod
  refine ⟨A, hAge, ?_, ?_⟩
  · simpa [R] using hcong
  · exact factorial_dvd_of_congruence_smallPrimePowerModulus
      (A := A) (k := k) (by simpa [R] using hcong)

end Erdos728

end CentralBinomialLean
