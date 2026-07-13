import CentralBinomialLean.Carry
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Kummer bridges for the deterministic Erdos #728 proof

This file rewrites Mathlib's binomial factorization/Kummer theorems into the
carry predicates used by `CentralBinomialLean.Carry`.
-/

namespace CentralBinomialLean

namespace Erdos728

open Finset

attribute [local instance] Classical.propDecidable

/-- If a carry predicate implies another predicate pointwise on a finite
window, then the corresponding filtered counts are ordered. -/
theorem card_filter_le_of_imp
    {α : Type*} [DecidableEq α] {s : Finset α}
    {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ x ∈ s, P x → Q x) :
    (s.filter P).card ≤ (s.filter Q).card := by
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h x hx.1 hx.2⟩

/-- A pointwise domination of carry indicators on a Kummer window gives
domination of the corresponding carry counts. -/
theorem bounded_carry_count_le_of_pointwise
    {A k p b : Nat}
    (h :
      ∀ j ∈ Finset.Ico 1 b,
        lowerCarry A k (p ^ j) → centralCarry A (p ^ j)) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  classical
  exact card_filter_le_of_imp h

/-- Kummer's theorem for the lower binomial coefficient, in the carry-predicate
language used by this project. -/
theorem factorization_choose_lowerCarry
    {p A k b : Nat} (hp : p.Prime) (hb : Nat.log p (A + k) < b) :
    (Nat.choose (A + k) k).factorization p =
      ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card := by
  classical
  rw [Nat.factorization_choose' hp hb]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨h.1, by
      unfold lowerCarry
      simpa [Nat.add_comm] using h.2⟩
  · intro h
    exact ⟨h.1, by
      unfold lowerCarry at h
      simpa [Nat.add_comm] using h.2⟩

/-- Kummer's theorem for the central binomial coefficient, in the
carry-predicate language used by this project. -/
theorem factorization_choose_centralCarry
    {p A b : Nat} (hp : p.Prime) (hb : Nat.log p (2 * A) < b) :
    (Nat.choose (2 * A) A).factorization p =
      ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  classical
  have hA : A ≤ 2 * A := by omega
  rw [Nat.factorization_choose hp hA hb]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨h.1, by
      unfold centralCarry
      have hsub : 2 * A - A = A := by omega
      simpa [hsub, two_mul] using h.2⟩
  · intro h
    exact ⟨h.1, by
      unfold centralCarry at h
      have hsub : 2 * A - A = A := by omega
      simpa [hsub, two_mul] using h.2⟩

/-- If every prime-power valuation of the lower binomial coefficient is
bounded by the corresponding valuation of the central binomial coefficient,
then the desired central binomial divisibility follows. -/
theorem lower_choose_dvd_central_choose_of_factorization_le
    {A k : Nat}
    (hfac :
      (Nat.choose (A + k) k).factorization ≤
        (Nat.choose (2 * A) A).factorization) :
    Nat.choose (A + k) k ∣ Nat.choose (2 * A) A := by
  exact (Nat.factorization_le_iff_dvd
    (Nat.choose_ne_zero (Nat.le_add_left k A))
    (Nat.choose_ne_zero (by omega : A ≤ 2 * A))).mp hfac

/-- Prime-indexed version of
`lower_choose_dvd_central_choose_of_factorization_le`. Non-prime indices have
zero factorization on both sides, so it suffices to check primes. -/
theorem lower_choose_dvd_central_choose_of_prime_factorization_le
    {A k : Nat}
    (hprime :
      ∀ p, p.Prime →
        (Nat.choose (A + k) k).factorization p ≤
          (Nat.choose (2 * A) A).factorization p) :
    Nat.choose (A + k) k ∣ Nat.choose (2 * A) A := by
  apply lower_choose_dvd_central_choose_of_factorization_le
  intro p
  by_cases hp : p.Prime
  · exact hprime p hp
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

/-- Carry-count domination over a sufficiently large finite Kummer window for
each prime implies the central binomial divisibility. -/
theorem lower_choose_dvd_central_choose_of_bounded_carry_count_le
    {A k : Nat}
    (hcarry :
      ∀ p, p.Prime →
        ∃ b,
          Nat.log p (A + k) < b ∧
          Nat.log p (2 * A) < b ∧
          ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
            ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card) :
    Nat.choose (A + k) k ∣ Nat.choose (2 * A) A := by
  apply lower_choose_dvd_central_choose_of_prime_factorization_le
  intro p hp
  rcases hcarry p hp with ⟨b, hbLower, hbCentral, hle⟩
  rw [factorization_choose_lowerCarry hp hbLower,
    factorization_choose_centralCarry hp hbCentral]
  exact hle

end Erdos728

end CentralBinomialLean
