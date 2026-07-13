import CentralBinomialLean.Kummer

/-!
# Reduction back to factorial divisibility

This file formalizes the algebraic reduction in Section 2 of `../erdos728.pdf`
for the central specialization `n = 2A`, `a = A`, `b = A + k`.
-/

namespace CentralBinomialLean

namespace Erdos728

attribute [local instance] Classical.propDecidable

/-- The central binomial divisibility implies the specialized factorial
divisibility from the original Erdos #728 statement. -/
theorem factorial_dvd_of_lower_choose_dvd_central_choose
    {A k : Nat}
    (h : Nat.choose (A + k) k ∣ Nat.choose (2 * A) A) :
    A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial := by
  rcases h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hA : A ≤ 2 * A := by omega
  have hk : k ≤ A + k := Nat.le_add_left k A
  have hcentral :
      Nat.choose (2 * A) A * A.factorial * A.factorial = (2 * A).factorial := by
    have h0 := Nat.choose_mul_factorial_mul_factorial hA
    have hsub : 2 * A - A = A := by omega
    simpa [hsub] using h0
  have hlower :
      Nat.choose (A + k) k * k.factorial * A.factorial = (A + k).factorial := by
    have h0 := Nat.choose_mul_factorial_mul_factorial hk
    have hsub : A + k - k = A := by omega
    simpa [hsub] using h0
  calc
    (2 * A).factorial * k.factorial
        = (Nat.choose (2 * A) A * A.factorial * A.factorial) * k.factorial := by
            rw [hcentral]
    _ = ((Nat.choose (A + k) k * m) * A.factorial * A.factorial) * k.factorial := by
            rw [hm]
    _ = (A.factorial * (Nat.choose (A + k) k * k.factorial * A.factorial)) * m := by
            ring
    _ = (A.factorial * (A + k).factorial) * m := by
            rw [hlower]

/-- Carry-count domination for every prime implies the specialized factorial
divisibility from the original statement. -/
theorem factorial_dvd_of_bounded_carry_count_le
    {A k : Nat}
    (hcarry :
      ∀ p, p.Prime →
        ∃ b,
          Nat.log p (A + k) < b ∧
          Nat.log p (2 * A) < b ∧
          ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
            ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card) :
    A.factorial * (A + k).factorial ∣ (2 * A).factorial * k.factorial :=
  factorial_dvd_of_lower_choose_dvd_central_choose
    (lower_choose_dvd_central_choose_of_bounded_carry_count_le hcarry)

end Erdos728

end CentralBinomialLean
