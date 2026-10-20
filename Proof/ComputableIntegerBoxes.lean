module

public import Mathlib
public import EnumerationAlgorithm

@[expose] public section

namespace ArithmeticThetaEnumeration

theorem integerInterval_membership (R : ℕ) (x : ℤ) :
    x ∈ (Finset.range (2 * R + 1)).image (fun k : ℕ => (k : ℤ) - (R : ℤ)) ↔
      -(R : ℤ) ≤ x ∧ x ≤ (R : ℤ) := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨(x + (R : ℤ)).toNat, ?_, ?_⟩ <;> omega

theorem box_membership (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (m : ℕ) (x : Fin n → ℤ) :
    x ∈ Fintype.piFinset (fun j : Fin n =>
      (Finset.range (2 * Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) + 1)).image
        (fun k : ℕ => (k : ℤ) - (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ))) ↔
      ∀ j : Fin n,
        -(Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) ≤ x j ∧
        x j ≤ (Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs) : ℤ) := by
  simp only [Fintype.mem_piFinset, integerInterval_membership]

end ArithmeticThetaEnumeration
