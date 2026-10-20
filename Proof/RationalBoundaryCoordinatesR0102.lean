module

public import ScopedCuspDefinitionsR0102
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

noncomputable section
namespace ArithmeticThetaIntegralCuspsR0102

/-- A determinant-one first column cannot vanish. -/
lemma first_entry_ne_zero_of_lower_zero (A : Marking) (h : A 1 0 = 0) :
    A 0 0 ≠ 0 := by
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  intro ha
  simp [h, ha] at hd

/-- Equality of the extended rational slopes is the integral cross-product identity. -/
lemma boundary_eq_iff_cross (A B : Marking) :
    boundary A = boundary B ↔ A 0 0 * B 1 0 = B 0 0 * A 1 0 := by
  by_cases ha : A 1 0 = 0
  · by_cases hb : B 1 0 = 0
    · simp [boundary, ha, hb]
    · have han := first_entry_ne_zero_of_lower_zero A ha
      simp [boundary, ha, hb, han]
  · by_cases hb : B 1 0 = 0
    · have hbn := first_entry_ne_zero_of_lower_zero B hb
      simp [boundary, ha, hb, hbn]
    · have haq : (A 1 0 : ℚ) ≠ 0 := by exact_mod_cast ha
      have hbq : (B 1 0 : ℚ) ≠ 0 := by exact_mod_cast hb
      simp only [boundary, if_neg ha, if_neg hb, WithTop.coe_inj]
      rw [div_eq_div_iff haq hbq]
      exact_mod_cast (Iff.rfl : A 0 0 * B 1 0 = B 0 0 * A 1 0 ↔ _)

set_option backward.isDefEq.respectTransparency false in
/-- The lower-left entry of the change-of-marking matrix is the cross product. -/
lemma parabolic_inv_mul_iff (A B : Marking) :
    Parabolic (A⁻¹ * B) ↔ A 0 0 * B 1 0 = B 0 0 * A 1 0 := by
  change ((A⁻¹).val * B.val) 1 0 = 0 ↔ _
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change -A 1 0 * B 0 0 + A 0 0 * B 1 0 = 0 ↔ _
  constructor <;> intro h <;> nlinarith

/-- Every rational projective coordinate has an integral determinant-one marking. -/
lemma boundary_surjective : Function.Surjective boundary := by
  intro x
  cases x using WithTop.recTopCoe with
  | top =>
      refine ⟨1, ?_⟩
      simp [boundary]
  | coe q =>
      obtain ⟨A, ha, hc⟩ := q.isCoprime_num_den.exists_SL2_col 0
      refine ⟨A, ?_⟩
      have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
      simp only [boundary, hc, if_neg hd, ha, Int.cast_natCast]
      rw [Rat.num_div_den]

/-- Rational boundary coordinates are precisely right parabolic cosets of integral markings. -/
theorem rational_boundary_coordinates :
    (∀ x : WithTop ℚ, ∃ A : Marking, boundary A = x) ∧
    (∀ A B : Marking, boundary A = boundary B ↔
      ∃ p : Marking, Parabolic p ∧ B = A * p) := by
  refine ⟨boundary_surjective, ?_⟩
  intro A B
  rw [boundary_eq_iff_cross, ← parabolic_inv_mul_iff]
  constructor
  · intro h
    exact ⟨A⁻¹ * B, h, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    simpa using hp

end ArithmeticThetaIntegralCuspsR0102
