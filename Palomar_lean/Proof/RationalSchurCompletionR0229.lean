module

public import LDLEnumerationDefinitionsR0229
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

/-! One rational completion-of-squares step, including the empty tail. -/
set_option autoImplicit false
namespace ArithmeticThetaLDLEnumerationR0229
namespace RationalSchurCompletion

private theorem energy_eq_form {n : ℕ} (A : QMatrix n) (x : Fin n → ℚ) :
    energy A x = A.toQuadraticForm' x := by
  simp [energy, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap, mul_comm, mul_left_comm]

private theorem energy_head {n : ℕ} (A : QMatrix (n+1)) (hs : A.IsSymm)
    (z : ℚ) (y : Fin n → ℚ) :
    energy A (Fin.cons z y) = A 0 0 * z^2 +
      2 * z * (∑ j, A 0 j.succ * y j) +
      ∑ i, ∑ j, y i * A i.succ j.succ * y j := by
  simp only [energy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_add_distrib]
  have hcross : (∑ i : Fin n, y i * A i.succ 0 * z) =
      z * ∑ i : Fin n, A 0 i.succ * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hs.apply 0 i.succ]
    ring
  rw [hcross]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  ring

private theorem energy_schur {n : ℕ} (A : QMatrix (n+1)) (y : Fin n → ℚ) :
    energy (schur A) y = (∑ i, ∑ j, y i * A i.succ j.succ * y j) -
      (∑ j, A 0 j.succ * y j)^2 / A 0 0 := by
  simp only [energy, schur, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem completion {n : ℕ} (A : QMatrix (n+1)) (hs : A.IsSymm)
    (ha : A 0 0 ≠ 0) (z : ℚ) (y : Fin n → ℚ) :
    energy A (Fin.cons z y) = A 0 0 *
      (z + (∑ j, A 0 j.succ * y j) / A 0 0)^2 + energy (schur A) y := by
  rw [energy_head A hs, energy_schur]
  field_simp
  ring

end RationalSchurCompletion

open RationalSchurCompletion in
/-- The actual rational Schur update preserves positive definiteness and
completes the head square without any dimension restriction on the tail. -/
theorem rational_schur_completion (n : ℕ) (A : QMatrix (n+1))
    (hs : A.IsSymm) (hp : A.toQuadraticForm'.PosDef) :
    0 < A 0 0 ∧ (schur A).IsSymm ∧ (schur A).toQuadraticForm'.PosDef ∧
      ∀ (z : ℚ) (y : Fin n → ℚ),
        energy A (Fin.cons z y) = A 0 0 *
          (z + (∑ j : Fin n, A 0 j.succ * y j) / A 0 0)^2 +
          energy (schur A) y := by
  have he : (Fin.cons 1 (fun _ => 0) : Fin (n+1) → ℚ) ≠ 0 := by
    intro h
    have hh := congrFun h 0
    simp at hh
  have ha : 0 < A 0 0 := by
    have h := hp _ he
    rw [← energy_eq_form, energy_head A hs] at h
    simpa using h
  refine ⟨ha, ?_, ?_, completion A hs (ne_of_gt ha)⟩
  · apply Matrix.IsSymm.ext
    intro i j
    simp only [schur, hs.apply i.succ j.succ]
    ring
  · intro y hy
    let z : ℚ := -(∑ j : Fin n, A 0 j.succ * y j) / A 0 0
    have hv : (Fin.cons z y : Fin (n+1) → ℚ) ≠ 0 := by
      intro h
      apply hy
      funext i
      exact congrFun h i.succ
    have h := hp _ hv
    rw [← energy_eq_form, completion A hs (ne_of_gt ha)] at h
    simpa [z, neg_div, energy_eq_form] using h

end ArithmeticThetaLDLEnumerationR0229

#print axioms ArithmeticThetaLDLEnumerationR0229.rational_schur_completion
