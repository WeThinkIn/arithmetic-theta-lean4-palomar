import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FourTorsionDefinitions

namespace ArithmeticThetaFourTorsion

universe u

open WeierstrassCurve

/-- The affine equation of the split cubic is the displayed product equation. -/
theorem split_equation {k : Type u} [Field k] [CharZero k] (e₁ e₂ e₃ x y : k) :
    (splitCurve e₁ e₂ e₃).Equation x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [splitCurve]
  ring

lemma split_delta {k : Type u} [Field k] [CharZero k] (e₁ e₂ e₃ : k) :
    (splitCurve e₁ e₂ e₃).Δ =
      16 * ((e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2) := by
  simp [splitCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma split_elliptic {k : Type u} [Field k] [CharZero k] (e₁ e₂ e₃ : k)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    (splitCurve e₁ e₂ e₃).IsElliptic := by
  apply WeierstrassCurve.IsElliptic.mk
  rw [split_delta]
  exact isUnit_iff_ne_zero.mpr <| mul_ne_zero (by norm_num) <| mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr h12))
      (pow_ne_zero 2 (sub_ne_zero.mpr h13)))
    (pow_ne_zero 2 (sub_ne_zero.mpr h23))

/-- Pairwise distinct roots give the elliptic curve and all three labelled affine points. -/
theorem split_smooth {k : Type u} [Field k] [CharZero k] (e₁ e₂ e₃ : k)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    (splitCurve e₁ e₂ e₃).IsElliptic ∧
      (splitCurve e₁ e₂ e₃).Nonsingular e₁ 0 ∧
      (splitCurve e₁ e₂ e₃).Nonsingular e₂ 0 ∧
      (splitCurve e₁ e₂ e₃).Nonsingular e₃ 0 := by
  refine ⟨split_elliptic e₁ e₂ e₃ h12 h13 h23, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Nonsingular]
    refine ⟨?_, Or.inl ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp [splitCurve]
      ring
    · rw [WeierstrassCurve.Affine.evalEval_polynomialX]
      simp [splitCurve]
      intro h
      have hp : (e₁ - e₂) * (e₁ - e₃) ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)
      apply hp
      have hprod : (e₁ - e₂) * (e₁ - e₃) = 0 := by
        ring_nf at h
        calc
          (e₁ - e₂) * (e₁ - e₃) =
              -(-e₂ * e₃ + e₂ * e₁ + e₃ * e₁ - e₁ ^ 2) := by ring
          _ = 0 := by simpa [h]
      exact hprod
  · rw [WeierstrassCurve.Affine.Nonsingular]
    refine ⟨?_, Or.inl ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp [splitCurve]
      ring
    · rw [WeierstrassCurve.Affine.evalEval_polynomialX]
      simp [splitCurve]
      intro h
      have hp : (e₂ - e₁) * (e₂ - e₃) ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (Ne.symm h12)) (sub_ne_zero.mpr h23)
      apply hp
      have hprod : (e₂ - e₁) * (e₂ - e₃) = 0 := by
        ring_nf at h
        calc
          (e₂ - e₁) * (e₂ - e₃) =
              -(e₂ * e₃ + e₂ * e₁ - e₂ ^ 2 - e₃ * e₁) := by ring
          _ = 0 := by simpa [h]
      exact hprod
  · rw [WeierstrassCurve.Affine.Nonsingular]
    refine ⟨?_, Or.inl ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp [splitCurve]
      ring
    · rw [WeierstrassCurve.Affine.evalEval_polynomialX]
      simp [splitCurve]
      intro h
      have hp : (e₃ - e₁) * (e₃ - e₂) ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (Ne.symm h13)) (sub_ne_zero.mpr (Ne.symm h23))
      apply hp
      have hprod : (e₃ - e₁) * (e₃ - e₂) = 0 := by
        ring_nf at h
        calc
          (e₃ - e₁) * (e₃ - e₂) =
              -(e₂ * e₃ - e₂ * e₁ + e₃ * e₁ - e₃ ^ 2) := by ring
          _ = 0 := by simpa [h]
      exact hprod

end ArithmeticThetaFourTorsion
