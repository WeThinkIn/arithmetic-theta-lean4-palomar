module

public import FourTorsionDefinitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

@[expose] public section

/-! The tangent-and-chord duplication identity for the split cubic.
This module proves only the universal coordinate identity, with no torsion
or distinct-root hypothesis. -/

namespace ArithmeticThetaFourTorsion

universe u

/-- The duplication coordinate is the square of the displayed root expression. -/
theorem duplication_coordinate :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e₁ e₂ e₃ x y : k),
      (splitCurve e₁ e₂ e₃).Equation x y → y ≠ 0 →
      (splitCurve e₁ e₂ e₃).addX x x ((splitCurve e₁ e₂ e₃).slope x x y y) - e₁ =
        (rootExpression e₁ e₂ e₃ x y)^2 := by
  intro k _ _ _ e₁ e₂ e₃ x y hEq hy
  have htwo : (2 : k) ≠ 0 := by norm_num
  have hneg : y ≠ (splitCurve e₁ e₂ e₃).negY x y := by
    simp only [WeierstrassCurve.Affine.negY, splitCurve, zero_mul, sub_zero]
    intro h
    apply hy
    have hmul : (2 : k) * y = 0 := by linear_combination h
    exact (mul_eq_zero.mp hmul).resolve_left htwo
  rw [WeierstrassCurve.Affine.equation_iff] at hEq
  simp only [splitCurve, zero_mul, add_zero] at hEq
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    splitCurve, rootExpression, zero_mul, sub_zero, sub_neg_eq_add]
  rw [← two_mul y]
  field_simp
  linear_combination 4 * (e₂ + e₃ - 2 * x) * hEq

end ArithmeticThetaFourTorsion
