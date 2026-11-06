module

public import FourTorsionDefinitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The two field-level transformation laws for the source root expression.
These identities do not assert descent to a section on moduli.
-/
namespace ArithmeticThetaFourTorsion

universe u

/-- Weight-one covariance of the rational expression under a simultaneous
translation and a nonzero change of scale. The statement includes `y = 0`
with Lean's totalized field division. -/
theorem root_coordinate_covariance
    (k : Type u) [Field k] [CharZero k]
    (e₁ e₂ e₃ x y : k) (c r : k) (hc : c ≠ 0) :
    rootExpression (c^2*e₁+r) (c^2*e₂+r) (c^2*e₃+r) (c^2*x+r) (c^3*y) =
      c * (rootExpression e₁ e₂ e₃ x y) := by
  by_cases hy : y = 0
  · simp [rootExpression, hy]
  · unfold rootExpression
    field_simp
    ring

/-- Reversing the completed-square ordinate reverses the sign of the
root expression, including the zero-denominator case. -/
theorem root_negation
    (k : Type u) [Field k] [CharZero k] (e₁ e₂ e₃ x y : k) :
    rootExpression e₁ e₂ e₃ x (-y) = -(rootExpression e₁ e₂ e₃ x y) := by
  simp [rootExpression, div_neg]

end ArithmeticThetaFourTorsion
