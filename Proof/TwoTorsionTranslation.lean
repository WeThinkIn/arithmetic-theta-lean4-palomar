module

public import FourTorsionDefinitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace ArithmeticThetaFourTorsion

universe u

/-- Translation by the first labelled two-torsion point preserves the root expression. -/
theorem two_torsion_translation : ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e₁ e₂ e₃ x y : k), e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → (ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).Equation x y → y ≠ 0 → (ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).addX x e₁ ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).slope x e₁ y 0) = e₁ + (e₁-e₂)*(e₁-e₃)/(x-e₁) ∧ (ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).addY x e₁ y ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).slope x e₁ y 0) = -(e₁-e₂)*(e₁-e₃)*y/(x-e₁)^2 ∧ ArithmeticThetaFourTorsion.rootExpression e₁ e₂ e₃ ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).addX x e₁ ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).slope x e₁ y 0)) ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).addY x e₁ y ((ArithmeticThetaFourTorsion.splitCurve e₁ e₂ e₃).slope x e₁ y 0)) = ArithmeticThetaFourTorsion.rootExpression e₁ e₂ e₃ x y := by
  intro k _ _ _ e₁ e₂ e₃ x y h12 h13 _ hE hy
  -- Expand the actual Weierstrass equation into the split cubic.
  have hcurve : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp hE
    simp only [splitCurve, zero_mul, add_zero] at h
    linear_combination h
  -- A nonzero ordinate excludes the vertical-chord branch of slope.
  have hx : x ≠ e₁ := by
    intro heq
    apply hy
    have : y ^ 2 = 0 := by simpa [heq] using hcurve
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp this
  have hu : x - e₁ ≠ 0 := sub_ne_zero.mpr hx
  have hs : (splitCurve e₁ e₂ e₃).slope x e₁ y 0 = y / (x - e₁) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, sub_zero]
  -- Clear denominators and use the curve equation for the abscissa.
  have hX : (splitCurve e₁ e₂ e₃).addX x e₁
      ((splitCurve e₁ e₂ e₃).slope x e₁ y 0) =
      e₁ + (e₁-e₂)*(e₁-e₃)/(x-e₁) := by
    rw [hs]
    simp only [WeierstrassCurve.Affine.addX, splitCurve, zero_mul, add_zero]
    field_simp
    linear_combination hcurve
  -- The ordinate follows from the abscissa and Mathlib's negated chord formula.
  have hY : (splitCurve e₁ e₂ e₃).addY x e₁ y
      ((splitCurve e₁ e₂ e₃).slope x e₁ y 0) =
      -(e₁-e₂)*(e₁-e₃)*y/(x-e₁)^2 := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [hX, hs]
    simp only [WeierstrassCurve.Affine.negY, splitCurve, zero_mul, sub_zero]
    field_simp
    ring
  -- The remaining rational identity uses only nonzero roots and denominators.
  refine ⟨hX, hY, ?_⟩
  rw [hX, hY]
  unfold rootExpression
  have hA : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr h12
  have hB : e₁ - e₃ ≠ 0 := sub_ne_zero.mpr h13
  field_simp
  ring

end ArithmeticThetaFourTorsion
