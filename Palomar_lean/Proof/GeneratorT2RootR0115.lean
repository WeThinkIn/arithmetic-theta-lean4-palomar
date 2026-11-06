module

public import BasisCoordinateGeometryR0115
public import BasisRightActionR0115
public import TwoTorsionTranslation

@[expose] public section

/-! Invariance of the literal root under the actual `T²` marking action. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

/-- The source root is invariant under `(P,Q) ↦ (P,Q+2P)` on actual bases. -/
theorem generator_t2_root :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k]
      (e : Fin 3 → k), Function.Injective e →
      ∀ b : Marking k e, IsBasis k e b →
        root k e (act k e b generatorT2) = root k e b := by
  intro k _ _ _ e he b hb
  obtain ⟨hfinite, ⟨σ, hlabels⟩, hcurve, hd, _, _⟩ :=
    basis_coordinate_geometry k e he b hb
  have hlinj : Function.Injective (labels k e b) := by
    rw [hlabels]
    exact he.comp σ.injective
  have hact : act k e b generatorT2 = ![b 0, 2 • b 0 + b 1] := by
    funext j
    have hv1 : (1 : ZMod 4).val = 1 := by decide
    have hv2 : (2 : ZMod 4).val = 2 := by decide
    fin_cases j <;> simp [act, generatorT2, hv1, hv2]
  have h20 : 2 • (2 • b 0) = 0 := by
    rw [← mul_nsmul]
    exact hb.1 0
  have hlabels_act : labels k e ![b 0, 2 • b 0 + b 1] = labels k e b := by
    funext j
    fin_cases j <;> simp [labels, h20]
  obtain ⟨h0, hd0⟩ := hd 0
  change (Curve k e).Nonsingular (labels k e b 0) 0 at h0
  change 2 • b 0 = Point.some (labels k e b 0) 0 h0 at hd0
  rw [hact]
  unfold root
  rw [hlabels_act]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  cases hp : b 1 with
  | zero => exact False.elim ((hfinite 1).1 (by rw [hp]; rfl))
  | some x y hxy =>
    have hy : y ≠ 0 := by simpa [hp, pointY] using (hfinite 1).2
    have hEq : (splitCurve (labels k e b 0) (labels k e b 1)
        (labels k e b 2)).Equation x y := by
      change (Curve k (labels k e b)).Equation x y
      rw [← hcurve]
      exact hxy.1
    have hxne : x ≠ labels k e b 0 := by
      intro heq
      apply hy
      have hc := (split_equation (labels k e b 0) (labels k e b 1)
        (labels k e b 2) x y).mp hEq
      have hz : y ^ 2 = 0 := by simpa [heq] using hc
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz
    rw [hd0, add_comm]
    rw [Point.add_of_X_ne (h₁ := hxy) (h₂ := h0) hxne]
    simp only [pointX, pointY]
    have htrans := (two_torsion_translation k
      (labels k e b 0) (labels k e b 1) (labels k e b 2) x y
      (hlinj.ne (by decide)) (hlinj.ne (by decide))
      (hlinj.ne (by decide)) hEq hy).2.2
    change rootExpression _ _ _ ((Curve k e).addX _ _ ((Curve k e).slope _ _ _ _))
      ((Curve k e).addY _ _ _ ((Curve k e).slope _ _ _ _)) = _
    rw [hcurve]
    exact htrans

end ArithmeticThetaMarkingR0115
