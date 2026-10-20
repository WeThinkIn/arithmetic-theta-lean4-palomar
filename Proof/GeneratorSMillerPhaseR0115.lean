module

public import BasisRightActionR0115
public import BasisCoordinateGeometryR0115

@[expose] public section

/-! The generator-S phase for arbitrary actual full-four markings. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

private lemma half_on_equal_curve {k : Type u} [Field k] [DecidableEq k]
    (W : WeierstrassCurve.Affine k) (l : Fin 3 → k) (hW : W = Curve k l)
    (i : Fin 3) (x y : k) (hP : W.Nonsingular x y)
    (hD : W.Nonsingular (l i) 0)
    (hd : 2 • Point.some x y hP = Point.some (l i) 0 hD) :
    ArithmeticThetaMillerR0114.IsHalf k l i x y := by
  subst W
  exact ⟨hP, hD, hd⟩

/-- The right S-action is the ordered marking (Q,-P). -/
lemma act_generatorS {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (b : Marking k e) (hb : ∀ i, 4 • b i = 0) :
    act k e b generatorS = ![b 1, -b 0] := by
  have h3 : 3 • b 0 = -b 0 := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [show 4 = 3 + 1 from rfl, add_nsmul, one_nsmul] using hb 0
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  have hvn : (-1 : ZMod 4).val = 3 := by decide
  funext i
  fin_cases i <;> simp [act, generatorS, hv1, hvn, h3]

/-- S interchanges the first two recovered labels and fixes the third. -/
lemma labels_generatorS {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (b : Marking k e) (hb : ∀ i, 4 • b i = 0) :
    labels k e (act k e b generatorS) =
      ![labels k e b 1, labels k e b 0, labels k e b 2] := by
  have hn : -(2 • b 0 : (Curve k e).Point) = 2 • b 0 := by
    apply neg_eq_of_add_eq_zero_left
    simpa only [show 4 = 2 + 2 from rfl, add_nsmul] using hb 0
  rw [act_generatorS e b hb]
  funext i
  fin_cases i <;> simp [labels, hn, add_comm]

/-- The normalized tangent-evaluation phase and its exact root transformation. -/
theorem generator_s_miller_phase :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ b : Marking k e, IsBasis k e b →
    phase k e b = root k e b / root k e (act k e b generatorS) ∧
    IsPrimitiveRoot (phase k e b) 4 ∧
    root k e (act k e b generatorS) = (phase k e b)⁻¹ * root k e b := by
  intro k _ _ _ e he b hb
  obtain ⟨hfinite, ⟨σ, hl⟩, hcurve, hd, hroot, _⟩ :=
    basis_coordinate_geometry k e he b hb
  have hli : Function.Injective (labels k e b) := by
    rw [hl]
    exact he.comp σ.injective
  have haff : ∀ i : Fin 2, ∃ (x y : k) (h : (Curve k e).Nonsingular x y),
      b i = Point.some x y h := by
    intro i
    cases hp : b i with
    | zero => exact False.elim ((hfinite i).1 hp)
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨x₁, y₁, hP, hp⟩ := haff 0
  obtain ⟨x₂, y₂, hQ, hq⟩ := haff 1
  obtain ⟨hD₁, hd₁⟩ := hd 0
  obtain ⟨hD₂, hd₂⟩ := hd 1
  have hh₁ := half_on_equal_curve (Curve k e) (labels k e b) hcurve 0
    x₁ y₁ hP hD₁ (by simpa [hp] using hd₁)
  have hh₂ := half_on_equal_curve (Curve k e) (labels k e b) hcurve 1
    x₂ y₂ hQ hD₂ (by simpa [hq] using hd₂)
  have hphase : phase k e b =
      ArithmeticThetaMillerR0114.millerRatio k (labels k e b) x₁ y₁ x₂ y₂ := by
    unfold phase tangent ArithmeticThetaMillerR0114.millerRatio
      ArithmeticThetaMillerR0114.millerValue ArithmeticThetaMillerR0114.tangentValue
      ArithmeticThetaMillerR0114.tangentSlope
    simp only [hp, hq, pointX, pointY]
    change ArithmeticThetaMillerR0114.Curve k e =
      ArithmeticThetaMillerR0114.Curve k (labels k e b) at hcurve
    rw [hcurve]
  obtain ⟨hratio, hprim⟩ := ArithmeticThetaMillerR0114.actual_miller_phase k
    (labels k e b) hli x₁ y₁ x₂ y₂ hh₁ hh₂
  have hnx : pointX k e (-b 0) = x₁ := by rw [hp]; rfl
  have hny : pointY k e (-b 0) = -y₁ := by
    rw [hp]
    change (Curve k e).negY x₁ y₁ = -y₁
    simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, splitCurve]
  have hSroot : root k e (act k e b generatorS) =
      rootExpression (labels k e b 1) (labels k e b 0) (labels k e b 2) x₁ (-y₁) := by
    unfold root
    rw [labels_generatorS e b hb.1, act_generatorS e b hb.1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, hnx, hny]
    rfl
  have hr : phase k e b = root k e b / root k e (act k e b generatorS) := by
    rw [hphase, hSroot]
    simpa only [root, hq, pointX, pointY] using hratio
  refine ⟨hr, (by rw [hphase]; exact hprim), ?_⟩
  rw [hr, inv_div, div_mul_cancel₀ _ hroot]

end ArithmeticThetaMarkingR0115
