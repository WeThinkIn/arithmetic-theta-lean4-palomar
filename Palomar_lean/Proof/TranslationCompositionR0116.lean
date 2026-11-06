module

public import FunctionFieldTranslationsR0116

@[expose] public section

/-! The generic point turns the frozen chord substitutions into the genuine
point-group action, including exceptional additions of constant points. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord xFunction yFunction)

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

lemma generic_nonsingular (he : Function.Injective e) :
    ((Curve k e).baseChange (FF k e)).Nonsingular (xFunction k e) (yFunction k e) := by
  have hy : yFunction k e ≠ 0 := by
    simpa only [yFunction, map_zero] using (IsFractionRing.injective (Coord k e) (FF k e)).ne
      (CoordinateRing.YClass_ne_zero (W' := Curve k e) 0)
  let : CharZero (FF k e) := charZero_of_injective_algebraMap (algebraMap k (FF k e)).injective
  rw [nonsingular_iff']
  constructor
  · rw [equation_iff]
    have h := generic_equation k e he
    simp only [Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_neg,
      map_zero, zero_mul, add_zero] at *
    linear_combination h
  · right
    simpa [Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map] using
      mul_ne_zero (two_ne_zero : (2 : FF k e) ≠ 0) hy

def genericPoint (he : Function.Injective e) : ((Curve k e).baseChange (FF k e)).Point :=
  .some _ _ (generic_nonsingular k e he)

def constantPoint : (Curve k e).Point →+ ((Curve k e).baseChange (FF k e)).Point :=
  Point.map (W' := Curve k e) (Algebra.ofId k (FF k e))

omit [CharZero k] in
lemma constantPoint_some (a b : k) (hn : (Curve k e).Nonsingular a b) :
    constantPoint k e (Point.some a b hn) =
      Point.some (algebraMap k (FF k e) a) (algebraMap k (FF k e) b)
        (((Curve k e).map_nonsingular (algebraMap k (FF k e)).injective a b).mpr hn) := rfl

omit [CharZero k] in
lemma map_constant (A : FF k e →ₐ[k] FF k e) (P : (Curve k e).Point) :
    Point.map (W' := Curve k e) A (constantPoint k e P) = constantPoint k e P := by
  cases P with
  | zero => rfl
  | some a b hn =>
    rw [constantPoint_some, Point.map_some, Point.some.injEq]
    exact ⟨A.commutes a, A.commutes b⟩

lemma map_generic_translation (he : Function.Injective e) (T : Translations k e)
    (hT : IsTranslationSystem k e T) (P : (Curve k e).Point) :
    Point.map (W' := Curve k e) (T P).toAlgHom (genericPoint k e he) =
      genericPoint k e he + constantPoint k e P := by
  classical
  cases P with
  | zero =>
    change Point.map (W' := Curve k e) (T 0).toAlgHom (genericPoint k e he) =
      genericPoint k e he + 0
    rw [add_zero]
    change Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact hT 0
  | some a b hn =>
    have hx : xFunction k e ≠ algebraMap k (FF k e) a :=
      sub_ne_zero.mp (x_sub_ne_zero k e a)
    rw [constantPoint_some]
    simp only [genericPoint, Point.map_some,
      Point.add_of_X_ne hx, Point.some.injEq]
    have h := hT (Point.some a b hn)
    simp only [translatedCoordinates] at h
    change T (Point.some a b hn) (xFunction k e) = _ ∧
      T (Point.some a b hn) (yFunction k e) = _
    rw [h.1, h.2]
    simp [slope_of_X_ne hx, addX, addY, negY, negAddY, Curve,
      ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
    constructor <;> ring

omit [CharZero k] [DecidableEq k] in
lemma translation_zero (T : Translations k e) (hT : IsTranslationSystem k e T) :
    T 0 = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply ff_ext k e
  · exact (hT 0).1
  · exact (hT 0).2

lemma translation_comp (he : Function.Injective e) (T : Translations k e)
    (hT : IsTranslationSystem k e T) (P Q : (Curve k e).Point) :
    (T P).toAlgHom.comp (T Q).toAlgHom = (T (P + Q)).toAlgHom := by
  classical
  have hp : Point.map (W' := Curve k e) (T P).toAlgHom
      (Point.map (W' := Curve k e) (T Q).toAlgHom (genericPoint k e he)) =
      Point.map (W' := Curve k e) (T (P + Q)).toAlgHom (genericPoint k e he) := by
    rw [map_generic_translation k e he T hT Q, map_add,
      map_generic_translation k e he T hT P, map_constant,
      map_generic_translation k e he T hT (P + Q), map_add, add_assoc]
  change Point.some _ _ _ = Point.some _ _ _ at hp
  obtain ⟨hx, hy⟩ := Point.some.inj hp
  exact ff_ext k e hx hy

/-- Pullback by addition is the genuine translation action, over every
characteristic-zero field and with all point-group additions included. -/
theorem translation_composition :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Function.Injective e → ∀ T : Translations k e, IsTranslationSystem k e T →
      T 0 = AlgEquiv.refl ∧
      (∀ P Q : (Curve k e).Point, ∀ f : FF k e, T P (T Q f) = T (P + Q) f) ∧
      (∀ P : (Curve k e).Point, (T P).symm = T (-P)) := by
  intro k _ _ _ e he T hT
  have hz := translation_zero k e T hT
  have hc (P Q : (Curve k e).Point) (f : FF k e) :
      T P (T Q f) = T (P + Q) f :=
    DFunLike.congr_fun (translation_comp k e he T hT P Q) f
  refine ⟨hz, hc, ?_⟩
  intro P
  ext f
  apply (T P).injective
  rw [AlgEquiv.apply_symm_apply, hc, add_neg_cancel, hz]
  rfl

end ArithmeticThetaReciprocityR0116
