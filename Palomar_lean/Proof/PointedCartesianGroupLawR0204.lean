module

public import SchemeLevelDefinitionsR0204
public import SchemeLocalWeierstrassR0203
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

@[expose] public section

/-! Pointed Cartesian comparisons preserve the actual elliptic group laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaSchemeLevelR0204
namespace PointedCartesianGroupLaw
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 GoodReductionJacobian

section Transport
variable {S B X Y : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ B}
  {b : B ⟶ S} {f : Y ⟶ X} (h : IsPullback f q p b)

/-- The Cartesian universal property on all test schemes. -/
def pointEquiv {U : Scheme.{u}} (t : U ⟶ B) :
    SchemeHomOver t q ≃ SchemeHomOver (t ≫ b) p where
  toFun x := ⟨x.val ≫ f, by rw [Category.assoc, h.w, ← Category.assoc, x.property]⟩
  invFun x := ⟨h.lift x.val t x.property, h.lift_snd _ _ _⟩
  left_inv x := Subtype.ext (h.hom_ext (h.lift_fst _ _ _)
    ((h.lift_snd _ _ _).trans x.property.symm))
  right_inv x := Subtype.ext (h.lift_fst _ _ _)

lemma point_natural {U V : Scheme.{u}} (t : U ⟶ B) (s : V ⟶ B)
    (a : V ⟶ U) (ha : a ≫ t = s) (x : SchemeHomOver t q) :
    pointEquiv h s (schemeHomOverComp a ha x) =
      schemeHomOverComp a (by rw [← Category.assoc, ha]) (pointEquiv h t x) :=
  Subtype.ext (Category.assoc _ _ _)

end Transport

section AffineTransport
variable {S X Y : Scheme.{u}} {R : Type u} [CommRing R]
  {p : X ⟶ S} {q : Y ⟶ Base R} {b : Base R ⟶ S} {f : Y ⟶ X}
  (h : IsPullback f q p b) (G : SchemeLaw p)

/-- Transport along an actual Cartesian square with affine new base. -/
def transportedLaw : WeierstrassProjModel.RelativeGroupLaw R q where
  mul t x y := (pointEquiv h t).symm (G.mul _ (pointEquiv h t x) (pointEquiv h t y))
  one t := (pointEquiv h t).symm (G.one _)
  inv t x := (pointEquiv h t).symm (G.inv _ (pointEquiv h t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, G.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, G.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t s a ha x y := by
    apply (pointEquiv h s).injective
    change pointEquiv h s (schemeHomOverComp a ha _) =
      pointEquiv h s ((pointEquiv h s).symm (G.mul _
        (pointEquiv h s (schemeHomOverComp a ha x))
        (pointEquiv h s (schemeHomOverComp a ha y))))
    rw [point_natural]
    simp only [Equiv.apply_symm_apply]
    rw [G.mul_natural]
    rw [point_natural, point_natural]

lemma transported_mul {U : Scheme.{u}} (t : U ⟶ Base R)
    (x y : SchemeHomOver t q) :
    ((transportedLaw h G).mul t x y).val ≫ f =
      (G.mul _ (pointEquiv h t x) (pointEquiv h t y)).val :=
  h.lift_fst _ _ _

lemma transported_one {U : Scheme.{u}} (t : U ⟶ Base R) :
    ((transportedLaw h G).one t).val ≫ f = (G.one (t ≫ b)).val :=
  h.lift_fst _ _ _

end AffineTransport

/-- A pointed Cartesian Weierstrass chart preserves multiplication even when
the old base is not affine. The transported law lives on the same equation. -/
lemma weierstrass_comparison {S : Scheme.{u}} (E : Family S)
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (H : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W H)
    (b : Base R ⟶ S) (f : ArithmeticThetaRelativeKatoR0169.Curve R W ⟶ E.curve)
    (h : IsPullback f (ArithmeticThetaRelativeKatoR0169.structureMap R W) E.p b)
    (hz : ArithmeticThetaRelativeKatoR0169.origin R W ≫ f = b ≫ E.zero)
    {U : Scheme.{u}} (t : U ⟶ Base R)
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W))
    (x' y' : SchemeHomOver (t ≫ b) E.p)
    (hx : x'.val = x.val ≫ f) (hy : y'.val = y.val ≫ f) :
    (E.law.mul _ x' y').val = (H.mul t x y).val ≫ f := by
  let J := transportedLaw h E.law
  have hJ : (J.one (𝟙 _)).val = ArithmeticThetaRelativeKatoR0169.origin R W := by
    apply h.hom_ext
    · rw [transported_one, hz]
      exact (congrArg Subtype.val (SchemeLocal.one_natural E.law (𝟙 S)
        ((𝟙 (Base R)) ≫ b) b (by simp))).symm
    · have ho := (H.one (𝟙 _)).property
      rw [hH.1, Category.id_comp] at ho
      exact (J.one (𝟙 _)).property.trans ho.symm
  have h1 : (H.one (𝟙 _)).val = (J.one (𝟙 _)).val := by
    rw [hH.1, Category.id_comp, hJ]
  have hm := WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
    W.toProjective H J h1 t x y
  have ex : x' = pointEquiv h t x := Subtype.ext hx
  have ey : y' = pointEquiv h t y := Subtype.ext hy
  rw [ex, ey, hm]
  exact (transported_mul h E.law t x y).symm

attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- The assertion on a test map factoring through one presentation of F. -/
lemma on_chart {k : Type u} [Field k] [CharZero k]
    {S T : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (h : IsPullback f F.p E.p b)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (P : LocalPresentation k T (b ≫ σ) F)
    {U : Scheme.{u}} (t : U ⟶ Base P.ring)
    (x y : SchemeHomOver (t ≫ P.base) F.p)
    (x' y' : SchemeHomOver ((t ≫ P.base) ≫ b) E.p)
    (hx : x'.val = x.val ≫ f) (hy : y'.val = y.val ≫ f) :
    (E.law.mul _ x' y').val = (F.law.mul _ x y).val ≫ f := by
  letI := P.elliptic
  let xx := (pointEquiv P.cartesian t).symm x
  let yy := (pointEquiv P.cartesian t).symm y
  have hxx : x.val = xx.val ≫ P.comparison := (P.cartesian.lift_fst _ _ _).symm
  have hyy : y.val = yy.val ≫ P.comparison := (P.cartesian.lift_fst _ _ _).symm
  have hs := P.cartesian.paste_horiz h
  have ho : ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation ≫
      (P.comparison ≫ f) = (P.base ≫ b) ≫ E.zero := by
    rw [← Category.assoc, P.zero_eq, Category.assoc, hz, Category.assoc]
  let X : SchemeHomOver (t ≫ (P.base ≫ b)) E.p :=
    ⟨x'.val, x'.property.trans (Category.assoc _ _ _)⟩
  let Y : SchemeHomOver (t ≫ (P.base ≫ b)) E.p :=
    ⟨y'.val, y'.property.trans (Category.assoc _ _ _)⟩
  calc
    (E.law.mul _ x' y').val = (E.law.mul _ X Y).val :=
      SchemeLocal.mul_val_congr E.law (Category.assoc _ _ _) _ _ _ _ rfl rfl
    _ = (P.law.mul t xx yy).val ≫ (P.comparison ≫ f) := by
      apply weierstrass_comparison E P.equation P.law P.originLaw _ _ hs ho
      · exact hx.trans (by rw [hxx, Category.assoc])
      · exact hy.trans (by rw [hyy, Category.assoc])
    _ = (F.law.mul _ x y).val ≫ f := by
      rw [P.mul_eq U t xx yy x y hxx hyy, Category.assoc]

end PointedCartesianGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 GoodReductionJacobian
open PointedCartesianGroupLaw
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- An origin-preserving Cartesian comparison preserves multiplication on
all scheme-valued points, with no affineness or reducedness assumption. -/
theorem pointed_cartesian_group_law :
    ∀ (k : Type u) [Field k] [CharZero k] (S T : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S) (F : Family T)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve),
      IsPullback f F.p E.p b → F.zero ≫ f = b ≫ E.zero →
      Multiplicative E F b f := by
  intro k _ _ S T σ E F b f h hz
  classical
  choose P hP using scheme_local_weierstrass k T (b ≫ σ) F
  let C : T.OpenCover := Scheme.Cover.mkOfCovers T
    (fun i => Base (P i).ring) (fun i => (P i).base)
    (fun i => ⟨i, hP i⟩) (fun i => (P i).openImmersion)
  intro U t x y x' y' hx hy
  apply (C.pullback₁ t).hom_ext
  intro i
  let a := (C.pullback₁ t).f i
  let s := C.pullbackHom t i
  have ha : a ≫ t = s ≫ (P i).base := (C.pullbackHom_map t i).symm
  have hab : a ≫ (t ≫ b) = (s ≫ (P i).base) ≫ b := by
    rw [← Category.assoc, ha]
  let X := schemeHomOverComp a ha x
  let Y := schemeHomOverComp a ha y
  let X' := schemeHomOverComp a hab x'
  let Y' := schemeHomOverComp a hab y'
  have he : a ≫ (E.law.mul _ x' y').val = (E.law.mul _ X' Y').val :=
    congrArg Subtype.val (E.law.mul_natural _ _ a hab x' y')
  have hf : a ≫ (F.law.mul _ x y).val = (F.law.mul _ X Y).val :=
    congrArg Subtype.val (F.law.mul_natural _ _ a ha x y)
  change a ≫ (E.law.mul _ x' y').val = a ≫ ((F.law.mul _ x y).val ≫ f)
  calc
    _ = (E.law.mul _ X' Y').val := he
    _ = (F.law.mul _ X Y).val ≫ f := by
      apply on_chart σ E F b f h hz (P i) s X Y X' Y'
      · change a ≫ x'.val = (a ≫ x.val) ≫ f
        rw [hx, Category.assoc]
      · change a ≫ y'.val = (a ≫ y.val) ≫ f
        rw [hy, Category.assoc]
    _ = a ≫ ((F.law.mul _ x y).val ≫ f) := by rw [← hf, Category.assoc]

#print axioms pointed_cartesian_group_law
end ArithmeticThetaSchemeLevelR0204
