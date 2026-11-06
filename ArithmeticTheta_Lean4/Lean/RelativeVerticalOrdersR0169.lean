import RelativeCurveGeometryR0169
import RelativeGenericComparisonR0169
import RelativeMultiplicationDegreeR0169
import Theorems.Thm_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq
import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.LocalRing.Length

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
namespace VerticalOrders
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150

lemma fieldMap_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (h : Y ⟶ Z)
    (φ : Y.functionField →+* X.functionField) (ψ : Z.functionField →+* Y.functionField)
    (hφ : IsFieldMap f φ) (hψ : IsFieldMap h ψ) :
    IsFieldMap (f ≫ h) (φ.comp ψ) := by
  unfold IsFieldMap at *
  rw [← Category.assoc, hφ, Category.assoc, hψ, ← Category.assoc]
  rw [← Spec.map_comp]
  rfl

/-- The actual generic comparison intertwines the two multiplication field maps. -/
lemma multiplication_field_square
    (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
    [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)]
    (G : Law R W) (C : GenericComparison R W G) (d : ℕ)
    (φ : (Curve R W).functionField →+* (Curve R W).functionField)
    (ψ : (GenericCurve R W).functionField →+* (GenericCurve R W).functionField)
    (hφ : IsFieldMap (G.schemeNsmul d) φ)
    (hψ : IsFieldMap (C.law.schemeNsmul d) ψ) :
    ψ.comp C.field.toRingHom = C.field.toRingHom.comp φ := by
  apply ActualMultiplicationFieldNorm.fieldMap_unique
    (C.map ≫ G.schemeNsmul d) (C.field.toRingHom.comp φ)
      (ψ.comp C.field.toRingHom)
  · exact fieldMap_comp _ _ _ _ C.field_eq hφ
  · rw [← C.multiplication_eq d]
    exact fieldMap_comp _ _ _ _ hψ C.field_eq

/-- Norm comparison along the induced function-field isomorphism, with both
scalar structures fixed by the geometric multiplication maps. -/
lemma multiplication_norm_comparison
    (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
    [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)]
    (G : Law R W) (C : GenericComparison R W G) (d : ℕ)
    (φ : (Curve R W).functionField →+* (Curve R W).functionField)
    (ψ : (GenericCurve R W).functionField →+* (GenericCurve R W).functionField)
    (hφ : IsFieldMap (G.schemeNsmul d) φ)
    (hψ : IsFieldMap (C.law.schemeNsmul d) ψ)
    (g : (Curve R W).functionField) :
    C.field (fieldNorm φ g) = fieldNorm ψ (C.field g) := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  have he := @Algebra.norm_eq_of_equiv_equiv
    (Curve R W).functionField (Curve R W).functionField
    (GenericCurve R W).functionField (GenericCurve R W).functionField
    _ _ _ _ φ.toAlgebra ψ.toAlgebra C.field C.field
    (multiplication_field_square R W G C d φ ψ hφ hψ) g
  exact C.field.symm.injective (by simpa only [fieldNorm, RingEquiv.symm_apply_apply] using he)

/-- A vertical codimension-one point is the generic point of its integral fiber. -/
lemma vertical_fiber_generic {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (p : X ⟶ S) [Flat p] [GeometricallyIntegral p]
    (x : X) (hx : Order.coheight x = 1) (hv : p x ≠ genericPoint S) :
    p.fiberι (p x) (genericPoint (p.fiber (p x))) = x := by
  let z := p.fiberι (p x) (genericPoint (p.fiber (p x)))
  have hz : p z = p x := (p.fiberHomeo (p x) (genericPoint (p.fiber (p x)))).property
  have hs : z ⤳ x := by
    simpa only [Scheme.Hom.fiberι_asFiber] using
      (genericPoint_specializes (p.asFiber x)).map (p.fiberι (p x)).continuous
  by_contra hne
  have hlt : x < z := ⟨hs, fun h => hne (Specializes.antisymm hs h).eq⟩
  have hc : Order.coheight z < 1 := by
    exact (Order.coheight_le_coe_iff.mp (show Order.coheight x ≤ (1 : ℕ) by simpa using hx.le)) z hlt
  have hc0 : Order.coheight z = 0 := by simpa using hc
  have he : z = genericPoint X := by
    have hm := Order.coheight_eq_zero.mp hc0
    exact (Specializes.antisymm (hm (show z ≤ (⊤ : X) from le_top))
      (genericPoint_specializes z)).eq
  exact hv (hz.symm.trans (he ▸ GenericComparisonProof.generic_eq_of_flat p))

/-- Every positive finite surjection over the base fixes the generic point of
an integral fiber, and its inverse image there is a singleton. -/
lemma vertical_fiber_singleton {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (p : X ⟶ S) [Flat p] [GeometricallyIntegral p]
    (f : X ⟶ X) [IsFinite f] [Surjective f] (hf : f ≫ p = p)
    (x : X) (hx : Order.coheight x = 1) (hv : p x ≠ genericPoint S) :
    f x = x ∧ ∀ y : X, f y = x → y = x := by
  have hover (y : X) : p (f y) = p y := congrArg (fun h : X ⟶ S => h y) hf
  let i := p.fiberι (p x)
  have hr : Set.range (fun z : p.fiber (p x) => f (i z)) = Set.range i := by
    rw [p.range_fiberι]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change p (f (i z)) = p x
      rw [hover]
      exact (p.fiberHomeo (p x) z).property
    · intro hy
      obtain ⟨z, hz⟩ := f.surjective y
      have hz' : z ∈ Set.range i := by
        rw [p.range_fiberι]
        change p z = p x
        rw [← hover z, hz]
        exact hy
      obtain ⟨z', hz'⟩ := hz'
      exact ⟨z', (congrArg f hz').trans hz⟩
  have hi := (genericPoint_spec (p.fiber (p x))).image i.continuous
  have hi' := (genericPoint_spec (p.fiber (p x))).image (f.continuous.comp i.continuous)
  simp only [Set.image_univ, Function.comp_def] at hi hi'
  rw [hr] at hi'
  have hfix : f x = x := by
    rw [← vertical_fiber_generic p x hx hv]
    exact hi'.eq hi
  refine ⟨hfix, ?_⟩
  intro y hy
  have hpy : p y = p x := (hover y).symm.trans (congrArg p hy)
  obtain ⟨z, hz⟩ := (p.range_fiberι (p x)).symm ▸ (show y ∈ p ⁻¹' {p x} from hpy)
  have hs : x ⤳ y := by
    rw [← vertical_fiber_generic p x hx hv, ← hz]
    exact (genericPoint_specializes z).map i.continuous
  exact ((f.isDiscrete_preimage_singleton x).eq_of_specializes hs hfix hy).symm

lemma generic_norm_invariant
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (C : GenericComparison R W G) (c d : ℕ)
    (hd : 0 < d) (hcd : Nat.Coprime c d)
    (g : (Curve R W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g))
    (φ : (Curve R W).functionField →+* (Curve R W).functionField)
    (hφ : IsFieldMap (G.schemeNsmul d) φ) : fieldNorm φ g = g := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨_, _, hs, _, ψ, hψ, _⟩ :=
    ArithmeticThetaGeneralEllipticKatoR0168.general_multiplication_degree
      (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw d hd
  apply C.field.injective
  exact (multiplication_norm_comparison R W G C d φ ψ hφ hψ g).trans
    (hg.2 d hd hcd ψ hψ)

/-- Compatibility of the actual local-ring action with the function-field map. -/
lemma stalk_field_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (x : X) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom =
      φ.comp (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (f x))).mp
  change Spec.map (f.stalkMap x ≫ X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ _ =
    Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (f x)) ≫
      CommRingCat.ofHom φ) ≫ _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact hφ

/-- Finite étale local extensions multiply orders by their rank. -/
lemma local_norm_order (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsPrincipalIdealRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B] [Algebra.Etale A B]
    (a : B) (ha : a ≠ 0) :
    ((Ring.ord A (Algebra.norm A a)).toNat : ℤ) =
      (Module.finrank A B : ℤ) * ((Ring.ord B a).toNat : ℤ) := by
  letI : Module.Free A B := Module.free_of_flat_of_isLocalRing
  rw [NormOrders.ord_norm_eq_length (Module.Free.chooseBasis A B) a ha,
    IsLocalRing.length_restrictScalars A B (B ⧸ Ideal.span {a}),
    Module.length_eq_finrank, ← IsLocalRing.finrank_eq_finrank_residueField,
    ENat.toNat_mul, Nat.cast_mul, mul_comm]
  rfl

/-- At a singleton fiber the stalk is a finite étale algebra; its norm is
exactly the restriction of the geometric field norm. -/
lemma singleton_norm_order {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (x : X) (hx : Order.coheight x = 1) (hy : Order.coheight (f x) = 1)
    [IsPrincipalIdealRing (Y.presheaf.stalk (f x))]
    (hfiber : ∀ z : X, f z = f x → z = x)
    (g : X.functionField) (hg : g ≠ 0) :
    Scheme.ord (fieldNorm φ g) (f x) = (fieldDegree φ : ℤ) * Scheme.ord g x := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  letI := (f.stalkMap x).hom.toAlgebra
  letI : Module.Finite A B := IsFinite.finite_hom_stalkMap_of_forall_base_eq f x hfiber
  letI : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  letI : Module.Flat A B := Flat.stalkMap f x
  letI : Algebra.FormallyUnramified A B := FormallyUnramified.stalkMap f x
  letI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.Etale A B := Algebra.Etale.of_formallyUnramified_of_flat
  letI : Module.Free A B := Module.free_of_flat_of_isLocalRing
  letI := φ.toAlgebra
  letI : Algebra A X.functionField := (φ.comp (algebraMap A Y.functionField)).toAlgebra
  letI : IsScalarTower A Y.functionField X.functionField := .of_algebraMap_eq' rfl
  letI : IsScalarTower A B X.functionField :=
    .of_algebraMap_eq' (stalk_field_square f φ hφ x).symm
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr (by
      intro a b hab
      apply IsFractionRing.injective A Y.functionField
      apply φ.injective
      have he := DFunLike.congr_fun (stalk_field_square f φ hφ x)
      exact (he a).symm.trans ((congrArg (algebraMap B X.functionField) hab).trans (he b)))
  have hrank : fieldDegree φ = Module.finrank A B :=
    IsFractionRing.finrank_eq A Y.functionField B X.functionField
  have hnorm (a : B) : algebraMap A Y.functionField (Algebra.norm A a) =
      fieldNorm φ (algebraMap B X.functionField a) :=
    (Algebra.norm_localization A (nonZeroDivisors A) a).symm
  have hlocal (a : B) (ha : a ≠ 0) :
      Scheme.ord (fieldNorm φ (algebraMap B X.functionField a)) (f x) =
        (fieldDegree φ : ℤ) * Scheme.ord (algebraMap B X.functionField a) x := by
    rw [← hnorm]
    change ArithmeticThetaCurveDegree.principalOrder Y _ _ =
      (fieldDegree φ : ℤ) * ArithmeticThetaCurveDegree.principalOrder X _ _
    rw [ArithmeticThetaCurveDegree.principalOrder_stalk_eq_length Y (f x) hy _
      (Algebra.norm_ne_zero_iff.mpr ha),
      ArithmeticThetaCurveDegree.principalOrder_stalk_eq_length X x hx _ ha]
    change ((Ring.ord A (Algebra.norm A a)).toNat : ℤ) = _
    rw [hrank]
    exact local_norm_order A B a ha
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors B) g
  have hb : (b : B) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbF : algebraMap B X.functionField (b : B) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B X.functionField)).mpr hb
  change g * algebraMap B X.functionField (b : B) = algebraMap B X.functionField a at hab
  have ha : a ≠ 0 := by
    intro he
    have := mul_ne_zero hg hbF
    apply this
    rw [hab, he, map_zero]
  have H := hlocal a ha
  rw [← hab, NormOrders.fieldNorm_mul,
    Scheme.ord_mul (NormOrders.fieldNorm_ne_zero f φ hφ hg)
      (NormOrders.fieldNorm_ne_zero f φ hφ hbF),
    Scheme.ord_mul hg hbF, mul_add, hlocal b hb] at H
  exact add_right_cancel H

lemma normal_stalk_pid {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsPrincipalIdealRing (X.presheaf.stalk x) := by
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 3 0).mp
  exact ⟨inferInstance, fun P hp hprime =>
    IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hp)⟩

end VerticalOrders
open AlgebraicGeometry ArithmeticThetaGeometricNormR0150

/-- The normalized generic Kato function has no vertical codimension-one orders. -/
theorem relative_vertical_orders :
∀ (R : Type u)
    [CommRing R]
    [IsDomain R]
    [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [Algebra ℚ R]
    (W : WeierstrassCurve R)
    [W.IsElliptic]
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)]
    [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)]
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)]
    [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    (C : ArithmeticThetaRelativeKatoR0169.GenericComparison R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)),
    ∀ x : (ArithmeticThetaRelativeKatoR0169.Curve R W), Order.coheight x = 1 →
      ArithmeticThetaRelativeKatoR0169.structureMap R W x ≠ _root_.genericPoint (AlgebraicGeometry.Spec (CommRingCat.of R)) →
      AlgebraicGeometry.Scheme.ord g x = 0 := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG C c hc hc6 g hg x hx hv
  have hgeom := relative_curve_geometry R W
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R W) := hgeom.2.2.2.2.2.2
  obtain ⟨hf, he, hs, hrank, φ, hφ, hdegree⟩ :=
    relative_multiplication_degree R W G hG 2 (by decide)
  letI := hf
  letI := he
  letI := hs
  obtain ⟨hfix, hsingle⟩ := VerticalOrders.vertical_fiber_singleton
    (structureMap R W) (G.schemeNsmul 2) (G.schemeNsmul_over 2) x hx hv
  letI : IsIntegrallyClosed ((Curve R W).presheaf.stalk (G.schemeNsmul 2 x)) :=
    hgeom.2.2.1 _
  letI : IsPrincipalIdealRing ((Curve R W).presheaf.stalk (G.schemeNsmul 2 x)) :=
    VerticalOrders.normal_stalk_pid _ (by simpa only [hfix] using hx)
  have hg0 : g ≠ 0 := fun h => hg.1.1 (by rw [h, map_zero])
  have hnorm := VerticalOrders.generic_norm_invariant R W G C c 2 (by decide)
    (hc6.of_dvd_right (by decide : 2 ∣ 6)) g hg φ hφ
  have ho := VerticalOrders.singleton_norm_order (G.schemeNsmul 2) φ hφ x hx
    (by simpa only [hfix] using hx) (fun z hz => hsingle z (hz.trans hfix)) g hg0
  have hd : fieldDegree φ = 4 := hdegree.2
  rw [hnorm, hfix, hd] at ho
  norm_num at ho
  omega

#print axioms relative_vertical_orders
end ArithmeticThetaRelativeKatoR0169
