import RelativeKatoDefinitionsR0169
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
namespace GenericComparisonProof
open CategoryTheory AlgebraicGeometry

lemma generalizing_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    GeneralizingMap f := by
  letI := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
    (topologically GeneralizingMap)
  have hp : @Flat ≤ topologically GeneralizingMap := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Flat),
      HasRingHomProperty.eq_affineLocally (P := topologically GeneralizingMap)]
    apply affineLocally_le
    intro R S _ _ g hg
    exact hg.generalizingMap_comap
  exact hp _ _ f inferInstance

lemma generic_eq_of_flat {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x, hx, hfx⟩ := generalizing_of_flat f
    (genericPoint_specializes (f (genericPoint X)))
  have he : x = genericPoint X := (hx.antisymm (genericPoint_specializes x)).eq
  simpa only [he] using hfx

lemma field_equiv {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] [IsPreimmersion f] :
    ∃ e : Y.functionField ≃+* X.functionField,
      ArithmeticThetaGeometricNormR0150.IsFieldMap f e.toRingHom := by
  have h := generic_eq_of_flat f
  let φ : Y.presheaf.stalk (genericPoint Y) →+* X.presheaf.stalk (genericPoint X) :=
    (f.stalkMap (genericPoint X)).hom.comp
      (Y.presheaf.stalkCongr (.of_eq h.symm)).hom.hom
  have hs : Function.Surjective φ :=
    (f.stalkMap_surjective _).comp (ConcreteCategory.bijective_of_isIso _).2
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, ?_⟩
  change X.fromSpecStalk _ ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ _
  have square (x : X) (y : Y) (hy : f x = y) :
      X.fromSpecStalk x ≫ f =
        Spec.map ((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap x) ≫
          Y.fromSpecStalk y := by
    subst y
    simpa using (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  exact square _ _ h

end GenericComparisonProof
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaGeneralEllipticKatoR0168.BaseChange

/-- The actual pointed generic fibre comparison, including its induced field isomorphism. -/
theorem relative_generic_comparison :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
      [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
      (G : Law R W) (hG : IsOriginLaw R W G), Nonempty (GenericComparison R W G) := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG
  let K := FractionRing R
  let ι := algebraMap R K
  let Wb := W.map ι
  let fb := ArithmeticThetaGeneralEllipticKatoR0168.structureMap K Wb
  obtain ⟨α, hα⟩ := projModel_isPullback_baseChange_ring W.toProjective K
  obtain ⟨b, hb, he⟩ := pointed_cartesian ι fb α hα G (kwZeroSect K Wb)
  have he' : ArithmeticThetaGeneralEllipticKatoR0168.origin K Wb ≫ b =
      Spec.map (CommRingCat.ofHom ι) ≫ origin R W := he.trans (hG.1 _)
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι (structureMap R W) fb b hb G
  have hH : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw K Wb H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [ho, hG.1, Category.assoc, he']
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z) (kwZeroSect K Wb).property).trans
            (Category.comp_id t)).symm)
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  letI : Flat (Spec.map (CommRingCat.ofHom ι)) := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  letI : IsPreimmersion (Spec.map (CommRingCat.ofHom ι)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  letI : Flat b := MorphismProperty.of_isPullback (P := @Flat) hb.flip inferInstance
  letI : IsPreimmersion b :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hb.flip inferInstance
  obtain ⟨e, hefield⟩ := GenericComparisonProof.field_equiv b
  exact ⟨{
    law := H
    originLaw := hH
    map := b
    cartesian := hb
    origin_eq := he'
    multiplication_eq := nsmul_comp ι fb b hb G H hm ho
    field := e
    field_eq := hefield }⟩

#print axioms relative_generic_comparison
end ArithmeticThetaRelativeKatoR0169
