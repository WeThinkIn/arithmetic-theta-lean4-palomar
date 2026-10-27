import RelativeGenericComparisonR0169

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
namespace HorizontalOrdersProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange

lemma stalk_bijective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsPreimmersion f]
    (α : Y.functionField →+* X.functionField) (hα : IsFieldMap f α) (x : X) :
    Function.Bijective (f.stalkMap x).hom := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply α.injective
  have hs := DFunLike.congr_fun (stalk_field_square f α hα x)
  simp only [RingHom.comp_apply] at hs
  rw [← hs a, ← hs b, hab]

lemma order_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] [IsPreimmersion f]
    (α : Y.functionField →+* X.functionField) (hα : IsFieldMap f α)
    (x : X) (hx : Order.coheight (f x) = 1)
    (g : Y.functionField) (hg : g ≠ 0) : Scheme.ord (α g) x = Scheme.ord g (f x) := by
  let e := RingEquiv.ofBijective (f.stalkMap x).hom (stalk_bijective f α hα x)
  have hdim := ringKrullDim_eq_of_ringEquiv e
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hdim
  have hx' : Order.coheight x = 1 := by exact_mod_cast hdim.symm.trans (congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hx)
  have hlen : ArithmeticThetaDegreeAssembly.stalkFiberLength f x = 1 := by
    change (Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat = 1
    letI : IsSimpleModule (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ (f.stalkMap_surjective x), Module.length_eq_one]
    rfl
  rw [ord_map_flat f α hα x hx' hx g hg, hlen]
  simp

lemma section_range {S Sb X Xb : Scheme.{u}}
    (b : Xb ⟶ X) (i : Sb ⟶ S) (e : S ⟶ X) (eb : Sb ⟶ Xb)
    (h : IsPullback eb i b e) (x : Xb) :
    b x ∈ Set.range e ↔ x ∈ Set.range eb := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback h x s hs.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨i z, (congrArg (fun t : Sb ⟶ X => t z) h.w).symm⟩

end HorizontalOrdersProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange

/-- The generic divisor determines every horizontal codimension-one order. -/
theorem relative_horizontal_orders :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (C : ArithmeticThetaRelativeKatoR0169.GenericComparison R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)), ∀ x : (ArithmeticThetaRelativeKatoR0169.Curve R W), Order.coheight x = 1 → ArithmeticThetaRelativeKatoR0169.structureMap R W x = _root_.genericPoint (AlgebraicGeometry.Spec (CommRingCat.of R)) → AlgebraicGeometry.Scheme.ord g x = ArithmeticThetaRelativeKatoR0169.katoOrder R W G c x := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG C c hc hc6 g hg x hx hbase
  let K := FractionRing R
  let ι := algebraMap R K
  let i := Spec.map (CommRingCat.ofHom ι)
  letI : Flat i := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  letI : IsPreimmersion i := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  letI : Flat C.map := MorphismProperty.of_isPullback (P := @Flat) C.cartesian.flip inferInstance
  letI : IsPreimmersion C.map :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) C.cartesian.flip inferInstance
  have hi := GenericComparisonProof.generic_eq_of_flat i
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback C.cartesian x
    (_root_.genericPoint (Spec (CommRingCat.of K))) (hbase.trans hi.symm)
  subst x
  have hg0 : g ≠ 0 := by
    intro h
    exact hg.1.1 (by rw [h, map_zero])
  rw [← HorizontalOrdersProof.order_eq C.map C.field.toRingHom C.field_eq y hx g hg0]
  change Scheme.ord (C.field g) y = _
  rw [hg.1.2 y]
  have he : ∀ z : GenericCurve R W,
      C.map z ∈ Set.range (origin R W) ↔
        z = ArithmeticThetaGeneralEllipticKatoR0168.originPoint K (W.map ι) := by
    intro z
    rw [HorizontalOrdersProof.section_range C.map i (origin R W)
      (ArithmeticThetaGeneralEllipticKatoR0168.origin K (W.map ι))
      (section_pullback (structureMap R W)
        (ArithmeticThetaGeneralEllipticKatoR0168.structureMap K (W.map ι))
        C.map i C.cartesian _ _
        (WeierstrassProjModel.kwZeroSect R W).property
        (WeierstrassProjModel.kwZeroSect K (W.map ι)).property C.origin_eq)]
    constructor
    · rintro ⟨s, rfl⟩
      exact congrArg _ (Subsingleton.elim s (IsLocalRing.closedPoint K))
    · intro hz
      exact ⟨IsLocalRing.closedPoint K, hz.symm⟩
  have hm : G.schemeNsmul c (C.map y) = C.map (C.law.schemeNsmul c y) :=
    (congrArg (fun t : GenericCurve R W ⟶ Curve R W => t y) (C.multiplication_eq c)).symm
  classical
  simp only [katoOrder, ArithmeticThetaGeneralEllipticKatoR0168.katoOrder, hm, he]
  rfl

#print axioms relative_horizontal_orders
end ArithmeticThetaRelativeKatoR0169
