module

public import RelativeHorizontalOrdersR0169
public import RelativeVerticalOrdersR0169
public import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
public import Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
namespace RelativeExistence
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
  [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
  (G : Law R W) (hG : IsOriginLaw R W G)

lemma comparison_independent (C D : GenericComparison R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)) :
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) D.law c (D.field g) := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  let e := D.cartesian.isoIsPullback _ _ C.cartesian
  have he : e.hom ≫ C.map = D.map := D.cartesian.isoIsPullback_hom_fst _ _ C.cartesian
  have hep : e.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.structureMap
      (FractionRing R) (W.map (algebraMap R (FractionRing R))) =
      ArithmeticThetaGeneralEllipticKatoR0168.structureMap
      (FractionRing R) (W.map (algebraMap R (FractionRing R))) :=
    D.cartesian.isoIsPullback_hom_snd _ _ C.cartesian
  have hb : ArithmeticThetaGeneralEllipticKatoR0168.IsBaseChange
      (FractionRing R) (FractionRing R) (W.map (algebraMap R (FractionRing R)))
      (W.map (algebraMap R (FractionRing R))) C.law D.law (RingHom.id _) e.hom := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [show CommRingCat.ofHom (RingHom.id (FractionRing R)) = 𝟙 _ from rfl,
        Spec.map_id]
      apply IsPullback.of_horiz_isIso
      constructor
      simpa using hep
    · apply C.cartesian.hom_ext
      · simp only [Category.assoc, he, C.origin_eq, D.origin_eq]
        simp
      · rw [Category.assoc, hep]
        simp [ArithmeticThetaGeneralEllipticKatoR0168.origin,
          ArithmeticThetaGeneralEllipticKatoR0168.structureMap]
    · intro n
      apply C.cartesian.hom_ext
      · simp only [Category.assoc, he, C.multiplication_eq, D.multiplication_eq]
        simp only [← Category.assoc, he]
      · simp only [Category.assoc, hep, C.law.schemeNsmul_over,
          D.law.schemeNsmul_over]
  obtain ⟨α, hα, _⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_base_change
    (FractionRing R) _ C.law C.originLaw (FractionRing R) _ D.law D.originLaw
    (RingHom.id _) e.hom hb
  have hs : α.comp C.field.toRingHom = D.field.toRingHom := by
    exact ActualMultiplicationFieldNorm.fieldMap_unique D.map D.field.toRingHom
      (α.comp C.field.toRingHom) D.field_eq
      (he ▸ VerticalOrders.fieldMap_comp e.hom C.map α C.field.toRingHom hα.1 C.field_eq)
  have hv := hα.2 c hc hc6 (C.field g) hg
  have heval : α (C.field g) = D.field g := DFunLike.congr_fun hs g
  rwa [heval] at hv

/-- The normal-ring height-one intersection criterion, applied on affine neighborhoods. -/
lemma section_of_orders {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (q : X.functionField) (hq : q ≠ 0)
    (hord : ∀ x ∈ U, Order.coheight x = 1 → Scheme.ord q x = 0) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = q := by
  suffices h : q ∈ (algebraMap Γ(X, U) X.functionField).range from h
  rw [Scheme.Opens.range_algebraMap_functionField_eq_iInf]
  refine Subring.mem_iInf.mpr fun x => Subring.mem_iInf.mpr fun hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : IsIntegrallyClosed Γ(X, V) :=
    IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk hnormal V hV
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  have hp : ∀ (p : Ideal Γ(X, V)) [p.IsPrime], p.height = 1 →
      ∃ r s : Γ(X, V), s ∉ p ∧ q * algebraMap Γ(X, V) X.functionField s =
        algebraMap Γ(X, V) X.functionField r := by
    intro p _ hp
    let y : V := ⟨hV.fromSpec.base ⟨p, ‹_›⟩, by
      change hV.fromSpec (⟨p, ‹_›⟩ : PrimeSpectrum Γ(X, V)) ∈ (V : Set X)
      rw [← hV.range_fromSpec]
      exact Set.mem_range_self _⟩
    have hyp : (hV.primeIdealOf y).asIdeal = p := by
      have H := hV.fromSpec_primeIdealOf y
      exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective H)
    letI : Algebra Γ(X, V) (X.presheaf.stalk y.1) := X.presheaf.algebra_section_stalk y
    letI : IsLocalization.AtPrime (X.presheaf.stalk y.1) p := by
      have H := hV.isLocalization_stalk y
      simpa only [hyp] using H
    have hyco : Order.coheight y.1 = 1 := by
      have H := IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk y.1)
      rw [ringKrullDim_stalk_eq_coheight, hp] at H
      exact_mod_cast H
    letI : IsScalarTower Γ(X, V) (X.presheaf.stalk y.1) X.functionField :=
      functionField_isScalarTower X V y
    letI := hnormal y.1
    letI : IsPrincipalIdealRing (X.presheaf.stalk y.1) := VerticalOrders.normal_stalk_pid _ hyco
    letI : IsDiscreteValuationRing (X.presheaf.stalk y.1) :=
      ArithmeticThetaSectionCompletion.normal_stalk_dvr X
        (fun V hV _ => IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
          hnormal V hV) y.1 hyco
    have hm : q ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk y.1)) :=
      (Scheme.ord_eq_iff hyco hq).mp (hord y.1 (hVU y.2) hyco)
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hm
    obtain ⟨a, _, ha⟩ := hm
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨r, s, s.2, ?_⟩
    have H := congrArg (algebraMap (X.presheaf.stalk y.1) X.functionField) hrs
    simpa only [map_mul, ha, ← IsScalarTower.algebraMap_apply Γ(X, V) (X.presheaf.stalk y.1) X.functionField] using H
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField q hp
  refine ⟨X.presheaf.germ V x hxV a, ?_⟩
  exact (X.algebraMap_germ_eq_germToFunctionField hxV a).trans ha

lemma unit_of_orders {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (q : X.functionField) (hq : q ≠ 0)
    (hord : ∀ x ∈ U, Order.coheight x = 1 → Scheme.ord q x = 0) :
    ∃! a : Γ(X, U), X.germToFunctionField U a = q ∧ IsUnit a := by
  obtain ⟨a, ha⟩ := section_of_orders hnormal U q hq hord
  have hinv : ∀ x ∈ U, Order.coheight x = 1 → Scheme.ord q⁻¹ x = 0 := by
    intro x hx hco
    have H := Scheme.ord_mul (x := x) hq (inv_ne_zero hq)
    have Hone : Scheme.ord (1 : X.functionField) x = 0 := by
      have H := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
        (one_ne_zero (α := X.functionField))
      rw [one_mul] at H
      omega
    rw [mul_inv_cancel₀ hq, Hone, hord x hx hco, zero_add] at H
    exact H.symm
  obtain ⟨b, hb⟩ := section_of_orders hnormal U q⁻¹ (inv_ne_zero hq) hinv
  have hab : a * b = 1 := by
    apply X.germToFunctionField_injective U
    change (X.germToFunctionField U).hom (a * b) = (X.germToFunctionField U).hom 1
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hq]
  refine ⟨a, ⟨ha, ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, rfl⟩⟩, ?_⟩
  intro a' ha'
  exact X.germToFunctionField_injective U (ha'.1.trans ha.symm)

include hG in
lemma origin_fixed (n : ℕ) : origin R W ≫ G.schemeNsmul n = origin R W := by
  have ho : (G.one (𝟙 _)).val = origin R W := by
    simpa only [Category.id_comp] using hG.1 (𝟙 _)
  rw [← ho, ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
    G.nsmul_unit]

include hG in
lemma vertical_katoOrder_zero (C : GenericComparison R W G)
    (c : ℕ) (hc : 1 < c) (g : (Curve R W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g))
    (x : Curve R W) (hx : Order.coheight x = 1)
    (hv : structureMap R W x ≠ genericPoint (Spec (CommRingCat.of R))) :
    katoOrder R W G c x = 0 := by
  classical
  let K := FractionRing R
  let Wg := W.map (algebraMap R K)
  let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
  letI : Flat i := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  letI : IsPreimmersion i := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  letI : Flat C.map := MorphismProperty.of_isPullback (P := @Flat) C.cartesian.flip inferInstance
  letI : IsPreimmersion C.map :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) C.cartesian.flip inferInstance
  let o := ArithmeticThetaGeneralEllipticKatoR0168.originPoint K Wg
  have hofix : C.law.schemeNsmul c o = o := by
    have ho : (C.law.one (𝟙 _)).val = ArithmeticThetaGeneralEllipticKatoR0168.origin K Wg := by
      simpa only [Category.id_comp] using C.originLaw.1 (𝟙 _)
    have H : ArithmeticThetaGeneralEllipticKatoR0168.origin K Wg ≫
        C.law.schemeNsmul c = ArithmeticThetaGeneralEllipticKatoR0168.origin K Wg := by
      rw [← ho, ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
        C.law.nsmul_unit]
    exact congrArg (fun f => f (IsLocalRing.closedPoint K)) H
  have hong : o ≠ genericPoint (GenericCurve R W) := by
    intro H
    have hord := hg.1.2 o
    have he : ArithmeticThetaGeneralEllipticKatoR0168.katoOrder K Wg C.law c o =
        (c : ℤ)^2 - 1 := by
      change (if o = o then (c : ℤ)^2 else 0) -
        (if C.law.schemeNsmul c o = o then 1 else 0) = _
      rw [hofix]
      simp only [if_true]
    rw [he, H, NormOrders.ord_generic] at hord
    have hc' : (1 : ℤ) < c := by exact_mod_cast hc
    nlinarith
  let z := origin R W (genericPoint (Spec (CommRingCat.of R)))
  have hpo : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  have hpz : structureMap R W z = genericPoint (Spec (CommRingCat.of R)) :=
    congrArg (fun f => f (genericPoint (Spec (CommRingCat.of R)))) hpo
  have hzo : C.map o = z := by
    have H := congrArg (fun f => f (IsLocalRing.closedPoint K)) C.origin_eq
    change C.map o = origin R W (i (IsLocalRing.closedPoint K)) at H
    rw [show IsLocalRing.closedPoint K = genericPoint (Spec (CommRingCat.of K)) from
      Subsingleton.elim _ _, GenericComparisonProof.generic_eq_of_flat i] at H
    exact H
  have hzng : z ≠ genericPoint (Curve R W) := by
    intro H
    apply hong
    apply C.map.isEmbedding.injective
    rw [hzo, H, GenericComparisonProof.generic_eq_of_flat C.map]
  have hxo : x ∉ Set.range (origin R W) := by
    rintro ⟨s, hs⟩
    have hspec : z ⤳ x := hs ▸ (genericPoint_specializes s).map (origin R W).continuous
    have hne : z ≠ x := fun H => hv (H ▸ hpz)
    have hlt : x < z := ⟨hspec, fun H => hne (Specializes.antisymm hspec H).eq⟩
    have hzco : Order.coheight z < 1 :=
      (Order.coheight_le_coe_iff.mp (show Order.coheight x ≤ (1 : ℕ) by simpa using hx.le)) z hlt
    have hz0 : Order.coheight z = 0 := by simpa using hzco
    have hm := Order.coheight_eq_zero.mp hz0
    exact hzng (Specializes.antisymm (hm (show z ≤ (⊤ : Curve R W) from le_top))
      (genericPoint_specializes z)).eq
  have hgeom := relative_curve_geometry R W
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R W) := hgeom.2.2.2.2.2.2
  obtain ⟨hf, _, hs, _⟩ := relative_multiplication_degree R W G hG c (by omega)
  letI := hf
  letI := hs
  have hfix := (VerticalOrders.vertical_fiber_singleton (structureMap R W)
    (G.schemeNsmul c) (G.schemeNsmul_over c) x hx hv).1
  unfold katoOrder
  rw [hfix]
  simp only [if_neg hxo, sub_self]

include hG in
lemma relative_of_generic (C : GenericComparison R W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)) :
    IsRelativeKato R W G c g ∧ UnitOnComplement R W G c g := by
  have hg0 : g ≠ 0 := fun h => hg.1.1 (by rw [h, map_zero])
  have horders : ∀ x : Curve R W, Order.coheight x = 1 →
      Scheme.ord g x = katoOrder R W G c x := by
    intro x hx
    by_cases hv : structureMap R W x = genericPoint (Spec (CommRingCat.of R))
    · exact relative_horizontal_orders R W G hG C c hc hc6 g hg x hx hv
    · rw [relative_vertical_orders R W G hG C c hc hc6 g hg x hx hv,
        vertical_katoOrder_zero R W G hG C c hc g hg x hx hv]
  refine ⟨⟨hg0, horders, ?_⟩, ?_⟩
  · intro d hd hcd φ hφ
    exact VerticalOrders.generic_norm_invariant R W G C c d hd hcd g hg φ hφ
  · intro U hnonempty hU
    apply unit_of_orders (relative_curve_geometry R W).2.2.1 U g hg0
    intro x hx hco
    have hxo : x ∉ Set.range (origin R W) := by
      rintro ⟨s, rfl⟩
      apply hU _ hx
      refine ⟨s, ?_⟩
      exact (congrArg (fun f => f s) (origin_fixed R W G hG c)).symm
    rw [horders x hco]
    classical
    unfold katoOrder
    rw [if_neg hxo, if_neg (hU x hx), sub_self]

end RelativeExistence
open CategoryTheory AlgebraicGeometry

/-- The unique normalized relative Kato function and its genuine regular unit sections. -/
theorem relative_kato_existence :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∃ G : ArithmeticThetaRelativeKatoR0169.Law R W, ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G ∧ ∃! g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField, ArithmeticThetaRelativeKatoR0169.IsRelativeKato R W G c g ∧ ArithmeticThetaRelativeKatoR0169.UnitOnComplement R W G c g ∧ (∀ C : ArithmeticThetaRelativeKatoR0169.GenericComparison R W G, ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)) := by
  intro R _ _ _ _ _ W _ _ _ _ _ c hc hc6
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hgeom := relative_curve_geometry R W
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R W) := hgeom.2.2.2.2.2.2
  have htwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  letI : Invertible (2 : R) := htwo.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists W
    (inferInstance : Smooth (structureMap R W)) hgeom.2.2.2.2.2.2 W.isUnit_Δ
  have hG : IsOriginLaw R W G := ⟨hone, hcomm⟩
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  obtain ⟨f, hf, hfunique⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6
  let g := C.field.symm f
  have hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g) := by
    simpa only [g, RingEquiv.apply_symm_apply] using hf
  have hrel := RelativeExistence.relative_of_generic R W G hG C c hc hc6 g hg
  refine ⟨G, hG, g, ⟨hrel.1, hrel.2, ?_⟩, ?_⟩
  · intro D
    exact RelativeExistence.comparison_independent R W G C D c hc hc6 g hg
  · intro g' hg'
    apply C.field.injective
    exact (hfunique (C.field g') (hg'.2.2 C)).trans (C.field.apply_symm_apply f).symm

#print axioms relative_kato_existence
end ArithmeticThetaRelativeKatoR0169
