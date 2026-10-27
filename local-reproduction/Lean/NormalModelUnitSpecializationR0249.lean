import ArbitraryKatoUnitDefinitionsR0249

/-! Specialization of the full normalized unit through an actual normal model.
The target ring has no reducedness, domain, or Noetherian hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryKatoUnitR0249
namespace NormalModelUnitSpecialization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaSchemeLevelR0204.PointedCartesianGroupLaw

/-- Cartesian transport and elliptic uniqueness compare multiplication without
any condition on the target coefficient ring beyond ellipticity. -/
theorem comparison_nsmul
    {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} [V.IsElliptic]
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law S V) (hH : IsOriginLaw S V H) (n : ℕ) :
    H.schemeNsmul n ≫ C.map = C.map ≫ G.schemeNsmul n := by
  let L : ArithmeticThetaLocalWeierstrassR0203.SchemeLaw (structureMap R W) :=
    ⟨G.mul, G.one, G.inv, G.mul_assoc, G.one_mul, G.mul_one,
      G.inv_mul_cancel, hG.2, G.mul_natural⟩
  let J := transportedLaw C.cartesian L
  have hone {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
      pointEquiv C.cartesian t (H.one t) =
        G.one (t ≫ Spec.map (CommRingCat.ofHom ι)) := by
    apply Subtype.ext
    change (H.one t).val ≫ C.map = _
    rw [hH.1, hG.1, Category.assoc, C.pointed, Category.assoc]
  have h1 : (H.one (𝟙 _)).val = (J.one (𝟙 _)).val := by
    apply congrArg Subtype.val
    apply (pointEquiv C.cartesian (𝟙 _)).injective
    rw [hone]
    exact (Equiv.apply_symm_apply _ _).symm
  have hmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (x y : SchemeHomOver t (structureMap S V)) :
      pointEquiv C.cartesian t (H.mul t x y) =
        G.mul _ (pointEquiv C.cartesian t x) (pointEquiv C.cartesian t y) := by
    rw [WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
      V.toProjective H J h1]
    exact Equiv.apply_symm_apply _ _
  have hn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (x : SchemeHomOver t (structureMap S V)) (j : ℕ) :
      pointEquiv C.cartesian t (H.nsmul t j x) =
        G.nsmul _ j (pointEquiv C.cartesian t x) := by
    induction j with
    | zero => exact hone t
    | succ j ih =>
      rw [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ,
        WeierstrassProjModel.RelativeGroupLaw.nsmul_succ, hmul, ih]
  have hh := congrArg Subtype.val
    (hn (structureMap S V) WeierstrassProjModel.RelativeGroupLaw.idPoint n)
  have hnat := congrArg Subtype.val
    (G.nsmul_natural (structureMap R W)
      (structureMap S V ≫ Spec.map (CommRingCat.ofHom ι))
      C.map C.cartesian.w n WeierstrassProjModel.RelativeGroupLaw.idPoint)
  exact hh.trans hnat.symm

/-- The specified pointed Cartesian map pulls back the actual identity ideal. -/
theorem identity_comap
    {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι) :
    (identityIdeal R W).comap C.map = identityIdeal S V := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  have hp := ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.section_pullback
    (structureMap R W) (structureMap S V) C.map (Spec.map (CommRingCat.ofHom ι))
    C.cartesian (origin R W) (origin S V)
    (WeierstrassProjModel.kwZeroSect R W).property
    (WeierstrassProjModel.kwZeroSect S V).property C.pointed
  change (origin R W).ker.comap C.map = (origin S V).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hp.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Torsion ideals commute with the same actual comparison. -/
theorem torsion_comap
    {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic]
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law S V) (hH : IsOriginLaw S V H) (n : ℕ) :
    (torsionIdeal R W G n).comap C.map = torsionIdeal S V H n := by
  unfold torsionIdeal
  rw [← Scheme.IdealSheafData.comap_comp, ← comparison_nsmul C G hG H hH n,
    Scheme.IdealSheafData.comap_comp, identity_comap C]

/-- The whole torsion complement pulls back, including an empty target. -/
theorem complement_eq
    {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic]
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law S V) (hH : IsOriginLaw S V H) (n : ℕ) :
    complement S V H n = C.map ⁻¹ᵁ complement R W G n := by
  unfold complement
  rw [← torsion_comap C G hG H hH n, Scheme.IdealSheafData.support_comap]
  rfl

#print axioms comparison_nsmul
#print axioms complement_eq

end NormalModelUnitSpecialization

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Every normal model specializes its full normalized unit, uniquely, on
the entire actual torsion complement of the arbitrary target. -/
theorem normal_model_unit_specialization :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
      [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ M : NormalModel R W,
      ∃! v : UnitSection R W G c, FromModel R W G M c v := by
  intro R _ _ W _ G hG c hc hc6 M
  have hU : Nonempty (complement M.ring M.equation M.law c) := by
    refine ⟨⟨genericPoint (Curve M.ring M.equation), ?_⟩⟩
    exact RelativeKatoFiberSpecialization.generic_not_support
      (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal M.ring M.equation M.law c)
      ((relative_torsion_cartier M.ring M.equation M.law M.originLaw).2 c (by omega))
  letI := hU
  obtain ⟨g, hg⟩ := normalized_exists M.ring M.equation M.law M.originLaw c hc hc6
  obtain ⟨a, ha, _⟩ := RelativeKatoFiberSpecialization.source_unit
    M.ring M.equation M.law M.originLaw c hc hc6 g hg
    (complement M.ring M.equation M.law c) (by
      intro x hx ht
      exact hx ((RelativeKatoFiberSpecialization.torsion_support
        M.ring M.equation M.law c x).mpr ht))
  have e : complement R W G c ≤
      M.comparison.map ⁻¹ᵁ complement M.ring M.equation M.law c :=
    le_of_eq (NormalModelUnitSpecialization.complement_eq
      M.comparison M.law M.originLaw G hG c)
  have hu := ha.2.map (M.comparison.map.appLE _ _ e).hom
  refine ⟨hu.unit, ⟨hU, g, hg, a, ha.2, ha.1, e, hu.unit_spec⟩, ?_⟩
  intro v hv
  obtain ⟨hU', g', hg', a', ha', hfield', e', hv⟩ := hv
  have hgg : g' = g :=
    normalized_unique M.ring M.equation M.law M.originLaw c hc hc6 g' g hg' hg
  have haa : a' = a := (Curve M.ring M.equation).germToFunctionField_injective
    (complement M.ring M.equation M.law c) (hfield'.trans (hgg.trans ha.1.symm))
  apply Units.ext
  rw [hv, haa, hu.unit_spec]

#print axioms normal_model_unit_specialization
end ArithmeticThetaArbitraryKatoUnitR0249
