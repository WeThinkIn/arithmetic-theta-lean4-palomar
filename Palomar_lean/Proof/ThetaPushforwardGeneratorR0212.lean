module

public import ThetaEvaluationDefinitionsR0212
public import RelativeWeierstrassPresentationR0174
public import FramedSchemeQuotientR0174
public import Theorems.Thm_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul
public import Theorems.Thm_WeierstrassProjModel_projModelCR_sections_twoChart
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
public import FullLevelBaseChangeR0175

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
universe u

namespace ArithmeticThetaThetaEvaluationR0212.PushforwardGenerator
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133

/-- The canonical internal-Hom section is the transpose of the original
ideal inclusion, including its prescribed unit normalization. -/
lemma canonical_section_uncurry {X : Scheme.{u}} (I : X.IdealSheafData) :
    MonoidalClosed.uncurry (fromSection I.invModule
      ((Scheme.Modules.ihomGlobalSectionsEquiv I.module (𝟙_ X.Modules)).symm I.moduleι)) =
      (ρ_ I.module).hom ≫ I.moduleι := by
  apply Scheme.Modules.tensor_hom_ext_monoidalV2
  intro U m a
  change Γ(X, U) at a
  rw [Scheme.Modules.uncurry_app_tensorSections]
  change Scheme.Modules.ihomEval I.module (𝟙_ X.Modules) U m
    (a • I.invModule.presheaf.map (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op
      ((Scheme.Modules.ihomGlobalSectionsEquiv I.module (𝟙_ X.Modules)).symm I.moduleι)) = _
  erw [Scheme.Modules.ihomEval_smul_right,
    Scheme.Modules.ihomEval_map_ihomGlobalSectionsEquiv_symm]
  change a • I.moduleι.app U m = I.moduleι.app U ((ρ_ I.module).hom.app U
    (Scheme.Modules.tensorSections m a))
  rw [Scheme.Modules.rightUnitor_hom_app_tensorSections,
    Scheme.Modules.Hom.app_smul]

/-- Comparison between the internal-Hom dual and the dual specified by any
inverse-ideal pairing. Every arrow is an actual sheaf isomorphism. -/
def pairingComparison {X : Scheme.{u}} (I : X.IdealSheafData)
    (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) : I.invModule ≅ I.invModule := by
  haveI : IsIso ((ihom.ev I.module).app (𝟙_ X.Modules)) :=
    (MonoidalClosed.isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
      ((β_ I.module I.invModule) ≪≫ e)).1 _
  exact (λ_ I.invModule).symm ≪≫ whiskerRightIso e.symm I.invModule ≪≫
    (α_ I.invModule I.module I.invModule) ≪≫
    whiskerLeftIso I.invModule (asIso ((ihom.ev I.module).app (𝟙_ X.Modules))) ≪≫
    (ρ_ I.invModule)

lemma pairingComparison_canonical {X : Scheme.{u}} (I : X.IdealSheafData)
    (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) :
    fromSection I.invModule
      ((Scheme.Modules.ihomGlobalSectionsEquiv I.module (𝟙_ X.Modules)).symm I.moduleι) ≫
      (pairingComparison I e).hom = Filtration.idealSectionRight I e := by
  let c := fromSection I.invModule
    ((Scheme.Modules.ihomGlobalSectionsEquiv I.module (𝟙_ X.Modules)).symm I.moduleι)
  have hc : I.module ◁ c ≫ (ihom.ev I.module).app (𝟙_ X.Modules) =
      (ρ_ I.module).hom ≫ I.moduleι := canonical_section_uncurry I
  change c ≫ (λ_ I.invModule).inv ≫ e.inv ▷ I.invModule ≫
    (α_ I.invModule I.module I.invModule).hom ≫
    I.invModule ◁ (ihom.ev I.module).app (𝟙_ X.Modules) ≫
    (ρ_ I.invModule).hom = e.inv ≫ I.invModule ◁ I.moduleι ≫ (ρ_ I.invModule).hom
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, hc,
    whiskerLeft_comp]
  simp only [Category.assoc]
  erw [← rightUnitor_tensor_hom_assoc I.invModule I.module]
  erw [unitors_inv_equal]
  erw [← rightUnitor_inv_naturality_assoc e.inv]
  simp

lemma fromSection_top_one {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (fromSection M s).app ⊤ (Scheme.Modules.unitSection ⊤) = s := by
  change (1 : Γ(X, ⊤)) • M.presheaf.map
    (CategoryTheory.homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op s = s
  rw [show CategoryTheory.homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top) = 𝟙 ⊤ from
    Subsingleton.elim _ _, CategoryTheory.op_id, M.presheaf.map_id]
  exact one_smul _ _

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

/-- The accepted degree-one generation theorem, expressed in the inverse ideal
itself, with its original structural scalar action. -/
lemma origin_sections_generated (s : Γ(Q.zero.ker.invModule, ⊤)) :
    ∃ r : R, s = GradedOAlgebra.baseScalar Q.structureMap r •
      Filtration.originSection R Q := by
  let L := Q.zero.ker.invModule
  obtain ⟨r, hr⟩ := Filtration.degreeOne_generated R Q
    ((λ_ L).inv.app ⊤ s)
  refine ⟨r, ?_⟩
  have h := congrArg (fun t => (λ_ L).hom.app ⊤ t) hr
  have hc : (λ_ L).hom.app ⊤ ((λ_ L).inv.app ⊤ s) = s := by
    change ((λ_ L).inv ≫ (λ_ L).hom).app ⊤ s = s
    rw [Iso.inv_hom_id]
    rfl
  rw [hc] at h
  simpa only [Scheme.Modules.Hom.app_smul, Filtration.originDegreeOne,
    Scheme.Modules.tensorPowSection_one,
    Scheme.Modules.leftUnitor_hom_app_tensorSections,
    Scheme.Modules.unitSection, one_smul] using h

#print axioms origin_sections_generated

/-- The canonical divisor section, without an arbitrary pairing, generates
all global sections of the inverse origin ideal. -/
lemma canonical_origin_sections_generated (s : Γ(Q.zero.ker.invModule, ⊤)) :
    ∃ r : R, s = GradedOAlgebra.baseScalar Q.structureMap r •
      (Scheme.Modules.ihomGlobalSectionsEquiv Q.zero.ker.module
        (𝟙_ Q.target.Modules)).symm Q.zero.ker.moduleι := by
  let δ := pairingComparison Q.zero.ker (Filtration.originPairing R Q)
  have hz : δ.hom.app ⊤ ((Scheme.Modules.ihomGlobalSectionsEquiv Q.zero.ker.module
      (𝟙_ Q.target.Modules)).symm Q.zero.ker.moduleι) = Filtration.originSection R Q := by
    have h := congrArg (fun f => f.app ⊤ (Scheme.Modules.unitSection ⊤))
      (pairingComparison_canonical Q.zero.ker (Filtration.originPairing R Q))
    change δ.hom.app ⊤ ((fromSection _ _).app ⊤ (Scheme.Modules.unitSection ⊤)) = _ at h
    rw [fromSection_top_one] at h
    exact h
  obtain ⟨r, hr⟩ := origin_sections_generated R Q (δ.hom.app ⊤ s)
  refine ⟨r, ?_⟩
  apply (Scheme.Modules.Hom.mono_iff_injective δ.hom).mp inferInstance ⊤
  rw [Scheme.Modules.Hom.app_smul, hz]
  exact hr

#print axioms canonical_origin_sections_generated

lemma canonical_origin_section_ne_zero :
    (Scheme.Modules.ihomGlobalSectionsEquiv Q.zero.ker.module
      (𝟙_ Q.target.Modules)).symm Q.zero.ker.moduleι ≠ 0 := by
  intro hzero
  have h := congrArg (fun f => f.app ⊤ (Scheme.Modules.unitSection ⊤))
    (pairingComparison_canonical Q.zero.ker (Filtration.originPairing R Q))
  change (pairingComparison Q.zero.ker (Filtration.originPairing R Q)).hom.app ⊤
    ((fromSection _ _).app ⊤ (Scheme.Modules.unitSection ⊤)) =
      Filtration.originSection R Q at h
  rw [fromSection_top_one, hzero, map_zero] at h
  exact Filtration.originSection_ne_zero R Q h.symm

lemma origin_sections_equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap Q.zero.ker.invModule ⊤
    Nonempty (Γ(Q.zero.ker.invModule, ⊤) ≃ₗ[R] R) := by
  let L := Q.zero.ker.invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap L ⊤
  let P := (Q.zero.ker ^ 1).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap P ⊤
  obtain ⟨ε₀⟩ := SectionExact.origin_first_sections R Q
  let δ : L ≅ P := eqToIso (congrArg Scheme.IdealSheafData.invModule
    (pow_one Q.zero.ker).symm)
  exact ⟨FibreCohomology.sectionsIsoLinear Q.structureMap δ ⊤ ≪≫ₗ ε₀⟩

/-- Bijectivity uses the given structural scalar action, not a choice of
abstract rank-one identification as the resulting map. -/
lemma canonical_origin_scalar_bijective :
    Function.Bijective (fun r : R => GradedOAlgebra.baseScalar Q.structureMap r •
      (Scheme.Modules.ihomGlobalSectionsEquiv Q.zero.ker.module
        (𝟙_ Q.target.Modules)).symm Q.zero.ker.moduleι) := by
  let L := Q.zero.ker.invModule
  let z : Γ(L, ⊤) := (Scheme.Modules.ihomGlobalSectionsEquiv Q.zero.ker.module
    (𝟙_ Q.target.Modules)).symm Q.zero.ker.moduleι
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap L ⊤
  obtain ⟨ε⟩ := origin_sections_equiv R Q
  have hz : ε z ≠ 0 := by
    intro hz
    apply canonical_origin_section_ne_zero R Q
    change z = 0
    exact ε.injective (hz.trans ε.map_zero.symm)
  refine ⟨?_, fun s => ?_⟩
  · intro r t h
    simp only [GeometricCubic.baseScalar_eq_const] at h
    change r • z = t • z at h
    have h' := congrArg ε h
    exact mul_right_cancel₀ hz (by simpa only [map_smul, smul_eq_mul] using h')
  · obtain ⟨r, hr⟩ := canonical_origin_sections_generated R Q s
    exact ⟨r, hr.symm⟩

#print axioms canonical_origin_scalar_bijective

open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

/-- The accepted framed-curve API instantiated by the specified Weierstrass
scheme, structural map and group law. -/
def weierstrassFrame (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) : FramedCurve R where
  target := Curve R W
  structureMap := ArithmeticThetaRelativeKatoR0169.structureMap R W
  law := toGRJ G
  geometry := ArithmeticThetaFullLevelCoverR0175.BaseChange.geometry R W G
  dimension := WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  hodge := by
    have hz : ((toGRJ G).one (𝟙 (Base R))).val = origin R W := by
      change (G.one (𝟙 (Base R))).val = origin R W
      simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))
    rw [hz]
    exact ArithmeticThetaRelativeCyclicQuotientR0173.FramedSchemeQuotientR0174.OriginHodge.source_hodge_trivial R W

lemma weierstrassFrame_zero (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) : (weierstrassFrame R W G hG).zero = origin R W := by
  change (G.one (𝟙 (Base R))).val = origin R W
  simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))

/-- Regular functions over every base open are exactly structural scalars. -/
lemma weierstrass_structure_app_bijective (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (U : (Base R).Opens) :
    Function.Bijective ((structureMap R W).app U) :=
  (weierstrassFrame R W G hG).structure_app_bijective U

#print axioms weierstrass_structure_app_bijective

namespace Transport
open NeronModelInfra

variable (e : Q.target ≅ Q.target) (he : e.hom ≫ Q.structureMap = Q.structureMap)

include he in
lemma inv_over : e.inv ≫ Q.structureMap = Q.structureMap := by
  calc
    e.inv ≫ Q.structureMap = e.inv ≫ (e.hom ≫ Q.structureMap) := by rw [he]
    _ = Q.structureMap := by simp

/-- Transport of points through the given geometric automorphism. -/
def pointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    SchemeHomOver t Q.structureMap ≃ SchemeHomOver t Q.structureMap where
  toFun x := ⟨x.val ≫ e.inv, by rw [Category.assoc, inv_over R Q e he, x.property]⟩
  invFun x := ⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

lemma point_natural {T U : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (s : U ⟶ Spec (.of R)) (q : U ⟶ T) (hq : q ≫ t = s)
    (x : SchemeHomOver t Q.structureMap) :
    pointEquiv R Q e he s (GoodReductionJacobian.schemeHomOverComp q hq x) =
      GoodReductionJacobian.schemeHomOverComp q hq (pointEquiv R Q e he t x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- The group law obtained by conjugation with the actual automorphism. -/
def law : GoodReductionJacobian.RelativeGroupLaw R Q.structureMap where
  mul t x y := (pointEquiv R Q e he t).symm
    (Q.law.mul t (pointEquiv R Q e he t x) (pointEquiv R Q e he t y))
  one t := (pointEquiv R Q e he t).symm (Q.law.one t)
  inv t x := (pointEquiv R Q e he t).symm (Q.law.inv t (pointEquiv R Q e he t x))
  mul_assoc t x y z := by
    apply (pointEquiv R Q e he t).injective
    simp only [Equiv.apply_symm_apply, Q.law.mul_assoc]
  one_mul t x := by
    apply (pointEquiv R Q e he t).injective
    simp only [Equiv.apply_symm_apply, Q.law.one_mul]
  mul_one t x := by
    apply (pointEquiv R Q e he t).injective
    simp only [Equiv.apply_symm_apply, Q.law.mul_one]
  inv_mul_cancel t x := by
    apply (pointEquiv R Q e he t).injective
    simp only [Equiv.apply_symm_apply, Q.law.inv_mul_cancel]
  mul_natural t s q hq x y := by
    apply (pointEquiv R Q e he s).injective
    rw [point_natural]
    simp only [Equiv.apply_symm_apply, Q.law.mul_natural, point_natural]

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaRelativeIsogenyHodgeR0172

/-- The new origin is the old origin translated by `e`; its cotangent frame
is transported by the differential of that same scheme automorphism. -/
def frame : FramedCurve R where
  target := Q.target
  structureMap := Q.structureMap
  law := law R Q e he
  geometry := Q.geometry
  dimension := Q.dimension
  hodge := by
    letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
    let d := differentialMap Q.structureMap Q.structureMap e.hom (by simpa using he)
    haveI : IsIso d :=
      EtaleHodgePullbackIsomorphismR0172.differentialMap_isIso_etale
        Q.structureMap Q.structureMap e.hom he
    obtain ⟨η⟩ := Q.hodge
    exact ⟨η ≪≫ (Scheme.Modules.pullback Q.zero).mapIso (asIso d).symm ≪≫
      (Scheme.Modules.pullbackComp Q.zero e.hom).app Q.structureMap.kaehler⟩

lemma frame_zero : (frame R Q e he).zero = Q.zero ≫ e.hom := rfl

#print axioms frame
end Transport

lemma canonical_section_scalar_bijective_at (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (p : NeronModelInfra.SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    Function.Bijective (fun r : R => GradedOAlgebra.baseScalar (structureMap R W) r •
      (Scheme.Modules.ihomGlobalSectionsEquiv p.val.ker.module
        (𝟙_ (Curve R W).Modules)).symm p.val.ker.moduleι) := by
  obtain ⟨τ, hτ, hτmul⟩ := G.exists_iso_comp_eq_and_comp_hom_eq_mul p
  let Q₀ := weierstrassFrame R W G hG
  let Q₁ := Transport.frame R Q₀ τ hτ
  have hz : Q₁.zero = p.val := by
    rw [Transport.frame_zero, weierstrassFrame_zero]
    have h := hτmul (𝟙 (Base R)) (G.one (𝟙 (Base R)))
    rw [G.one_mul] at h
    have hp : WeierstrassProjModel.schemeHomOverComp (𝟙 (Base R))
        (Category.comp_id _) p = p := Subtype.ext (Category.id_comp _)
    rw [hp] at h
    simpa only [hG.1, Category.id_comp] using h
  have h := canonical_origin_scalar_bijective R Q₁
  change Function.Bijective (fun r : R => GradedOAlgebra.baseScalar (structureMap R W) r •
    (Scheme.Modules.ihomGlobalSectionsEquiv Q₁.zero.ker.module
      (𝟙_ (Curve R W).Modules)).symm Q₁.zero.ker.moduleι) at h
  rw [hz] at h
  exact h

#print axioms canonical_section_scalar_bijective_at

/-- The actual projective Weierstrass scheme is covered by the Y and Z charts. -/
def weierstrassTwoAffineCover (W : WeierstrassCurve R) : (Curve R W).TwoAffineOpenCover := by
  let A := WeierstrassProjModel.projModelGradingCR W.toProjective
  let Y : WeierstrassProjModel.ProjModelRingCR W.toProjective :=
    Ideal.Quotient.mk _ (MvPolynomial.X 1)
  let Z : WeierstrassProjModel.ProjModelRingCR W.toProjective :=
    Ideal.Quotient.mk _ (MvPolynomial.X 2)
  have hY : Y ∈ A 1 := HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
  have hZ : Z ∈ A 1 := HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
  refine ⟨Proj.basicOpen A Y, Proj.basicOpen A Z,
    Proj.isAffineOpen_basicOpen A Y hY one_pos,
    Proj.isAffineOpen_basicOpen A Z hZ one_pos, ?_, ?_⟩
  · exact top_le_iff.mp
      (P2MW.S_WeierstrassProjModel_projModelCR_sections_twoChart.K1bAlphaAux.top_le_sup W.toProjective)
  · rw [← Proj.basicOpen_mul]
    exact Proj.isAffineOpen_basicOpen A (Y * Z) (SetLike.mul_mem_graded hY hZ)
      (by decide : 0 < 1 + 1)

/-- Localization on the standard affine basis upgrades global bijectivity to
an isomorphism on every open. -/
lemma isIso_of_bijective_global {A : CommRingCat.{u}} {F H : (Spec A).Modules}
    (f : F ⟶ H) [IsIso F.fromTildeΓ] [IsIso H.fromTildeΓ]
    (hf : Function.Bijective (f.app ⊤)) : IsIso f := by
  have ht : IsIso ((modulesSpecToSheaf.map f).hom.app (Opposite.op ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  haveI : IsIso (modulesSpecToSheaf.map f) := isLocalizing_of_isIso_app_top ht
    ((isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance)
    ((isIso_fromTildeΓ_iff_isLocalizing H).mp inferInstance)
  exact isIso_of_reflects_iso f modulesSpecToSheaf

open ArithmeticThetaFullLevelCoverR0175

lemma evenPoint_over (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G 4 (𝟙 (Base R))) :
    evenPoint R W G M ≫ structureMap R W = 𝟙 (Base R) :=
  (G.mul (𝟙 _) (G.nsmul (𝟙 _) (4 / 2) M.x) (G.nsmul (𝟙 _) (4 / 2) M.y)).property

lemma theta_scalar_bijective (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (M : FullLevel R W G 4 (𝟙 (Base R))) :
    Function.Bijective (fun r : R => GradedOAlgebra.baseScalar (structureMap R W) r •
      thetaSection R W G M) :=
  canonical_section_scalar_bijective_at R W G hG
    ⟨evenPoint R W G M, evenPoint_over R W G M⟩

#print axioms theta_scalar_bijective

lemma fromSection_top_apply {X : Scheme.{u}} (F : X.Modules) (s : Γ(F, ⊤))
    (a : Γ(X, ⊤)) : (fromSection F s).app ⊤ a = a • s := by
  rw [fromSection_apply]
  rw [show CategoryTheory.homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top) = 𝟙 ⊤ from
    Subsingleton.elim _ _, CategoryTheory.op_id, F.presheaf.map_id]
  rfl

lemma generator_global_bijective (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (M : FullLevel R W G 4 (𝟙 (Base R))) :
    Function.Bijective ((generator R W G M).app ⊤) := by
  apply (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)).mp
  change Function.Bijective (fun r : R => (thetaMap R W G M).app ⊤
    ((structureMap R W).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))
  convert theta_scalar_bijective R W G hG M using 1
  funext r
  exact fromSection_top_apply (thetaLine R W G M) (thetaSection R W G M)
    ((structureMap R W).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

#print axioms generator_global_bijective

end ArithmeticThetaThetaEvaluationR0212.PushforwardGenerator

namespace ArithmeticThetaThetaEvaluationR0212
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 PushforwardGenerator

set_option maxHeartbeats 1000000 in
/-- The specified structural-scalar map to the theta pushforward is an
isomorphism of sheaves, hence gives a bijection on every base open. -/
theorem theta_pushforward_generator
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 4 (𝟙 (Base R))) : IsIso (generator R W G M) := by
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hI : (thetaIdeal R W G M).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (evenPoint R W G M) (evenPoint_over R W G M)
  have hL : Scheme.Modules.IsInvertible (thetaLine R W G M) := hI.isInvertible_invModule
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) (pushforwardLine R W G M)) :=
    Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial (A := R) (structureMap R W)
      (weierstrassTwoAffineCover R W) (thetaLine R W G M) hL.1
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) (𝟙_ (Base R).Modules)) :=
    Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial (R := CommRingCat.of R) _
      (fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩)
  exact isIso_of_bijective_global (A := CommRingCat.of R)
    (generator R W G M) (generator_global_bijective R W G hG M)

#print axioms theta_pushforward_generator
end ArithmeticThetaThetaEvaluationR0212
