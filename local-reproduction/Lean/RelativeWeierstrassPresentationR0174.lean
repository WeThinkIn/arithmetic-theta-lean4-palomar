import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso_morphismRestrict_basicOpen_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_mul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChart_of_section_invModule_global
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem_global
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import P2M.Util
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import SplitCyclicKernelR0173
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isImmersion_proj

/-! General origin-section prerequisites for the frozen relative presentation.
The bundled data below are precisely geometric hypotheses of the target;
no equation, coordinates, basis, relation, or projective presentation is assumed.
Generalized from the frozen r0173 reference; all helpers are owned here. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe u
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169

structure FramedCurve (R : Type u) [CommRing R] where
  target : Scheme.{u}
  structureMap : target ⟶ Spec (.of R)
  law : GoodReductionJacobian.RelativeGroupLaw R structureMap
  geometry : GoodReductionJacobian.AbelianSchemePropertyBundle R structureMap
  dimension : SmoothOfRelativeDimension 1 structureMap
  hodge : Nonempty ((SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules) ≅
    (Scheme.Modules.pullback (law.one (𝟙 _)).val).obj structureMap.kaehler)

namespace FramedCurve
variable {R : Type u} [CommRing R] (Q : FramedCurve R)
def zero : Spec (.of R) ⟶ Q.target := (Q.law.one (𝟙 _)).val
lemma zero_over : Q.zero ≫ Q.structureMap = 𝟙 _ := (Q.law.one (𝟙 _)).property
lemma smooth_dimension_one : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
lemma hodge_trivial : Nonempty ((SheafOfModules.unit (Spec (.of R)).ringCatSheaf :
    (Spec (.of R)).Modules) ≅ (Scheme.Modules.pullback Q.zero).obj Q.structureMap.kaehler) := Q.hodge
lemma zero_ideal_invertible : Q.zero.ker.IsInvertible := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id Q.zero Q.zero_over
variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
theorem geometrically_integral : GeometricallyIntegral Q.structureMap :=
  Q.geometry.geometricallyIntegral_of_commRing

/-- The actual quotient is integral, locally Noetherian and normal. -/
theorem total_geometry : IsIntegral Q.target ∧ IsLocallyNoetherian Q.target ∧
    ∀ x : Q.target, IsIntegrallyClosed (Q.target.presheaf.stalk x) := by
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : GeometricallyIntegral Q.structureMap := geometrically_integral Q
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) := MulEquiv.isDomain R e.symm.toMulEquiv
  letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) := IsIntegrallyClosed.of_equiv e
  exact ⟨GeometricallyIntegral.isIntegral_of_isLocallyNoetherian Q.structureMap,
    LocallyOfFiniteType.isLocallyNoetherian Q.structureMap,
    fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk Q.structureMap x).2⟩

/-- Regular functions on the framed curve over an open of the base come uniquely
from that open. This uses the actual structural sheaf map. -/
theorem structure_app_bijective (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Bijective (Q.structureMap.app U) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : GeometricallyIntegral Q.structureMap := geometrically_integral Q
  letI : GeometricallyConnected Q.structureMap := ⟨by
    intro K _ y Z fst snd hpb
    letI : IsIntegral Z :=
      (geometrically_integral Q).1 y fst snd hpb
    infer_instance⟩
  exact bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
    Q.structureMap U


end FramedCurve

open Opposite
namespace FibreCohomology
open P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one.GenusH1
open P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.T0aKS

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

def affineKaehlerSections (U : X.Opens) (hU : IsAffineOpen U) :
    letI := c.sectionsAlgebra U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler U
    Ω[Γ(X,U)⁄R] ≃ₗ[R] Γ(c.kaehler,U) := by
  letI := c.sectionsAlgebra U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler U
  letI := Scheme.TwoAffineOpenCover.isScalarTower_sections c c.kaehler U
  let e : Ω[Γ(X,U)⁄R] ≃ₗ[Γ(X,U)] Γ(c.kaehler,U) :=
    LinearEquiv.ofBijective (c.kaehlerToSectionsₗ U)
      (c.kaehlerToSections_bijective_of_isAffineOpen hU)
  exact e.restrictScalars R

lemma kaehlerH0_equiv (𝒱 : X.TwoAffineOpenCover) :
    Nonempty ((𝒱.kaehlerSections c).H0 ≃ₗ[R] (𝒱.sectionsOf c c.kaehler).H0) := by
  apply (h0h1_of_equiv _ _ (affineKaehlerSections c 𝒱.U0 𝒱.isAffineOpen_U0)
    (affineKaehlerSections c 𝒱.U1 𝒱.isAffineOpen_U1)
    (affineKaehlerSections c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf) ?_ ?_).1
  · intro m
    exact res_toSh c inf_le_left m
  · intro m
    exact res_toSh c inf_le_right m

def sectionsIsoLinear {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c N U
    Γ(M,U) ≃ₗ[R] Γ(N,U) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c N U
  refine {
    toFun := e.hom.app U
    invFun := e.inv.app U
    map_add' := fun a b => map_add _ a b
    map_smul' := ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro r s
    exact Scheme.Modules.Hom.app_smul e.hom
      ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r) s
  · intro s
    change (e.hom ≫ e.inv).app U s = s
    rw [e.hom_inv_id]; rfl
  · intro s
    change (e.inv ≫ e.hom).app U s = s
    rw [e.inv_hom_id]; rfl

lemma sectionsH0_equiv {M N : X.Modules} (e : M ≅ N) (𝒱 : X.TwoAffineOpenCover) :
    Nonempty ((𝒱.sectionsOf c M).H0 ≃ₗ[R] (𝒱.sectionsOf c N).H0) := by
  apply (h0h1_of_equiv _ _ (sectionsIsoLinear c e 𝒱.U0)
    (sectionsIsoLinear c e 𝒱.U1) (sectionsIsoLinear c e (𝒱.U0 ⊓ 𝒱.U1)) ?_ ?_).1
  · intro m
    exact (congrArg (fun f => f.hom m)
      (e.hom.val.naturality (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op)).symm
  · intro m
    exact (congrArg (fun f => f.hom m)
      (e.hom.val.naturality (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op)).symm

open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

lemma group_kaehlerH0_finrank {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g]
    [SmoothOfRelativeDimension 1 g] [GeometricallyIntegral g]
    (L : GoodReductionJacobian.RelativeGroupLaw K g) (𝒱 : Y.TwoAffineOpenCover) :
    Module.finrank K (𝒱.kaehlerSections g).H0 = 1 := by
  letI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton g
  obtain ⟨ω,hω,-⟩ := L.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq g 1
  obtain ⟨e,-⟩ := iso_of_global_frame ω hω
  let eΩ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ g.kaehler :=
    e ≪≫ detOneIso Y g.kaehler
  obtain ⟨eH⟩ := sectionsH0_equiv g eΩ 𝒱
  obtain ⟨eK⟩ := kaehlerH0_equiv g 𝒱
  obtain ⟨⟨eU⟩,-⟩ := unit_equiv 𝒱 g
  rw [eK.finrank_eq, ← eH.finrank_eq, eU.finrank_eq]
  exact (AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed 𝒱 g).2.2.1

open AlgebraicCurve CategoryTheory.Limits NeronModelInfra

lemma group_curveModel_genus {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g]
    [SmoothOfRelativeDimension 1 g] [GeometricallyIntegral g]
    (LG : GoodReductionJacobian.RelativeGroupLaw K g)
    (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L)
    (e : M.C ≅ Y) (he : e.hom ≫ g = M.toBase)
    (Kc : Divisor K L) (g' : ℕ)
    (hRR : ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') :
    g' = 1 := by
  letI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton g
  obtain ⟨𝒱,-⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed K g
    ((LG.one (𝟙 _)).val (IsLocalRing.closedPoint K))
  letI := (baseToFunctionField g).toAlgebra
  have hgenus : genusFF K Y.functionField = 1 := by
    rw [← (finite_H0_H1_structureSheaf_of_isAlgClosed 𝒱 g).2.2.2,
      ← 𝒱.finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral g]
    exact group_kaehlerH0_finrank g LG 𝒱
  letI := M.functionFieldAlgebra
  obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase g e he
  exact (M.eq_genusFF_of_forall_ell_sub_ell_eq hRR).trans
    ((genusFF_eq_of_algEquiv M.ffAlgEquiv).trans
      ((genusFF_eq_of_algEquiv φ).trans hgenus))

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

lemma origin_geometric_genus (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ Spec (.of R)) (L : Type u) [Field L] [Algebra K L]
    (M : CurveModel K L) (e : M.C ≅ pullback Q.structureMap s)
    (he : e.hom ≫ pullback.snd Q.structureMap s = M.toBase) (Kc : Divisor K L) (g' : ℕ)
    (hRR : ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') :
    g' = 1 := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one
  letI : GeometricallyIntegral Q.structureMap := Q.geometrically_integral
  let QK := Q.geometry.baseChange_of_field s
  obtain ⟨LG⟩ := QK.hasGroupLaw
  exact group_curveModel_genus (pullback.snd Q.structureMap s) LG L M e he Kc g' hRR

open AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory

/-- Positive origin powers have vanishing H¹ and rank equal to the pole bound
on every field fibre, with its actual structural map. -/
lemma origin_fibre_positive_cohomology (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] (sK : Spec (.of K) ⟶ Spec (.of R))
    (𝒱 : (pullback Q.structureMap sK).TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).H1 ∧
    Module.finrank K (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).H0 = m := by
  let c := Q.structureMap
  let C := Q.target
  let ε := Q.law.one (𝟙 _)
  letI : IsProper c := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 c := Q.smooth_dimension_one
  letI : GeometricallyIntegral c := Q.geometrically_integral
  have hg := origin_geometric_genus R Q

  let S : Scheme.{u} := Spec (CommRingCat.of R)
  let ψ : SchemeHomOver sK (𝟙 S) := ⟨sK, Category.comp_id _⟩
  let g' : pullback c sK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg'π : g' ≫ π = pullback.fst c sK := by
    simp only [g', π, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c (𝟙 S) = pullback.snd c sK ≫ sK := by
    simp only [g', baseChangeSnd, pullback.lift_snd]
    rfl

  have hcart : IsPullback g' (pullback.snd c sK) (pullback.snd c (𝟙 S)) sK := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c (𝟙 S))
    rw [hg'π, Category.comp_id]
    exact IsPullback.of_hasPullback c sK

  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hI : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 hεc
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσ : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S := by
    simp only [rigSection, pullback.lift_snd]
  have hI' : (rigSection c (𝟙 S) ε).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ
  have hσπ : rigSection c (𝟙 S) ε ≫ π = ε.1 := by
    simp only [rigSection, π, pullback.lift_fst, Category.id_comp]

  obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
    (rigSection c (𝟙 S) ε) hσπ hI hI' m).1

  let N : C.Modules := (ε.1.ker ^ m).invModule
  let M : (pullback c (𝟙 S)).Modules :=
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)).L ⊗ sectionTwist c ε (𝟙 S) m
  have eS : (Scheme.Modules.pullback π).obj N ≅ M :=
    eπ ≪≫ (λ_ (sectionTwist c ε (𝟙 S) m)).symm
  have e : (Scheme.Modules.pullback (pullback.fst c sK)).obj N ≅ (Scheme.Modules.pullback g').obj M :=
    (Scheme.Modules.pullbackCongr hg'π.symm).app N ≪≫ ((Scheme.Modules.pullbackComp g' π).app N).symm ≪≫
      (Scheme.Modules.pullback g').mapIso eS

  obtain ⟨𝒲, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c (𝟙 S) M sK
      (pullback.snd c sK) g' hcart ((Scheme.Modules.pullback (pullback.fst c sK)).obj N) e 𝒱

  obtain ⟨h1, h0⟩ :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
      R c ε 1 hg (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)) (fibrewiseAlgEquivZero_unit (𝟙 S)) m (by omega) K sK 𝒲
  haveI := h1
  exact ⟨eH1.toEquiv.subsingleton, eH0.finrank_eq.trans (by simpa using h0)⟩

/-- On every geometric fibre the two-chart cover is constructed, and the
positive-degree cohomology statements hold for every pole bound. -/
lemma origin_exists_fibre_positive_cohomology_cover
    (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (K : Type u) [Field K] [IsAlgClosed K] (sK : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ 𝒱 : (pullback Q.structureMap sK).TwoAffineOpenCover, ∀ m : ℕ, 0 < m →
      Subsingleton (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
        ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
          (((Q.zero).ker ^ m).invModule))).H1 ∧
      Module.finrank K (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
        ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
          (((Q.zero).ker ^ m).invModule))).H0 = m := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one
  letI : GeometricallyIntegral Q.structureMap := Q.geometrically_integral
  obtain ⟨LG⟩ := (Q.geometry.baseChange_of_field sK).hasGroupLaw
  obtain ⟨𝒱,-⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed K
    (pullback.snd Q.structureMap sK) ((LG.one (𝟙 _)).val (IsLocalRing.closedPoint K))
  exact ⟨𝒱, fun m hm => origin_fibre_positive_cohomology R Q m hm K sK 𝒱⟩

end FibreCohomology
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
end

/-! The following owned cohomology implementation is adapted from the checked
library proofs of exists_cochain_baseChange_equiv_of_locallyTrivial,
nonempty_cech_baseChange_equiv_of_locallyTrivial, and
finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc.
It uses the existing OrderedAffineCover.comap from the frozen
ProperFormalFunctions module. Importing the newer library comap module would
duplicate its declarations. All new implementation names stay in this module's
PositiveSections namespace; no frozen source or declaration is changed.
The final Actual.positive_sections_baseChange instantiates the general argument
using proved vanishing for this framed curve's origin powers. -/
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false


p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.AlgebraicGeometry TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Spec Scheme Scheme.Hom.preimage_mono IsSeparated isAffineOpen_top isAffineHom_diagonal_iff Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules IsAffineHom OModulePresheaf OModulePresheaf.res_res OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap OModulePresheaf.ofModules Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_res cochain d d_apply unit res res_refl obj res_comp ofModules"
namespace CechBaseChange
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section EqRes
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {ρ : Y ⟶ Spec (.of R)} (G : OModulePresheaf ρ)

def eqRes {U U' : Y.Opens} (h : U = U') : G.obj U' ≃ₗ[R] G.obj U :=
  LinearEquiv.ofLinear (G.res h.le) (G.res h.ge)
    (by rw [← G.res_comp h.le h.ge]; exact G.res_refl U)
    (by rw [← G.res_comp h.ge h.le]; exact G.res_refl U')

theorem eqRes_apply {U U' : Y.Opens} (h : U = U') (x : G.obj U') : eqRes G h x = G.res h.le x := rfl

theorem res_res_eq_res_res {U V V' W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ V') (h₄ : V' ≤ W) (x : G.obj W) :
    G.res h₁ (G.res h₂ x) = G.res h₃ (G.res h₄ x) := by
  rw [G.res_res, G.res_res]

end EqRes

section Affine
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (𝒰 : X.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated' [IsSeparated π] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter' [IsSeparated π] {i : ℕ} (s : 𝒰.Idx i) : IsAffineOpen (𝒰.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → 𝒰.ι), IsAffineOpen (⨅ j, 𝒰.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, 𝒰.U (t j)) = 𝒰.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact 𝒰.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), 𝒰.U (t j)) = 𝒰.U (t 0) ⊓ (⨅ j : Fin (m + 1), 𝒰.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated' π (𝒰.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

end Affine

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (M : X.Modules)
  (A : Type u) [CommRing A] [Algebra R A]

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U' ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U)
    (m : (OModulePresheaf.ofModules π M).obj U) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U'
        (M.presheaf.map (homOfLE h).op m)
      = ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map (homOfLE h').op
          (show (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
              ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
              ((Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst π (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)) = homOfLE h' :=
    Subsingleton.elim _ _
  show (((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [IsSeparated π] (𝒰 : X.OrderedAffineCover)
  (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

omit [IsSeparated π] in

def unitAt {i : ℕ} (s : 𝒰.Idx i) :
    (OModulePresheaf.ofModules π M).obj (𝒰.inter s) →+
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
      (𝒰.baseChange_inter_le π A s)).toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
      (𝒰.inter s)).hom

omit [IsSeparated π] in
theorem unitAt_apply {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 s m
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
            (𝒰.inter s)).hom m) :=
  rfl

include htriv in
theorem exists_eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    ∃ e : A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s),
      ∀ m, e ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m := by
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial π M htriv
    (𝒰.inter s) (isAffineOpen_inter' π 𝒰 s) A
  refine ⟨e.trans (eqRes (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)) (𝒰.baseChange_inter π A s)),
    fun m => ?_⟩
  exact congrArg ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s))
    (he m)

def eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  (exists_eSimplex π M A 𝒰 htriv s).choose

theorem eSimplex_one_tmul {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m :=
  (exists_eSimplex π M A 𝒰 htriv s).choose_spec m

theorem eSimplex_tmul {i : ℕ} (s : 𝒰.Idx i) (a : A) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s (a ⊗ₜ[R] m) = a • unitAt π M A 𝒰 s m := by
  rw [tmul_eq_smul_one_tmul (R := R) A a m, map_smul, eSimplex_one_tmul]

def E (i : ℕ) :
    A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).cochain (𝒰.baseChange π A) i :=
  (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))).trans
    (LinearEquiv.piCongrRight fun s : 𝒰.Idx i => eSimplex π M A 𝒰 htriv s)

theorem E_tmul (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i (a ⊗ₜ[R] c) s = a • unitAt π M A 𝒰 s (c s) := by
  change eSimplex π M A 𝒰 htriv s
      (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))
        (a ⊗ₜ[R] c) s) = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, eSimplex_tmul]

theorem E_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c) s = unitAt π M A 𝒰 s (c s) := by
  rw [E_tmul, one_smul]

omit [IsSeparated π] in

theorem unitAt_res {i i' : ℕ} (s : 𝒰.Idx i) (t : 𝒰.Idx i') (h : 𝒰.inter t ≤ 𝒰.inter s)
    (hA : (𝒰.baseChange π A).inter t ≤ (𝒰.baseChange π A).inter s)
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 t ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res hA (unitAt π M A 𝒰 s m) := by
  rw [unitAt_apply, unitAt_apply, OModulePresheaf.res_res]
  have h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter t ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
    Scheme.Hom.preimage_mono _ h
  have key := unit_res π M A h h' m

  have : (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
        (𝒰.inter t)).hom ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res h'
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
              (𝒰.inter s)).hom m) := by
    exact key
  rw [this, OModulePresheaf.res_res]

theorem E_d_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) :
    E π M A 𝒰 htriv (i + 1) ((1 : A) ⊗ₜ[R] (OModulePresheaf.ofModules π M).d 𝒰 i c)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
          (E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c)) := by
  funext t
  rw [E_one_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, E_one_tmul]
  congr 1

  exact unitAt_res π M A 𝒰 (𝒰.face t j) t (𝒰.inter_le_inter_face t j)
    ((𝒰.baseChange π A).inter_le_inter_face t j) (c (𝒰.face t j))

theorem E_d (i : ℕ) :
    (E π M A 𝒰 htriv (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
        ∘ₗ (E π M A 𝒰 htriv i).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul]
    rw [tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a c, map_smul, map_smul, map_smul,
      E_d_one_tmul]

end Main

end AlgebraicGeometry.OModulePresheaf.CechBaseChange

end

open AlgebraicGeometry.OModulePresheaf.CechBaseChange in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ E : ∀ i : ℕ, A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i,
      (∀ i : ℕ, (E (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
        = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
          ∘ₗ (E i).toLinearMap) ∧
      (∀ (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i),
        E i (a ⊗ₜ[R] c) s
          = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
              (𝒰.baseChange_inter_le π A s)
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                (𝒰.inter s)).hom (c s))) :=
  ⟨E π M A 𝒰 htriv, E_d π M A 𝒰 htriv, E_tmul π M A 𝒰 htriv⟩
#print axioms solution
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains

namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace LinearMap
p2m_export "LinearMap" "mem_range range snd exact_map_mkQ_range codRestrict zero_apply exact_subtype_ker_map fst ker_comp coe_coe ext comp baseChange ker mem_ker comp_apply baseChange_comp mem_range_self lTensor_surjective"
namespace HomologyTransport
p2m_open "LinearMap"

variable {S : Type u} [CommRing S]
variable {P₀ P₁ P₂ Q₀ Q₁ Q₂ : Type u}
  [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
  [AddCommGroup Q₀] [Module S Q₀] [AddCommGroup Q₁] [Module S Q₁] [AddCommGroup Q₂] [Module S Q₂]
variable (e₀ : P₀ ≃ₗ[S] Q₀) (e₁ : P₁ ≃ₗ[S] Q₁) (e₂ : P₂ ≃ₗ[S] Q₂)
variable (f : P₀ →ₗ[S] P₁) (g : P₁ →ₗ[S] P₂) (f' : Q₀ →ₗ[S] Q₁) (g' : Q₁ →ₗ[S] Q₂)
variable (hf : e₁.toLinearMap ∘ₗ f = f' ∘ₗ e₀.toLinearMap) (hg : e₂.toLinearMap ∘ₗ g = g' ∘ₗ e₁.toLinearMap)

include hf in
theorem apply_f (x : P₀) : e₁ (f x) = f' (e₀ x) := by
  have := LinearMap.congr_fun hf x
  simpa using this

include hf in
theorem comap_ker : (LinearMap.ker f').comap e₀.toLinearMap = LinearMap.ker f := by
  ext x
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearMap.mem_ker]
  rw [← apply_f e₀ e₁ f f' hf, map_eq_zero_iff _ e₁.injective]

def kerEquiv : LinearMap.ker f ≃ₗ[S] LinearMap.ker f' :=
  (LinearEquiv.ofEq _ _ (comap_ker e₀ e₁ f f' hf).symm).trans (e₀.ofSubmodule' (LinearMap.ker f'))

theorem kerEquiv_apply_coe (x : LinearMap.ker f) : (kerEquiv e₀ e₁ f f' hf x : Q₀) = e₀ x := rfl

include hf hg in

theorem comap_kerEquiv_comap_range :
    ((LinearMap.range f').comap (LinearMap.ker g').subtype).comap (kerEquiv e₁ e₂ g g' hg).toLinearMap
      = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  ext z
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.coe_subtype, LinearMap.mem_range,
    kerEquiv_apply_coe]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₀.symm y, e₁.injective ?_⟩
    rw [apply_f e₀ e₁ f f' hf, e₀.apply_symm_apply, hy]
  · rintro ⟨x, hx⟩
    exact ⟨e₀ x, by rw [← apply_f e₀ e₁ f f' hf, hx]⟩

include hf hg in
theorem map_kerEquiv_comap_range :
    ((LinearMap.range f).comap (LinearMap.ker g).subtype).map (kerEquiv e₁ e₂ g g' hg).toLinearMap
      = (LinearMap.range f').comap (LinearMap.ker g').subtype := by
  rw [← comap_kerEquiv_comap_range e₀ e₁ e₂ f g f' g' hf hg]
  exact Submodule.map_comap_eq_of_surjective (kerEquiv e₁ e₂ g g' hg).surjective _

end LinearMap.HomologyTransport

namespace LinearMap
p2m_export "LinearMap" "mem_range range snd exact_map_mkQ_range codRestrict zero_apply exact_subtype_ker_map fst ker_comp coe_coe ext comp baseChange ker mem_ker comp_apply baseChange_comp mem_range_self lTensor_surjective"
namespace FlatKerBC
p2m_open "LinearMap"

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
variable (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)

theorem subtype_baseChange_injective [Module.Flat R A] :
    Function.Injective ((LinearMap.ker g).subtype.baseChange A) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := A) (LinearMap.ker g).subtype
    (LinearMap.ker g).injective_subtype

theorem range_subtype_baseChange [Module.Flat R A] :
    LinearMap.range ((LinearMap.ker g).subtype.baseChange A) = LinearMap.ker (g.baseChange A) := by
  have hexact : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  have hexA : Function.Exact ((LinearMap.ker g).subtype.baseChange A) (g.baseChange A) := by
    have := Module.Flat.lTensor_exact A hexact
    intro y; exact this y
  exact hexA.linearMap_ker_eq.symm

def theta [Module.Flat R A] : A ⊗[R] LinearMap.ker g ≃ₗ[A] LinearMap.ker (g.baseChange A) :=
  (LinearEquiv.ofInjective _ (subtype_baseChange_injective A g)).trans
    (LinearEquiv.ofEq _ _ (range_subtype_baseChange A g))

theorem theta_apply_coe [Module.Flat R A] (z : A ⊗[R] LinearMap.ker g) :
    (theta A g z : A ⊗[R] M₁) = ((LinearMap.ker g).subtype.baseChange A) z := rfl

variable (hgf : g ∘ₗ f = 0)

def toKer : M₀ →ₗ[R] LinearMap.ker g :=
  LinearMap.codRestrict (LinearMap.ker g) f fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hgf, LinearMap.zero_apply]

theorem subtype_comp_toKer : (LinearMap.ker g).subtype ∘ₗ toKer f g hgf = f := rfl

theorem range_toKer : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩ ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

include hgf in
theorem comap_theta [Module.Flat R A] :
    ((LinearMap.range (f.baseChange A)).comap (LinearMap.ker (g.baseChange A)).subtype).comap
        (theta A g).toLinearMap
      = LinearMap.range ((toKer f g hgf).baseChange A) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, subtype_baseChange_injective A g ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer, hx]
    rfl
  · rintro _ ⟨x, rfl⟩
    show (((theta A g) ((toKer f g hgf).baseChange A x) : LinearMap.ker (g.baseChange A)) : A ⊗[R] M₁)
      ∈ LinearMap.range (f.baseChange A)
    rw [theta_apply_coe, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer]
    exact LinearMap.mem_range_self _ x

include hgf in

theorem nonempty_quotEquiv :
    Nonempty (((A ⊗[R] LinearMap.ker g) ⧸ LinearMap.range ((toKer f g hgf).baseChange A))
      ≃ₗ[A] A ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  have hr : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker g).subtype :=
    range_toKer f g hgf
  have hexact : Function.Exact (toKer f g hgf) ((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ := by
    rw [← hr]; exact LinearMap.exact_map_mkQ_range _
  have hsurj : Function.Surjective ((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ :=
    Submodule.mkQ_surjective _
  have hexA : Function.Exact ((toKer f g hgf).baseChange A)
      (((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ.baseChange A) := by
    have := lTensor_exact A hexact hsurj
    intro y; exact this y
  have hsurjA : Function.Surjective (((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ.baseChange A) := by
    have := LinearMap.lTensor_surjective A hsurj
    intro y; exact this y
  exact ⟨hexA.linearEquivOfSurjective hsurjA⟩

end LinearMap.FlatKerBC

end

set_option maxHeartbeats 1600000 in
open LinearMap.HomologyTransport LinearMap.FlatKerBC in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    (Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) ∧
      ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype) ∧
    (Module.Flat R A →
      Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).H0 𝒰) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).HSucc 𝒰 i)) := by
  obtain ⟨E, hEd, -⟩ :=
    ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.solution π 𝒰 M htriv A

  have h0 : Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) :=
    ⟨(kerEquiv (E 0) (E 1) _ _ (hEd 0)).symm⟩

  have h1 : ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype := by
    intro i
    let κ := kerEquiv (E (i + 1)) (E (i + 2)) _ _ (hEd (i + 1))
    refine ⟨(Submodule.mkQ _) ∘ₗ κ.toLinearMap, ?_, ?_⟩
    · exact (Submodule.mkQ_surjective _).comp κ.surjective
    · rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      exact comap_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1))
  refine ⟨⟨h0, h1⟩, fun hflat => ?_⟩
  haveI := hflat
  have hdd : ∀ i : ℕ, (OModulePresheaf.ofModules π M).d 𝒰 (i + 1) ∘ₗ (OModulePresheaf.ofModules π M).d 𝒰 i = 0 :=
    fun i => AlgebraicGeometry.OModulePresheaf.d_comp_d _ 𝒰 i
  refine ⟨?_, fun i => ?_⟩
  ·
    obtain ⟨e'⟩ := h0
    exact ⟨e' ≪≫ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 0)).symm⟩
  ·
    let κ := kerEquiv (E (i + 1)) (E (i + 2)) (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)
      _ (hEd (i + 1))
    let Φ := (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).trans κ
    have hΦ : (LinearMap.range ((toKer ((OModulePresheaf.ofModules π M).d 𝒰 i)
          ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)).baseChange A)).map Φ.toLinearMap
        = (LinearMap.range ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) i)).comap
          (LinearMap.ker ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) (i + 1))).subtype := by
      rw [← map_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1)),
        ← comap_theta A ((OModulePresheaf.ofModules π M).d 𝒰 i) ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)]
      show Submodule.map (κ.toLinearMap ∘ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).toLinearMap) _ = _
      rw [Submodule.map_comp, Submodule.map_comap_eq_of_surjective
        (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).surjective]
    obtain ⟨e₁⟩ := nonempty_quotEquiv A ((OModulePresheaf.ofModules π M).d 𝒰 i)
      ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)
    let e₂ := Submodule.Quotient.equiv _ _ Φ hΦ
    exact ⟨e₂.symm ≪≫ₗ e₁⟩
#print axioms solution
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology

namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mSectionsBaseChangeH0

section Cover

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x := rfl

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def sectionsEquivH0 :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩

theorem coe_sectionsEquivH0 (x : Γ(M, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    ((sectionsEquivH0 π M K x : (OModulePresheaf.ofModules π M).H0 K) :
      (OModulePresheaf.ofModules π M).cochain K 0) = toCochain π M K x := rfl

end H0

section Unit

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

lemma app_map {N N' : X.Modules} (φ : N ⟶ N') {W W' : X.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma map_map (N : X.Modules) {W W' W'' : X.Opens} (i : W' ⟶ W) (j : W'' ⟶ W') (k : W'' ⟶ W)
    (n : Γ(N, W)) :
    N.presheaf.map j.op (N.presheaf.map i.op n) = N.presheaf.map k.op n := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  rfl

abbrev unitApp (M : X.Modules) (U : X.Opens) (e : Γ(M, U)) :
    Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U e

lemma unitApp_map (M : X.Modules) {U W : X.Opens} (i : W ⟶ U) (k : p ⁻¹ᵁ W ⟶ p ⁻¹ᵁ U) (e : Γ(M, U)) :
    unitApp p M W (M.presheaf.map i.op e)
      = ((Scheme.Modules.pullback p).obj M).presheaf.map k.op (unitApp p M U e) := by
  have h := app_map ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) i e
  refine h.trans ?_
  obtain rfl : k = (Opens.map p.base).map i := Subsingleton.elim _ _
  rfl

end Unit

section KerTransfer

variable {R : Type u} [CommRing R]
variable {K0 K1 C0 C1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem lid_baseChange_apply (f : C0 →ₗ[R] C1) (x : R ⊗[R] C0) :
    TensorProduct.lid R C1 (f.baseChange R x) = f (TensorProduct.lid R C0 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rw [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
  (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK)

theorem tmul_one_mem_ker {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (x : LinearMap.ker f) :
    (1 : R) ⊗ₜ[R] (x : N) ∈ LinearMap.ker (f.baseChange R) := by
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp x.2, tmul_zero]

theorem kerMap_bijective (h : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R)) :
    Function.Bijective (TwoChartCech.kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    have hv : ι0 x = ι0 y := congrArg Subtype.val hxy
    have h1 : TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK x⟩
        = TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK y⟩ := by
      apply Subtype.ext
      change ι0.baseChange R ((1 : R) ⊗ₜ[R] (x : K0)) = ι0.baseChange R ((1 : R) ⊗ₜ[R] (y : K0))
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hv]
    have h2 := congrArg (fun z => TensorProduct.lid R K0 (Subtype.val z)) (h.1 h1)
    simp only [TensorProduct.lid_tmul, one_smul] at h2
    exact Subtype.ext h2
  · intro y
    obtain ⟨x, hx⟩ := h.2 ⟨_, tmul_one_mem_ker d y⟩
    have hxv : ι0.baseChange R (x : R ⊗[R] K0) = (1 : R) ⊗ₜ[R] (y : C0) := congrArg Subtype.val hx
    refine ⟨⟨TensorProduct.lid R K0 x, ?_⟩, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, ← lid_baseChange_apply, LinearMap.mem_ker.mp x.2, map_zero]
    · change ι0 (TensorProduct.lid R K0 x) = y
      rw [← lid_baseChange_apply, hxv, TensorProduct.lid_tmul, one_smul]

end KerTransfer

section KerOfEquiv

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {C0 C1 D0 D1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
  [AddCommGroup D0] [Module A D0] [AddCommGroup D1] [Module A D1]

def kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A] D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) :
    LinearMap.ker d ≃ₗ[A] LinearMap.ker d' :=
  (LinearEquiv.ofEq _ _ (by
    rw [← LinearEquiv.ker_comp E1 d, h, LinearMap.ker_comp])).trans (E0.ofSubmodule' (LinearMap.ker d'))

theorem coe_kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A] D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (x : LinearMap.ker d) :
    (kerEquivOfEquiv d d' E0 E1 h x : D0) = E0 x := rfl

theorem coe_kerEquivOfEquiv_symm (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0)
    (E1 : C1 ≃ₗ[A] D1) (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (y : LinearMap.ker d') :
    ((kerEquivOfEquiv d d' E0 E1 h).symm y : C0) = E0.symm y := by
  set x := (kerEquivOfEquiv d d' E0 E1 h).symm y with hx
  have hy : (kerEquivOfEquiv d d' E0 E1 h) x = y := LinearEquiv.apply_symm_apply _ _
  have hcoe : E0 (x : C0) = (y : D0) := by
    rw [← coe_kerEquivOfEquiv d d' E0 E1 h x, hy]
  rw [← hcoe, LinearEquiv.symm_apply_apply]

end KerOfEquiv

end P2mSectionsBaseChangeH0

namespace Engine19

p2m_open "ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.P2mSectionsBaseChangeH0 AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem isEmpty_idx {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι < i + 1) :
    IsEmpty (𝒰.Idx i) := by
  refine ⟨fun s => ?_⟩
  have h := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at h
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι ≤ i) :
    Subsingleton (F.cochain 𝒰 i) := by
  haveI : IsEmpty (𝒰.Idx i) := isEmpty_idx 𝒰 i (by omega)
  change Subsingleton (∀ s : 𝒰.Idx i, F.obj (𝒰.inter s))
  infer_instance

theorem ker_le_range_of_subsingleton {A : Type u} [CommRing A] {C0 C1 C2 H : Type u}
    [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1] [AddCommGroup C2] [Module A C2]
    [AddCommGroup H] [Module A H] [Subsingleton H]
    (d0 : C0 →ₗ[A] C1) (d1 : C1 →ₗ[A] C2) (φ : LinearMap.ker d1 →ₗ[A] H)
    (hφ : LinearMap.ker φ = (LinearMap.range d0).comap (LinearMap.ker d1).subtype) :
    LinearMap.ker d1 ≤ LinearMap.range d0 := by
  intro x hx
  have h1 : (⟨x, hx⟩ : LinearMap.ker d1) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [hφ] at h1
  exact h1

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hH : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ 𝒲 : (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
        Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R K))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R K))).obj M)).HSucc 𝒲 i)) :
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) m := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  let F := OModulePresheaf.ofModules f M
  letI instM := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
  haveI : ∀ i, Module.Flat R (F.cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M htriv 𝒰 i
  have hdd : ∀ i, F.d 𝒰 (i + 1) ∘ₗ F.d 𝒰 i = 0 := fun i => OModulePresheaf.d_comp_d F 𝒰 i
  have hbd : ∀ i, Fintype.card 𝒰.ι ≤ i → Subsingleton (F.cochain 𝒰 i) := fun i hi => subsingleton_cochain F 𝒰 i hi
  have hCF : F.CechFinite 𝒰 := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M htriv 𝒰
  have hMinv : Scheme.Modules.IsInvertible M := ⟨htriv⟩

  have hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((F.d 𝒰 (i + 1)).baseChange K) ≤ LinearMap.range ((F.d 𝒰 i).baseChange K) := by
    intro K _ _ i
    obtain ⟨𝒲, h𝒲⟩ := hH K
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    let MK : (Limits.pullback f (specMap R K)).Modules := (Scheme.Modules.pullback p₁).obj M
    have htrivK := (hMinv.pullback p₁).1
    have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial p₂ MK htrivK
    obtain ⟨eK⟩ := (OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated p₂ MK hq
      (𝒰.baseChange f K) 𝒲).2 i
    haveI := h𝒲 i
    haveI : Subsingleton ((OModulePresheaf.ofModules p₂ MK).HSucc (𝒰.baseChange f K) i) := eK.toEquiv.subsingleton
    obtain ⟨φ, -, hφ⟩ := (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology.solution f 𝒰 M htriv K).1.2 i
    exact ker_le_range_of_subsingleton _ _ φ hφ

  obtain ⟨hproj, hbij, -⟩ :=
    Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
      (fun i => F.cochain 𝒰 i) (fun i => F.d 𝒰 i) hdd (Fintype.card 𝒰.ι) hbd hCF.1 hCF.2 hfib

  let ε₀ : Γ(M, ⊤) ≃ₗ[R] F.H0 𝒰 := sectionsEquivH0 f M 𝒰
  haveI : Module.Finite R (F.H0 𝒰) := hCF.1
  haveI : Module.Projective R (F.H0 𝒰) := hproj
  refine ⟨⟨Module.Finite.equiv ε₀.symm, Module.Projective.of_equiv ε₀.symm⟩, ?_⟩
  intro A _ _
  let p₁ := Limits.pullback.fst f (specMap R A)
  let p₂ := Limits.pullback.snd f (specMap R A)
  let MA : (Limits.pullback f (specMap R A)).Modules := (Scheme.Modules.pullback p₁).obj M
  let FA := OModulePresheaf.ofModules p₂ MA
  letI instMA := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ MA ⊤
  obtain ⟨E, hEd, hEf⟩ := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Cochains.solution f 𝒰 M htriv A
  let e1 : Γ(MA, ⊤) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) := sectionsEquivH0 p₂ MA (𝒰.baseChange f A)
  let e2 : LinearMap.ker ((F.d 𝒰 0).baseChange A) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) :=
    kerEquivOfEquiv ((F.d 𝒰 0).baseChange A) (FA.d (𝒰.baseChange f A) 0) (E 0) (E 1) (hEd 0)
  let e3 : A ⊗[R] F.H0 𝒰 ≃ₗ[A] LinearMap.ker ((F.d 𝒰 0).baseChange A) :=
    LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A) (hbij A)
  let e0 : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] A ⊗[R] F.H0 𝒰 := ε₀.baseChange R A _ _
  let e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] Γ(MA, ⊤) := e0.trans (e3.trans (e2.trans e1.symm))
  have key : ∀ m : Γ(M, ⊤), e1 (unitApp p₁ M ⊤ m) = e2 (e3 ((1 : A) ⊗ₜ[R] ε₀ m)) := by
    intro m
    apply Subtype.ext
    rw [coe_kerEquivOfEquiv]
    change ((e1 _ : FA.H0 (𝒰.baseChange f A)) : FA.cochain (𝒰.baseChange f A) 0) =
      E 0 ((TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A ((1 : A) ⊗ₜ[R] ε₀ m) : A ⊗[R] F.cochain 𝒰 0))
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul, Submodule.subtype_apply,
      coe_sectionsEquivH0, coe_sectionsEquivH0]
    funext s
    rw [hEf 0 1 (toCochain f M 𝒰 m) s, one_smul, toCochain_apply, toCochain_apply]
    have h2 := unitApp_map p₁ M (homOfLE (le_top : 𝒰.inter s ≤ ⊤))
      (homOfLE (le_top : p₁ ⁻¹ᵁ 𝒰.inter s ≤ p₁ ⁻¹ᵁ ⊤)) m
    change MA.presheaf.map (homOfLE (le_top : (𝒰.baseChange f A).inter s ≤ ⊤)).op (unitApp p₁ M ⊤ m)
      = FA.res (𝒰.baseChange_inter_le f A s)
        (unitApp p₁ M (𝒰.inter s) (M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op m))
    rw [h2, OModulePresheaf.ofModules_res_apply]
    exact (map_map MA _ _ _ _).symm
  have key1 : ∀ m : Γ(M, ⊤), e ((1 : A) ⊗ₜ[R] m) = unitApp p₁ M ⊤ m := by
    intro m
    change e1.symm (e2 (e3 (e0 ((1 : A) ⊗ₜ[R] m)))) = _
    rw [LinearEquiv.symm_apply_eq]
    have h0 : e0 ((1 : A) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] ε₀ m := by simp [e0]
    rw [h0]
    exact (key m).symm
  have key2 : ∀ (a : A) (m : Γ(M, ⊤)), e (a ⊗ₜ[R] m) = a • (show Γ(MA, ⊤) from unitApp p₁ M ⊤ m) := by
    intro a m
    have hsm : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm, map_smul, key1]
  exact ⟨e, fun a m => key2 a m⟩

end Engine19

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hH : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ 𝒲 : (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
        Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R K))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R K))).obj M)).HSucc 𝒲 i)) :
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) m :=
  Engine19.main f M htriv hH
#print axioms solution
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections

namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Vanishing
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

lemma all_covers_of_two_chart {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsSeparated π] (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h1 : Subsingleton (𝒱.sectionsOf π M).H1) (𝒰 : X.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc 𝒰 i) := by
  let F := OModulePresheaf.ofModules π M
  have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial π M hM.1
  obtain ⟨e⟩ := (OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
    π M hq 𝒰 𝒱.toOrderedAffineCover).2 i
  haveI : Subsingleton (F.HSucc 𝒱.toOrderedAffineCover i) := by
    cases i with
    | zero =>
      letI : Subsingleton (F.twoChartSections 𝒱).H1 := h1
      exact (P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquiv
        𝒱 F).toEquiv.subsingleton
    | succ i =>
      exact (F.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
        𝒱.toOrderedAffineCover).2.2.1 (i + 1) (by
          change Fintype.card (ULift.{u} (Fin 2)) ≤ i + 1 + 1
          simp only [Fintype.card_ulift, Fintype.card_fin]; omega)
  exact e.toEquiv.subsingleton

lemma descend_field_vanishing {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsSeparated π] (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (𝒰 : X.OrderedAffineCover)
    (K' : Type u) [Field K'] [Algebra K K']
    (h : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules
      (pullback.snd π (Scheme.TwoAffineOpenCover.specMap K K'))
      ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap K K'))).obj M)).HSucc
      (𝒰.baseChange π K') i)) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc 𝒰 i) := by
  obtain ⟨-, hflat⟩ := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Homology.solution π 𝒰 M hM.1 K'
  obtain ⟨-, hsucc⟩ := hflat inferInstance
  obtain ⟨e⟩ := hsucc i
  haveI : Subsingleton (K' ⊗[K] (OModulePresheaf.ofModules π M).HSucc 𝒰 i) :=
    e.symm.toEquiv.subsingleton_congr.mpr (h i)
  haveI : Module.FaithfullyFlat K K' := inferInstance
  exact Module.FaithfullyFlat.lTensor_reflects_triviality K K'
    ((OModulePresheaf.ofModules π M).HSucc 𝒰 i)

#print axioms all_covers_of_two_chart
#print axioms descend_field_vanishing
end
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Vanishing

namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Actual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.FibreCohomology
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Vanishing
open scoped TensorProduct

lemma fibre_vanishing (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] (sK : Spec (.of K) ⟶ Spec (.of R))
    (𝒰 : (pullback Q.structureMap sK).OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).HSucc 𝒰 i) := by
  let c := Q.structureMap
  let M := ((Q.zero).ker ^ m).invModule
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  letI : IsProper c := Q.geometry.proper
  let π := pullback.snd c sK
  let MK := (Scheme.Modules.pullback (pullback.fst c sK)).obj M
  let s : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Scheme.TwoAffineOpenCover.specMap K (AlgebraicClosure K)
  apply descend_field_vanishing π MK (hM.pullback _) 𝒰 (AlgebraicClosure K) ?_ i
  intro j
  let ψ : SchemeHomOver (s ≫ sK) sK := ⟨s, rfl⟩
  let g' : pullback c (s ≫ sK) ⟶ pullback c sK := RelPicard.baseChangeSnd c ψ
  let y := pullback.snd c (s ≫ sK)
  have hgf : g' ≫ pullback.fst c sK = pullback.fst c (s ≫ sK) := by
    simp only [g', RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hgs : g' ≫ π = y ≫ s := by
    simp only [g', π, RelPicard.baseChangeSnd, pullback.lift_snd]
    rfl
  have hcart : IsPullback g' y π s := by
    refine IsPullback.of_right ?_ hgs (IsPullback.of_hasPullback c sK)
    rw [hgf]
    exact IsPullback.of_hasPullback c (s ≫ sK)
  let F := (Scheme.Modules.pullback (pullback.fst c (s ≫ sK))).obj M
  let e : F ≅ (Scheme.Modules.pullback g').obj MK :=
    (Scheme.Modules.pullbackCongr hgf.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp g' (pullback.fst c sK)).app M).symm
  obtain ⟨𝒱,h𝒱⟩ := origin_exists_fibre_positive_cohomology_cover
    R Q (AlgebraicClosure K) (s ≫ sK)
  obtain ⟨𝒲,-,⟨eH⟩⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    c sK MK s y g' hcart F e 𝒱
  haveI : Subsingleton (𝒱.sectionsOf y F).H1 := (h𝒱 m hm).1
  have hW : Subsingleton (𝒲.sectionsOf (pullback.snd π s)
      ((Scheme.Modules.pullback (pullback.fst π s)).obj MK)).H1 :=
    eH.symm.toEquiv.subsingleton
  exact all_covers_of_two_chart (pullback.snd π s) _
    ((hM.pullback (pullback.fst c sK)).pullback (pullback.fst π s)) 𝒲 hW
    (𝒰.baseChange π (AlgebraicClosure K)) j


/-- Positive origin-power sections are finite projective and commute with
arbitrary ring base change, by the actual pullback of local sections. -/
lemma positive_sections_baseChange (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let f := Q.structureMap
    let M := ((Q.zero).ker ^ m).invModule
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (x : Γ(M, ⊤)),
          e (a ⊗ₜ[R] x) = a • Scheme.Modules.pullbackLocalSection
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) x := by
  let M := ((Q.zero).ker ^ m).invModule
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : Smooth Q.structureMap := Q.geometry.smooth
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.solution Q.structureMap M hM.1
  intro K _ _
  let sK := Scheme.TwoAffineOpenCover.specMap R K
  haveI : CompactSpace (pullback Q.structureMap sK : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Q.structureMap sK)
  let 𝒰 := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact
    (pullback Q.structureMap sK)
  exact ⟨𝒰, fun i => fibre_vanishing R Q m hm K sK 𝒰 i⟩

#print axioms positive_sections_baseChange

#print axioms fibre_vanishing

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections

lemma positive_higher_cohomology (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (𝒰 : Q.target.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules Q.structureMap
      (((Q.zero).ker ^ m).invModule)).HSucc 𝒰 i) := by
  let f := Q.structureMap
  let M := ((Q.zero).ker ^ m).invModule
  let F := OModulePresheaf.ofModules f M
  letI : IsProper f := Q.geometry.proper
  letI : Smooth f := Q.geometry.smooth
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  haveI : ∀ j, Module.Flat R (F.cochain 𝒰 j) := fun j =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M hM.1 𝒰 j
  have hdd : ∀ j, F.d 𝒰 (j + 1) ∘ₗ F.d 𝒰 j = 0 := fun j => OModulePresheaf.d_comp_d F 𝒰 j
  have hbd : ∀ j, Fintype.card 𝒰.ι ≤ j → Subsingleton (F.cochain 𝒰 j) :=
    fun j hj => Sections.Engine19.subsingleton_cochain F 𝒰 j hj
  have hCF : F.CechFinite 𝒰 :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M hM.1 𝒰
  have hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      LinearMap.ker ((F.d 𝒰 (j + 1)).baseChange K) ≤ LinearMap.range ((F.d 𝒰 j).baseChange K) := by
    intro K _ _ j
    let sK := Scheme.TwoAffineOpenCover.specMap R K
    haveI : Subsingleton ((OModulePresheaf.ofModules (pullback.snd f sK)
        ((Scheme.Modules.pullback (pullback.fst f sK)).obj M)).HSucc (𝒰.baseChange f K) j) :=
      fibre_vanishing R Q m hm K sK (𝒰.baseChange f K) j
    obtain ⟨φ,-,hφ⟩ := (Homology.solution f 𝒰 M hM.1 K).1.2 j
    exact Sections.Engine19.ker_le_range_of_subsingleton _ _ φ hφ
  obtain ⟨-,-,hAll⟩ :=
    Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
      (fun j => F.cochain 𝒰 j) (fun j => F.d 𝒰 j) hdd (Fintype.card 𝒰.ι) hbd hCF.1 hCF.2 hfib
  have hker : LinearMap.ker (F.d 𝒰 (i + 1)) ≤ LinearMap.range (F.d 𝒰 i) := by
    intro x hx
    have hxR : (1 : R) ⊗ₜ[R] x ∈ LinearMap.ker ((F.d 𝒰 (i + 1)).baseChange R) := by
      rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hx,
        TensorProduct.tmul_zero]
    obtain ⟨z,hz⟩ := hAll R i hxR
    refine ⟨TensorProduct.lid R _ z, ?_⟩
    have h := congrArg (TensorProduct.lid R _) hz
    rw [Sections.P2mSectionsBaseChangeH0.lid_baseChange_apply, TensorProduct.lid_tmul,
      one_smul] at h
    exact h
  have htop : (LinearMap.range (F.d 𝒰 i)).comap (LinearMap.ker (F.d 𝒰 (i + 1))).subtype = ⊤ := by
    apply top_unique
    intro x _
    exact hker x.property
  change Subsingleton (LinearMap.ker (F.d 𝒰 (i + 1)) ⧸ _)
  rw [htop]
  infer_instance

#print axioms positive_higher_cohomology


lemma positive_sections_geometric_rank (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
    let M := ((Q.zero).ker ^ m).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Module.finrank K (K ⊗[R] Γ(M,⊤)) = m := by
  let M := ((Q.zero).ker ^ m).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  let sK := Scheme.TwoAffineOpenCover.specMap R K
  let MK := (Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj M
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd Q.structureMap sK) MK ⊤
  obtain ⟨e,-⟩ := (positive_sections_baseChange R Q m hm).2 K
  obtain ⟨𝒱,h𝒱⟩ := origin_exists_fibre_positive_cohomology_cover R Q K sK
  obtain ⟨eH,-⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 (pullback.snd Q.structureMap sK) MK
  let e' : K ⊗[R] Γ(M,⊤) ≃ₗ[K] Γ(MK,⊤) := e
  exact e'.finrank_eq.trans (eH.finrank_eq.trans (h𝒱 m hm).2)

#print axioms positive_sections_geometric_rank
end
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Actual


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
section Augmentation
variable [Algebra A R] [IsScalarTower R A R]

lemma augmentation_surjective : Function.Surjective (algebraMap A R) := by
  intro r
  refine ⟨algebraMap R A r, ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  rfl

lemma conormal_differential_bijective :
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor R A R) := by
  let e := retractionKerCotangentToTensorEquivSection
    (R := R) (P := A) (S := R) (augmentation_surjective R A)
  have hsec : ∃ g, (IsScalarTower.toAlgHom R A R).kerSquareLift.comp g = AlgHom.id R R := by
    refine ⟨(Algebra.ofId R (A ⧸ (RingHom.ker (algebraMap A R) ^ 2))), ?_⟩
    exact Subsingleton.elim _ _
  obtain ⟨g,hg⟩ := hsec
  obtain ⟨l,hl⟩ := e.symm ⟨g,hg⟩
  constructor
  · exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hl x)
  · intro x
    exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A R
      (augmentation_surjective R A) x).mp (Subsingleton.elim _ _)

def augmentationExtension : Algebra.Extension R R where
  Ring := A
  σ := algebraMap R A
  algebraMap_σ r := by rw [← IsScalarTower.algebraMap_apply]; rfl

def conormalTensorEquiv :
    R ⊗[A] RingHom.ker (algebraMap A R) ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
  (augmentationExtension R A).cotangentEquiv ≪≫ₗ
    LinearEquiv.ofBijective (augmentationExtension R A).cotangentComplex
      (conormal_differential_bijective R A)

lemma conormalTensorEquiv_tmul (r : R) (x : RingHom.ker (algebraMap A R)) :
    conormalTensorEquiv R A (r ⊗ₜ[A] x) = r ⊗ₜ[A] KaehlerDifferential.D R A x.1 := by
  change (augmentationExtension R A).cotangentComplex
    (r • Algebra.Extension.Cotangent.mk x) = _
  rw [map_smul, Algebra.Extension.cotangentComplex_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

end Augmentation
section General
variable {B : Type u} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable [Algebra.FormallySmooth R A] [Algebra.FormallyEtale R B]

def etaleExtension (h : Function.Surjective (algebraMap A B)) : Algebra.Extension R B where
  Ring := A
  σ := Function.surjInv h
  algebraMap_σ := Function.surjInv_eq h

lemma etale_conormal_bijective (h : Function.Surjective (algebraMap A B)) :
    Function.Bijective (etaleExtension R A h).cotangentComplex := by
  constructor
  · exact (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      (R := R) h).mpr inferInstance
  · intro x
    exact ((etaleExtension R A h).exact_cotangentComplex_toKaehler x).mp
      (Subsingleton.elim _ _)

def etaleConormalTensorEquiv (h : Function.Surjective (algebraMap A B)) :
    B ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[B] B ⊗[A] Ω[A⁄R] :=
  (etaleExtension R A h).cotangentEquiv ≪≫ₗ
    LinearEquiv.ofBijective _ (etale_conormal_bijective R A h)

lemma etaleConormalTensorEquiv_tmul (h : Function.Surjective (algebraMap A B))
    (b : B) (x : RingHom.ker (algebraMap A B)) :
    etaleConormalTensorEquiv R A h (b ⊗ₜ[A] x) = b ⊗ₜ[A] KaehlerDifferential.D R A x.1 := by
  change (etaleExtension R A h).cotangentComplex (b • Algebra.Extension.Cotangent.mk x) = _
  rw [map_smul, Algebra.Extension.cotangentComplex_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl
end General

#print axioms etaleConormalTensorEquiv
#print axioms conormalTensorEquiv
#print axioms conormal_differential_bijective
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (e : S ⟶ X)

lemma section_ideal_zero (U : X.Opens) (x : Γ(e.ker.module,U)) :
    e.app U (e.ker.moduleι.app U x) = 0 := by
  have hx : e.ker.subschemeι.app U (e.ker.moduleι.app U x) = 0 :=
    congrArg (fun f => f.val.app (op U) x) (kernel.condition e.ker.subschemeι.unitToPushforwardUnit)
  have h0 : (e.toImage ≫ e.ker.subschemeι).app U (e.ker.moduleι.app U x) = 0 := by
    change e.toImage.app _ (e.ker.subschemeι.app U (e.ker.moduleι.app U x)) = 0
    rw [hx, map_zero]
  have h := Scheme.Hom.congr_app e.toImage_imageι.symm U
  have hh := congrArg (fun f => f.hom (show Γ(X,U) from e.ker.moduleι.app U x)) h
  change (e.app U).hom (show Γ(X,U) from e.ker.moduleι.app U x) = 0
  rw [hh]
  change S.presheaf.map _ ((e.toImage ≫ e.ker.subschemeι).app U (e.ker.moduleι.app U x)) = 0
  rw [h0, map_zero]

def conormalLocal (U : X.Opens) :
    Γ(e.ker.module,U) →ₗ[Γ(X,U)]
      Γ((Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj c.kaehler),U) where
  toFun x := Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x))
  map_add' x y := by
    rw [map_add, relativeD_add, Scheme.Modules.pullbackLocalSection_add]
  map_smul' a x := by
    rw [Scheme.Modules.Hom.app_smul]
    change Scheme.Modules.pullbackLocalSection e (relativeD c U (a * (show Γ(X,U) from e.ker.moduleι.app U x))) = _
    rw [relativeD_mul, Scheme.Modules.pullbackLocalSection_add,
      Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.pullbackLocalSection_smul,
      section_ideal_zero, zero_smul, add_zero]
    rfl

def conormalToPushforward :
    e.ker.module ⟶ (Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj c.kaehler) :=
  ⟨{ app := fun U => @ModuleCat.ofHom _ _
       (e.ker.module.val.obj U)
       (((Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj c.kaehler)).val.obj U)
       _ _ _ _ (conormalLocal c e U.unop)
     naturality := by
       intro U V i
       ext x
       change conormalLocal c e V.unop (e.ker.module.val.map i x) =
         ((Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj c.kaehler)).val.map i
           (conormalLocal c e U.unop x)
       change Scheme.Modules.pullbackLocalSection e
         (relativeD c V.unop (e.ker.moduleι.app V.unop (e.ker.module.val.map i x))) =
         ((Scheme.Modules.pullback e).obj c.kaehler).presheaf.map
           ((TopologicalSpace.Opens.map e.base).map i.unop).op
           (Scheme.Modules.pullbackLocalSection e (relativeD c U.unop (e.ker.moduleι.app U.unop x)))
       rw [Scheme.Modules.map_pullbackLocalSection]
       have hi : i = (homOfLE (leOfHom i.unop)).op := Subsingleton.elim _ _
       rw [hi]
       erw [relativeD_restrict]
       apply congrArg (fun a => Scheme.Modules.pullbackLocalSection e (relativeD c V.unop a))
       exact (ConcreteCategory.congr_hom (e.ker.moduleι.val.naturality i) x)
    }⟩

def conormalMap : (Scheme.Modules.pullback e).obj e.ker.module ⟶
    (Scheme.Modules.pullback e).obj c.kaehler :=
  ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).symm (conormalToPushforward c e)

lemma conormalMap_pullback (U : X.Opens) (x : Γ(e.ker.module,U)) :
    (conormalMap c e).app (e ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection e x) =
      Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x)) := by
  exact Scheme.Modules.homEquiv_symm_app_pullbackLocalSection e (conormalToPushforward c e) x

#print axioms conormalMap
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (e : S ⟶ X)

def idealSectionsToKernel (U : X.Opens) :
    Γ(e.ker.module,U) →ₗ[Γ(X,U)] RingHom.ker (e.app U).hom :=
  ((e.ker.moduleι.val.app (op U)).hom : Γ(e.ker.module,U) →ₗ[Γ(X,U)] Γ(X,U)).codRestrict _
    (section_ideal_zero e U)

lemma idealSectionsToKernel_bijective [QuasiCompact e] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (idealSectionsToKernel e U) := by
  haveI : Mono e.ker.moduleι := inferInstanceAs (Mono (kernel.ι e.ker.subschemeι.unitToPushforwardUnit))
  constructor
  · intro x y h
    apply mono_app_injective e.ker.moduleι U
    exact congrArg Subtype.val h
  · intro x
    have hr := (ideal_realization e.ker).2 ⟨U,hU⟩
    have hx : (x : Γ(X,U)) ∈ Set.range (fun s => (e.ker.moduleι.app U s : Γ(X,U))) := by
      rw [show Set.range (fun s => (e.ker.moduleι.app U s : Γ(X,U))) =
        (e.ker.ideal ⟨U,hU⟩).carrier from hr]
      change (x : Γ(X,U)) ∈ e.ker.ideal ⟨U,hU⟩
      rw [Scheme.Hom.ker_apply]
      exact x.property
    obtain ⟨y,hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

def idealSectionsEquiv [QuasiCompact e] (U : X.Opens) (hU : IsAffineOpen U) :
    Γ(e.ker.module,U) ≃ₗ[Γ(X,U)] RingHom.ker (e.app U).hom :=
  LinearEquiv.ofBijective _ (idealSectionsToKernel_bijective e U hU)

lemma conormalMap_app_bijective [IsClosedImmersion e]
    (hI : e.ker.IsInvertible) (hΩ : Scheme.Modules.IsInvertible c.kaehler)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hsmooth : letI := c.sectionsAlgebra U; Algebra.FormallySmooth R Γ(X,U))
    (hetale : letI := (c ≫ 𝟙 _).sectionsAlgebra U
      letI : Algebra Γ(X,U) Γ(S,e ⁻¹ᵁ U) := (e.app U).hom.toAlgebra
      letI : Algebra R Γ(S,e ⁻¹ᵁ U) := ((e.app U).hom.comp (algebraMap R Γ(X,U))).toAlgebra
      Algebra.FormallyEtale R Γ(S,e ⁻¹ᵁ U)) :
    Function.Bijective ((conormalMap c e).app (e ⁻¹ᵁ U)) := by
  let A := Γ(X,U)
  let B := Γ(S,e ⁻¹ᵁ U)
  letI := c.sectionsAlgebra U
  letI : Algebra A B := (e.app U).hom.toAlgebra
  letI : Algebra R B := ((e.app U).hom.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallySmooth R A := hsmooth
  haveI : Algebra.FormallyEtale R B := by simpa only [Category.comp_id] using hetale
  have hB := hU.preimage e
  have hsurj : Function.Surjective (algebraMap A B) := e.app_surjective U hU
  let κ := LinearEquiv.ofBijective (c.kaehlerToSectionsₗ U)
    (c.kaehlerToSections_bijective_of_isAffineOpen hU)
  have hβI₀ := hI.isInvertible_module.exists_baseChange_sections_linearEquiv_pullback_of_le
    e U hU (e ⁻¹ᵁ U) hB le_rfl
  have hβΩ₀ := hΩ.exists_baseChange_sections_linearEquiv_pullback_of_le
    e U hU (e ⁻¹ᵁ U) hB le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at hβI₀ hβΩ₀
  obtain ⟨βI,hβI⟩ := hβI₀
  obtain ⟨βΩ,hβΩ⟩ := hβΩ₀
  let E : Γ((Scheme.Modules.pullback e).obj e.ker.module,e ⁻¹ᵁ U) ≃ₗ[B]
      Γ((Scheme.Modules.pullback e).obj c.kaehler,e ⁻¹ᵁ U) :=
    βI.symm ≪≫ₗ LinearEquiv.baseChange A B _ _ (idealSectionsEquiv e U hU) ≪≫ₗ
      etaleConormalTensorEquiv R A hsurj ≪≫ₗ LinearEquiv.baseChange A B _ _ κ ≪≫ₗ βΩ
  have hE : ((conormalMap c e).val.app (op (e ⁻¹ᵁ U))).hom = E.toLinearMap := by
    suffices h : ((conormalMap c e).val.app (op (e ⁻¹ᵁ U))).hom.comp βI.toLinearMap =
        E.toLinearMap.comp βI.toLinearMap by
      ext x
      obtain ⟨y,rfl⟩ := βI.surjective x
      exact LinearMap.congr_fun h y
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      have hβI' (x : Γ(e.ker.module,U)) : βI (1 ⊗ₜ[A] x) =
          Scheme.Modules.pullbackLocalSection e x := by simpa using hβI x
      have hβΩ' (x : Γ(c.kaehler,U)) : βΩ (1 ⊗ₜ[A] x) =
          Scheme.Modules.pullbackLocalSection e x := by simpa using hβΩ x
      have hbI : βI (b ⊗ₜ[A] x) = b • Scheme.Modules.pullbackLocalSection e x := by
        calc
          _ = βI (b • ((1:B) ⊗ₜ[A] x)) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          _ = _ := by rw [map_smul, hβI']
      change (conormalMap c e).app (e ⁻¹ᵁ U) (βI (b ⊗ₜ[A] x)) = E (βI (b ⊗ₜ[A] x))
      have hleft : (conormalMap c e).app (e ⁻¹ᵁ U) (βI (b ⊗ₜ[A] x)) =
          b • Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x)) := by
        erw [hbI, Scheme.Modules.Hom.app_smul, conormalMap_pullback]
      rw [hleft]
      simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      change b • Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x)) =
        βΩ ((LinearEquiv.baseChange A B _ _ κ)
          (etaleConormalTensorEquiv R A hsurj (b ⊗ₜ[A] (idealSectionsEquiv e U hU x))))
      have hstep := etaleConormalTensorEquiv_tmul R A hsurj b (idealSectionsEquiv e U hU x)
      rw [hstep]
      change b • Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x)) =
        βΩ (b ⊗ₜ[A] (relativeD c U (e.ker.moduleι.app U x)))
      rw [show b ⊗ₜ[A] (relativeD c U (e.ker.moduleι.app U x)) =
        b • ((1:B) ⊗ₜ[A] (relativeD c U (e.ker.moduleι.app U x))) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hβΩ']
  change Function.Bijective ((conormalMap c e).val.app (op (e ⁻¹ᵁ U))).hom
  rw [hE]
  exact E.bijective

#print axioms conormalMap_app_bijective
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

lemma isIso_of_affine_preimage_bijective {X S : Scheme.{u}} (e : S ⟶ X) [IsClosedImmersion e]
    {M N : S.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Bijective (φ.app (e ⁻¹ᵁ U.1))) : IsIso φ := by
  let F : TopCat.Sheaf AddCommGrpCat S := ⟨M.presheaf,M.isSheaf⟩
  let G : TopCat.Sheaf AddCommGrpCat S := ⟨N.presheaf,N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  have hb : TopologicalSpace.Opens.IsBasis (Set.range (fun U : X.affineOpens => e ⁻¹ᵁ U.1)) := by
    have hb₀ := X.isBasis_affineOpens.isInducing e.isEmbedding.isInducing
    have hset : (SetLike.coe '' Set.range (fun U : X.affineOpens => e ⁻¹ᵁ U.1)) =
        (Set.preimage e '' (SetLike.coe '' X.affineOpens)) := by
      ext V
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨V,⟨U,rfl⟩,rfl⟩
        exact ⟨U.1, ⟨U.1,U.2,rfl⟩,rfl⟩
      · rintro ⟨V,⟨U,hU,rfl⟩,hV⟩
        exact ⟨e ⁻¹ᵁ U, ⟨⟨U,hU⟩,rfl⟩,hV⟩
    change TopologicalSpace.IsTopologicalBasis (SetLike.coe '' Set.range (fun U : X.affineOpens => e ⁻¹ᵁ U.1))
    rw [hset]
    exact hb₀
  haveI : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hb fun U =>
    by
    exact (AddEquiv.ofBijective _ (h U)).toAddCommGrpIso.isIso_hom
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  haveI : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  haveI : IsIso (ψ.hom.app (op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (op V))
    infer_instance
  exact inferInstanceAs (IsIso (ψ.hom.app (op V)))

#print axioms isIso_of_affine_preimage_bijective
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (e : Spec (.of R) ⟶ X)

lemma smooth_sections [Smooth c] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := c.sectionsAlgebra U
    Algebra.FormallySmooth R Γ(X,U) := by
  have h : (c.appLE ⊤ U le_top).hom.FormallySmooth :=
    (c.smooth_appLE (isAffineOpen_top _) hU le_top).formallySmooth
  have h' : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.FormallySmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr h
  exact h'.toAlgebra

lemma etale_sections_id (U : (Spec (.of R)).Opens) (hU : IsAffineOpen U) :
    ((Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op U)).hom.Etale := by
  have h : (Scheme.Hom.appLE (𝟙 (Spec (.of R))) ⊤ U le_top).hom.Etale :=
    Scheme.Hom.etale_appLE (𝟙 (Spec (.of R))) (isAffineOpen_top _) hU le_top
  have h' : ((Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Hom.appLE (𝟙 (Spec (.of R))) ⊤ U le_top).hom.Etale := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).mpr h
  exact h'

lemma section_scalar (he : e ≫ c = 𝟙 _) (U : X.Opens) :
    c.constToPresheaf.app (op U) ≫ e.app U =
      (Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op (e ⁻¹ᵁ U)) := by
  dsimp only [Scheme.Hom.constToPresheaf]
  rw [Category.assoc, e.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  congr 1
  rw [he]

lemma section_conormal_bijective [IsClosedImmersion e] [Smooth c]
    (he : e ≫ c = 𝟙 _) (hI : e.ker.IsInvertible)
    (hΩ : Scheme.Modules.IsInvertible c.kaehler) (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective ((conormalMap c e).app (e ⁻¹ᵁ U)) := by
  apply conormalMap_app_bijective c e hI hΩ U hU (smooth_sections c U hU)
  have hring : ((e.app U).hom.comp (c.constToPresheaf.app (op U)).hom).Etale := by
    rw [← CommRingCat.hom_comp, section_scalar c e he U]
    exact etale_sections_id (e ⁻¹ᵁ U) (hU.preimage e)
  exact hring.toAlgebra.formallyEtale

#print axioms section_conormal_bijective
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

lemma section_conormal_isIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (e : Spec (.of R) ⟶ X)
    [IsClosedImmersion e] [Smooth c] (he : e ≫ c = 𝟙 _)
    (hI : e.ker.IsInvertible) (hΩ : Scheme.Modules.IsInvertible c.kaehler) :
    IsIso (conormalMap c e) :=
  isIso_of_affine_preimage_bijective e (conormalMap c e) fun U =>
    section_conormal_bijective c e he hI hΩ U.1 U.2

lemma origin_conormal_trivial (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R) :
    Nonempty ((SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules) ≅
      (Scheme.Modules.pullback (Q.zero)).obj (Q.zero).ker.module) := by
  let c := Q.structureMap
  let e := Q.zero
  have he : e ≫ c = 𝟙 _ := Q.zero_over
  letI : IsProper c := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 c := Q.smooth_dimension_one
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ c) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e c
  have hΩ : Scheme.Modules.IsInvertible c.kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (c.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  haveI : IsIso (conormalMap c e) :=
    section_conormal_isIso c e he (Q.zero_ideal_invertible) hΩ
  obtain ⟨η⟩ := Q.hodge_trivial
  exact ⟨η ≪≫ (asIso (conormalMap c e)).symm⟩

#print axioms origin_conormal_trivial
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

lemma pullback_pow_module_trivial {X S : Scheme.{u}} (e : S ⟶ X) (I : X.IdealSheafData)
    (hI : I.IsInvertible) (h : Nonempty ((Scheme.Modules.pullback e).obj I.module ≅ 𝟙_ S.Modules))
    (m : ℕ) (hm : 0 < m) :
    Nonempty ((Scheme.Modules.pullback e).obj (I ^ m).module ≅ 𝟙_ S.Modules) := by
  obtain ⟨η⟩ := h
  induction m, hm using Nat.le_induction with
  | base => simpa only [pow_one] using (⟨η⟩ : Nonempty _)
  | succ m hm ih =>
    obtain ⟨α⟩ := ih
    obtain ⟨β⟩ := (hI.pow m).nonempty_mul_module_iso_tensor hI
    rw [pow_succ]
    exact ⟨(Scheme.Modules.pullback e).mapIso β ≪≫ Scheme.Modules.pullbackTensorObjIso e _ _ ≪≫
      (α ⊗ᵢ η) ≪≫ (λ_ (𝟙_ S.Modules))⟩

lemma pullback_pow_invModule_trivial {X S : Scheme.{u}} (e : S ⟶ X) (I : X.IdealSheafData)
    (hI : I.IsInvertible) (h : Nonempty ((Scheme.Modules.pullback e).obj I.module ≅ 𝟙_ S.Modules))
    (m : ℕ) (hm : 0 < m) :
    Nonempty ((Scheme.Modules.pullback e).obj (I ^ m).invModule ≅ 𝟙_ S.Modules) := by
  obtain ⟨η⟩ := pullback_pow_module_trivial e I hI h m hm
  obtain ⟨β⟩ := ((hI.pow m).isInvertible_module).pullback_dual e
  let δ := ((MonoidalClosed.internalHom (C := S.Modules)).mapIso η.symm.op).app (𝟙_ S.Modules)
  exact ⟨β ≪≫ δ ≪≫ MonoidalClosed.unitIsoSelf _⟩

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
lemma origin_power_restriction_trivial (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    Nonempty ((Scheme.Modules.pullback (Q.zero)).obj
      ((Q.zero).ker ^ m).invModule ≅ 𝟙_ (Spec (.of R)).Modules) := by
  obtain ⟨η⟩ := origin_conormal_trivial R Q
  exact pullback_pow_invModule_trivial (Q.zero) _
    (Q.zero_ideal_invertible) ⟨η.symm⟩ m hm

#print axioms origin_power_restriction_trivial
#print axioms pullback_pow_invModule_trivial
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
open PositiveSections.Sections.P2mSectionsBaseChangeH0
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

 def ofModulesHom {M N : X.Modules} (φ : M ⟶ N) :
    OModulePresheaf.Hom (OModulePresheaf.ofModules c M) (OModulePresheaf.ofModules c N) where
  app U :=
    { toFun := φ.app U
      map_add' := map_add _
      map_smul' r x := by
        change φ.app U ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r • x) = _
        exact Scheme.Modules.Hom.app_smul φ _ x }
  app_smul U a x := Scheme.Modules.Hom.app_smul φ a x
  naturality {U V} h := by
    ext x
    exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

def ofShortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hM : Scheme.Modules.IsInvertible S.X₁) :
    OModulePresheaf.AffSES (OModulePresheaf.ofModules c S.X₁)
      (OModulePresheaf.ofModules c S.X₂) (OModulePresheaf.ofModules c S.X₃) where
  inc := (ofModulesHom c S.f).toAffHom
  proj := (ofModulesHom c S.g).toAffHom
  injective U := (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f U.1
  surjective U := Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS hM.1 U.1 U.2
  exact U := by
    haveI := hS.mono_f
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      change S.g.app U.1 (S.f.app U.1 x) = 0
      exact congrArg (fun φ => φ.app U.1 x) S.zero
    · intro x hx
      exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact U.1 x hx

lemma sectionsEquivH0_natural [IsSeparated c] {M N : X.Modules} (φ : M ⟶ N)
    (K : X.OrderedAffineCover) (x : Γ(M,⊤)) :
    (ofModulesHom c φ).toAffHom.H0Map K (sectionsEquivH0 c M K x) =
      sectionsEquivH0 c N K (φ.app ⊤ x) := by
  apply Subtype.ext
  funext s
  change φ.app (K.inter s) (M.presheaf.map (homOfLE le_top).op x) =
    N.presheaf.map (homOfLE le_top).op (φ.app ⊤ x)
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE le_top).op) x

lemma surjective_global_sections [IsSeparated c]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hM : Scheme.Modules.IsInvertible S.X₁) (K : X.OrderedAffineCover)
    (hH : Subsingleton ((OModulePresheaf.ofModules c S.X₁).HSucc K 0)) :
    Function.Surjective (S.g.app ⊤) := by
  let SES := ofShortExact c S hS hM
  obtain ⟨δ₀,δ,hδ₀,-,-,-⟩ := SES.exists_connectingHom K
  intro x
  have hx : sectionsEquivH0 c S.X₃ K x ∈ LinearMap.ker δ₀ := Subsingleton.elim _ _
  obtain ⟨z,hz⟩ := hδ₀ hx
  obtain ⟨y,hy⟩ := (sectionsEquivH0 c S.X₂ K).surjective z
  refine ⟨y, (sectionsEquivH0 c S.X₃ K).injective ?_⟩
  rw [← sectionsEquivH0_natural c S.g K y, hy]
  exact hz

lemma subsingleton_higher_of_iso [IsSeparated c] {M N : X.Modules} (e : M ≅ N)
    (K : X.OrderedAffineCover) (i : ℕ)
    (hN : Subsingleton ((OModulePresheaf.ofModules c N).HSucc K i)) :
    Subsingleton ((OModulePresheaf.ofModules c M).HSucc K i) := by
  let f := (ofModulesHom c e.hom).toAffHom.HSuccMap K i
  let g := (ofModulesHom c e.inv).toAffHom.HSuccMap K i
  have hgf : Function.LeftInverse g f := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk x
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      funext s
      exact congrArg (fun φ => φ.app (K.inter s) (x.1 s)) e.hom_inv_id
  exact hgf.injective.subsingleton

#print axioms subsingleton_higher_of_iso
#print axioms surjective_global_sections
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact

lemma ideal_tensor_succ_inv {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible) (m : ℕ) :
    Nonempty (I.module ⊗ (I ^ (m+1)).invModule ≅ (I ^ m).invModule) := by
  obtain ⟨α⟩ := hI.nonempty_mul_invModule_iso_tensor (hI.pow m)
  obtain ⟨⟨β⟩,-⟩ := hI.nonempty_module_tensor_invModule_iso
  rw [pow_succ']
  exact ⟨(Iso.refl _ ⊗ᵢ α) ≪≫ (α_ _ _ _).symm ≪≫ (β ⊗ᵢ Iso.refl _) ≪≫ (λ_ _)⟩

lemma origin_shortExact (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) :
    ∃ S : ShortComplex Q.target.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ ((Q.zero).ker ^ m).invModule) ∧
      Nonempty (S.X₂ ≅ ((Q.zero).ker ^ (m+1)).invModule) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (Q.zero)).obj
        (𝟙_ (Spec (.of R)).Modules)) := by
  let e := Q.zero
  let I := e.ker
  let M := (I ^ (m+1)).invModule
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ Q.structureMap) := by
      rw [Q.zero_over]; infer_instance
    exact IsClosedImmersion.of_comp e Q.structureMap
  have hI : I.IsInvertible := Q.zero_ideal_invertible
  have hM : Scheme.Modules.IsInvertible M := (hI.pow (m+1)).isInvertible_invModule
  obtain ⟨S,hS,⟨α⟩,h₂,⟨γ⟩⟩ := Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
    e M ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible M).mpr hM)
  obtain ⟨β⟩ := ideal_tensor_succ_inv I hI m
  obtain ⟨η⟩ := Conormal.origin_power_restriction_trivial R Q (m+1) (Nat.succ_pos _)
  exact ⟨S,hS,⟨α ≪≫ β⟩,h₂,⟨γ ≪≫ (Scheme.Modules.pushforward e).mapIso η⟩⟩

lemma origin_global_shortExact (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    ∃ S : ShortComplex Q.target.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ ((Q.zero).ker ^ m).invModule) ∧
      Nonempty (S.X₂ ≅ ((Q.zero).ker ^ (m+1)).invModule) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (Q.zero)).obj
        (𝟙_ (Spec (.of R)).Modules)) ∧ Function.Surjective (S.g.app ⊤) := by
  obtain ⟨S,hS,⟨α⟩,h₂,h₃⟩ := origin_shortExact R Q m
  have hM : Scheme.Modules.IsInvertible S.X₁ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨η⟩⟩ := ((Q.zero_ideal_invertible).pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso α ≪≫ η⟩⟩
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : CompactSpace Q.target := QuasiCompact.compactSpace_of_compactSpace Q.structureMap
  let K := PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact Q.target
  have hH := PositiveSections.Actual.positive_higher_cohomology R Q m hm K 0
  exact ⟨S,hS,⟨α⟩,h₂,h₃,surjective_global_sections Q.structureMap S hS hM K
    (subsingleton_higher_of_iso Q.structureMap α K 0 hH)⟩

#print axioms origin_global_shortExact
#print axioms origin_shortExact
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact

lemma split_linear_sequence {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g) :
    Nonempty (N ≃ₗ[R] M × P) := by
  obtain ⟨s,hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hgf (x : M) : g (f x) = 0 := by
    exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f x)
  have hgs (x : P) : g (s x) = x := LinearMap.congr_fun hs x
  let l := f.coprod s
  have hl : Function.Bijective l := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨x,y⟩ h
      have hy : y = 0 := by
        have hh := congrArg g h
        simpa only [l, LinearMap.coprod_apply, map_add, hgf, hgs, zero_add, map_zero] using hh
      have hx : x = 0 := hf (by simpa [l,hy] using h)
      simp [hx,hy]
    · intro x
      have hx : x - s (g x) ∈ LinearMap.range f := by
        rw [hex,LinearMap.mem_ker,map_sub,hgs,sub_self]
      obtain ⟨y,hy⟩ := hx
      exact ⟨(y,g x),by simpa [l,hy]⟩
  exact ⟨(LinearEquiv.ofBijective l hl).symm⟩

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

def pushforward_unit_sections (e : Spec (.of R) ⟶ X) (he : e ≫ c = 𝟙 _) :
    let M := (Scheme.Modules.pushforward e).obj (𝟙_ (Spec (.of R)).Modules)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    Γ(M,⊤) ≃ₗ[R] R := by
  let M := (Scheme.Modules.pushforward e).obj (𝟙_ (Spec (.of R)).Modules)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
  let φ : Γ(M,⊤) ≃+ R :=
    ((Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toAddEquiv : Γ(Spec (.of R),⊤) ≃+ R)
  refine { φ with map_smul' := ?_ }
  intro r x
  have hr := congrArg (fun f => f.hom r) (Conormal.section_scalar c e he ⊤)
  change (Scheme.ΓSpecIso (.of R)).hom.hom
      ((show Γ(Spec (.of R),⊤) from (e.app ⊤).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ ⊤ le_top).hom r)) * (show Γ(Spec (.of R),⊤) from x)) =
    r * (Scheme.ΓSpecIso (.of R)).hom.hom x
  rw [map_mul]
  congr 1
  rw [← CommRingCat.comp_apply]
  change (Scheme.ΓSpecIso (.of R)).hom.hom ((c.constToPresheaf.app (op ⊤) ≫ e.app ⊤).hom r) = r
  rw [hr]
  simp [Scheme.Hom.constToPresheaf,Scheme.Hom.appLE]

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
lemma origin_sections_succ_split (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let M := ((Q.zero).ker ^ m).invModule
    let N := ((Q.zero).ker ^ (m+1)).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
    Nonempty (Γ(N,⊤) ≃ₗ[R] Γ(M,⊤) × R) := by
  let M := ((Q.zero).ker ^ m).invModule
  let N := ((Q.zero).ker ^ (m+1)).invModule
  let T := (Scheme.Modules.pushforward (Q.zero)).obj (𝟙_ (Spec (.of R)).Modules)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap T ⊤
  obtain ⟨S,hS,⟨α⟩,⟨β⟩,⟨γ⟩,hsurj⟩ := origin_global_shortExact R Q m hm
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₁ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₂ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₃ ⊤
  let e₁ := FibreCohomology.sectionsIsoLinear Q.structureMap α ⊤
  let e₂ := FibreCohomology.sectionsIsoLinear Q.structureMap β ⊤
  let e₃ := (FibreCohomology.sectionsIsoLinear Q.structureMap γ ⊤) ≪≫ₗ
    pushforward_unit_sections Q.structureMap (Q.zero) (Q.zero_over)
  letI : Module.Projective R Γ(S.X₃,⊤) := Module.Projective.of_equiv e₃.symm
  let f : Γ(S.X₁,⊤) →ₗ[R] Γ(S.X₂,⊤) := (ofModulesHom Q.structureMap S.f).app ⊤
  let g : Γ(S.X₂,⊤) →ₗ[R] Γ(S.X₃,⊤) := (ofModulesHom Q.structureMap S.g).app ⊤
  haveI := hS.mono_f
  have hf : Function.Injective f := (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f ⊤
  have hex : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      change S.g.app ⊤ (S.f.app ⊤ x) = 0
      exact congrArg (fun φ => φ.app ⊤ x) S.zero
    · intro x hx
      exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact ⊤ x hx
  obtain ⟨ε⟩ := split_linear_sequence f g hf hsurj hex
  exact ⟨e₂.symm ≪≫ₗ ε ≪≫ₗ e₁.prodCongr e₃⟩

#print axioms origin_sections_succ_split
#print axioms pushforward_unit_sections
#print axioms split_linear_sequence
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open scoped TensorProduct
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact

lemma exact_rank_one (R K M : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [Module.Flat R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hRK : Function.Injective (algebraMap R K))
    (hM : Module.finrank K (K ⊗[R] M) = 1)
    (f : R →ₗ[R] M) (g : M →ₗ[R] R) (hf : Function.Injective f)
    (hex : LinearMap.range f = LinearMap.ker g) : Function.Bijective f := by
  have hfK : Function.Injective (f.baseChange K) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hr : Module.finrank K (K ⊗[R] R) = Module.finrank K (K ⊗[R] M) := by
    rw [hM, (TensorProduct.AlgebraTensorModule.rid R K K).finrank_eq, Module.finrank_self]
  have hsK : Function.Surjective (f.baseChange K) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp hfK
  have hgf : g ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro r
    change g (f r) = 0
    exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f r)
  have hgK : g.baseChange K = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := hsK x
    change ((g.baseChange K) ∘ₗ (f.baseChange K)) y = 0
    rw [← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_zero]
    rfl
  have hg : g = 0 := by
    ext x
    have h := LinearMap.congr_fun hgK ((1 : K) ⊗ₜ[R] x)
    have h' := congrArg (TensorProduct.AlgebraTensorModule.rid R K K) h
    apply hRK
    simpa [LinearMap.baseChange_tmul, Algebra.smul_def] using h'
  refine ⟨hf, LinearMap.range_eq_top.mp ?_⟩
  rw [hex,hg,LinearMap.ker_zero]

lemma zero_power_inv_trivial {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible) :
    Nonempty ((I ^ 0).invModule ≅ 𝟙_ X.Modules) := by
  obtain ⟨α⟩ := ideal_tensor_succ_inv I hI 0
  obtain ⟨⟨β⟩,-⟩ := hI.nonempty_module_tensor_invModule_iso
  simp only [zero_add, pow_one] at α
  exact ⟨α.symm ≪≫ β⟩

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
def unit_sections (hc : Function.Bijective (c.app ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c (𝟙_ X.Modules) ⊤
    R ≃ₗ[R] Γ(𝟙_ X.Modules,⊤) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c (𝟙_ X.Modules) ⊤
  let f : R →ₗ[R] Γ(𝟙_ X.Modules,⊤) :=
    { toFun := algebraMap R Γ(X,⊤)
      map_add' := map_add _
      map_smul' := fun r s => by
        change (algebraMap R Γ(X,⊤)) (r*s) = (algebraMap R Γ(X,⊤)) r * (algebraMap R Γ(X,⊤)) s
        exact map_mul _ _ _ }
  apply LinearEquiv.ofBijective f
  change Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ ⊤ le_top).hom
  have hc' : Function.Bijective (c.appLE ⊤ ⊤ le_top) := by
    simpa [Scheme.Hom.appLE] using hc
  exact hc'.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)

#print axioms exact_rank_one
#print axioms unit_sections

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
lemma origin_first_sections (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R) :
    let M := ((Q.zero).ker ^ 1).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Nonempty (Γ(M,⊤) ≃ₗ[R] R) := by
  let I := (Q.zero).ker
  let M := (I ^ 1).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  obtain ⟨S,hS,⟨α⟩,⟨β⟩,⟨γ⟩⟩ := origin_shortExact R Q 0
  obtain ⟨δ⟩ := zero_power_inv_trivial I (Q.zero_ideal_invertible)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₁ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₂ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₃ ⊤
  let e₁ := (FibreCohomology.sectionsIsoLinear Q.structureMap (α ≪≫ δ) ⊤) ≪≫ₗ
    (unit_sections Q.structureMap (Q.structure_app_bijective ⊤)).symm
  let e₂ : Γ(S.X₂,⊤) ≃ₗ[R] Γ(M,⊤) := FibreCohomology.sectionsIsoLinear Q.structureMap β ⊤
  let e₃ := (FibreCohomology.sectionsIsoLinear Q.structureMap γ ⊤) ≪≫ₗ
    pushforward_unit_sections Q.structureMap (Q.zero) (Q.zero_over)
  let f₀ : Γ(S.X₁,⊤) →ₗ[R] Γ(S.X₂,⊤) := (ofModulesHom Q.structureMap S.f).app ⊤
  let g₀ : Γ(S.X₂,⊤) →ₗ[R] Γ(S.X₃,⊤) := (ofModulesHom Q.structureMap S.g).app ⊤
  let f := f₀ ∘ₗ e₁.symm.toLinearMap
  let g := e₃.toLinearMap ∘ₗ g₀
  haveI := hS.mono_f
  have hf₀ : Function.Injective f₀ := (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f ⊤
  have hex : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨r,rfl⟩
      change e₃ (S.g.app ⊤ (S.f.app ⊤ (e₁.symm r))) = 0
      rw [show S.g.app ⊤ (S.f.app ⊤ (e₁.symm r)) = 0 from
        congrArg (fun φ => φ.app ⊤ (e₁.symm r)) S.zero, map_zero]
    · intro x hx
      change e₃ (S.g.app ⊤ x) = 0 at hx
      have hx₀ : S.g.app ⊤ x = 0 := e₃.injective (by simpa only [map_zero] using hx)
      obtain ⟨y,hy⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact ⊤ x hx₀
      refine ⟨e₁ y, ?_⟩
      change S.f.app ⊤ (e₁.symm (e₁ y)) = x
      rw [e₁.symm_apply_apply]
      exact hy
  haveI : Module.Finite R Γ(M,⊤) :=
    (PositiveSections.Actual.positive_sections_baseChange R Q 1 (by omega)).1.1
  letI : Module.Finite R Γ(S.X₂,⊤) := Module.Finite.equiv e₂.symm
  let K := AlgebraicClosure (FractionRing R)
  letI : Module.Flat R K := Module.Flat.trans R (FractionRing R) K
  have hRK : Function.Injective (algebraMap R K) :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hr : Module.finrank K (K ⊗[R] Γ(S.X₂,⊤)) = 1 :=
    (e₂.baseChange R K _ _).finrank_eq.trans
      (PositiveSections.Actual.positive_sections_geometric_rank R Q 1 (by omega) K)
  have hf := exact_rank_one R K Γ(S.X₂,⊤) hRK hr f g (hf₀.comp e₁.symm.injective) hex
  exact ⟨e₂.symm ≪≫ₗ (LinearEquiv.ofBijective f hf).symm⟩

#print axioms origin_first_sections
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact

lemma origin_positive_sections_free (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let M := ((Q.zero).ker ^ m).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Module.Free R Γ(M,⊤) ∧ Module.finrank R Γ(M,⊤) = m := by
  induction m, hm using Nat.le_induction with
  | base =>
    let M := ((Q.zero).ker ^ 1).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    obtain ⟨ε⟩ := origin_first_sections R Q
    exact ⟨Module.Free.of_equiv ε.symm, ε.finrank_eq.trans (Module.finrank_self R)⟩
  | succ m hm ih =>
    let M := ((Q.zero).ker ^ m).invModule
    let N := ((Q.zero).ker ^ (m+1)).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
    haveI : Module.Free R Γ(M,⊤) := ih.1
    haveI : Module.Finite R Γ(M,⊤) :=
      (PositiveSections.Actual.positive_sections_baseChange R Q m hm).1.1
    obtain ⟨ε⟩ := origin_sections_succ_split R Q m hm
    refine ⟨Module.Free.of_equiv ε.symm, ε.finrank_eq.trans ?_⟩
    rw [Module.finrank_prod, ih.2, Module.finrank_self]

lemma origin_positive_sections_basis (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let M := ((Q.zero).ker ^ m).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Nonempty (Module.Basis (Fin m) R Γ(M,⊤)) := by
  let M := ((Q.zero).ker ^ m).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  obtain ⟨hfree,hrank⟩ := origin_positive_sections_free R Q m hm
  letI := hfree
  letI : Module.Finite R Γ(M,⊤) :=
    (PositiveSections.Actual.positive_sections_baseChange R Q m hm).1.1
  exact ⟨Module.finBasisOfFinrankEq R Γ(M,⊤) hrank⟩

#print axioms origin_positive_sections_free
#print axioms origin_positive_sections_basis
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionExact
end


namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionRing
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeCyclicQuotientR0173

/-- The framed curve has an actual graded section ring for the inverse
origin ideal.  This packages all positive origin-power sections and their
multiplication without choosing bases or assuming a presentation. -/
theorem exists_origin_section_ring (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (Q : FramedCurve R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (𝓐 : ℕ → Submodule R A) (_ : GradedAlgebra 𝓐)
      (ι : ∀ m : ℕ, 𝓐 m → Γ(((Q.zero).ker.invModule).tensorPow m, ⊤)),
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing Q.structureMap
        (Q.zero).ker.invModule A 𝓐 ι := by
  let I := (Q.zero).ker
  have hI : I.IsInvertible := Q.zero_ideal_invertible
  exact AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
    Q.structureMap I.invModule hI.isInvertible_invModule

#print axioms exists_origin_section_ring
end
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionRing

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open SectionExact
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

/-- Surjectivity for the actual adjunction restriction map to the origin subscheme. -/
lemma surjective_origin_restriction (m : ℕ) (hm : 0 < m) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction Q.zero.ker.subschemeι).unit.app
      (Q.zero.ker ^ (m+1)).invModule).app ⊤) := by
  let I := Q.zero.ker
  let M := (I ^ m).invModule
  let N := (I ^ (m+1)).invModule
  have hI := Q.zero_ideal_invertible
  have hN : Scheme.Modules.IsLocallyFreeOfRank 1 N :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
      (hI.pow (m+1)).isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I N hN
  let S := ShortComplex.mk ((N ◁ I.moduleι) ≫ (ρ_ N).hom) _ w
  obtain ⟨α⟩ := ideal_tensor_succ_inv I hI m
  let δ : N ⊗ I.module ≅ M := (β_ N I.module) ≪≫ α
  have hM : Scheme.Modules.IsInvertible (N ⊗ I.module) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨η⟩⟩ := (hI.pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ ≪≫ η⟩⟩
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : CompactSpace Q.target := QuasiCompact.compactSpace_of_compactSpace Q.structureMap
  let K := PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact Q.target
  have hH := PositiveSections.Actual.positive_higher_cohomology R Q m hm K 0
  exact surjective_global_sections Q.structureMap S hS hM K
    (subsingleton_higher_of_iso Q.structureMap δ K 0 hH)


lemma surjective_identity_restriction (m : ℕ) (hm : 0 < m) :
    Function.Surjective (Scheme.Modules.pullbackLocalSection Q.zero
      (L := (Q.zero.ker ^ (m+1)).invModule) (U := ⊤)) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by
    rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  intro y
  exact Scheme.Modules.exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
    Q.zero.ker.subschemeι (asIso Q.zero.toImage) Q.zero Q.zero.toImage_imageι
    _ (surjective_origin_restriction R Q m hm) y

lemma surjective_pullback_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (e : M ≅ N)
    (h : Function.Surjective (Scheme.Modules.pullbackLocalSection f (L := M) (U := ⊤))) :
    Function.Surjective (Scheme.Modules.pullbackLocalSection f (L := N) (U := ⊤)) := by
  let δ := (Scheme.Modules.pullback f).mapIso e
  intro y
  obtain ⟨x,hx⟩ := h (δ.inv.app (f ⁻¹ᵁ ⊤) y)
  refine ⟨e.hom.app ⊤ x, ?_⟩
  rw [Scheme.Modules.pullbackLocalSection_app, hx]
  change (δ.inv ≫ δ.hom).app (f ⁻¹ᵁ ⊤) y = y
  rw [δ.inv_hom_id]
  rfl

lemma invPower_tensorPower {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.IsInvertible) (m : ℕ) :
    Nonempty ((I ^ m).invModule ≅ I.invModule.tensorPow m) := by
  induction m with
  | zero => exact zero_power_inv_trivial I hI
  | succ m ih =>
    obtain ⟨α⟩ := (hI.pow m).nonempty_mul_invModule_iso_tensor hI
    obtain ⟨β⟩ := ih
    rw [pow_succ]
    exact ⟨α ≪≫ (β ⊗ᵢ Iso.refl _)⟩

/-- Every prescribed value at the actual identity lifts to a section of L^m,
for m at least two, where L is the actual inverse origin ideal. -/
lemma surjective_identity_tensorPower (m : ℕ) (hm : 0 < m) :
    Function.Surjective (Scheme.Modules.pullbackLocalSection Q.zero
      (L := Q.zero.ker.invModule.tensorPow (m+1)) (U := ⊤)) := by
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible (m+1)
  exact surjective_pullback_of_iso Q.zero δ (surjective_identity_restriction R Q m hm)


/-- A frame of the actual inverse origin ideal restricted to the identity. -/
def identityLineFrame : (Scheme.Modules.pullback Q.zero).obj Q.zero.ker.invModule ≅
    𝟙_ (Spec (CommRingCat.of R)).Modules := by
  let η := (Conormal.origin_power_restriction_trivial R Q 1 (by omega)).some
  simpa only [pow_one] using η

/-- Tensor-compatible restriction, before identifying powers of the unit line. -/
def powerRestriction (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    Γ((𝟙_ (Spec (CommRingCat.of R)).Modules).tensorPow m, ⊤) :=
  ((Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
      Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m).hom.app ⊤)
    (Scheme.Modules.pullbackLocalSection Q.zero s)

def unitPower (m : ℕ) : Γ((𝟙_ (Spec (CommRingCat.of R)).Modules).tensorPow m, ⊤) :=
  Scheme.Modules.tensorPowSection (Scheme.Modules.unitSection (X := Spec (CommRingCat.of R)) ⊤) m

lemma exists_normalized_section (m : ℕ) (hm : 0 < m) :
    ∃ s : Γ(Q.zero.ker.invModule.tensorPow (m+1), ⊤),
      powerRestriction R Q (m+1) s = unitPower R (m+1) := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule (m+1) ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) (m+1)
  obtain ⟨s,hs⟩ := surjective_identity_tensorPower R Q m hm
    (η.inv.app ⊤ (unitPower R (m+1)))
  refine ⟨s, ?_⟩
  change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s) = _
  rw [hs]
  change (η.inv ≫ η.hom).app ⊤ (unitPower R (m+1)) = _
  rw [η.inv_hom_id]
  rfl

lemma powerRestriction_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤)) :
    powerRestriction R Q (m+n)
      ((Scheme.Modules.tensorPowAdd Q.zero.ker.invModule m n).hom.app ⊤
        (Scheme.Modules.tensorSections s t)) =
      (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (CommRingCat.of R)).Modules) m n).hom.app ⊤
        (Scheme.Modules.tensorSections (powerRestriction R Q m s) (powerRestriction R Q n t)) :=
  Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
    Q.zero Q.zero.ker.invModule _ (identityLineFrame R Q) m n s t

lemma normalized_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤))
    (hs : powerRestriction R Q m s = unitPower R m)
    (ht : powerRestriction R Q n t = unitPower R n) :
    powerRestriction R Q (m+n)
      ((Scheme.Modules.tensorPowAdd Q.zero.ker.invModule m n).hom.app ⊤
        (Scheme.Modules.tensorSections s t)) = unitPower R (m+n) := by
  rw [powerRestriction_mul, hs, ht]
  exact Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection _ m n

lemma exists_normalized_coordinates :
    ∃ (x : Γ(Q.zero.ker.invModule.tensorPow 2, ⊤))
      (y : Γ(Q.zero.ker.invModule.tensorPow 3, ⊤)),
      powerRestriction R Q 2 x = unitPower R 2 ∧
      powerRestriction R Q 3 y = unitPower R 3 := by
  obtain ⟨x,hx⟩ := exists_normalized_section R Q 1 (by omega)
  obtain ⟨y,hy⟩ := exists_normalized_section R Q 2 (by omega)
  exact ⟨x,y,hx,hy⟩


def sectionMul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤)) :
    Γ(Q.zero.ker.invModule.tensorPow (m+n), ⊤) :=
  (Scheme.Modules.tensorPowAdd Q.zero.ker.invModule m n).hom.app ⊤
    (Scheme.Modules.tensorSections s t)

lemma powerRestriction_sub (m : ℕ) (s t : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    powerRestriction R Q m (s-t) = powerRestriction R Q m s - powerRestriction R Q m t := by
  unfold powerRestriction
  rw [Scheme.Modules.pullbackLocalSection_sub, map_sub]

/-- The leading polar coefficients of y² and x³ agree.  The full cubic relation
requires the subsequent filtration descent, which is not asserted here. -/
lemma exists_coordinates_cubic_difference_restricts_zero :
    ∃ (x : Γ(Q.zero.ker.invModule.tensorPow 2, ⊤))
      (y : Γ(Q.zero.ker.invModule.tensorPow 3, ⊤)),
      powerRestriction R Q 2 x = unitPower R 2 ∧
      powerRestriction R Q 3 y = unitPower R 3 ∧
      powerRestriction R Q 6
        (sectionMul R Q 3 3 y y - sectionMul R Q 4 2 (sectionMul R Q 2 2 x x) x) = 0 := by
  obtain ⟨x,y,hx,hy⟩ := exists_normalized_coordinates R Q
  refine ⟨x,y,hx,hy,?_⟩
  rw [powerRestriction_sub]
  have hy2 := normalized_mul R Q 3 3 y y hy hy
  have hx2 := normalized_mul R Q 2 2 x x hx hx
  have hx3 := normalized_mul R Q 4 2 (sectionMul R Q 2 2 x x) x hx2 hx
  exact sub_eq_zero.mpr (hy2.trans hx3.symm)

#print axioms exists_coordinates_cubic_difference_restricts_zero
#print axioms exists_normalized_coordinates
#print axioms normalized_mul
#print axioms surjective_identity_tensorPower
#print axioms surjective_origin_restriction
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

lemma pullbackLocalSection_injective_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Y.Modules) (U : Y.Opens) :
    Function.Injective (Scheme.Modules.pullbackLocalSection e.hom (L := M) (U := U)) := by
  have δ : M ≅ (Scheme.Modules.pushforward e.hom).obj
      ((Scheme.Modules.pushforward e.inv).obj M) :=
    ((Scheme.Modules.pushforwardId Y).app M).symm ≪≫
      ((Scheme.Modules.pushforwardCongr e.inv_hom_id).app M).symm ≪≫
      ((Scheme.Modules.pushforwardComp e.inv e.hom).app M).symm
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M) :=
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom).isIso_unit_app_of_iso δ
  exact (Scheme.Modules.Hom.mono_iff_injective _).mp (inferInstance : Mono
    ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M)) U

lemma restriction_zero_of_iso_hom_comp_eq {X P X₀ : Scheme.{u}}
    (p : P ⟶ X) (e : X₀ ≅ P) (g : X₀ ⟶ X) (hge : e.hom ≫ p = g)
    (M : X.Modules) (s : Γ(M,⊤))
    (hs : Scheme.Modules.pullbackLocalSection g s = 0) :
    Scheme.Modules.pullbackLocalSection p s = 0 := by
  subst hge
  apply (pullbackLocalSection_injective_of_iso e ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ ⊤))
  rw [Scheme.Modules.pullbackLocalSection_zero]
  have h := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection e.hom p M ⊤ s
  rw [hs] at h
  exact (Scheme.Modules.Hom.mono_iff_injective
    ((Scheme.Modules.pullbackComp e.hom p).hom.app M)).mp inferInstance _
      (by simpa only [map_zero] using h)

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

/-- The actual zero restriction criterion gives a lift through multiplication
by the actual ideal inclusion, before cancelling its inverse line. -/
lemma exists_ideal_lift (m : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (hs : powerRestriction R Q m s = 0) :
    ∃ t : Γ(Q.zero.ker.invModule.tensorPow m ⊗ Q.zero.ker.module, ⊤),
      ((Q.zero.ker.invModule.tensorPow m ◁ Q.zero.ker.moduleι) ≫
        (ρ_ (Q.zero.ker.invModule.tensorPow m)).hom).app ⊤ t = s := by
  let I := Q.zero.ker
  let M := I.invModule.tensorPow m
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero I.invModule m ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m
  have hzero : Scheme.Modules.pullbackLocalSection Q.zero s = 0 :=
    (Scheme.Modules.Hom.mono_iff_injective η.hom).mp inferInstance ⊤
      (by
        rw [map_zero]
        exact hs)
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by
    rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  have hz := restriction_zero_of_iso_hom_comp_eq I.subschemeι (asIso Q.zero.toImage)
    Q.zero Q.zero.toImage_imageι M s hzero
  obtain ⟨δ⟩ := invPower_tensorPower I Q.zero_ideal_invertible m
  have hMinv : Scheme.Modules.IsInvertible M := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨ε⟩⟩ := (Q.zero_ideal_invertible.pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ.symm ≪≫ ε⟩⟩
  have hM : Scheme.Modules.IsLocallyFreeOfRank 1 M :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hMinv
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I M hM
  haveI := hS.mono_f
  exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
    (ShortComplex.mk _ _ w) hS.exact ⊤ s hz

#print axioms exists_ideal_lift
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
end

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicAlgebra
variable {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R) (z : 𝓐 1)
variable (drop : ∀ m (a : 𝓐 (m+1)), lead (m+1) a = 0 →
  ∃ b : 𝓐 m, (z : A) * b = a)

include drop
lemma subtract_lift (m : ℕ) (t a : 𝓐 (m+1)) (ht : lead (m+1) t = 1) :
    ∃ b : 𝓐 m, (z : A) * b + algebraMap R A (lead (m+1) a) * t = a := by
  have h : lead (m+1) (a - (lead (m+1) a) • t) = 0 := by
    rw [map_sub, map_smul, ht, smul_eq_mul, mul_one, sub_self]
  obtain ⟨b,hb⟩ := drop m _ h
  refine ⟨b, ?_⟩
  simp only [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def] at hb
  exact eq_sub_iff_add_eq.mp hb

/-- Algebraic descent through the actual graded restriction kernels will
supply this lemma's hypotheses. This lemma performs all coefficient extraction;
it does not assume the cubic relation. -/
lemma cubic_of_exact_pole_filtration
    (mul_lead : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
      lead (m+n) ⟨(a : A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
    (degree_one : ∀ a : 𝓐 1, ∃ r : R, (a : A) = algebraMap R A r * z)
    (x : 𝓐 2) (y : 𝓐 3) (hx : lead 2 x = 1) (hy : lead 3 y = 1) :
    ∃ a1 a2 a3 a4 a6 : R,
      (y : A)^2 + algebraMap R A a1 * x * y * z + algebraMap R A a3 * y * z^3 =
        (x : A)^3 + algebraMap R A a2 * x^2 * z^2 +
          algebraMap R A a4 * x * z^4 + algebraMap R A a6 * z^6 := by
  let xx : 𝓐 4 := ⟨(x : A)*x, SetLike.mul_mem_graded x.2 x.2⟩
  let xy : 𝓐 5 := ⟨(x : A)*y, SetLike.mul_mem_graded x.2 y.2⟩
  let yy : 𝓐 6 := ⟨(y : A)*y, SetLike.mul_mem_graded y.2 y.2⟩
  let xxx : 𝓐 6 := ⟨(xx : A)*x, SetLike.mul_mem_graded xx.2 x.2⟩
  have hxx : lead 4 xx = 1 := by rw [mul_lead 2 2 x x, hx, one_mul]
  have hxy : lead 5 xy = 1 := by rw [mul_lead 2 3 x y, hx, hy, one_mul]
  have hyy : lead 6 yy = 1 := by rw [mul_lead 3 3 y y, hy, one_mul]
  have hxxx : lead 6 xxx = 1 := by rw [mul_lead 4 2 xx x, hxx, hx, one_mul]
  have hdiff : lead 6 (yy-xxx) = 0 := by rw [map_sub, hyy, hxxx, sub_self]
  obtain ⟨b5,h5⟩ := drop 5 (yy-xxx) hdiff
  obtain ⟨b4,h4⟩ := subtract_lift 𝓐 lead z drop 4 xy b5 hxy
  obtain ⟨b3,h3⟩ := subtract_lift 𝓐 lead z drop 3 xx b4 hxx
  obtain ⟨b2,h2⟩ := subtract_lift 𝓐 lead z drop 2 y b3 hy
  obtain ⟨b1,h1⟩ := subtract_lift 𝓐 lead z drop 1 x b2 hx
  obtain ⟨r,hr⟩ := degree_one b1
  refine ⟨-lead 5 b5, lead 4 b4, -lead 3 b3, lead 2 b2, r, ?_⟩
  change (z : A)*b5 = (y : A)*y - ((x : A)*x)*x at h5
  change (z : A)*b4 + algebraMap R A (lead 5 b5) * ((x : A)*y) = b5 at h4
  change (z : A)*b3 + algebraMap R A (lead 4 b4) * ((x : A)*x) = b4 at h3
  rw [← h4, ← h3, ← h2, ← h1, hr] at h5
  simp only [map_neg]
  linear_combination -h5

#print axioms cubic_of_exact_pole_filtration
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicAlgebra
end


/-! The actual pole-filtration kernel factors through one fixed origin section. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
variable {X : Scheme.{u}}
def idealSectionRight (I : X.IdealSheafData) (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) :
    𝟙_ X.Modules ⟶ I.invModule := e.inv ≫ (I.invModule ◁ I.moduleι) ≫ (ρ_ I.invModule).hom

def cancelIdealRight (I : X.IdealSheafData) (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules)
    (M : X.Modules) : (M ⊗ I.invModule) ⊗ I.module ≅ M :=
  (α_ M I.invModule I.module) ≪≫ (Iso.refl M ⊗ᵢ e) ≪≫ (ρ_ M)

lemma cancelTensorRight_section {C : Type*} [Category C] [MonoidalCategory C]
    (I L M : C) (i : I ⟶ 𝟙_ C) (e : L ⊗ I ≅ 𝟙_ C) :
    ((α_ M L I) ≪≫ (Iso.refl M ⊗ᵢ e) ≪≫ (ρ_ M)).inv ≫
      ((M ⊗ L) ◁ i) ≫ (ρ_ _).hom =
      (ρ_ M).inv ≫ (M ◁ (e.inv ≫ (L ◁ i) ≫ (ρ_ L).hom)) := by
  dsimp [tensorIso]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_right_assoc]
  simp only [rightUnitor_tensor_hom, Iso.inv_hom_id_assoc]

lemma cancelIdealRight_section (I : X.IdealSheafData)
    (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) (M : X.Modules) :
    (cancelIdealRight I e M).inv ≫ ((M ⊗ I.invModule) ◁ I.moduleι) ≫ (ρ_ _).hom =
      (ρ_ M).inv ≫ (M ◁ idealSectionRight I e) :=
  cancelTensorRight_section I.module I.invModule M I.moduleι e

lemma rightUnitor_inv_section (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) :
    (ρ_ M).inv.app U s = Scheme.Modules.tensorSections s (Scheme.Modules.unitSection U) := by
  apply (Scheme.Modules.Hom.mono_iff_injective (ρ_ M).hom).mp inferInstance U
  change ((ρ_ M).inv ≫ (ρ_ M).hom).app U s = _
  rw [Iso.inv_hom_id]
  change s = _
  simpa only [Scheme.Modules.unitSection, one_smul] using
    (Scheme.Modules.rightUnitor_hom_app_tensorSections s (1 : Γ(X,U))).symm

lemma exists_tensor_factor (I : X.IdealSheafData)
    (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) (M : X.Modules)
    (s : Γ(M ⊗ I.invModule, ⊤))
    (t : Γ((M ⊗ I.invModule) ⊗ I.module, ⊤))
    (ht : (((M ⊗ I.invModule) ◁ I.moduleι) ≫ (ρ_ _).hom).app ⊤ t = s) :
    ∃ v : Γ(M, ⊤), Scheme.Modules.tensorSections v
      ((idealSectionRight I e).app ⊤ (Scheme.Modules.unitSection ⊤)) = s := by
  let δ := cancelIdealRight I e M
  refine ⟨δ.hom.app ⊤ t, ?_⟩
  have heq := congrArg (fun f => f.app ⊤ (δ.hom.app ⊤ t)) (cancelIdealRight_section I e M)
  have hleft : (δ.inv ≫ ((M ⊗ I.invModule) ◁ I.moduleι) ≫ (ρ_ _).hom).app ⊤
      (δ.hom.app ⊤ t) = s := by
    change ((δ.hom ≫ δ.inv) ≫ (((M ⊗ I.invModule) ◁ I.moduleι) ≫ (ρ_ _).hom)).app ⊤ t = s
    rw [δ.hom_inv_id, Category.id_comp]
    exact ht
  rw [hleft] at heq
  change s = (M ◁ idealSectionRight I e).app ⊤ ((ρ_ M).inv.app ⊤ (δ.hom.app ⊤ t)) at heq
  rw [rightUnitor_inv_section, Scheme.Modules.whiskerLeft_app_tensorSections] at heq
  exact heq.symm

lemma tensorPowAdd_one_section (L : X.Modules) (m : ℕ)
    (t : Γ(L.tensorPow m, ⊤)) (z : Γ(L, ⊤)) :
    (Scheme.Modules.tensorPowAdd L m 1).hom.app ⊤
      (Scheme.Modules.tensorSections t (Scheme.Modules.tensorPowSection z 1)) =
        Scheme.Modules.tensorSections t z := by
  let M := L.tensorPow m
  have hα := Scheme.Modules.associator_hom_app_tensorSections_monoidalV2
    t (Scheme.Modules.unitSection ⊤) z
  have hαinv : (α_ M (𝟙_ X.Modules) L).inv.app ⊤
      (Scheme.Modules.tensorSections t (Scheme.Modules.tensorSections (Scheme.Modules.unitSection ⊤) z)) =
      Scheme.Modules.tensorSections (Scheme.Modules.tensorSections t (Scheme.Modules.unitSection ⊤)) z := by
    rw [← hα]
    change ((α_ M (𝟙_ X.Modules) L).hom ≫ (α_ M (𝟙_ X.Modules) L).inv).app ⊤ _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [Scheme.Modules.tensorPowSection_one]
  change ((ρ_ M).hom ▷ L).app ⊤ ((α_ M (𝟙_ X.Modules) L).inv.app ⊤ _) = _
  rw [hαinv, Scheme.Modules.whiskerRight_app_tensorSections]
  rw [Scheme.Modules.rightUnitor_hom_app_tensorSections]
  exact congrArg (fun a => Scheme.Modules.tensorSections a z) (one_smul _ t)

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

def originPairing : Q.zero.ker.invModule ⊗ Q.zero.ker.module ≅ 𝟙_ Q.target.Modules :=
  Q.zero_ideal_invertible.nonempty_module_tensor_invModule_iso.2.some

def originSection : Γ(Q.zero.ker.invModule, ⊤) :=
  (idealSectionRight Q.zero.ker (originPairing R Q)).app ⊤ (Scheme.Modules.unitSection ⊤)

def originDegreeOne : Γ(Q.zero.ker.invModule.tensorPow 1, ⊤) :=
  Scheme.Modules.tensorPowSection (originSection R Q) 1

lemma exists_pole_filtration_factor (m : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow (m+1), ⊤))
    (hs : powerRestriction R Q (m+1) s = 0) :
    ∃ t : Γ(Q.zero.ker.invModule.tensorPow m, ⊤),
      sectionMul R Q m 1 t (originDegreeOne R Q) = s := by
  obtain ⟨v,hv⟩ := exists_ideal_lift R Q (m+1) s hs
  obtain ⟨t,ht⟩ := exists_tensor_factor Q.zero.ker (originPairing R Q)
    (Q.zero.ker.invModule.tensorPow m) s v hv
  refine ⟨t, ?_⟩
  change (Scheme.Modules.tensorPowAdd _ m 1).hom.app ⊤
    (Scheme.Modules.tensorSections t (Scheme.Modules.tensorPowSection (originSection R Q) 1)) = s
  rw [tensorPowAdd_one_section]
  exact ht

#print axioms exists_pole_filtration_factor
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

def frameScalarEquiv {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (hc : Function.Bijective (c.app ⊤))
    (M : X.Modules) (s : Γ(M,⊤)) (hs : Scheme.Modules.IsFrameOn s ⊤) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    R ≃ₗ[R] Γ(M,⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
  let f := LinearMap.toSpanSingleton R Γ(M,⊤) s
  apply LinearEquiv.ofBijective f
  have h := hs.bijective (le_refl ⊤) (le_refl ⊤)
  have hid : M.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op s = s := by
    rw [Subsingleton.elim (homOfLE (le_refl (⊤ : X.Opens))) (𝟙 ⊤), op_id, M.presheaf.map_id]; rfl
  simp only [hid] at h
  let η := SectionExact.unit_sections c hc
  change Function.Bijective (fun r : R => r • s)
  exact h.comp η.bijective

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

lemma unitPower_isFrame (m : ℕ) : Scheme.Modules.IsFrameOn (unitPower R m) ⊤ :=
  (Scheme.Modules.isFrameOn_unitSection ⊤).tensorPowSection m

def unitPowerScalarEquiv (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    R ≃ₗ[R] Γ((𝟙_ (Spec (.of R)).Modules).tensorPow m, ⊤) :=
  frameScalarEquiv (𝟙 _) (by simpa using Function.bijective_id) _ (unitPower R m) (unitPower_isFrame R m)

def identityRestrictionLinear (M : Q.target.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj M) ⊤
    Γ(M,⊤) →ₗ[R] Γ((Scheme.Modules.pullback Q.zero).obj M, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj M) ⊤
  refine { toFun := Scheme.Modules.pullbackLocalSection Q.zero
           map_add' := Scheme.Modules.pullbackLocalSection_add Q.zero
           map_smul' := ?_ }
  intro r s
  change Scheme.Modules.pullbackLocalSection Q.zero
    ((Q.structureMap.constToPresheaf.app (op ⊤)).hom r • s) =
    ((Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op (Q.zero ⁻¹ᵁ ⊤))).hom r •
      Scheme.Modules.pullbackLocalSection Q.zero s
  rw [Scheme.Modules.pullbackLocalSection_smul]
  have h := congrArg (fun f : CommRingCat.of R ⟶ _ => f.hom r)
    (Conormal.section_scalar Q.structureMap Q.zero Q.zero_over ⊤)
  exact congrArg (fun a => a • Scheme.Modules.pullbackLocalSection Q.zero s) h

def powerRestrictionLinear (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    Γ(Q.zero.ker.invModule.tensorPow m, ⊤) →ₗ[R]
      Γ((𝟙_ (Spec (.of R)).Modules).tensorPow m, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((Scheme.Modules.pullback Q.zero).obj (Q.zero.ker.invModule.tensorPow m)) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  exact (FibreCohomology.sectionsIsoLinear (𝟙 (Spec (.of R)))
    (Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
      Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m) ⊤).toLinearMap ∘ₗ
        identityRestrictionLinear R Q _

def leadingCoefficient (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
    Γ(Q.zero.ker.invModule.tensorPow m, ⊤) →ₗ[R] R := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  exact (unitPowerScalarEquiv R m).symm.toLinearMap ∘ₗ powerRestrictionLinear R Q m

lemma leadingCoefficient_spec (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
    powerRestriction R Q m s = leadingCoefficient R Q m s • unitPower R m := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
      ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  change powerRestriction R Q m s = (unitPowerScalarEquiv R m)
    ((unitPowerScalarEquiv R m).symm (powerRestriction R Q m s))
  exact ((unitPowerScalarEquiv R m).apply_symm_apply (powerRestriction R Q m s)).symm

lemma leadingCoefficient_eq_zero_iff (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤)) :
    leadingCoefficient R Q m s = 0 ↔ powerRestriction R Q m s = 0 := by
  change (unitPowerScalarEquiv R m).symm (powerRestriction R Q m s) = 0 ↔ _
  exact (unitPowerScalarEquiv R m).symm.map_eq_zero_iff

#print axioms leadingCoefficient_spec
#print axioms leadingCoefficient_eq_zero_iff
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
lemma restriction_zero_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g)
    (M : Y.Modules) (s : Γ(M,⊤)) (hs : Scheme.Modules.pullbackLocalSection f s = 0) :
    Scheme.Modules.pullbackLocalSection g s = 0 := by
  subst g
  exact hs

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

lemma originSection_ne_zero : originSection R Q ≠ 0 := by
  let I := Q.zero.ker
  let L := I.invModule
  have hL : Scheme.Modules.IsLocallyFreeOfRank 1 L :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr Q.zero_ideal_invertible.isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I L hL
  haveI := hS.mono_f
  haveI : Mono (idealSectionRight I (originPairing R Q)) := by
    change Mono ((originPairing R Q).inv ≫ ((L ◁ I.moduleι) ≫ (ρ_ L).hom))
    infer_instance
  letI : IsIntegral Q.target := Q.total_geometry.1
  intro hz
  have h : Scheme.Modules.unitSection (X := Q.target) ⊤ = 0 :=
    (Scheme.Modules.Hom.mono_iff_injective (idealSectionRight I (originPairing R Q))).mp inferInstance ⊤
      (by rw [map_zero]; exact hz)
  change (1 : Γ(Q.target, ⊤)) = 0 at h
  exact one_ne_zero h

lemma originSection_identity_zero : Scheme.Modules.pullbackLocalSection Q.zero (originSection R Q) = 0 := by
  let I := Q.zero.ker
  let L := I.invModule
  have hL : Scheme.Modules.IsLocallyFreeOfRank 1 L :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr Q.zero_ideal_invertible.isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I L hL
  have hzmap : idealSectionRight I (originPairing R Q) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L = 0 := by
    change (originPairing R Q).inv ≫ ((L ◁ I.moduleι) ≫ (ρ_ L).hom) ≫ _ = 0
    rw [w, CategoryTheory.Limits.comp_zero]
  have hz : Scheme.Modules.pullbackLocalSection I.subschemeι (originSection R Q) = 0 :=
    congrArg (fun f => f.app ⊤ (Scheme.Modules.unitSection ⊤)) hzmap
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  let e := asIso Q.zero.toImage
  have he : e.hom ≫ I.subschemeι = Q.zero := Q.zero.toImage_imageι
  have hcomp := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection e.hom I.subschemeι L ⊤
    (originSection R Q)
  rw [hz, Scheme.Modules.pullbackLocalSection_zero, map_zero] at hcomp
  exact restriction_zero_congr (e.hom ≫ I.subschemeι) Q.zero he L (originSection R Q) hcomp.symm

lemma originDegreeOne_restriction_zero : powerRestriction R Q 1 (originDegreeOne R Q) = 0 := by
  let L := Q.zero.ker.invModule
  have hunit : (λ_ L).inv.app ⊤ (originSection R Q) = originDegreeOne R Q := by
    apply (Scheme.Modules.Hom.mono_iff_injective (λ_ L).hom).mp inferInstance ⊤
    change ((λ_ L).inv ≫ (λ_ L).hom).app ⊤ (originSection R Q) = _
    rw [Iso.inv_hom_id]
    change originSection R Q = (λ_ L).hom.app ⊤
      (Scheme.Modules.tensorSections (Scheme.Modules.unitSection ⊤) (originSection R Q))
    simpa only [Scheme.Modules.unitSection, one_smul] using
      (Scheme.Modules.leftUnitor_hom_app_tensorSections (1 : Γ(Q.target, ⊤)) (originSection R Q)).symm
  have hpb := Scheme.Modules.pullbackLocalSection_app Q.zero (λ_ L).inv (originSection R Q)
  rw [originSection_identity_zero, map_zero] at hpb
  have hz : Scheme.Modules.pullbackLocalSection Q.zero (originDegreeOne R Q) = 0 := by
    rw [hunit] at hpb
    exact hpb
  unfold powerRestriction
  rw [hz, map_zero]

#print axioms originSection_ne_zero
#print axioms originDegreeOne_restriction_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

lemma unitPowerScalar_mul (m n : ℕ) (r t : R) :
    (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (.of R)).Modules) m n).hom.app ⊤
      (Scheme.Modules.tensorSections ((unitPowerScalarEquiv R m) r) ((unitPowerScalarEquiv R n) t)) =
        (unitPowerScalarEquiv R (m+n)) (r*t) := by
  let a : R →+* Γ(Spec (.of R), ⊤) :=
    ((Scheme.Hom.constToPresheaf (𝟙 (Spec (.of R)))).app (op ⊤)).hom
  change (Scheme.Modules.tensorPowAdd (𝟙_ (Spec (.of R)).Modules) m n).hom.app ⊤
    (Scheme.Modules.tensorSections (a r • unitPower R m) (a t • unitPower R n)) =
      a (r*t) • unitPower R (m+n)
  rw [Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, smul_smul, ← map_mul]
  exact congrArg (fun b => a (r*t) • b)
    (Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection _ m n)

lemma leadingCoefficient_mul (m n : ℕ)
    (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (t : Γ(Q.zero.ker.invModule.tensorPow n, ⊤)) :
    leadingCoefficient R Q (m+n) (sectionMul R Q m n s t) =
      leadingCoefficient R Q m s * leadingCoefficient R Q n t := by
  apply (unitPowerScalarEquiv R (m+n)).injective
  change (unitPowerScalarEquiv R (m+n)) ((unitPowerScalarEquiv R (m+n)).symm
    (powerRestriction R Q (m+n) (sectionMul R Q m n s t))) = _
  rw [LinearEquiv.apply_symm_apply]
  unfold sectionMul
  rw [powerRestriction_mul]
  have hs : powerRestriction R Q m s = (unitPowerScalarEquiv R m) (leadingCoefficient R Q m s) :=
    leadingCoefficient_spec R Q m s
  have ht : powerRestriction R Q n t = (unitPowerScalarEquiv R n) (leadingCoefficient R Q n t) :=
    leadingCoefficient_spec R Q n t
  rw [hs,ht]
  exact unitPowerScalar_mul R m n _ _

lemma leadingCoefficient_normalized (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
    (hs : powerRestriction R Q m s = unitPower R m) : leadingCoefficient R Q m s = 1 := by
  apply (unitPowerScalarEquiv R m).injective
  change (unitPowerScalarEquiv R m) ((unitPowerScalarEquiv R m).symm (powerRestriction R Q m s)) = _
  rw [LinearEquiv.apply_symm_apply, hs]
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Spec (.of R)))
    ((𝟙_ (Spec (.of R)).Modules).tensorPow m) ⊤
  change unitPower R m = (1 : R) • unitPower R m
  exact (one_smul _ _).symm

lemma originDegreeOne_ne_zero : originDegreeOne R Q ≠ 0 := by
  intro hz
  apply originSection_ne_zero R Q
  have h := Scheme.Modules.leftUnitor_hom_app_tensorSections
    (1 : Γ(Q.target, ⊤)) (originSection R Q)
  change (λ_ Q.zero.ker.invModule).hom.app ⊤ (originDegreeOne R Q) = _ at h
  rw [hz, map_zero, one_smul] at h
  exact h.symm

lemma linear_zero_of_rank_one_kernel {R M : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (g : M →ₗ[R] R)
    (z : M) (hz : z ≠ 0) (hgz : g z = 0) : g = 0 := by
  let b := e.symm 1
  have hx (x : M) : x = (e x) • b := by
    apply e.injective
    simp [b]
  have hez : e z ≠ 0 := fun h => hz (e.injective (by simpa only [map_zero] using h))
  have hgb : g b = 0 := by
    have h : e z * g b = 0 := by
      rw [← smul_eq_mul, ← g.map_smul, ← hx z]
      exact hgz
    exact (mul_eq_zero.mp h).resolve_left hez
  apply LinearMap.ext
  intro x
  rw [hx x, g.map_smul, hgb, smul_zero]
  rfl

lemma degreeOne_restriction_zero (s : Γ(Q.zero.ker.invModule.tensorPow 1, ⊤)) :
    powerRestriction R Q 1 s = 0 := by
  let L := Q.zero.ker.invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap (L.tensorPow 1) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap (Q.zero.ker ^ 1).invModule ⊤
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible 1
  obtain ⟨ε⟩ := SectionExact.origin_first_sections R Q
  let e := FibreCohomology.sectionsIsoLinear Q.structureMap δ.symm ⊤ ≪≫ₗ ε
  have hg := linear_zero_of_rank_one_kernel e (leadingCoefficient R Q 1) (originDegreeOne R Q)
    (originDegreeOne_ne_zero R Q)
    ((leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q))
  apply (leadingCoefficient_eq_zero_iff R Q 1 s).mp
  exact LinearMap.congr_fun hg s

lemma degreeOne_generated (s : Γ(Q.zero.ker.invModule.tensorPow 1, ⊤)) :
    ∃ r : R, s = (GradedOAlgebra.baseScalar Q.structureMap r) • originDegreeOne R Q := by
  obtain ⟨t,ht⟩ := exists_pole_filtration_factor R Q 0 s (degreeOne_restriction_zero R Q s)
  let η := SectionExact.unit_sections Q.structureMap (Q.structure_app_bijective ⊤)
  obtain ⟨r,hr⟩ := η.surjective t
  refine ⟨r, ?_⟩
  rw [← ht]
  unfold sectionMul originDegreeOne
  rw [tensorPowAdd_one_section]
  change Scheme.Modules.tensorSections t (originSection R Q) = _
  have hscalar : t = GradedOAlgebra.baseScalar Q.structureMap r •
      Scheme.Modules.unitSection (X := Q.target) ⊤ := by
    rw [← hr]
    rw [Scheme.Modules.smul_unitSection]
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ Q.structureMap.appLE ⊤ ⊤ le_top).hom r =
      (Q.structureMap.app ⊤).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [hscalar, Scheme.Modules.tensorSections_smul_left]
  rfl

#print axioms leadingCoefficient_mul
#print axioms degreeOne_generated
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open Filtration
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)

lemma baseScalar_eq_const {S : Type u} [CommRing S] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of S)) (r : S) :
    GradedOAlgebra.baseScalar c r = (c.constToPresheaf.app (op ⊤)).hom r := by
  change (c.app ⊤).hom ((Scheme.ΓSpecIso (.of S)).inv.hom r) =
    ((Scheme.ΓSpecIso (.of S)).inv ≫ c.appLE ⊤ ⊤ le_top).hom r
  rw [Scheme.Hom.app_eq_appLE]
  rfl

def sectionLinearEquiv (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
    𝓐 m ≃ₗ[R] Γ(Q.zero.ker.invModule.tensorPow m, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  exact LinearEquiv.ofBijective
    { toFun := ι m
      map_add' := hRing.map_add m
      map_smul' := fun r a => by
        change ι m (r • a) = (Q.structureMap.constToPresheaf.app (op ⊤)).hom r • ι m a
        rw [← baseScalar_eq_const]
        exact hRing.map_smul m r a }
    (hRing.bijective m)

def gradedLead (m : ℕ) : 𝓐 m →ₗ[R] R := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap
      (Q.zero.ker.invModule.tensorPow m) ⊤
  exact leadingCoefficient R Q m ∘ₗ (sectionLinearEquiv R Q A 𝓐 ι hRing m).toLinearMap

include hRing
lemma gradedLead_mul (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n) :
    gradedLead R Q A 𝓐 ι hRing (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ =
      gradedLead R Q A 𝓐 ι hRing m a * gradedLead R Q A 𝓐 ι hRing n b := by
  change leadingCoefficient R Q (m+n) (ι (m+n) _) = _
  rw [hRing.map_mul]
  exact leadingCoefficient_mul R Q m n (ι m a) (ι n b)

lemma gradedLead_drop (z : 𝓐 1) (hz : ι 1 z = originDegreeOne R Q)
    (m : ℕ) (a : 𝓐 (m+1)) (ha : gradedLead R Q A 𝓐 ι hRing (m+1) a = 0) :
    ∃ b : 𝓐 m, (z:A)*b = a := by
  have ha' : powerRestriction R Q (m+1) (ι (m+1) a) = 0 :=
    (leadingCoefficient_eq_zero_iff R Q (m+1) _).mp ha
  obtain ⟨t,ht⟩ := exists_pole_filtration_factor R Q m (ι (m+1) a) ha'
  obtain ⟨b,hb⟩ := (hRing.bijective m).2 t
  refine ⟨b, ?_⟩
  have hba : (⟨(b:A)*z, SetLike.mul_mem_graded b.2 z.2⟩ : 𝓐 (m+1)) = a := by
    apply (hRing.bijective (m+1)).1
    rw [hRing.map_mul, hb, hz]
    exact ht
  simpa only [mul_comm] using congrArg Subtype.val hba

lemma graded_degree_one (z : 𝓐 1) (hz : ι 1 z = originDegreeOne R Q) (a : 𝓐 1) :
    ∃ r : R, (a:A) = algebraMap R A r * z := by
  obtain ⟨r,hr⟩ := degreeOne_generated R Q (ι 1 a)
  refine ⟨r, ?_⟩
  have h : a = r • z := by
    apply (hRing.bijective 1).1
    rw [hRing.map_smul, hz]
    exact hr
  simpa only [Submodule.coe_smul, Algebra.smul_def] using congrArg Subtype.val h

/-- The cubic relation in the actual section ring, with the origin section
and coordinates whose leading polar coefficients are one. -/
lemma exists_sectionRing_cubic :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (a1 a2 a3 a4 a6 : R),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      (y:A)^2 + algebraMap R A a1 * x * y * z + algebraMap R A a3 * y * z^3 =
        (x:A)^3 + algebraMap R A a2 * x^2 * z^2 +
          algebraMap R A a4 * x * z^4 + algebraMap R A a6 * z^6 := by
  obtain ⟨z,hz⟩ := (hRing.bijective 1).2 (originDegreeOne R Q)
  obtain ⟨sx,sy,hsx,hsy⟩ := exists_normalized_coordinates R Q
  obtain ⟨x,hx⟩ := (hRing.bijective 2).2 sx
  obtain ⟨y,hy⟩ := (hRing.bijective 3).2 sy
  have hx' : powerRestriction R Q 2 (ι 2 x) = unitPower R 2 := by rw [hx]; exact hsx
  have hy' : powerRestriction R Q 3 (ι 3 y) = unitPower R 3 := by rw [hy]; exact hsy
  obtain ⟨a1,a2,a3,a4,a6,heq⟩ := CubicAlgebra.cubic_of_exact_pole_filtration 𝓐
    (gradedLead R Q A 𝓐 ι hRing) z (gradedLead_drop R Q A 𝓐 ι hRing z hz)
    (gradedLead_mul R Q A 𝓐 ι hRing) (graded_degree_one R Q A 𝓐 ι hRing z hz)
    x y (leadingCoefficient_normalized R Q 2 _ hx') (leadingCoefficient_normalized R Q 3 _ hy')
  exact ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx',hy',heq⟩

omit hRing in
/-- Coordinates and a Weierstrass equation are constructed on the actual inverse
origin-ideal section ring. No coordinate, basis or relation is assumed. -/
theorem exists_origin_cubic :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R),
        j 1 z = originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x) = unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y) = unitPower R 3 ∧
        (y:B)^2 + algebraMap R B W.a₁ * x * y * z + algebraMap R B W.a₃ * y * z^3 =
          (x:B)^3 + algebraMap R B W.a₂ * x^2 * z^2 +
            algebraMap R B W.a₄ * x * z^4 + algebraMap R B W.a₆ * z^6 := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  obtain ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx,hy,hrel⟩ := exists_sectionRing_cubic R Q B 𝓑 j hj
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,z,x,y,⟨a1,a2,a3,a4,a6⟩,hz,hx,hy,hrel⟩

#print axioms exists_sectionRing_cubic
#print axioms exists_origin_cubic
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic

end

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Generation
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R) (x : 𝓐 2) (y : 𝓐 3)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)

include hmul
lemma normalized_monomial (hx : lead 2 x = 1) (hy : lead 3 y = 1) :
    ∀ n : ℕ, 2 ≤ n → ∃ t : 𝓐 n,
      lead n t = 1 ∧ (t:A) ∈ Algebra.adjoin R ({(x:A), (y:A)} : Set A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : n = 2
    · subst n
      exact ⟨x,hx,Algebra.subset_adjoin (by simp)⟩
    by_cases h3 : n = 3
    · subst n
      exact ⟨y,hy,Algebra.subset_adjoin (by simp)⟩
    have hn4 : 4 ≤ n := by omega
    obtain ⟨t,ht,htmem⟩ := ih (n-2) (by omega) (by omega)
    have he : 2 + (n-2) = n := by omega
    let v : 𝓐 (2+(n-2)) := ⟨(x:A)*t, SetLike.mul_mem_graded x.2 t.2⟩
    have hv : lead (2+(n-2)) v = 1 := by rw [hmul, hx, ht, one_mul]
    have hm : (v:A) ∈ Algebra.adjoin R ({(x:A),(y:A)} : Set A) :=
      Subalgebra.mul_mem _ (Algebra.subset_adjoin (by simp)) htmem
    have hex : ∃ t : 𝓐 (2+(n-2)), lead (2+(n-2)) t = 1 ∧
        (t:A) ∈ Algebra.adjoin R ({(x:A),(y:A)} : Set A) := ⟨v,hv,hm⟩
    exact he ▸ hex

variable (z : 𝓐 1)
variable (drop : ∀ m (a : 𝓐 (m+1)), lead (m+1) a = 0 → ∃ b : 𝓐 m, (z:A)*b = a)
variable (deg0 : ∀ a : 𝓐 0, ∃ r : R, (a:A) = algebraMap R A r)
variable (deg1 : ∀ a : 𝓐 1, ∃ r : R, (a:A) = algebraMap R A r * z)
include hmul drop deg0 deg1
lemma homogeneous_generated (hx : lead 2 x = 1) (hy : lead 3 y = 1)
    (n : ℕ) (a : 𝓐 n) : (a:A) ∈ Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A) := by
  let S := Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A)
  have hzS : (z:A) ∈ S := Algebra.subset_adjoin (by simp)
  have hxy : Algebra.adjoin R ({(x:A),(y:A)} : Set A) ≤ S :=
    Algebra.adjoin_mono (by intro b hb; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *; aesop)
  induction n with
  | zero =>
    obtain ⟨r,hr⟩ := deg0 a
    rw [hr]
    exact S.algebraMap_mem r
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      obtain ⟨r,hr⟩ := deg1 a
      rw [hr]
      exact S.mul_mem (S.algebraMap_mem r) hzS
    obtain ⟨t,ht,htmem⟩ := normalized_monomial 𝓐 lead x y hmul hx hy (n+1) (by omega)
    have hd : lead (n+1) (a - lead (n+1) a • t) = 0 := by
      rw [map_sub, map_smul, ht, smul_eq_mul, mul_one, sub_self]
    obtain ⟨b,hb⟩ := drop n _ hd
    have heq : (a:A) = (z:A)*b + algebraMap R A (lead (n+1) a) * t := by
      simpa only [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def] using
        (eq_add_of_sub_eq (show (a:A) - algebraMap R A (lead (n+1) a) * t = (z:A)*b from
          (by simpa only [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def] using hb.symm)))
    rw [heq]
    exact S.add_mem (S.mul_mem hzS (ih b)) (S.mul_mem (S.algebraMap_mem _) (hxy htmem))

lemma adjoin_eq_top (hx : lead 2 x = 1) (hy : lead 3 y = 1) :
    Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A) = ⊤ := by
  have hall : ∀ a : A, a ∈ Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A) := by
    intro a
    apply DirectSum.Decomposition.inductionOn 𝓐 (motive := fun a =>
      a ∈ Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A)) ?_ ?_ ?_ a
    · exact Subalgebra.zero_mem _
    · intro n a
      exact homogeneous_generated 𝓐 lead x y hmul z drop deg0 deg1 hx hy n a
    · intro a b ha hb
      exact Subalgebra.add_mem _ ha hb
  exact top_unique (fun a _ => hall a)

#print axioms adjoin_eq_top
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Generation

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open Filtration
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma graded_degree_zero (a : 𝓐 0) : ∃ r : R, (a:A) = algebraMap R A r := by
  let η := SectionExact.unit_sections Q.structureMap (Q.structure_app_bijective ⊤)
  obtain ⟨r,hr⟩ := η.surjective (ι 0 a)
  have ha : a = r • (⟨1, SetLike.GradedOne.one_mem⟩ : 𝓐 0) := by
    apply (hRing.bijective 0).1
    rw [hRing.map_smul, hRing.map_one, Scheme.Modules.smul_unitSection]
    rw [← hr]
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ Q.structureMap.appLE ⊤ ⊤ le_top).hom r =
      (Q.structureMap.app ⊤).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨r, ?_⟩
  simpa only [Submodule.coe_smul, Algebra.smul_def, mul_one] using congrArg Subtype.val ha

lemma coordinates_generate (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    Algebra.adjoin R ({(z:A),(x:A),(y:A)} : Set A) = ⊤ := by
  exact Generation.adjoin_eq_top 𝓐 (gradedLead R Q A 𝓐 ι hRing) x y
    (gradedLead_mul R Q A 𝓐 ι hRing) z (gradedLead_drop R Q A 𝓐 ι hRing z hz)
    (graded_degree_zero R Q A 𝓐 ι hRing) (graded_degree_one R Q A 𝓐 ι hRing z hz)
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)

#print axioms coordinates_generate
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

lemma tensor_originSection_injective {X : Scheme.{u}} (I : X.IdealSheafData)
    (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible (M ⊗ I.invModule)) :
    Function.Injective (fun s : Γ(M,⊤) => Scheme.Modules.tensorSections s
      ((idealSectionRight I e).app ⊤ (Scheme.Modules.unitSection ⊤))) := by
  have hMf : Scheme.Modules.IsLocallyFreeOfRank 1 (M ⊗ I.invModule) :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hM
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I (M ⊗ I.invModule) hMf
  let δ := cancelIdealRight I e M
  haveI := hS.mono_f
  haveI : Mono ((ρ_ M).inv ≫ (M ◁ idealSectionRight I e)) := by
    rw [← cancelIdealRight_section]
    infer_instance
  have hi := (Scheme.Modules.Hom.mono_iff_injective ((ρ_ M).inv ≫ (M ◁ idealSectionRight I e))).mp inferInstance ⊤
  intro a b hab
  apply hi
  change (M ◁ idealSectionRight I e).app ⊤ ((ρ_ M).inv.app ⊤ a) =
    (M ◁ idealSectionRight I e).app ⊤ ((ρ_ M).inv.app ⊤ b)
  rw [rightUnitor_inv_section, rightUnitor_inv_section,
    Scheme.Modules.whiskerLeft_app_tensorSections, Scheme.Modules.whiskerLeft_app_tensorSections]
  exact hab

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
lemma sectionMul_origin_injective (m : ℕ) :
    Function.Injective (fun s : Γ(Q.zero.ker.invModule.tensorPow m,⊤) =>
      sectionMul R Q m 1 s (originDegreeOne R Q)) := by
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible (m+1)
  have hM : Scheme.Modules.IsInvertible (Q.zero.ker.invModule.tensorPow (m+1)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨ε⟩⟩ := (Q.zero_ideal_invertible.pow (m+1)).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ.symm ≪≫ ε⟩⟩
  have hi := tensor_originSection_injective Q.zero.ker (originPairing R Q)
    (Q.zero.ker.invModule.tensorPow m) hM
  intro a b hab
  apply hi
  unfold sectionMul originDegreeOne at hab
  dsimp only at hab
  rw [tensorPowAdd_one_section, tensorPowAdd_one_section] at hab
  exact hab

lemma leadingCoefficient_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (leadingCoefficient R Q (m+1)) := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule (m+1) ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) (m+1)
  intro r
  obtain ⟨s,hs⟩ := surjective_identity_tensorPower R Q m hm
    (η.inv.app ⊤ ((unitPowerScalarEquiv R (m+1)) r))
  refine ⟨s, ?_⟩
  apply (unitPowerScalarEquiv R (m+1)).injective
  change (unitPowerScalarEquiv R (m+1)) ((unitPowerScalarEquiv R (m+1)).symm
    (powerRestriction R Q (m+1) s)) = _
  rw [LinearEquiv.apply_symm_apply]
  change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s) = _
  rw [hs]
  change (η.inv ≫ η.hom).app ⊤ ((unitPowerScalarEquiv R (m+1)) r) = _
  rw [η.inv_hom_id]
  rfl

#print axioms sectionMul_origin_injective
#print axioms leadingCoefficient_surjective
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open Filtration
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] in
 def weightedCubic (W : WeierstrassCurve R) : MvPolynomial (Fin 3) R :=
  let z := MvPolynomial.X (0 : Fin 3)
  let x := MvPolynomial.X (1 : Fin 3)
  let y := MvPolynomial.X (2 : Fin 3)
  y^2 + MvPolynomial.C W.a₁ * x * y * z + MvPolynomial.C W.a₃ * y * z^3 -
    (x^3 + MvPolynomial.C W.a₂ * x^2 * z^2 + MvPolynomial.C W.a₄ * x * z^4 + MvPolynomial.C W.a₆ * z^6)

include hRing
lemma coordinates_aeval_surjective (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    Function.Surjective (MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]) := by
  apply (AlgHom.range_eq_top _).mp
  rw [← Algebra.adjoin_range_eq_range_aeval]
  have hr : Set.range ![(z:A),(x:A),(y:A)] = ({(z:A),(x:A),(y:A)} : Set A) := by
    ext a
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  rw [hr]
  exact coordinates_generate R Q A 𝓐 ι hRing z x y hz hx hy

lemma exists_surjective_polynomial_map_cubic :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      Function.Surjective (MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]) ∧
      MvPolynomial.aeval ![(z:A),(x:A),(y:A)] (weightedCubic R W) = 0 := by
  obtain ⟨z,x,y,a1,a2,a3,a4,a6,hz,hx,hy,hrel⟩ := exists_sectionRing_cubic R Q A 𝓐 ι hRing
  refine ⟨z,x,y,⟨a1,a2,a3,a4,a6⟩,hz,hx,hy,coordinates_aeval_surjective R Q A 𝓐 ι hRing z x y hz hx hy, ?_⟩
  simpa [weightedCubic] using sub_eq_zero.mpr hrel

#print axioms exists_surjective_polynomial_map_cubic
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic

end


/-! Exact coordinate kernel: GlobalLeadingProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Filtration GeometricCubic
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R)

def globalLead (n : ℕ) : A →ₗ[R] R :=
  lead n ∘ₗ DirectSum.component R ℕ (fun n => 𝓐 n) n ∘ₗ (DirectSum.decomposeLinearEquiv 𝓐).toLinearMap

lemma globalLead_homogeneous (n : ℕ) (a : 𝓐 n) : globalLead 𝓐 lead n a = lead n a := by
  change lead n (DirectSum.decompose 𝓐 (a:A) n) = lead n a
  congr 1
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same 𝓐 a.2

lemma globalLead_homogeneous_ne (m n : ℕ) (a : 𝓐 m) (hmn : m ≠ n) :
    globalLead 𝓐 lead n a = 0 := by
  change lead n (DirectSum.decompose 𝓐 (a:A) n) = 0
  have h : DirectSum.decompose 𝓐 (a:A) n = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne 𝓐 a.2 hmn)
  rw [h,map_zero]

variable (z : 𝓐 1)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
include hmul
lemma globalLead_z_mul (hz : lead 1 z = 0) (n : ℕ) (a : A) :
    globalLead 𝓐 lead n ((z:A)*a) = 0 := by
  cases n with
  | zero =>
    have h : DirectSum.decompose 𝓐 ((z:A)*a) 0 = 0 := Subtype.ext
      (DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝓐 z.2 (by omega))
    change lead 0 (DirectSum.decompose 𝓐 ((z:A)*a) 0) = 0
    rw [h,map_zero]
  | succ n =>
    have h : DirectSum.decompose 𝓐 ((z:A)*a) (1+n) =
        ⟨(z:A) * DirectSum.decompose 𝓐 a n,
          SetLike.mul_mem_graded z.2 (DirectSum.decompose 𝓐 a n).2⟩ :=
      Subtype.ext (DirectSum.coe_decompose_mul_add_of_left_mem 𝓐 z.2)
    change lead (n+1) (DirectSum.decompose 𝓐 ((z:A)*a) (n+1)) = 0
    have hh : lead (1+n) (DirectSum.decompose 𝓐 ((z:A)*a) (1+n)) = 0 := by
      rw [h,hmul,hz,zero_mul]
    exact (Nat.add_comm 1 n) ▸ hh

omit hmul in
lemma z_mul_injective (hinj : ∀ n : ℕ, Function.Injective (fun a : 𝓐 n => (z:A)*a)) :
    Function.Injective (fun a : A => (z:A)*a) := by
  intro a b hab
  apply (DirectSum.decomposeLinearEquiv 𝓐).injective
  ext n
  have h := congrArg (fun v => (DirectSum.decompose 𝓐 v (1+n) : A)) hab
  rw [DirectSum.coe_decompose_mul_add_of_left_mem 𝓐 z.2,
    DirectSum.coe_decompose_mul_add_of_left_mem 𝓐 z.2] at h
  exact congrArg Subtype.val (hinj n h)

omit hmul
variable (R) [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
  (Q : FramedCurve R)
variable (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma graded_z_mul_injective (hz : ι 1 z = originDegreeOne R Q) (n : ℕ) :
    Function.Injective (fun a : 𝓐 n => (z:A)*a) := by
  intro a b hab
  have h : (⟨(a:A)*z,SetLike.mul_mem_graded a.2 z.2⟩ : 𝓐 (n+1)) =
      ⟨(b:A)*z,SetLike.mul_mem_graded b.2 z.2⟩ :=
    Subtype.ext (by simpa only [mul_comm] using hab)
  have he := congrArg (ι (n+1)) h
  rw [hRing.map_mul,hRing.map_mul,hz] at he
  apply (hRing.bijective n).1
  exact sectionMul_origin_injective R Q n he

lemma actual_z_mul_injective (hz : ι 1 z = originDegreeOne R Q) :
    Function.Injective (fun a : A => (z:A)*a) :=
  z_mul_injective 𝓐 z (graded_z_mul_injective (R := R) (𝓐 := 𝓐) (z := z) (Q := Q) (ι := ι) (hRing := hRing) hz)

lemma gradedLead_one : gradedLead R Q A 𝓐 ι hRing 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1 := by
  apply leadingCoefficient_normalized R Q 0
  change powerRestriction R Q 0 (ι 0 ⟨1,SetLike.GradedOne.one_mem⟩) = unitPower R 0
  rw [hRing.map_one]
  exact Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection
    Q.zero Q.zero.ker.invModule _ (identityLineFrame R Q)

#print axioms actual_z_mul_injective
#print axioms gradedLead_one
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: AdicIndependenceProbe development. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N]
variable (z : A) (v : N →ₗ[R] A)
  (hz : Function.Injective (fun a : A => z*a))
  (hv : ∀ (b : N) (a : A), v b = z*a → b = 0)

include hz hv
lemma polynomial_sequence_independent (n : ℕ) (b : ℕ → N)
    (h : ∑ i ∈ Finset.range n, z^i * v (b i) = 0) : ∀ i < n, b i = 0 := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have he : v (b 0) + z * (∑ i ∈ Finset.range n, z^i * v (b (i+1))) = 0 := by
      rw [Finset.sum_range_succ'] at h
      simpa only [pow_zero,one_mul,pow_succ',mul_assoc,← Finset.mul_sum,add_comm] using h
    have hb0 : b 0 = 0 := hv (b 0) (-∑ i ∈ Finset.range n, z^i * v (b (i+1))) (by
      rw [mul_neg]
      exact eq_neg_of_add_eq_zero_left he)
    have ht : ∑ i ∈ Finset.range n, z^i * v (b (i+1)) = 0 := by
      apply hz
      change z * _ = z * 0
      rw [mul_zero]
      simpa only [hb0,map_zero,zero_add] using he
    intro i hi
    cases i with
    | zero => exact hb0
    | succ i => exact ih (fun j => b (j+1)) ht i (Nat.lt_of_succ_lt_succ hi)

#print axioms polynomial_sequence_independent
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: NormalMonomialsProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
variable (hone : lead 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1)

def Normalized (n : ℕ) (a : A) : Prop := ∃ h : a ∈ 𝓐 n, lead n ⟨a,h⟩ = 1
include hmul
lemma Normalized.mul {m n : ℕ} {a b : A} (ha : Normalized 𝓐 lead m a)
    (hb : Normalized 𝓐 lead n b) : Normalized 𝓐 lead (m+n) (a*b) := by
  obtain ⟨ha,ha'⟩ := ha
  obtain ⟨hb,hb'⟩ := hb
  refine ⟨SetLike.mul_mem_graded ha hb, ?_⟩
  exact (hmul m n ⟨a,ha⟩ ⟨b,hb⟩).trans (by rw [ha',hb',one_mul])

include hone
lemma Normalized.pow {m : ℕ} {a : A} (ha : Normalized 𝓐 lead m a) (n : ℕ) :
    Normalized 𝓐 lead (n*m) (a^n) := by
  induction n with
  | zero =>
    simpa only [Nat.zero_mul,pow_zero] using
      (show Normalized 𝓐 lead 0 1 from ⟨SetLike.GradedOne.one_mem, hone⟩)
  | succ n ih =>
    have h := Normalized.mul 𝓐 lead hmul ih ha
    simpa only [Nat.succ_mul,pow_succ] using h

omit hmul hone in
lemma Normalized.globalLead {m n : ℕ} {a : A} (ha : Normalized 𝓐 lead m a) :
    globalLead 𝓐 lead n a = if m=n then 1 else 0 := by
  obtain ⟨ha,hv⟩ := ha
  by_cases h : m=n
  · subst n
    rw [if_pos rfl]
    exact (globalLead_homogeneous 𝓐 lead m ⟨a,ha⟩).trans hv
  · rw [if_neg h]
    exact globalLead_homogeneous_ne 𝓐 lead m n ⟨a,ha⟩ h

variable (x : 𝓐 2) (y : 𝓐 3) (hx : lead 2 x = 1) (hy : lead 3 y = 1)
include hmul hone hx hy
lemma globalLead_normal_monomial (n j : ℕ) (k : Fin 2) :
    globalLead 𝓐 lead n ((x:A)^j * (y:A)^(k:ℕ)) =
      if j*2+(k:ℕ)*3=n then 1 else 0 := by
  have h := Normalized.mul 𝓐 lead hmul
    (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 2 x from ⟨x.2,hx⟩) j)
    (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 3 y from ⟨y.2,hy⟩) (k:ℕ))
  exact Normalized.globalLead 𝓐 lead h

lemma globalLead_polynomial_mul (j : ℕ) (k l : Fin 2) (p : Polynomial R) :
    globalLead 𝓐 lead (j*2+(k:ℕ)*3)
      ((Polynomial.aeval (x:A)) p * (y:A)^(l:ℕ)) =
        if k=l then p.coeff j else 0 := by
  classical
  rw [Polynomial.aeval_def,Polynomial.eval₂_eq_sum,Polynomial.sum_def,Finset.sum_mul, map_sum]
  have hterm (i : ℕ) :
      globalLead 𝓐 lead (j*2+(k:ℕ)*3)
        (algebraMap R A (p.coeff i) * (x:A)^i * (y:A)^(l:ℕ)) =
      if i=j ∧ l=k then p.coeff i else 0 := by
    rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul,
      globalLead_normal_monomial 𝓐 lead hmul hone x y hx hy]
    have he : i*2+(l:ℕ)*3=j*2+(k:ℕ)*3 ↔ i=j ∧ l=k := by
      have hk := k.isLt
      have hl := l.isLt
      constructor
      · intro h
        have hv : (l:ℕ)=(k:ℕ) := by omega
        exact ⟨by omega,Fin.ext hv⟩
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [he]
    split_ifs <;> simp
  simp_rw [hterm]
  by_cases h : k=l
  · subst l
    simp only [and_true,ite_true]
    rw [Finset.sum_ite_eq']
    split_ifs with hj
    · rfl
    · exact (show p.coeff j = 0 from by simpa only [Polynomial.mem_support_iff, not_not] using hj).symm
  · have hlk : l ≠ k := Ne.symm h
    simp [h,hlk]

#print axioms globalLead_polynomial_mul
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: NormalPairProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def normalPairEval (x y : A) : Polynomial R × Polynomial R →ₗ[R] A where
  toFun p := (Polynomial.aeval x) p.1 + (Polynomial.aeval x) p.2 * y
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul]; abel
  map_smul' r p := by
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,smul_mul_assoc,RingHom.id_apply]

variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
variable (hone : lead 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1)
variable (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
variable (hz : lead 1 z = 0) (hx : lead 2 x = 1) (hy : lead 3 y = 1)
include hmul hone hz hx hy
lemma normalPair_mod_z (p : Polynomial R × Polynomial R) (a : A)
    (h : normalPairEval (x:A) (y:A) p = (z:A)*a) : p = 0 := by
  have he (j : ℕ) (k : Fin 2) :
      globalLead 𝓐 lead (j*2+(k:ℕ)*3) (normalPairEval (x:A) (y:A) p) = 0 :=
    (congrArg (globalLead 𝓐 lead (j*2+(k:ℕ)*3)) h).trans
      (globalLead_z_mul 𝓐 lead z hmul hz _ a)
  have hp (j : ℕ) : p.1.coeff j = 0 ∧ p.2.coeff j = 0 := by
    have he0 := he j 0
    have he1 := he j 1
    change globalLead 𝓐 lead (j*2+0*3)
      ((Polynomial.aeval (x:A)) p.1 + (Polynomial.aeval (x:A)) p.2 * y) = 0 at he0
    change globalLead 𝓐 lead (j*2+1*3)
      ((Polynomial.aeval (x:A)) p.1 + (Polynomial.aeval (x:A)) p.2 * y) = 0 at he1
    rw [map_add] at he0 he1
    have h00 := globalLead_polynomial_mul 𝓐 lead hmul hone x y hx hy j 0 0 p.1
    have h01 := globalLead_polynomial_mul 𝓐 lead hmul hone x y hx hy j 0 1 p.2
    have h10 := globalLead_polynomial_mul 𝓐 lead hmul hone x y hx hy j 1 0 p.1
    have h11 := globalLead_polynomial_mul 𝓐 lead hmul hone x y hx hy j 1 1 p.2
    simp only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,ite_true,ite_false,
      show (0:Fin 2) ≠ 1 from by decide, show (1:Fin 2) ≠ 0 from by decide] at h00 h01 h10 h11
    rw [h00,h01,add_zero] at he0
    rw [h10,h11,zero_add] at he1
    exact ⟨he0,he1⟩
  apply Prod.ext
  · ext j; exact (hp j).1
  · ext j; exact (hp j).2

lemma normalPair_sequence_independent
    (hzinj : Function.Injective (fun a : A => (z:A)*a)) (n : ℕ)
    (b : ℕ → Polynomial R × Polynomial R)
    (h : ∑ i ∈ Finset.range n, (z:A)^i * normalPairEval (x:A) (y:A) (b i) = 0) :
    ∀ i < n, b i = 0 :=
  polynomial_sequence_independent (z:A) (normalPairEval (x:A) (y:A)) hzinj
    (normalPair_mod_z 𝓐 lead hmul hone z x y hz hx hy) n b h

#print axioms normalPair_mod_z
#print axioms normalPair_sequence_independent
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: BivariateIndependenceProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def evalXZ (x z : A) : Polynomial (Polynomial R) →+* A :=
  Polynomial.eval₂RingHom (Polynomial.aeval x).toRingHom z

lemma evalXZ_pair_sum (x y z : A) (p q : Polynomial (Polynomial R)) (n : ℕ)
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    evalXZ x z p + evalXZ x z q * y =
      ∑ i ∈ Finset.range n, z^i * normalPairEval x y (p.coeff i,q.coeff i) := by
  change Polynomial.eval₂ (Polynomial.aeval x).toRingHom z p +
    Polynomial.eval₂ (Polynomial.aeval x).toRingHom z q * y = _
  rw [Polynomial.eval₂_eq_sum_range' _ hp,Polynomial.eval₂_eq_sum_range' _ hq,
    Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (Polynomial.aeval x) (p.coeff i)*z^i + (Polynomial.aeval x) (q.coeff i)*z^i*y =
    z^i*((Polynomial.aeval x) (p.coeff i)+(Polynomial.aeval x) (q.coeff i)*y)
  ring

lemma bivariate_pair_eq_zero
    (x y z : A) (hzinj : Function.Injective (fun a : A => z*a))
    (hmod : ∀ (p : Polynomial R × Polynomial R) (a : A),
      normalPairEval x y p = z*a → p = 0)
    (p q : Polynomial (Polynomial R)) (h : evalXZ x z p + evalXZ x z q * y = 0) :
    p = 0 ∧ q = 0 := by
  let n := max p.natDegree q.natDegree + 1
  have hp : p.natDegree < n := Nat.lt_succ_of_le (le_max_left _ _)
  have hq : q.natDegree < n := Nat.lt_succ_of_le (le_max_right _ _)
  have he := polynomial_sequence_independent z (normalPairEval x y) hzinj hmod n
    (fun i => (p.coeff i,q.coeff i)) ((evalXZ_pair_sum x y z p q n hp hq).symm.trans h)
  have hcoeff (i : ℕ) : p.coeff i = 0 ∧ q.coeff i = 0 := by
    by_cases hi : i < n
    · have h' := he i hi
      exact ⟨congrArg Prod.fst h',congrArg Prod.snd h'⟩
    · exact ⟨Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩
  constructor
  · apply Polynomial.ext; intro i; simpa only [Polynomial.coeff_zero] using (hcoeff i).1
  · apply Polynomial.ext; intro i; simpa only [Polynomial.coeff_zero] using (hcoeff i).2

#print axioms bivariate_pair_eq_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: QuadraticKernelProbe development. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
open Polynomial
variable {S A : Type u} [CommRing S] [CommRing A]

def monicQuadratic (b c : S) : Polynomial S := X^2 + (C b * X + C c)

lemma monicQuadratic_monic (b c : S) : (monicQuadratic b c).Monic := by
  apply monic_X_pow_add
  exact (degree_add_le _ _).trans_lt (max_lt
    ((degree_C_mul_X_le b).trans_lt (by norm_num))
    (degree_C_le.trans_lt (by norm_num)))

lemma monicQuadratic_degree [Nontrivial S] (b c : S) :
    (monicQuadratic b c).degree = 2 := by
  have h : (C b * X + C c : Polynomial S).degree < 2 :=
    (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le b).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))
  rw [monicQuadratic, degree_add_eq_left_of_degree_lt]
  · simp
  · simpa [degree_X_pow] using h

lemma eval_quadratic_kernel [Nontrivial S] (f : S →+* A) (y : A) (b c : S)
    (hroot : eval₂ f y (monicQuadratic b c) = 0)
    (hlin : ∀ p q : S, f p + f q * y = 0 → p = 0 ∧ q = 0)
    (p : Polynomial S) : eval₂ f y p = 0 ↔ monicQuadratic b c ∣ p := by
  constructor
  · intro hp
    let q := p %ₘ monicQuadratic b c
    have hq : q.degree < 2 := by
      simpa only [monicQuadratic_degree] using degree_modByMonic_lt p (monicQuadratic_monic b c)
    have hsum : q = C (q.coeff 0) + C (q.coeff 1)*X := by
      have h := q.sum_fin (fun i a => monomial i a) (by simp) hq
      rw [sum_monomial_eq] at h
      simpa [Fin.sum_univ_two,monomial_zero_left,← C_mul_X_pow_eq_monomial] using h.symm
    have he : eval₂ f y q = 0 := by
      have h := congrArg (eval₂ f y) (modByMonic_add_div p (monicQuadratic b c))
      simpa only [eval₂_add,eval₂_mul,hroot,zero_mul,add_zero,hp] using h
    rw [hsum,eval₂_add,eval₂_C,eval₂_mul,eval₂_C,eval₂_X] at he
    obtain ⟨h0,h1⟩ := hlin _ _ he
    apply (modByMonic_eq_zero_iff_dvd (monicQuadratic_monic b c)).mp
    change q = 0
    rw [hsum,h0,h1,map_zero,zero_mul,add_zero]
  · rintro ⟨q,rfl⟩
    rw [eval₂_mul,hroot,zero_mul]

#print axioms eval_quadratic_kernel
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: ThreeVariablesProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
variable (R : Type u) [CommRing R]
open Polynomial

def threeVariablesEquiv : MvPolynomial (Fin 3) R ≃ₐ[R] Polynomial (Polynomial (Polynomial R)) :=
  (MvPolynomial.renameEquiv R ((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 1 2))).trans
    ((MvPolynomial.finSuccEquiv R 2).trans
      (Polynomial.mapAlgEquiv ((MvPolynomial.finSuccEquiv R 1).trans
        (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))))))

lemma threeVariablesEquiv_z : threeVariablesEquiv R (MvPolynomial.X 0) = C X := by
  unfold threeVariablesEquiv
  simp only [AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  have h : ((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 1 2)) 0 = (0:Fin 2).succ := by decide
  rw [h,MvPolynomial.finSuccEquiv_X_succ]
  simp only [Polynomial.coe_mapAlgEquiv,Polynomial.map_C,RingHom.coe_coe,AlgEquiv.trans_apply,
    MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X]

lemma threeVariablesEquiv_x : threeVariablesEquiv R (MvPolynomial.X 1) = C (C X) := by
  unfold threeVariablesEquiv
  simp only [AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  have h : ((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 1 2)) 1 = (1:Fin 2).succ := by decide
  rw [h,MvPolynomial.finSuccEquiv_X_succ]
  simp only [Polynomial.coe_mapAlgEquiv,Polynomial.map_C,AlgEquiv.trans_apply]
  change C ((Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (0:Fin 1).succ))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp only [Polynomial.coe_mapAlgEquiv,Polynomial.map_C]
  change C (C ((MvPolynomial.uniqueAlgEquiv R (Fin 1)) (MvPolynomial.X 0))) = _
  congr 2
  exact MvPolynomial.eval₂_X _ _ _

lemma threeVariablesEquiv_y : threeVariablesEquiv R (MvPolynomial.X 2) = X := by
  unfold threeVariablesEquiv
  simp only [AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  have h : ((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 1 2)) 2 = 0 := by decide
  rw [h,MvPolynomial.finSuccEquiv_X_zero]
  exact Polynomial.map_X _

lemma threeVariablesEquiv_C (r : R) : threeVariablesEquiv R (MvPolynomial.C r) = C (C (C r)) := by
  exact (threeVariablesEquiv R).commutes r

#print axioms threeVariablesEquiv_z
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: ExactKernelProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
open Polynomial GeometricCubic
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def evalXYZ (x y z : A) : Polynomial (Polynomial (Polynomial R)) →+* A :=
  Polynomial.eval₂RingHom (evalXZ x z) y

lemma evalXYZ_threeVariablesEquiv (x y z : A) (p : MvPolynomial (Fin 3) R) :
    evalXYZ x y z (threeVariablesEquiv R p) = MvPolynomial.aeval ![z,x,y] p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [threeVariablesEquiv_C]
    simp [evalXYZ,evalXZ]
  | add p q hp hq => rw [map_add,map_add,map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,map_mul,map_mul,hp]
    congr 1
    fin_cases i
    · change evalXYZ x y z (threeVariablesEquiv R (MvPolynomial.X 0)) = _
      rw [threeVariablesEquiv_z]; simp [evalXYZ,evalXZ]
    · change evalXYZ x y z (threeVariablesEquiv R (MvPolynomial.X 1)) = _
      rw [threeVariablesEquiv_x]; simp [evalXYZ,evalXZ]
    · change evalXYZ x y z (threeVariablesEquiv R (MvPolynomial.X 2)) = _
      rw [threeVariablesEquiv_y]; simp [evalXYZ,evalXZ]

def cubicLinear (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  C (C W.a₁) * C X * X + C (C W.a₃) * X^3

def cubicConstant (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  -(C X ^ 3 + C (C W.a₂) * C X ^ 2 * X^2 + C (C W.a₄) * C X * X^4 + C (C W.a₆) * X^6)

lemma threeVariablesEquiv_cubic (W : WeierstrassCurve R) :
    threeVariablesEquiv R (weightedCubic R W) = monicQuadratic (cubicLinear W) (cubicConstant W) := by
  unfold weightedCubic monicQuadratic cubicLinear cubicConstant
  simp only [map_sub,map_add,map_mul,map_pow,map_neg,threeVariablesEquiv_C,
    threeVariablesEquiv_z,threeVariablesEquiv_x,threeVariablesEquiv_y]
  ring

lemma weightedCubic_dvd_iff_eval_zero [Nontrivial R]
    (x y z : A) (W : WeierstrassCurve R)
    (hzinj : Function.Injective (fun a : A => z*a))
    (hmod : ∀ (p : Polynomial R × Polynomial R) (a : A),
      normalPairEval x y p = z*a → p = 0)
    (hrel : MvPolynomial.aeval ![z,x,y] (weightedCubic R W) = 0)
    (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval ![z,x,y] p = 0 ↔ weightedCubic R W ∣ p := by
  have hroot : eval₂ (evalXZ x z) y (monicQuadratic (cubicLinear W) (cubicConstant W)) = 0 := by
    rw [← threeVariablesEquiv_cubic]
    exact (evalXYZ_threeVariablesEquiv x y z _).trans hrel
  have h := eval_quadratic_kernel (evalXZ x z) y (cubicLinear W) (cubicConstant W) hroot
    (bivariate_pair_eq_zero x y z hzinj hmod) (threeVariablesEquiv R p)
  change evalXYZ x y z (threeVariablesEquiv R p) = 0 ↔ _ at h
  rw [evalXYZ_threeVariablesEquiv,← threeVariablesEquiv_cubic] at h
  apply h.trans
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨(threeVariablesEquiv R).symm q, ?_⟩
    apply (threeVariablesEquiv R).injective
    rw [map_mul,AlgEquiv.apply_symm_apply]
    exact hq
  · rintro ⟨q,rfl⟩
    exact ⟨threeVariablesEquiv R q, map_mul _ _ _⟩

#print axioms weightedCubic_dvd_iff_eval_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Kernel
end


/-! Exact coordinate kernel: GeometricKernelProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Filtration Kernel
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_cubic_kernel (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (hrel : MvPolynomial.aeval ![(z:A),(x:A),(y:A)] (weightedCubic R W) = 0) :
    RingHom.ker (MvPolynomial.aeval ![(z:A),(x:A),(y:A)]).toRingHom =
      Ideal.span {weightedCubic R W} := by
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z = 0 := by
    change leadingCoefficient R Q 1 (ι 1 z) = 0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hmod := normalPair_mod_z 𝓐 lead (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R := R) (𝓐 := 𝓐) (Q := Q) (ι := ι) (hRing := hRing)) z x y hzlead
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)
  have hzinj := actual_z_mul_injective (R := R) (𝓐 := 𝓐) (z := z) (Q := Q) (ι := ι) (hRing := hRing) hz
  ext p
  rw [RingHom.mem_ker,Ideal.mem_span_singleton]
  exact weightedCubic_dvd_iff_eval_zero (x:A) (y:A) (z:A) W hzinj hmod hrel p

lemma exists_cubic_quotient_equiv :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
      (e : (MvPolynomial (Fin 3) R ⧸ Ideal.span {weightedCubic R W}) ≃ₐ[R] A),
      ι 1 z = originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x) = unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y) = unitPower R 3 ∧
      ∀ p : MvPolynomial (Fin 3) R,
        e (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ![(z:A),(x:A),(y:A)] p := by
  obtain ⟨z,x,y,W,hz,hx,hy,hsurj,hrel⟩ := exists_surjective_polynomial_map_cubic R Q A 𝓐 ι hRing
  let f := MvPolynomial.aeval (R := R) ![(z:A),(x:A),(y:A)]
  have hk := actual_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hrel
  let e := (Ideal.quotientEquivAlgOfEq R hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨z,x,y,W,e,hz,hx,hy,?_⟩
  intro p
  change Ideal.quotientKerAlgEquivOfSurjective hsurj
    (Ideal.quotientEquivAlgOfEq R hk.symm (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hsurj p

omit hRing in
/-- The actual origin section ring has the constructed weighted cubic presentation. -/
theorem exists_origin_cubic_quotient :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R)
        (e : (MvPolynomial (Fin 3) R ⧸ Ideal.span {weightedCubic R W}) ≃ₐ[R] B),
        j 1 z = originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x) = unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y) = unitPower R 3 ∧
        ∀ p : MvPolynomial (Fin 3) R,
          e (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ![(z:B),(x:B),(y:B)] p := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,exists_cubic_quotient_equiv R Q B 𝓑 j hj⟩

#print axioms exists_origin_cubic_quotient
#print axioms actual_cubic_kernel
#print axioms exists_cubic_quotient_equiv
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
end


/-! Plane coordinate construction: DegreeThreeProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneCoordinates
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R) (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
variable (drop : ∀ m (a : 𝓐 (m+1)), lead (m+1) a = 0 → ∃ b : 𝓐 m, (z:A)*b = a)
variable (deg1 : ∀ a : 𝓐 1, ∃ r : R, (a:A) = algebraMap R A r * z)
include drop deg1
lemma degree_three_expansion (hx : lead 2 x = 1) (hy : lead 3 y = 1) (a : 𝓐 3) :
    ∃ r s t : R, (a:A) = algebraMap R A r * z^3 + algebraMap R A s * x*z + algebraMap R A t*y := by
  obtain ⟨b,hb⟩ := CubicAlgebra.subtract_lift 𝓐 lead z drop 2 y a hy
  obtain ⟨c,hc⟩ := CubicAlgebra.subtract_lift 𝓐 lead z drop 1 x b hx
  obtain ⟨r,hr⟩ := deg1 c
  refine ⟨r,lead 2 b,lead 3 a,?_⟩
  rw [← hc,hr] at hb
  linear_combination -hb

variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b, SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
variable (hone : lead 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1)
variable (hzinj : Function.Injective (fun a : A => (z:A)*a))
include hmul hone hzinj
omit drop deg1 in
lemma degree_three_coefficients_zero (hz : lead 1 z = 0) (hx : lead 2 x = 1)
    (hy : lead 3 y = 1) (r s t : R)
    (h : algebraMap R A r*z^3 + algebraMap R A s*x*z + algebraMap R A t*y = 0) :
    r=0 ∧ s=0 ∧ t=0 := by
  let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
  let zzz : 𝓐 3 := ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩
  let xz : 𝓐 3 := ⟨(x:A)*z,SetLike.mul_mem_graded x.2 z.2⟩
  have hzz : lead 2 zz = 0 := by rw [hmul 1 1 z z,hz,zero_mul]
  have hzzz : lead 3 zzz = 0 := by rw [hmul 2 1 zz z,hz,mul_zero]
  have hxz : lead 3 xz = 0 := by rw [hmul 2 1 x z,hz,mul_zero]
  have he : r • zzz + s • xz + t • y = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_add,Submodule.coe_smul,Algebra.smul_def,
      ZeroMemClass.coe_zero,zzz,zz,xz,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h
  have ht : t=0 := by
    have hh := congrArg (lead 3) he
    simpa only [map_add,map_smul,map_zero,hzzz,hxz,hy,smul_eq_mul,mul_zero,mul_one,
      zero_add] using hh
  subst t
  simp only [map_zero,zero_mul,add_zero] at h
  have hh : (z:A)*(algebraMap R A r*(z:A)^2+algebraMap R A s*x) = (z:A)*0 := by
    linear_combination h
  have hh' := hzinj hh
  have he2 : r • zz + s • x = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_add,Submodule.coe_smul,Algebra.smul_def,
      ZeroMemClass.coe_zero,zz,pow_two] using hh'
  have hs : s=0 := by
    have hh := congrArg (lead 2) he2
    simpa only [map_add,map_smul,map_zero,hzz,hx,smul_eq_mul,mul_zero,mul_one,
      zero_add] using hh
  subst s
  simp only [map_zero,zero_mul,add_zero] at hh'
  have hr : algebraMap R A r = 0 := by
    apply hzinj
    apply hzinj
    linear_combination hh'
  have he0 : r • (⟨1,SetLike.GradedOne.one_mem⟩ : 𝓐 0) = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_smul,Algebra.smul_def,mul_one,ZeroMemClass.coe_zero] using hr
  have hr0 : r=0 := by
    have hh := congrArg (lead 0) he0
    simpa only [map_smul,map_zero,hone,smul_eq_mul,mul_one] using hh
  exact ⟨hr0,rfl,rfl⟩

omit drop deg1 hmul hone hzinj in
def degreeThreeMap : (Fin 3 → R) →ₗ[R] 𝓐 3 where
  toFun c := c 0 • ⟨(z:A)*z*z,SetLike.mul_mem_graded (SetLike.mul_mem_graded z.2 z.2) z.2⟩ +
    c 1 • ⟨(x:A)*z,SetLike.mul_mem_graded x.2 z.2⟩ + c 2 • y
  map_add' c d := by simp only [Pi.add_apply,add_smul]; abel
  map_smul' r c := by simp only [Pi.smul_apply,smul_add,smul_smul,RingHom.id_apply,smul_eq_mul]

omit drop deg1 hmul hone hzinj in
lemma degreeThreeMap_coe (c : Fin 3 → R) :
    ((degreeThreeMap 𝓐 z x y c : 𝓐 3) : A) =
      algebraMap R A (c 0)*z^3 + algebraMap R A (c 1)*x*z + algebraMap R A (c 2)*y := by
  simp only [degreeThreeMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_add,Submodule.coe_smul,Algebra.smul_def]
  ring

lemma degreeThreeMap_bijective (hz : lead 1 z = 0) (hx : lead 2 x = 1)
    (hy : lead 3 y = 1) : Function.Bijective (degreeThreeMap 𝓐 z x y) := by
  constructor
  · apply (degreeThreeMap 𝓐 z x y).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have h := congrArg Subtype.val hc
    rw [degreeThreeMap_coe] at h
    obtain ⟨h0,h1,h2⟩ := degree_three_coefficients_zero 𝓐 lead z x y hmul hone hzinj hz hx hy
      (c 0) (c 1) (c 2) h
    funext i
    fin_cases i <;> assumption
  · intro a
    obtain ⟨r,s,t,h⟩ := degree_three_expansion 𝓐 lead z x y drop deg1 hx hy a
    refine ⟨![r,s,t],?_⟩
    apply Subtype.ext
    rw [degreeThreeMap_coe]
    exact h.symm

def degreeThreeEquiv (hz : lead 1 z=0) (hx : lead 2 x=1) (hy : lead 3 y=1) :
    (Fin 3 → R) ≃ₗ[R] 𝓐 3 :=
  LinearEquiv.ofBijective (degreeThreeMap 𝓐 z x y)
    (degreeThreeMap_bijective 𝓐 lead z x y drop deg1 hmul hone hzinj hz hx hy)

def degreeThreeBasis (hz : lead 1 z=0) (hx : lead 2 x=1) (hy : lead 3 y=1) :
    Module.Basis (Fin 3) R (𝓐 3) :=
  (Pi.basisFun R (Fin 3)).map (degreeThreeEquiv 𝓐 lead z x y drop deg1 hmul hone hzinj hz hx hy)

lemma degreeThreeBasis_coe (hz : lead 1 z=0) (hx : lead 2 x=1) (hy : lead 3 y=1) :
    (fun i => ((degreeThreeBasis 𝓐 lead z x y drop deg1 hmul hone hzinj hz hx hy i : 𝓐 3) : A)) =
      ![(z:A)^3,(x:A)*z,(y:A)] := by
  funext i
  fin_cases i <;>
    simp [degreeThreeBasis,degreeThreeEquiv,degreeThreeMap,Pi.basisFun_apply,Algebra.smul_def,pow_succ]

#print axioms degreeThreeBasis_coe
#print axioms degreeThreeMap_bijective
#print axioms degree_three_expansion
#print axioms degree_three_coefficients_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneCoordinates
end


/-! Plane coordinate construction: VeroneseGenerationProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.VeroneseGeneration
open Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R) (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b,SetLike.mul_mem_graded a.2 b.2⟩ = lead m a * lead n b)
variable (hone : lead 0 ⟨1,SetLike.GradedOne.one_mem⟩ = 1)

def padding (m : ℕ) : ℕ := (3-m%3)%3

lemma padding_step (m : ℕ) : ∃ k : ℕ, padding (m+1)+1 = 3*k+padding m := by
  unfold padding
  have h := Nat.mod_lt m (by omega : 0<3)
  have h' := Nat.mod_add_div m 3
  have h'' := Nat.mod_add_div (m+1) 3
  have hm := Nat.mod_lt (m+1) (by omega : 0<3)
  by_cases hz : m%3=0
  · exact ⟨1,by omega⟩
  · exact ⟨0,by omega⟩

lemma normal_weight (m : ℕ) (hm : 2 ≤ m) : ∃ k : ℕ, padding m*2+k*3=m := by
  unfold padding
  have h := Nat.mod_lt m (by omega : 0<3)
  have h' := Nat.mod_add_div m 3
  by_cases h1 : m%3=1
  · exact ⟨m/3-1,by omega⟩
  · exact ⟨m/3,by omega⟩

include hmul hone
lemma normalized_padded_monomial (hx : lead 2 x = 1) (hy : lead 3 y = 1)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ t : 𝓐 m, lead m t=1 ∧
      (z:A)^(padding m)*(t:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
  obtain ⟨k,hk⟩ := normal_weight m hm
  have hn := Normalized.mul 𝓐 lead hmul
    (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 2 (x:A) from ⟨x.2,hx⟩) (padding m))
    (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 3 (y:A) from ⟨y.2,hy⟩) k)
  rw [hk] at hn
  obtain ⟨ht,hl⟩ := hn
  refine ⟨⟨(x:A)^(padding m)*(y:A)^k,ht⟩,hl,?_⟩
  have he : (z:A)^(padding m)*((x:A)^(padding m)*(y:A)^k) =
      ((x:A)*z)^(padding m)*(y:A)^k := by rw [mul_pow]; ring
  change (z:A)^(padding m)*((x:A)^(padding m)*(y:A)^k) ∈ _
  rw [he]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _)

variable (drop : ∀ m (a : 𝓐 (m+1)), lead (m+1) a=0 → ∃ b : 𝓐 m, (z:A)*b=a)
variable (deg0 : ∀ a : 𝓐 0, ∃ r : R, (a:A)=algebraMap R A r)
variable (deg1 : ∀ a : 𝓐 1, ∃ r : R, (a:A)=algebraMap R A r*z)
include drop deg0 deg1
lemma padded_homogeneous_generated (hx : lead 2 x=1) (hy : lead 3 y=1)
    (m : ℕ) (a : 𝓐 m) :
    (z:A)^(padding m)*(a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
  let S := Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A)
  have hz3 : (z:A)^3 ∈ S := Algebra.subset_adjoin (by simp)
  induction m with
  | zero =>
    obtain ⟨r,hr⟩ := deg0 a
    simpa only [padding,Nat.zero_mod,Nat.sub_zero,Nat.mod_self,pow_zero,one_mul,hr] using S.algebraMap_mem r
  | succ m ih =>
    by_cases hm : m=0
    · subst m
      obtain ⟨r,hr⟩ := deg1 a
      change (z:A)^2*(a:A) ∈ S
      rw [hr]
      have he : (z:A)^2*(algebraMap R A r*z) = algebraMap R A r*(z:A)^3 := by ring
      rw [he]
      exact S.mul_mem (S.algebraMap_mem r) hz3
    obtain ⟨t,ht,htmem⟩ := normalized_padded_monomial 𝓐 lead z x y hmul hone hx hy (m+1) (by omega)
    obtain ⟨b,hb⟩ := CubicAlgebra.subtract_lift 𝓐 lead z drop m t a ht
    have he : (z:A)^(padding (m+1))*(a:A) =
        (z:A)^(padding (m+1)+1)*(b:A) +
          algebraMap R A (lead (m+1) a)*((z:A)^(padding (m+1))*(t:A)) := by
      rw [← hb,pow_succ]
      ring
    rw [he]
    apply S.add_mem _ (S.mul_mem (S.algebraMap_mem _) htmem)
    obtain ⟨k,hk⟩ := padding_step m
    rw [hk,pow_add,pow_mul,mul_assoc]
    exact S.mul_mem (S.pow_mem hz3 k) (ih b)

lemma third_veronese_generated (hx : lead 2 x=1) (hy : lead 3 y=1)
    (n : ℕ) (a : 𝓐 (3*n)) :
    (a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
  have h := padded_homogeneous_generated 𝓐 lead z x y hmul hone drop deg0 deg1 hx hy (3*n) a
  simpa [padding] using h

#print axioms third_veronese_generated
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.VeroneseGeneration
end


/-! Plane coordinate construction: PlaneSectionDataProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Filtration Kernel PlaneCoordinates
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_degree_three_basis (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3) :
    ∃ b : Module.Basis (Fin 3) R (𝓐 3),
      (fun i => ((b i : 𝓐 3) : A)) = ![(z:A)^3,(x:A)*z,(y:A)] := by
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hxlead := leadingCoefficient_normalized R Q 2 _ hx
  have hylead := leadingCoefficient_normalized R Q 3 _ hy
  exact ⟨degreeThreeBasis 𝓐 lead z x y (gradedLead_drop R Q A 𝓐 ι hRing z hz)
      (graded_degree_one R Q A 𝓐 ι hRing z hz) (gradedLead_mul R Q A 𝓐 ι hRing)
      (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
      (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
      hzlead hxlead hylead,
    degreeThreeBasis_coe 𝓐 lead z x y (gradedLead_drop R Q A 𝓐 ι hRing z hz)
      (graded_degree_one R Q A 𝓐 ι hRing z hz) (gradedLead_mul R Q A 𝓐 ι hRing)
      (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
      (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
      hzlead hxlead hylead⟩

lemma actual_third_veronese_generated (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (n : ℕ) (a : 𝓐 (3*n)) :
    (a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
  exact VeroneseGeneration.third_veronese_generated 𝓐 (gradedLead R Q A 𝓐 ι hRing) z x y
    (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing))
    (gradedLead_drop R Q A 𝓐 ι hRing z hz) (graded_degree_zero R Q A 𝓐 ι hRing)
    (graded_degree_one R Q A 𝓐 ι hRing z hz)
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy) n a

omit hRing in
lemma plane_polynomial_aeval (W : WeierstrassCurve R) (z x y : A) :
    MvPolynomial.aeval ![x*z,y,z^3] W.toProjective.polynomial =
      z^3 * MvPolynomial.aeval ![z,x,y] (weightedCubic R W) := by
  simp [WeierstrassCurve.Projective.polynomial,weightedCubic]
  ring

lemma exists_plane_coordinate_data :
    ∃ (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
      (b : Module.Basis (Fin 3) R (𝓐 3)),
      ι 1 z=originDegreeOne R Q ∧
      powerRestriction R Q 2 (ι 2 x)=unitPower R 2 ∧
      powerRestriction R Q 3 (ι 3 y)=unitPower R 3 ∧
      (fun i => ((b i : 𝓐 3) : A)) = ![(z:A)^3,(x:A)*z,(y:A)] ∧
      (∀ n (a : 𝓐 (3*n)), (a:A) ∈ Algebra.adjoin R ({(z:A)^3,(x:A)*z,(y:A)} : Set A)) ∧
      MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] W.toProjective.polynomial=0 ∧
      RingHom.ker (MvPolynomial.aeval ![(z:A),(x:A),(y:A)]).toRingHom =
        Ideal.span {weightedCubic R W} := by
  obtain ⟨z,x,y,W,hz,hx,hy,hs,hrel⟩ := exists_surjective_polynomial_map_cubic R Q A 𝓐 ι hRing
  obtain ⟨b,hb⟩ := actual_degree_three_basis R Q A 𝓐 ι hRing z x y hz hx hy
  refine ⟨z,x,y,W,b,hz,hx,hy,hb,
    actual_third_veronese_generated R Q A 𝓐 ι hRing z x y hz hx hy,?_,
    actual_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hrel⟩
  rw [plane_polynomial_aeval R A W,hrel,mul_zero]

#print axioms exists_plane_coordinate_data
#print axioms actual_degree_three_basis
#print axioms actual_third_veronese_generated
#print axioms plane_polynomial_aeval
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
end


/-! Plane coordinate construction: FrameAwayProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
lemma sections_empty_subsingleton {X : Scheme.{u}} (M : X.Modules) : Subsingleton Γ(M,⊥) := by
  haveI : Subsingleton Γ(X,⊥) := inferInstance
  exact Module.subsingleton Γ(X,⊥) _

lemma idealSectionRight_isFrameOn {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.IsInvertible) (e : I.invModule ⊗ I.module ≅ 𝟙_ X.Modules)
    (V : X.Opens) (hV : Disjoint (V : Set X) (I.support : Set X)) :
    Scheme.Modules.IsFrameOn
      ((idealSectionRight I e).app ⊤ (Scheme.Modules.unitSection ⊤)) V := by
  intro W hWtop hWV
  let L := I.invModule
  have hL : Scheme.Modules.IsLocallyFreeOfRank 1 L :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hI.isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I L hL
  haveI := hS.mono_f
  haveI : Mono (idealSectionRight I e) := by
    change Mono (e.inv ≫ ((L ◁ I.moduleι) ≫ (ρ_ L).hom))
    infer_instance
  have hp : I.subschemeι ⁻¹ᵁ W = ⊥ := by
    apply bot_unique
    intro q hq
    have hi : I.subschemeι q ∈ I.support := by
      change I.subschemeι q ∈ (I.support : Set X)
      rw [← I.range_subschemeι]
      exact Set.mem_range_self q
    exact (Set.disjoint_left.mp hV (hWV hq) hi).elim
  have hsub : Subsingleton Γ((Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj L),W) := by
    change Subsingleton Γ((Scheme.Modules.pullback I.subschemeι).obj L,I.subschemeι ⁻¹ᵁ W)
    rw [hp]
    exact sections_empty_subsingleton _
  have hbij : Function.Bijective ((idealSectionRight I e).app W) := by
    constructor
    · exact (Scheme.Modules.Hom.mono_iff_injective _).mp inferInstance W
    · intro a
      have hz : ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L).app W a = 0 :=
        @Subsingleton.elim _ hsub _ _
      obtain ⟨b,hb⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
        (ShortComplex.mk _ _ w) hS.exact W a hz
      refine ⟨e.hom.app W b,?_⟩
      change (e.hom ≫ e.inv ≫ (L ◁ I.moduleι) ≫ (ρ_ L).hom).app W b = a
      simpa only [e.hom_inv_id_assoc] using hb
  have hnat : I.invModule.presheaf.map (homOfLE hWtop).op
      ((idealSectionRight I e).app ⊤ (Scheme.Modules.unitSection ⊤)) =
      (idealSectionRight I e).app W (Scheme.Modules.unitSection W) := by
    have hn := (idealSectionRight I e).mapPresheaf.naturality (homOfLE hWtop).op
    have hh := congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) hn) (Scheme.Modules.unitSection ⊤)
    change (idealSectionRight I e).app W ((𝟙_ X.Modules).presheaf.map (homOfLE hWtop).op
      (Scheme.Modules.unitSection ⊤)) = _ at hh
    rw [Scheme.Modules.map_unitSection] at hh
    exact hh.symm
  rw [hnat]
  have he : (fun g : Γ(X,W) => g • (idealSectionRight I e).app W (Scheme.Modules.unitSection W)) =
      (fun g => (idealSectionRight I e).app W (Scheme.Modules.toUnitSection W g)) := by
    funext g
    rw [← Scheme.Modules.Hom.app_smul,Scheme.Modules.smul_unitSection]
    rfl
  rw [he]
  apply hbij.comp
  change Function.Bijective (fun g : Γ(X,W) => g)
  exact Function.bijective_id

#print axioms idealSectionRight_isFrameOn
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Filtration
end


/-! Plane coordinate construction: SectionFramesProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
variable {X Y : Scheme.{u}} {M : X.Modules}

def sectionHom (s : Γ(M,⊤)) : 𝟙_ X.Modules ⟶ M :=
  M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U => M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (fun U V f => by
      change M.presheaf.map f (M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) = _
      rw [← CategoryTheory.comp_apply,← M.presheaf.map_comp]
      rfl))

lemma sectionHom_app (s : Γ(M,⊤)) (U : X.Opens) (r : Γ(X,U)) :
    (sectionHom s).app U (Scheme.Modules.toUnitSection U r) =
      r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  rfl

lemma sectionHom_app_one (s : Γ(M,⊤)) :
    (sectionHom s).app ⊤ (Scheme.Modules.unitSection ⊤)=s := by
  change (sectionHom s).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)=s
  rw [sectionHom_app s ⊤ 1,one_smul]
  rw [Subsingleton.elim (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)) (𝟙 ⊤),op_id,M.presheaf.map_id]
  rfl

lemma isIso_of_frame_top (s : 𝟙_ X.Modules ⟶ M)
    (hs : Scheme.Modules.IsFrameOn (s.app ⊤ (Scheme.Modules.unitSection ⊤)) ⊤) : IsIso s := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hh := hs.bijective (show U ≤ ⊤ from le_top) (show U ≤ ⊤ from le_top)
  have hn := s.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have hn' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) hn) (Scheme.Modules.unitSection ⊤)
  change s.app U ((𝟙_ X.Modules).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (Scheme.Modules.unitSection ⊤)) = _ at hn'
  rw [Scheme.Modules.map_unitSection] at hn'
  change s.app U (Scheme.Modules.unitSection U) = M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (s.app ⊤ (Scheme.Modules.unitSection ⊤)) at hn'
  rw [← hn'] at hh
  have he : (fun g : Γ(X,U) => g • s.app U (Scheme.Modules.unitSection U)) =
      (fun g : Γ(X,U) => s.app U (Scheme.Modules.toUnitSection U g)) := by
    funext g
    rw [← Scheme.Modules.Hom.app_smul,Scheme.Modules.smul_unitSection]
    rfl
  rw [he] at hh
  exact hh

lemma zeroSchemeIdeal_of_isIso (s : 𝟙_ X.Modules ⟶ M) [IsIso s] :
    Scheme.Modules.zeroSchemeIdeal s=⊤ := by
  have he := Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (𝟙 (𝟙_ X.Modules)) s
  rw [Category.id_comp] at he
  rw [he]
  have h := Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul (𝟙 (𝟙_ X.Modules))
    (1 : Γ(X,⊤)) (by simp)
  rw [h]
  ext U
  simp [Ideal.map_top]

lemma pullbackSection_app_top (f : Y ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    (Scheme.Modules.pullbackSection f s).app ⊤ (Scheme.Modules.unitSection ⊤) =
      Scheme.Modules.pullbackLocalSection f (s.app ⊤ (Scheme.Modules.unitSection ⊤)) := by
  have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection f ⊤ (1 : Γ(X,⊤))
  rw [map_one] at h
  change (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ ⊤)
    (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.unitSection ⊤)) = Scheme.Modules.unitSection (f ⁻¹ᵁ ⊤) at h
  have h1 : (Scheme.Modules.pullbackUnitIso f).inv.app (f ⁻¹ᵁ ⊤) (Scheme.Modules.unitSection ⊤) =
      Scheme.Modules.pullbackLocalSection f (Scheme.Modules.unitSection ⊤) := by
    change (Scheme.Modules.pullbackUnitIso f).inv.app (f ⁻¹ᵁ ⊤) (Scheme.Modules.unitSection (f ⁻¹ᵁ ⊤)) = _
    rw [← h]
    change ((Scheme.Modules.pullbackUnitIso f).hom ≫ (Scheme.Modules.pullbackUnitIso f).inv).app _ _ = _
    rw [Iso.hom_inv_id]
    rfl
  change ((Scheme.Modules.pullback f).map s).app (f ⁻¹ᵁ ⊤)
    ((Scheme.Modules.pullbackUnitIso f).inv.app _ (Scheme.Modules.unitSection ⊤)) = _
  rw [h1]
  exact (Scheme.Modules.pullbackLocalSection_app f s _).symm

lemma disjoint_range_zeroSchemeIdeal_of_pullback_frame (f : Y ⟶ X)
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hs : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection f
      (s.app ⊤ (Scheme.Modules.unitSection ⊤))) ⊤) :
    Disjoint (Set.range f) ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  haveI : IsIso (Scheme.Modules.pullbackSection f s) := isIso_of_frame_top _ (by
    rw [pullbackSection_app_top]
    exact hs)
  have hz := zeroSchemeIdeal_of_isIso (Scheme.Modules.pullbackSection f s)
  rw [← hM.comap_zeroSchemeIdeal f s] at hz
  have hsup := congrArg Scheme.IdealSheafData.support hz
  rw [Scheme.IdealSheafData.support_comap,Scheme.IdealSheafData.support_top] at hsup
  apply Set.disjoint_left.mpr
  rintro q ⟨p,rfl⟩ hq
  have hp : p ∈ ((Scheme.Modules.zeroSchemeIdeal s).comap f).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hq
  rw [hz,Scheme.IdealSheafData.support_top] at hp
  exact hp

#print axioms sectionHom_app_one
#print axioms disjoint_range_zeroSchemeIdeal_of_pullback_frame
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
end


/-! Plane coordinate construction: PlaneMapProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open Filtration SectionFrames GeometricCubic
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)

lemma normalized_pullback_frame (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection Q.zero s) ⊤ := by
  let η := Scheme.Modules.pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫
    Scheme.Modules.tensorPowMapIso (identityLineFrame R Q) m
  have hf := (unitPower_isFrame R m).map_iso η.symm
  have he : η.inv.app ⊤ (unitPower R m)=Scheme.Modules.pullbackLocalSection Q.zero s := by
    change η.hom.app ⊤ (Scheme.Modules.pullbackLocalSection Q.zero s)=unitPower R m at hs
    rw [← hs]
    change (η.hom ≫ η.inv).app ⊤ _ = _
    rw [η.hom_inv_id]
    rfl
  change Scheme.Modules.IsFrameOn (η.inv.app ⊤ (unitPower R m)) ⊤ at hf
  rw [he] at hf
  exact hf

lemma normalized_frame_open (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    ∃ V : Q.target.Opens, Set.range Q.zero ⊆ (V : Set Q.target) ∧
      Scheme.Modules.IsFrameOn s V := by
  let J := Scheme.Modules.zeroSchemeIdeal (sectionHom s)
  let V : Q.target.Opens := J.support.compl
  have hM := Q.zero_ideal_invertible.isInvertible_invModule.tensorPow m
  have hd : Disjoint (Set.range Q.zero) (J.support : Set Q.target) :=
    disjoint_range_zeroSchemeIdeal_of_pullback_frame Q.zero hM (sectionHom s) (by
      rw [sectionHom_app_one]
      exact normalized_pullback_frame R Q m s hs)
  refine ⟨V,?_,?_⟩
  · intro p hp
    exact fun h => Set.disjoint_left.mp hd hp h
  · have hf := hM.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal (sectionHom s) V
      (show Disjoint (V : Set Q.target) (J.support : Set Q.target) from (Set.disjoint_left.mpr (fun _ ha hb => ha hb)))
    change Scheme.Modules.IsFrameOn ((sectionHom s).app ⊤ (Scheme.Modules.unitSection ⊤)) V at hf
    rw [sectionHom_app_one] at hf
    exact hf

lemma origin_complement_frame :
    Scheme.Modules.IsFrameOn (originDegreeOne R Q) Q.zero.ker.support.compl := by
  exact (idealSectionRight_isFrameOn Q.zero.ker Q.zero_ideal_invertible (originPairing R Q)
    Q.zero.ker.support.compl (Set.disjoint_left.mpr (fun _ ha hb => ha hb))).tensorPowSection 1

variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)

def planeZ (z : 𝓐 1) : 𝓐 3 :=
  ⟨(z:A)*z*z,SetLike.mul_mem_graded (SetLike.mul_mem_graded z.2 z.2) z.2⟩

def planeX (z : 𝓐 1) (x : 𝓐 2) : 𝓐 3 :=
  ⟨(x:A)*z,SetLike.mul_mem_graded x.2 z.2⟩

include hRing
lemma planeZ_frame (z : 𝓐 1) (hz : ι 1 z=originDegreeOne R Q) :
    Scheme.Modules.IsFrameOn (ι 3 (planeZ R A 𝓐 z)) Q.zero.ker.support.compl := by
  have hf : Scheme.Modules.IsFrameOn (ι 1 z) Q.zero.ker.support.compl := by
    rw [hz]
    exact origin_complement_frame R Q
  let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
  have hff : Scheme.Modules.IsFrameOn (ι 2 zz) Q.zero.ker.support.compl := by
    rw [hRing.map_mul 1 1 z z]
    exact (hf.tensorSections hf).map_iso (Scheme.Modules.tensorPowAdd Q.zero.ker.invModule 1 1)
  rw [show planeZ R A 𝓐 z = ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩ from rfl,hRing.map_mul 2 1 zz z]
  exact (hff.tensorSections hf).map_iso (Scheme.Modules.tensorPowAdd Q.zero.ker.invModule 2 1)

lemma exists_plane_projPresentation (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z=originDegreeOne R Q)
    (hy : powerRestriction R Q 3 (ι 3 y)=unitPower R 3) :
    ∃ 𝔓 : Scheme.Modules.ProjPresentation (Q.zero.ker.invModule.tensorPow 3) Q.structureMap 2,
      𝔓.σ = ![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)] := by
  obtain ⟨V,hV,hframeV⟩ := normalized_frame_open R Q 3 (ι 3 y) hy
  let U := Q.zero.ker.support.compl
  have hframeU := planeZ_frame R Q A 𝓐 ι hRing z hz
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  have hsupport : (Q.zero.ker.support : Set Q.target)=Set.range Q.zero := by
    rw [Scheme.Hom.support_ker]
    exact Q.zero.isClosedEmbedding.isClosed_range.closure_eq
  have hUV : U ⊔ V=⊤ := by
    apply top_unique
    intro p _
    by_cases hp : p ∈ (Q.zero.ker.support : Set Q.target)
    · exact Or.inr (hV (hsupport ▸ hp))
    · exact Or.inl hp
  let σ : Fin 3 → Γ(Q.zero.ker.invModule.tensorPow 3,⊤) :=
    ![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)]
  let O : Fin 3 → Q.target.Opens := ![⊥,V,U]
  have hO : iSup O=⊤ := by
    apply top_unique
    rw [← hUV]
    exact sup_le (le_iSup O (2 : Fin 3)) (le_iSup O (1 : Fin 3))
  obtain ⟨𝔓,hσ,hpre⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top Q.structureMap
    (Q.zero.ker.invModule.tensorPow 3) 2 σ O hO (by
      intro i W hW
      fin_cases i
      · change W ≤ ⊥ at hW
        have he : W=⊥ := le_antisymm hW bot_le
        subst W
        letI := sections_empty_subsingleton (Q.zero.ker.invModule.tensorPow 3)
        exact ⟨fun a b _ => Subsingleton.elim a b,fun a => ⟨0,Subsingleton.elim _ _⟩⟩
      · exact hframeV.bijective le_top hW
      · exact hframeU.bijective le_top hW)
  exact ⟨𝔓,hσ⟩

omit hRing in
/-- A genuine plane morphism with the constructed Weierstrass coordinate relation,
starting only from the frozen geometric hypotheses. -/
theorem exists_origin_plane_map :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (𝓑 : ℕ → Submodule R B) (_ : GradedAlgebra 𝓑)
      (j : ∀ m : ℕ, 𝓑 m → Γ(Q.zero.ker.invModule.tensorPow m,⊤)),
      GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule B 𝓑 j ∧
      ∃ (z : 𝓑 1) (x : 𝓑 2) (y : 𝓑 3) (W : WeierstrassCurve R)
        (𝔓 : Scheme.Modules.ProjPresentation (Q.zero.ker.invModule.tensorPow 3) Q.structureMap 2),
        j 1 z=originDegreeOne R Q ∧
        powerRestriction R Q 2 (j 2 x)=unitPower R 2 ∧
        powerRestriction R Q 3 (j 3 y)=unitPower R 3 ∧
        𝔓.σ = ![j 3 (planeX R B 𝓑 z x),j 3 y,j 3 (planeZ R B 𝓑 z)] ∧
        MvPolynomial.aeval ![(x:B)*z,(y:B),(z:B)^3] W.toProjective.polynomial=0 ∧
        RingHom.ker (MvPolynomial.aeval ![(z:B),(x:B),(y:B)]).toRingHom =
          Ideal.span {weightedCubic R W} := by
  obtain ⟨B,hB,hRB,𝓑,h𝓑,j,hj⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hB
  letI := hRB
  letI := h𝓑
  obtain ⟨z,x,y,W,b,hz,hx,hy,hb,hgen,hplane,hker⟩ := exists_plane_coordinate_data R Q B 𝓑 j hj
  obtain ⟨𝔓,hσ⟩ := exists_plane_projPresentation R Q B 𝓑 j hj z x y hz hy
  exact ⟨B,hB,hRB,𝓑,h𝓑,j,hj,z,x,y,W,𝔓,hz,hx,hy,hσ,hplane,hker⟩

#print axioms exists_origin_plane_map
#print axioms normalized_frame_open
#print axioms planeZ_frame
#print axioms exists_plane_projPresentation
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
end


/-! Ordinary cubic presentation: GradedEvaluationProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GradedEvaluation
universe v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {σ : Type v} (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (d : ℕ) (f : σ → A) (hf : ∀ i, f i ∈ 𝓐 d)
include hf
lemma aeval_mem_grade {n : ℕ} {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval f p ∈ 𝓐 (d*n) := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (𝓐 (d*n)).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (𝓐 (d*n)).add_mem hp hq
  | monomial e r he =>
    rw [MvPolynomial.aeval_monomial]
    have hprod := SetLike.prod_mem_graded 𝓐 (fun i => e i*d) (fun i => f i^(e i))
      (F:=e.support) (fun i _ => SetLike.pow_mem_graded (e i) (hf i))
    have he' : ∑ i ∈ e.support, e i=n := by
      simpa only [Finsupp.weight_apply,Finsupp.sum,Pi.one_apply,smul_eq_mul,mul_one] using he
    rw [← Finset.sum_mul,he',Nat.mul_comm n d] at hprod
    simpa only [Algebra.smul_def,Finsupp.prod] using (𝓐 (d*n)).smul_mem r hprod

lemma proj_aeval (hd : 0<d) (n : ℕ) (p : MvPolynomial σ R) :
    GradedAlgebra.proj 𝓐 (d*n) (MvPolynomial.aeval f p) =
      MvPolynomial.aeval f (MvPolynomial.homogeneousComponent n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
    have hmono : (MvPolynomial.monomial e r).IsHomogeneous e.degree :=
      MvPolynomial.isHomogeneous_monomial r rfl
    have hgrade := aeval_mem_grade 𝓐 d f hf hmono
    rw [MvPolynomial.homogeneousComponent_of_mem hmono]
    by_cases hn : n=e.degree
    · rw [if_pos hn]
      subst n
      exact DirectSum.decompose_of_mem_same 𝓐 hgrade
    · rw [if_neg hn,map_zero]
      exact DirectSum.decompose_of_mem_ne 𝓐 hgrade (by
        intro he
        apply hn
        exact (Nat.eq_of_mul_eq_mul_left hd he).symm)
  | add p q hp hq =>
    simp only [map_add,hp,hq]

lemma exists_homogeneous_lift (hd : 0<d) (n : ℕ) (a : 𝓐 (d*n))
    (ha : (a:A) ∈ Algebra.adjoin R (Set.range f)) :
    ∃ p : MvPolynomial σ R, p.IsHomogeneous n ∧ MvPolynomial.aeval f p=(a:A) := by
  rw [← MvPolynomial.aeval_range] at ha
  obtain ⟨p,hp⟩ := ha
  change MvPolynomial.aeval f p=(a:A) at hp
  refine ⟨MvPolynomial.homogeneousComponent n p,MvPolynomial.homogeneousComponent_isHomogeneous n p,?_⟩
  rw [← proj_aeval 𝓐 d f hf hd,hp]
  exact DirectSum.decompose_of_mem_same 𝓐 a.2

#print axioms exists_homogeneous_lift
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GradedEvaluation
end


/-! Ordinary cubic presentation: CubicNormalIndependenceProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
open Kernel
variable {S A : Type u} [CommRing S] [CommRing A]
variable (g : S →+* A) (x z : A)
variable (hzinj : Function.Injective (fun a : A => z*a))
variable (hmod : ∀ i : Fin 3, ∀ p : S, ∀ a : A, g p*x^(i:ℕ)=z*a → p=0)

include hzinj hmod
lemma cubic_normal_independent_bounded (n : ℕ) (p q r : Polynomial S)
    (hp : ∀ k, n≤k → p.coeff k=0) (hq : ∀ k, n≤k → q.coeff k=0)
    (hr : ∀ k, n≤k → r.coeff k=0)
    (h : Polynomial.eval₂ g (z^3) p + (x*z)*Polynomial.eval₂ g (z^3) q +
      (x*z)^2*Polynomial.eval₂ g (z^3) r=0) : p=0 ∧ q=0 ∧ r=0 := by
  induction n generalizing p q r with
  | zero => exact ⟨Polynomial.ext (fun k => (hp k (Nat.zero_le k)).trans (Polynomial.coeff_zero k).symm),
      Polynomial.ext (fun k => (hq k (Nat.zero_le k)).trans (Polynomial.coeff_zero k).symm),
      Polynomial.ext (fun k => (hr k (Nat.zero_le k)).trans (Polynomial.coeff_zero k).symm)⟩
  | succ n ih =>
    let e := Polynomial.eval₂RingHom g (z^3)
    have he (v : Polynomial S) : e v=z^3*e v.divX+g (v.coeff 0) := by
      have hh := congrArg e (Polynomial.X_mul_divX_add v)
      change Polynomial.eval₂ g (z^3) (Polynomial.X*v.divX+Polynomial.C (v.coeff 0)) =
        Polynomial.eval₂ g (z^3) v at hh
      change Polynomial.eval₂ g (z^3) v=z^3*Polynomial.eval₂ g (z^3) v.divX+g (v.coeff 0)
      simpa only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_X,
        Polynomial.eval₂_C] using hh.symm
    let t := e p.divX+(x*z)*e q.divX+(x*z)^2*e r.divX
    have h0 : g (p.coeff 0)+z*x*g (q.coeff 0)+z^2*x^2*g (r.coeff 0)+z^3*t=0 := by
      change e p+(x*z)*e q+(x*z)^2*e r=0 at h
      rw [he p,he q,he r] at h
      dsimp only [t]
      linear_combination h
    have hp0 := hmod 0 (p.coeff 0) (-(x*g (q.coeff 0)+z*x^2*g (r.coeff 0)+z^2*t)) (by
      simp only [Fin.val_zero,pow_zero,mul_one]
      linear_combination h0)
    rw [hp0,map_zero,zero_add] at h0
    have h1 : g (q.coeff 0)*x+z*g (r.coeff 0)*x^2+z^2*t=0 := by
      apply hzinj
      linear_combination h0
    have hq0 := hmod 1 (q.coeff 0) (-(g (r.coeff 0)*x^2+z*t)) (by
      norm_num only [Fin.val_one,pow_one]
      linear_combination h1)
    rw [hq0,map_zero,zero_mul,zero_add] at h1
    have h2 : g (r.coeff 0)*x^2+z*t=0 := by
      apply hzinj
      linear_combination h1
    have hr0 := hmod 2 (r.coeff 0) (-t) (by
      change g (r.coeff 0)*x^2=z*(-t)
      linear_combination h2)
    rw [hr0,map_zero,zero_mul,zero_add] at h2
    have ht : t=0 := hzinj (by simpa only [mul_zero] using h2)
    obtain ⟨hp',hq',hr'⟩ := ih p.divX q.divX r.divX
      (fun k hk => by rw [Polynomial.coeff_divX];exact hp (k+1) (by omega))
      (fun k hk => by rw [Polynomial.coeff_divX];exact hq (k+1) (by omega))
      (fun k hk => by rw [Polynomial.coeff_divX];exact hr (k+1) (by omega)) ht
    refine ⟨?_,?_,?_⟩
    · simpa only [hp',hp0,map_zero,mul_zero,add_zero] using (Polynomial.X_mul_divX_add p).symm
    · simpa only [hq',hq0,map_zero,mul_zero,add_zero] using (Polynomial.X_mul_divX_add q).symm
    · simpa only [hr',hr0,map_zero,mul_zero,add_zero] using (Polynomial.X_mul_divX_add r).symm

lemma cubic_normal_independent (p q r : Polynomial S)
    (h : Polynomial.eval₂ g (z^3) p+(x*z)*Polynomial.eval₂ g (z^3) q+
      (x*z)^2*Polynomial.eval₂ g (z^3) r=0) : p=0 ∧ q=0 ∧ r=0 := by
  apply cubic_normal_independent_bounded g x z hzinj hmod
    (p.natDegree+q.natDegree+r.natDegree+1) p q r
    (fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    (fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    (fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)) h

#print axioms cubic_normal_independent
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
end


/-! Ordinary cubic presentation: PlaneLeadingProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
open Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (lead : ∀ m, 𝓐 m →ₗ[R] R)
variable (hmul : ∀ (m n : ℕ) (a : 𝓐 m) (b : 𝓐 n),
  lead (m+n) ⟨(a:A)*b,SetLike.mul_mem_graded a.2 b.2⟩=lead m a*lead n b)
variable (hone : lead 0 ⟨1,SetLike.GradedOne.one_mem⟩=1)
variable (x : 𝓐 2) (y : 𝓐 3) (hx : lead 2 x=1) (hy : lead 3 y=1)
include hmul hone hx hy
lemma globalLead_polynomial_y_mul_x (i j : ℕ) (p : Polynomial R) :
    globalLead 𝓐 lead (j*3+i*2) (Polynomial.aeval (y:A) p*(x:A)^i)=p.coeff j := by
  classical
  rw [Polynomial.aeval_def,Polynomial.eval₂_eq_sum,Polynomial.sum_def,Finset.sum_mul,map_sum]
  have hterm (k : ℕ) : globalLead 𝓐 lead (j*3+i*2)
      (algebraMap R A (p.coeff k)*(y:A)^k*(x:A)^i) = if k=j then p.coeff k else 0 := by
    rw [mul_assoc,← Algebra.smul_def,map_smul,smul_eq_mul]
    have hn := Normalized.mul 𝓐 lead hmul
      (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 3 y from ⟨y.2,hy⟩) k)
      (Normalized.pow 𝓐 lead hmul hone (show Normalized 𝓐 lead 2 x from ⟨x.2,hx⟩) i)
    rw [Normalized.globalLead 𝓐 lead hn]
    have he : k*3+i*2=j*3+i*2 ↔ k=j := by omega
    simp only [he]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with hj
  · rfl
  · exact (show p.coeff j=0 by simpa only [Polynomial.mem_support_iff,not_not] using hj).symm

lemma polynomial_y_mul_x_mod_z (z : 𝓐 1) (hz : lead 1 z=0) (i : ℕ)
    (p : Polynomial R) (a : A) (h : Polynomial.aeval (y:A) p*(x:A)^i=(z:A)*a) : p=0 := by
  apply Polynomial.ext
  intro j
  have hh := congrArg (globalLead 𝓐 lead (j*3+i*2)) h
  rw [globalLead_polynomial_y_mul_x 𝓐 lead hmul hone x y hx hy] at hh
  rw [globalLead_z_mul 𝓐 lead z hmul hz] at hh
  exact hh

#print axioms polynomial_y_mul_x_mod_z
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
end


/-! Ordinary cubic presentation: MonicCubicKernelProbe development. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
open Polynomial
variable {S A : Type u} [CommRing S] [CommRing A]

def monicCubic (b c d : S) : Polynomial S := X^3+(C b*X^2+(C c*X+C d))

lemma cubic_tail_degree (b c d : S) : (C b*X^2+(C c*X+C d) : Polynomial S).degree<3 := by
  apply (degree_add_le _ _).trans_lt
  apply max_lt
  · exact (degree_C_mul_X_pow_le 2 b).trans_lt (by norm_num)
  · exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le c).trans_lt (by norm_num)) (degree_C_le.trans_lt (by norm_num)))

lemma monicCubic_monic (b c d : S) : (monicCubic b c d).Monic :=
  monic_X_pow_add (cubic_tail_degree b c d)

lemma monicCubic_degree [Nontrivial S] (b c d : S) : (monicCubic b c d).degree=3 := by
  rw [monicCubic,degree_add_eq_left_of_degree_lt]
  · simp
  · simpa [degree_X_pow] using cubic_tail_degree b c d

lemma eval_monicCubic_kernel [Nontrivial S] (f : S →+* A) (x : A) (b c d : S)
    (hroot : eval₂ f x (monicCubic b c d)=0)
    (hlin : ∀ p q r : S, f p+x*f q+x^2*f r=0 → p=0 ∧ q=0 ∧ r=0)
    (p : Polynomial S) : eval₂ f x p=0 ↔ monicCubic b c d ∣ p := by
  constructor
  · intro hp
    let q := p %ₘ monicCubic b c d
    have hq : q.degree<3 := by
      simpa only [monicCubic_degree] using degree_modByMonic_lt p (monicCubic_monic b c d)
    have hsum : q=C (q.coeff 0)+X*C (q.coeff 1)+X^2*C (q.coeff 2) := by
      have h := q.sum_fin (fun i a => monomial i a) (by simp) hq
      rw [sum_monomial_eq] at h
      rw [Fin.sum_univ_three] at h
      change monomial 0 (q.coeff 0)+monomial 1 (q.coeff 1)+monomial 2 (q.coeff 2)=q at h
      rw [← C_mul_X_pow_eq_monomial,← C_mul_X_pow_eq_monomial,← C_mul_X_pow_eq_monomial] at h
      simpa only [pow_zero,pow_one,mul_one,one_mul,mul_comm] using h.symm
    have he : eval₂ f x q=0 := by
      have h := congrArg (eval₂ f x) (modByMonic_add_div p (monicCubic b c d))
      simpa only [eval₂_add,eval₂_mul,hroot,zero_mul,add_zero,hp] using h
    rw [hsum,eval₂_add,eval₂_add,eval₂_C,eval₂_mul,eval₂_X,eval₂_C,
      eval₂_mul,eval₂_pow,eval₂_X,eval₂_C] at he
    obtain ⟨h0,h1,h2⟩ := hlin _ _ _ he
    apply (modByMonic_eq_zero_iff_dvd (monicCubic_monic b c d)).mp
    change q=0
    rw [hsum,h0,h1,h2,map_zero,mul_zero,mul_zero,add_zero,add_zero]
  · rintro ⟨q,rfl⟩
    rw [eval₂_mul,hroot,zero_mul]

#print axioms eval_monicCubic_kernel
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
end


/-! Ordinary cubic presentation: PlaneKernelProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
open Polynomial Kernel
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def planeVariablesEquiv (R : Type u) [CommRing R] :
    MvPolynomial (Fin 3) R ≃ₐ[R] Polynomial (Polynomial (Polynomial R)) :=
  (MvPolynomial.renameEquiv R (Equiv.swap (0:Fin 3) 2)).trans (threeVariablesEquiv R)

lemma planeVariablesEquiv_X : planeVariablesEquiv R (MvPolynomial.X 0)=X := by
  simp only [planeVariablesEquiv,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X,Equiv.swap_apply_left,threeVariablesEquiv_y]
lemma planeVariablesEquiv_Y : planeVariablesEquiv R (MvPolynomial.X 1)=C (C X) := by
  simp only [planeVariablesEquiv,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  rw [show Equiv.swap (0:Fin 3) 2 1=1 by decide,threeVariablesEquiv_x]
lemma planeVariablesEquiv_Z : planeVariablesEquiv R (MvPolynomial.X 2)=C X := by
  simp only [planeVariablesEquiv,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X,Equiv.swap_apply_right,threeVariablesEquiv_z]
lemma planeVariablesEquiv_C (r : R) : planeVariablesEquiv R (MvPolynomial.C r)=C (C (C r)) :=
  (planeVariablesEquiv R).commutes r

lemma evalXYZ_planeVariablesEquiv (x y z : A) (p : MvPolynomial (Fin 3) R) :
    evalXYZ y x z (planeVariablesEquiv R p)=MvPolynomial.aeval ![x,y,z] p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [planeVariablesEquiv_C];simp [evalXYZ,evalXZ]
  | add p q hp hq => rw [map_add,map_add,map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,map_mul,map_mul,hp]
    congr 1
    fin_cases i
    · change evalXYZ y x z (planeVariablesEquiv R (MvPolynomial.X 0))=_
      rw [planeVariablesEquiv_X];simp [evalXYZ,evalXZ]
    · change evalXYZ y x z (planeVariablesEquiv R (MvPolynomial.X 1))=_
      rw [planeVariablesEquiv_Y];simp [evalXYZ,evalXZ]
    · change evalXYZ y x z (planeVariablesEquiv R (MvPolynomial.X 2))=_
      rw [planeVariablesEquiv_Z];simp [evalXYZ,evalXZ]

def planeB (W : WeierstrassCurve R) : Polynomial (Polynomial R) := C (C W.a₂)*X

def planeC (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  C (C W.a₄)*X^2-C (C W.a₁)*C X*X

def planeD (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  C (C W.a₆)*X^3-C (C W.a₃)*C X*X^2-(C X)^2*X

lemma planeVariablesEquiv_polynomial (W : WeierstrassCurve R) :
    planeVariablesEquiv R (-W.toProjective.polynomial)=monicCubic (planeB W) (planeC W) (planeD W) := by
  unfold WeierstrassCurve.Projective.polynomial monicCubic planeB planeC planeD
  simp only [map_neg,map_sub,map_add,map_mul,map_pow,map_neg,planeVariablesEquiv_C,
    planeVariablesEquiv_X,planeVariablesEquiv_Y,planeVariablesEquiv_Z]
  ring

lemma planePolynomial_dvd_iff_eval_zero [Nontrivial R]
    (x y z : A) (W : WeierstrassCurve R)
    (hzinj : Function.Injective (fun a : A => z*a))
    (hmod : ∀ i : Fin 3, ∀ p : Polynomial R, ∀ a : A,
      Polynomial.aeval y p*x^(i:ℕ)=z*a → p=0)
    (hrel : MvPolynomial.aeval ![x*z,y,z^3] W.toProjective.polynomial=0)
    (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval ![x*z,y,z^3] p=0 ↔ W.toProjective.polynomial ∣ p := by
  have hroot : eval₂ (evalXZ y (z^3)) (x*z) (monicCubic (planeB W) (planeC W) (planeD W))=0 := by
    rw [← planeVariablesEquiv_polynomial]
    change evalXYZ y (x*z) (z^3) (planeVariablesEquiv R (-W.toProjective.polynomial))=0
    rw [evalXYZ_planeVariablesEquiv,map_neg,hrel,neg_zero]
  have h := eval_monicCubic_kernel (evalXZ y (z^3)) (x*z) (planeB W) (planeC W) (planeD W) hroot
    (by
      intro p q r h
      apply cubic_normal_independent (Polynomial.aeval y).toRingHom x z hzinj hmod p q r
      exact h) (planeVariablesEquiv R p)
  change evalXYZ y (x*z) (z^3) (planeVariablesEquiv R p)=0 ↔ _ at h
  rw [evalXYZ_planeVariablesEquiv,← planeVariablesEquiv_polynomial] at h
  apply h.trans
  have he : planeVariablesEquiv R (-W.toProjective.polynomial) ∣ planeVariablesEquiv R p ↔
      -W.toProjective.polynomial ∣ p := by
    constructor
    · rintro ⟨q,hq⟩
      refine ⟨(planeVariablesEquiv R).symm q,?_⟩
      apply (planeVariablesEquiv R).injective
      rw [map_mul,AlgEquiv.apply_symm_apply]
      exact hq
    · rintro ⟨q,rfl⟩
      exact ⟨planeVariablesEquiv R q,map_mul _ _ _⟩
  exact he.trans neg_dvd

#print axioms planePolynomial_dvd_iff_eval_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneKernel
end


/-! Ordinary cubic presentation: ActualPlaneKernelProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
open Filtration CubicAlgebra Kernel
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma actual_plane_cubic_kernel (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3) (W : WeierstrassCurve R)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (hrel : MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] W.toProjective.polynomial=0) :
    RingHom.ker (MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3]).toRingHom =
      Ideal.span {W.toProjective.polynomial} := by
  let lead := gradedLead R Q A 𝓐 ι hRing
  have hzlead : lead 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  ext p
  rw [RingHom.mem_ker,Ideal.mem_span_singleton]
  apply PlaneKernel.planePolynomial_dvd_iff_eval_zero (x:A) (y:A) (z:A) W
    (actual_z_mul_injective (R:=R) (𝓐:=𝓐) (z:=z) (Q:=Q) (ι:=ι) (hRing:=hRing) hz)
    _ hrel
  intro i p a h
  exact PlaneKernel.polynomial_y_mul_x_mod_z 𝓐 lead (gradedLead_mul R Q A 𝓐 ι hRing)
    (gradedLead_one (R:=R) (𝓐:=𝓐) (Q:=Q) (ι:=ι) (hRing:=hRing)) x y
    (leadingCoefficient_normalized R Q 2 _ hx) (leadingCoefficient_normalized R Q 3 _ hy)
    z hzlead i p a h

lemma actual_plane_homogeneous_lift (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z = originDegreeOne R Q)
    (hx : powerRestriction R Q 2 (ι 2 x) = unitPower R 2)
    (hy : powerRestriction R Q 3 (ι 3 y) = unitPower R 3)
    (n : ℕ) (a : 𝓐 (3*n)) :
    ∃ p : MvPolynomial (Fin 3) R, p.IsHomogeneous n ∧
      MvPolynomial.aeval ![(x:A)*z,(y:A),(z:A)^3] p=(a:A) := by
  refine GradedEvaluation.exists_homogeneous_lift 𝓐 3 ![(x:A)*z,(y:A),(z:A)^3] ?_ (by decide) n a ?_
  · intro i
    fin_cases i
    · exact SetLike.mul_mem_graded x.2 z.2
    · exact y.2
    · exact SetLike.pow_mem_graded 3 z.2
  · have h := actual_third_veronese_generated R Q A 𝓐 ι hRing z x y hz hx hy n a
    have he : Set.range ![(x:A)*z,(y:A),(z:A)^3] = ({(z:A)^3,(x:A)*z,(y:A)} : Set A) := by
      ext b
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · rintro (rfl|rfl|rfl)
        · exact ⟨2,rfl⟩
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [he]
    exact h

#print axioms actual_plane_cubic_kernel
#print axioms actual_plane_homogeneous_lift
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic
end


/-! Cubic quotient and affine comparison: PlaneQuotientProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneQuotient
open HomogeneousIdealQuotientGrading
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (f : Fin 3 → A) (hf : ∀ i, f i ∈ 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval f).toRingHom = Ideal.span {W.toProjective.polynomial})

def evaluation : WeierstrassProjModel.ProjModelRingCR W.toProjective →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval f) (by intro p hp; exact RingHom.mem_ker.mp (hk.symm ▸ hp))

lemma evaluation_mk (p : MvPolynomial (Fin 3) R) :
    evaluation f W hk (Ideal.Quotient.mk _ p)=MvPolynomial.aeval f p := rfl

lemma evaluation_injective : Function.Injective (evaluation f W hk) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact hk.le

include hf in
lemma evaluation_mem (n : ℕ) (b : WeierstrassProjModel.projModelGradingCR W.toProjective n) :
    evaluation f W hk b ∈ 𝓐 (3*n) := by
  obtain ⟨p,hp,hpb⟩ := (mem_quotGradingSubmodule_iff _ _).mp b.2
  rw [← hpb,evaluation_mk]
  exact GradedEvaluation.aeval_mem_grade 𝓐 3 f hf ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)

def degreeMap (n : ℕ) : WeierstrassProjModel.projModelGradingCR W.toProjective n →ₗ[R] 𝓐 (3*n) where
  toFun b := ⟨evaluation f W hk b,evaluation_mem 𝓐 f hf W hk n b⟩
  map_add' b c := Subtype.ext (map_add _ _ _)
  map_smul' r b := Subtype.ext ((evaluation f W hk).toLinearMap.map_smul r b)

lemma degreeMap_injective (n : ℕ) : Function.Injective (degreeMap 𝓐 f hf W hk n) := by
  intro b c h
  apply Subtype.ext
  apply evaluation_injective f W hk
  exact congrArg Subtype.val h

lemma degreeMap_surjective
    (hlift : ∀ n (a : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
      p.IsHomogeneous n ∧ MvPolynomial.aeval f p=(a:A)) (n : ℕ) :
    Function.Surjective (degreeMap 𝓐 f hf W hk n) := by
  intro a
  obtain ⟨p,hp,hpa⟩ := hlift n a
  refine ⟨⟨Ideal.Quotient.mk _ p,mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hp)⟩,?_⟩
  exact Subtype.ext hpa

def degreeEquiv
    (hlift : ∀ n (a : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
      p.IsHomogeneous n ∧ MvPolynomial.aeval f p=(a:A)) (n : ℕ) :
    WeierstrassProjModel.projModelGradingCR W.toProjective n ≃ₗ[R] 𝓐 (3*n) :=
  LinearEquiv.ofBijective (degreeMap 𝓐 f hf W hk n)
    ⟨degreeMap_injective 𝓐 f hf W hk n,degreeMap_surjective 𝓐 f hf W hk hlift n⟩

#print axioms degreeEquiv
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneQuotient
end


/-! Cubic quotient and affine comparison: AffineFramesProbe development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open Filtration SectionFrames
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
lemma normalized_affine_cover (m : ℕ) (hm : 1 ≤ m)
    (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    ∃ U V : Q.target.Opens,
      IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V=⊤ ∧
      (∀ q : Q.target, q ∈ U ↔ q ∉ Set.range Q.zero) ∧
      (∀ q : Q.target, q ∈ V ↔ q ∉ (Scheme.Modules.zeroSchemeIdeal (sectionHom s)).support) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
  letI : GeometricallyIntegral Q.structureMap := Q.geometrically_integral
  obtain ⟨δ⟩ := invPower_tensorPower Q.zero.ker Q.zero_ideal_invertible m
  let t : 𝟙_ Q.target.Modules ⟶ (Q.zero.ker^m).invModule := sectionHom s ≫ δ.inv
  have htzero : Scheme.Modules.zeroSchemeIdeal t = Scheme.Modules.zeroSchemeIdeal (sectionHom s) :=
    Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (sectionHom s) δ.inv
  have hd := disjoint_range_zeroSchemeIdeal_of_pullback_frame Q.zero
    (Scheme.Modules.IsInvertible.tensorPow Q.zero_ideal_invertible.isInvertible_invModule m)
    (sectionHom s) (by rw [sectionHom_app_one]; exact normalized_pullback_frame R Q m s hs)
  have ht : ∀ q ∈ Set.range Q.zero, q ∉ (Scheme.Modules.zeroSchemeIdeal t).support := by
    rw [htzero]
    exact fun q hq => fun hh => Set.disjoint_left.mp hd hq hh
  let ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) Q.structureMap := ⟨Q.zero,Q.zero_over⟩
  obtain ⟨U,V,hcov,hU,hV,f,g,hf,hg,hfg,_⟩ :=
    SmoothProperCurve.exists_twoChart_of_section_invModule_global R Q.structureMap ε m hm t ht
  have hεV : ∀ q ∈ Set.range ε.val.base, q ∈ V := by
    intro q hq
    exact (hV q).mpr (ht q hq)
  obtain ⟨htrU,htrV⟩ := SmoothProperCurve.transcendental_app_of_twoChart_of_section_mem_global
    R Q.structureMap ε U V hcov hU hεV f g hf hg hfg
  exact ⟨U,V,(Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart Q.structureMap U V f g hcov hg hfg htrU).1,
    (Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right Q.structureMap U V f g hcov hf hfg htrV).1,
    hcov,hU,by simpa only [htzero] using hV⟩

#print axioms normalized_affine_cover
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
end


/-! Scheme presentation: PointedCoordinates checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open Filtration GeometricCubic
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m, ⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma plane_restriction_at_identity (z : 𝓐 1) (x : 𝓐 2) (y : 𝓐 3)
    (hz : ι 1 z=originDegreeOne R Q)
    (hy : powerRestriction R Q 3 (ι 3 y)=unitPower R 3) :
    (fun i : Fin 3 => powerRestriction R Q 3
      (![ι 3 (planeX R A 𝓐 z x),ι 3 y,ι 3 (planeZ R A 𝓐 z)] i)) =
      ![0,unitPower R 3,0] := by
  have hzlead : gradedLead R Q A 𝓐 ι hRing 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hxz : powerRestriction R Q 3 (ι 3 (planeX R A 𝓐 z x))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    change gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(x:A)*z,SetLike.mul_mem_graded x.2 z.2⟩=0
    rw [gradedLead_mul R Q A 𝓐 ι hRing 2 1 x z,hzlead,mul_zero]
  have hzzz : powerRestriction R Q 3 (ι 3 (planeZ R A 𝓐 z))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
    change gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩=0
    rw [gradedLead_mul R Q A 𝓐 ι hRing 2 1 zz z,hzlead,mul_zero]
  funext i
  fin_cases i
  · exact hxz
  · exact hy
  · exact hzzz

#print axioms plane_restriction_at_identity
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
end


/-! Scheme presentation: TensorGrouping checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.TensorGrouping
open Scheme.Modules
variable {X : Scheme.{u}} (L : X.Modules)

def grouping (d : ℕ) : (n : ℕ) → L.tensorPow (d*n) ≅ (L.tensorPow d).tensorPow n
  | 0 => Iso.refl _
  | n+1 => (tensorPowAdd L (d*n) d).symm ≪≫ ((grouping d n) ⊗ᵢ Iso.refl _)

lemma tensorPowAdd_assoc (a b c : ℕ) :
    ((tensorPowAdd L a b).hom ▷ L.tensorPow c) ≫
      (tensorPowAdd L (a+b) c).hom ≫ eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c)) =
      (α_ _ _ _).hom ≫ (L.tensorPow a ◁ (tensorPowAdd L b c).hom) ≫
        (tensorPowAdd L a (b+c)).hom := by
  induction c with
  | zero =>
    simp only [tensorPowAdd,Nat.add_zero,eqToHom_refl,Category.comp_id]
    change ((tensorPowAdd L a b).hom ▷ 𝟙_ X.Modules) ≫ (ρ_ _).hom =
      (α_ _ _ _).hom ≫ (L.tensorPow a ◁ (ρ_ _).hom) ≫ (tensorPowAdd L a b).hom
    monoidal
  | succ c ih =>
    have hc : eqToHom (congrArg L.tensorPow (Nat.add_assoc a b (c+1))) =
        eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c)) ▷ L := by
      rw [eqToHom_whiskerRight]
    simp only [tensorPowAdd,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom]
    rw [hc]
    change ((tensorPowAdd L a b).hom ▷ (L.tensorPow c ⊗ L)) ≫
      ((α_ _ _ _).inv ≫ (tensorPowAdd L (a+b) c).hom ▷ L) ≫
        eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c)) ▷ L = _
    calc
      _ = (α_ (L.tensorPow a ⊗ L.tensorPow b) (L.tensorPow c) L).inv ≫
          (((tensorPowAdd L a b).hom ▷ L.tensorPow c ≫ (tensorPowAdd L (a+b) c).hom ≫
            eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c))) ▷ L) := by monoidal
      _ = _ := by rw [ih]; monoidal

@[reassoc]
lemma tensorPowAdd_split (a b c : ℕ) :
    (tensorPowAdd L a (b+c)).hom ≫
      eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c).symm) ≫
      (tensorPowAdd L (a+b) c).inv =
      (L.tensorPow a ◁ (tensorPowAdd L b c).inv) ≫ (α_ _ _ _).inv ≫
        (tensorPowAdd L a b).hom ▷ L.tensorPow c := by
  have h := congrArg (fun k => (L.tensorPow a ◁ (tensorPowAdd L b c).inv) ≫
    (α_ _ _ _).inv ≫ k ≫ eqToHom (congrArg L.tensorPow (Nat.add_assoc a b c).symm) ≫
      (tensorPowAdd L (a+b) c).inv) (tensorPowAdd_assoc L a b c)
  simpa only [Category.assoc,eqToHom_trans_assoc,eqToHom_trans,eqToHom_refl,Category.id_comp,
    Iso.hom_inv_id_assoc,Iso.inv_hom_id_assoc,← whiskerLeft_comp_assoc,
    Iso.inv_hom_id,Iso.hom_inv_id,whiskerLeft_id,Category.comp_id] using h.symm

@[reassoc]
lemma add_inv_transport {a b : ℕ} (e : a=b) (c : ℕ) :
    eqToHom (congrArg (fun k => L.tensorPow (k+c)) e) ≫ (tensorPowAdd L b c).inv =
      (tensorPowAdd L a c).inv ≫ eqToHom (congrArg L.tensorPow e) ▷ L.tensorPow c := by
  subst b
  simp

lemma grouping_mul (d m n : ℕ) :
    (tensorPowAdd L (d*m) (d*n)).hom ≫
      eqToHom (congrArg L.tensorPow (Nat.mul_add d m n).symm) ≫ (grouping L d (m+n)).hom =
      ((grouping L d m).hom ⊗ₘ (grouping L d n).hom) ≫
        (tensorPowAdd (L.tensorPow d) m n).hom := by
  induction n with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero,grouping,Iso.refl_hom,eqToHom_refl,
      tensorPowAdd,Category.id_comp]
    change (ρ_ _).hom ≫ (grouping L d m).hom =
      ((grouping L d m).hom ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ _).hom
    monoidal
  | succ n ih =>
    change (tensorPowAdd L (d*m) (d*n+d)).hom ≫
      eqToHom (congrArg L.tensorPow (Nat.mul_add d m (n+1)).symm) ≫
      ((tensorPowAdd L (d*(m+n)) d).inv ≫ ((grouping L d (m+n)).hom ⊗ₘ 𝟙 _)) =
      ((grouping L d m).hom ⊗ₘ
        ((tensorPowAdd L (d*n) d).inv ≫ ((grouping L d n).hom ⊗ₘ 𝟙 _))) ≫
        ((α_ _ _ _).inv ≫ (tensorPowAdd (L.tensorPow d) m n).hom ▷ _)
    have hc : eqToHom (congrArg L.tensorPow (Nat.mul_add d m (n+1)).symm) =
        eqToHom (congrArg L.tensorPow (Nat.add_assoc (d*m) (d*n) d).symm) ≫
          eqToHom (congrArg (fun k => L.tensorPow (k+d)) (Nat.mul_add d m n).symm) := by
      rw [eqToHom_trans]
    rw [hc]
    simp only [Category.assoc]
    rw [add_inv_transport_assoc L (Nat.mul_add d m n).symm d]
    rw [tensorPowAdd_split_assoc]
    calc
      _ = (L.tensorPow (d*m) ◁ (tensorPowAdd L (d*n) d).inv) ≫ (α_ _ _ _).inv ≫
          (((tensorPowAdd L (d*m) (d*n)).hom ≫
            eqToHom (congrArg L.tensorPow (Nat.mul_add d m n).symm) ≫
              (grouping L d (m+n)).hom) ▷ L.tensorPow d) := by
        simp only [comp_whiskerRight,tensorHom_id,Category.assoc]
      _ = _ := by
        rw [ih]
        simp only [MonoidalCategory.tensorHom_def,whiskerLeft_comp,comp_whiskerRight,Category.assoc]
        rw [← associator_inv_naturality_left_assoc,whisker_exchange_assoc,
          ← associator_inv_naturality_middle_assoc]
        simp only [whiskerLeft_id,Category.id_comp]

#print axioms tensorPowAdd_assoc
#print axioms grouping_mul
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.TensorGrouping
end


/-! Scheme presentation: PlaneSectionRing checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneSectionRing
open Scheme.Modules PlaneQuotient TensorGrouping
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (L : X.Modules)
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (ι : ∀ n : ℕ, 𝓐 n → Γ(L.tensorPow n,⊤))
variable (hRing : GradedOAlgebra.IsSectionRing c L A 𝓐 ι)

lemma section_transport {m n : ℕ} (h : m=n) (a : 𝓐 m) :
    (eqToHom (congrArg L.tensorPow h)).app ⊤ (ι m a) = ι n ⟨(a:A),h ▸ a.2⟩ := by
  subst n
  rfl

lemma tensorHom_sections {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (a : Γ(M,⊤)) (b : Γ(N,⊤)) :
    (f ⊗ₘ g).app ⊤ (tensorSections a b) = tensorSections (f.app ⊤ a) (g.app ⊤ b) := by
  rw [MonoidalCategory.tensorHom_def]
  change (M' ◁ g).app ⊤ ((f ▷ N).app ⊤ (tensorSections a b)) = _
  rw [whiskerRight_app_tensorSections,whiskerLeft_app_tensorSections]

include hRing in
lemma grouped_mul (d m n : ℕ) (a : 𝓐 (d*m)) (b : 𝓐 (d*n)) :
    (grouping L d (m+n)).hom.app ⊤
      (ι (d*(m+n)) ⟨(a:A)*b,by simpa only [Nat.mul_add] using SetLike.mul_mem_graded a.2 b.2⟩) =
      (tensorPowAdd (L.tensorPow d) m n).hom.app ⊤
        (tensorSections ((grouping L d m).hom.app ⊤ (ι (d*m) a))
          ((grouping L d n).hom.app ⊤ (ι (d*n) b))) := by
  have he := congrArg (fun k => k.app ⊤ (tensorSections (ι (d*m) a) (ι (d*n) b)))
    (grouping_mul L d m n)
  change (grouping L d (m+n)).hom.app ⊤
      ((eqToHom (congrArg L.tensorPow (Nat.mul_add d m n).symm)).app ⊤
        ((tensorPowAdd L (d*m) (d*n)).hom.app ⊤ (tensorSections (ι (d*m) a) (ι (d*n) b)))) =
    (tensorPowAdd (L.tensorPow d) m n).hom.app ⊤
      (((grouping L d m).hom ⊗ₘ (grouping L d n).hom).app ⊤
        (tensorSections (ι (d*m) a) (ι (d*n) b))) at he
  rw [← hRing.map_mul,section_transport L 𝓐 ι (Nat.mul_add d m n).symm,tensorHom_sections] at he
  exact he

variable (f : Fin 3 → A) (hf : ∀ i, f i ∈ 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval f).toRingHom=Ideal.span {W.toProjective.polynomial})
variable (hlift : ∀ n (a : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
  p.IsHomogeneous n ∧ MvPolynomial.aeval f p=(a:A))

def sections (n : ℕ) (a : WeierstrassProjModel.projModelGradingCR W.toProjective n) :
    Γ((L.tensorPow 3).tensorPow n,⊤) :=
  (grouping L 3 n).hom.app ⊤ (ι (3*n) (degreeMap 𝓐 f hf W hk n a))

include hRing hlift in
lemma isSectionRing : GradedOAlgebra.IsSectionRing c (L.tensorPow 3)
    (WeierstrassProjModel.ProjModelRingCR W.toProjective)
    (WeierstrassProjModel.projModelGradingCR W.toProjective)
    (sections L 𝓐 ι f hf W hk) := by
  constructor
  · intro n
    have he : Function.Bijective ((grouping L 3 n).hom.app ⊤) := by
      constructor
      · intro a b h
        have hh := congrArg ((grouping L 3 n).inv.app ⊤) h
        change ((grouping L 3 n).hom ≫ (grouping L 3 n).inv).app ⊤ a =
          ((grouping L 3 n).hom ≫ (grouping L 3 n).inv).app ⊤ b at hh
        rw [Iso.hom_inv_id] at hh
        exact hh
      · intro a
        refine ⟨(grouping L 3 n).inv.app ⊤ a,?_⟩
        change ((grouping L 3 n).inv ≫ (grouping L 3 n).hom).app ⊤ a=a
        rw [Iso.inv_hom_id]
        rfl
    exact he.comp ((hRing.bijective _).comp
      ⟨degreeMap_injective 𝓐 f hf W hk n,degreeMap_surjective 𝓐 f hf W hk hlift n⟩)
  · intro n a b
    simp only [sections,map_add,hRing.map_add]
  · intro n r a
    change (grouping L 3 n).hom.app ⊤ (ι (3*n) (degreeMap 𝓐 f hf W hk n (r • a))) = _
    rw [_root_.map_smul,hRing.map_smul,Scheme.Modules.Hom.app_smul]
    rfl
  · change ι 0 (degreeMap 𝓐 f hf W hk 0 ⟨1,SetLike.GradedOne.one_mem⟩) = _
    have he : degreeMap 𝓐 f hf W hk 0 ⟨1,SetLike.GradedOne.one_mem⟩ =
        (⟨1,SetLike.GradedOne.one_mem⟩ : 𝓐 0) := Subtype.ext (map_one _)
    rw [he,hRing.map_one]
  · intro m n a b
    have he : degreeMap 𝓐 f hf W hk (m+n)
        ⟨(a:WeierstrassProjModel.ProjModelRingCR W.toProjective)*b,SetLike.mul_mem_graded a.2 b.2⟩ =
        (⟨((degreeMap 𝓐 f hf W hk m a):A)*((degreeMap 𝓐 f hf W hk n b):A),
          by simpa only [Nat.mul_add] using (SetLike.mul_mem_graded
            (degreeMap 𝓐 f hf W hk m a).2 (degreeMap 𝓐 f hf W hk n b).2)⟩ : 𝓐 (3*(m+n))) := by
      apply Subtype.ext
      exact map_mul (evaluation f W hk) _ _
    unfold sections
    rw [he]
    exact grouped_mul c L 𝓐 ι hRing 3 m n _ _

#print axioms isSectionRing
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PlaneSectionRing
end


/-! Scheme presentation: CanonicalFrameCover checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules HomogeneousLocalization Opposite
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj.K10F2
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
theorem exists_canonical_of_frame_cover
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (N : ℕ) (τ : Fin (N+1) → 𝓡 1) (V : Fin (N+1) → X.Opens)
    (hV : (⨆ i, V i)=⊤) (hτV : ∀ i, IsFrameOn (ι 1 (τ i)) (V i)) :
    ∃ θ : X ⟶ Proj 𝓡, AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ := by
  classical

  have dh := fun i =>
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq f L R 𝓡 ι hR (τ i) (V i) (hτV i)
  choose φ hφa hφb hφc using dh

  have hφτ : ∀ i, φ i (τ i) = 1 := by
    intro i
    have h1 := hφc i 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hinj := ((hφb i 1) (le_top : V i ≤ ⊤) le_rfl).1
    have h2 : φ i ((τ i : R) ^ 1) = 1 := hinj (h1.trans (one_smul _ _).symm)
    simpa using h2

  have hunit : ∀ i j, IsUnit (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i))) := by
    intro i j
    have hc := hφc j 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hc' := congrArg ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
      Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at hc'
    have hfr : IsFrameOn ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
        (ι (1 • 1) ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩)) (V i ⊓ V j) :=
      ((hφb i 1).mono inf_le_left).map (homOfLE (le_top : V i ⊓ V j ≤ ⊤))
    rw [← hc'] at hfr
    have key := AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
      (ι (1 • 1) ⟨(τ j : R) ^ 1, SetLike.pow_mem_graded 1 (τ j).2⟩) (hφb j 1)
      (le_top : V i ⊓ V j ≤ ⊤) inf_le_right _ hfr
    simpa using key

  have hkey : ∀ i j (k : ℕ) (s : R) (hs : s ∈ 𝓡 (k • 1)),
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) *
        X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i)) ^ k =
      X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) := by
    intro i j k s hs
    apply ((hφb j k) (le_top : V i ⊓ V j ≤ ⊤) inf_le_right).1
    simp only

    have cj : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) (hφc j k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have ci : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op) (hφc i k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have cjs : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := cj ⟨s, hs⟩
    have cjτ : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j ((τ i : R) ^ k)) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) :=
      cj ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩
    have cis : X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := ci ⟨s, hs⟩
    rw [cjs, mul_smul, ← map_pow, ← map_pow, cjτ, cis]

  let θV : ∀ i, ((V i : X.Opens) : Scheme.{u}) ⟶ Proj 𝓡 := fun i => θOf R 𝓡 (V i) (φ i) (τ i) (hφτ i)
  have hcompat : ∀ i j, X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i =
      X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j := by
    intro i j
    apply AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen 𝓡
    intro w
    have hpa : (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V i) (φ i) (τ i) (hφτ i) _ rfl one_pos (τ i), gOf_apply, hφτ i,
        map_one, Scheme.basicOpen_one, Scheme.Hom.preimage_top]
    have hpb : (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V j) (φ j) (τ j) (hφτ j) _ rfl one_pos (τ i),
        Scheme.preimage_basicOpen_top]
      apply Scheme.basicOpen_of_isUnit
      rw [gOf_apply, homOfLE_appTop_topIso_inv _ ((homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op ≫
        (homOfLE ((V i ⊓ V j).ι_image_le ⊤)).op), Functor.map_comp, CategoryTheory.comp_apply]
      exact (hunit i j).map _
    refine ⟨1, (τ i : R), one_pos, (τ i).2, hpa.trans hpb.symm, by rw [hpa]; trivial, ?_⟩
    intro x
    obtain ⟨k, s, hs, rfl⟩ := Away.mk_surjective 𝓡 (τ i).2 x

    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) (θV i)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl le_rfl]
    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) (θV j)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
        (hpa.trans hpb.symm).le]
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, Scheme.homOfLE_appLE, Scheme.homOfLE_appLE]
    have hΩle : (V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) ≤
        V i ⊓ V j := (V i ⊓ V j).ι_image_le _
    have key2 : ∀ (m₁ : op ((V i).ι ''ᵁ ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))))
        (m₂ : op ((V j).ι ''ᵁ ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)))),
        X.presheaf.map m₁ ((θV i).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) =
        X.presheaf.map m₂ ((θV j).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) := by
      intro m₁ m₂
      have vi := θOf_value (V i) (φ i) (τ i) (hφτ i) (θV i) rfl one_pos (τ i) k s hs
        ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₁ (homOfLE (hΩle.trans inf_le_left)).op
      rw [hφτ i, map_one, one_pow, mul_one] at vi
      have vj := θOf_value (V j) (φ j) (τ j) (hφτ j) (θV j) rfl one_pos (τ i) k s hs
        ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₂ (homOfLE (hΩle.trans inf_le_right)).op
      have hk := congrArg (X.presheaf.map (homOfLE hΩle).op) (hkey i j k s hs)
      rw [map_mul, map_pow, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_left)).op,
        Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op,
        ← vi, ← vj] at hk
      have hu : IsUnit (X.presheaf.map (homOfLE (hΩle.trans inf_le_right)).op (φ j (τ i)) ^ k) := by
        have := ((hunit i j).map (ConcreteCategory.hom (X.presheaf.map (homOfLE hΩle).op))).pow k
        rwa [Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op] at this
      exact hu.mul_left_inj.mp hk
    exact key2 _ _

  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover V hV
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ θV i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ θV j := by
    intro i j
    have P := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ θV i = pullback.snd (V i).ι (V j).ι ≫ θV j
    rw [← cancel_epi P.isoPullback.hom, P.isoPullback_hom_fst_assoc, P.isoPullback_hom_snd_assoc]
    exact hcompat i j
  let θ : X ⟶ Proj 𝓡 := 𝒰.glueMorphisms θV hglue
  have hθV : ∀ i, (V i).ι ≫ θ = θV i := fun i => 𝒰.ι_glueMorphisms θV hglue i

  have hVW : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) (i),
      V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = X.basicOpen (φ i σ) := by
    intro n hn σ i
    rw [← image_θOf_preimage (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ, Scheme.Hom.comp_preimage,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hcovσ : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n),
      θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⨆ i, X.basicOpen (φ i σ) := by
    intro n hn σ
    calc θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = (⨆ i, V i) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by rw [hV, top_inf_eq]
      _ = ⨆ i, (V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) := iSup_inf_eq _ _
      _ = ⨆ i, X.basicOpen (φ i σ) := by simp_rw [hVW hn σ]
  refine ⟨θ, ⟨?_, ?_, ?_⟩⟩
  ·
    apply 𝒰.hom_ext
    intro i
    change (V i).ι ≫ θ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [← Category.assoc, hθV i]
    change Proj.fromOfGlobalSections 𝓡 (gOf R (V i) (φ i)) _ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
    have hr : (V i).ι ≫ f = ((V i : X.Opens) : Scheme.{u}).toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ((V i).ι ≫ f).appTop) := by
      rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [hr]
    congr 2
    apply CommRingCat.hom_ext
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Scheme.Hom.comp_appTop]
    have ha0 : algebraMap S R a ∈ 𝓡 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ a SetLike.GradedOne.one_mem
    have e1 : (GradedRing.projZeroRingHom' 𝓡) (algebraMap S R a) = ⟨algebraMap S R a, ha0⟩ :=
      GradedRing.projZeroRingHom'_apply_coe 𝓡 ⟨algebraMap S R a, ha0⟩
    rw [e1]
    change gOf R (V i) (φ i) (algebraMap S R a) = (V i).ι.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a))
    rw [gOf_apply, hφa i a, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact Xmap_comp _ _ _ _
  ·
    intro n hn σ
    rw [hcovσ hn σ]
    apply AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
    intro i
    have hn1 : n = n • 1 := by simp
    rw [isFrameOn_transport L 𝓡 ι hn1 σ]
    have hBV : X.basicOpen (φ i σ) ≤ V i := X.basicOpen_le _
    apply isFrameOn_of_restrict _ (hBV.trans le_top)
    have hc := hφc i n ⟨(σ : R), hn1 ▸ σ.2⟩
    have hc' := congrArg ((L.tensorPow (n • 1)).presheaf.map (homOfLE hBV).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op, Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op] at hc'
    rw [← hc']
    exact isFrameOn_smul_of_isUnit _ (hφb i n) le_top hBV _ (RingedSpace.isUnit_res_basicOpen _ (φ i σ))
  ·
    intro n hn σ k s
    have hkn : k • n = (k • n) • 1 := by simp
    apply sections_ext V hV
    intro i
    simp only [Scheme.Modules.map_smul]
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op]

    have hWle : V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ V i := inf_le_left
    have cσ := hφc i (k • n) ⟨((⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)) : R),
      hkn ▸ (⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)).2⟩
    have cs := hφc i (k • n) ⟨(s : R), hkn ▸ s.2⟩
    rw [smul_eq_transport L 𝓡 ι hkn ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ s]
    have cσ' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cσ
    have cs' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cs
    simp only [Scheme.Modules.map_smul] at cσ' cs'
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op] at cσ' cs'
    rw [← cσ', ← cs', smul_smul]
    congr 1

    have v := θOf_value (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ k (s : R) s.2
      (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
      (W₀ := V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
      (homOfLE (by rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op (homOfLE hWle).op
    rw [map_pow, map_pow, ← v]
    congr 1
    rw [← Scheme.Hom.appLE_comp_appLE ((V i).ι) θ (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
        (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl le_rfl, CategoryTheory.comp_apply, Scheme.Opens.ι_appLE]
    exact (Xmap_comp _ _ _ _).symm

#print axioms exists_canonical_of_frame_cover
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
end


/-! Scheme presentation: CanonicalAffineIso checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules HomogeneousLocalization Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section.F2SurjSol in
theorem exists_local_fraction
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (N : ℕ) (τ : Fin (N+1) → 𝓡 1)
    (hcov : (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))=⊤)
    (haff : ∀ i, IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)))
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    ∃ (k : ℕ) (t : 𝓡 (k • n)),
      g • (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) =
        (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) t) := by
  have C : ∀ i, ChartData L R 𝓡 ι (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) (τ i) :=
    fun i => (nonempty_chartData f L R 𝓡 ι hR _ (τ i) (hθ.isFrameOn 1 one_pos (τ i))).some
  have hD : ∀ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) =
      X.basicOpen ((C i).φ (σ : R)) := fun i => preimage_inf_eq_basicOpen hθ (C i) hn σ
  have hVV : ∀ i j, IsCompact ((θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ j : R) :
      X.Opens) : Set X) := by
    intro i j
    rw [preimage_inf_preimage_eq_basicOpen hθ (C i) (τ j)]
    exact ((haff i).basicOpen _).isCompact
  obtain ⟨K, d, hd, t, h⟩ := main hR hcov haff C hVV n σ _ hD g
  subst hd
  exact ⟨K, t, h⟩

#print axioms exists_local_fraction
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
end


/-! Scheme presentation: CanonicalLocalIso checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules HomogeneousLocalization Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
theorem local_iso_of_affine_cover
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (N : ℕ) (τs : Fin (N+1) → 𝓡 1)
    (hcov : (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τs i : R))=⊤)
    (haffs : ∀ i, IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τs i : R)))
    (m : ℕ) (hm : 0 < m) (τ : 𝓡 m) (haff : IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R))) :
    IsIso (θ ∣_ Proj.basicOpen 𝓡 (τ : R)) := by
  classical

  haveI : IsAffine (Proj.basicOpen 𝓡 (τ : R)) := Proj.isAffineOpen_basicOpen 𝓡 (τ : R) τ.2 hm
  haveI : IsAffine (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := haff

  haveI hι : IsIso (Proj.awayToSection 𝓡 (τ : R)) := by
    rw [← Proj.basicOpenIsoAway_hom 𝓡 (τ : R) τ.2 hm]; infer_instance

  have hbij : Function.Bijective (Proj.awayToSection 𝓡 (τ : R) ≫
      θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl).hom := by

    have aux : ∀ (n k : ℕ) (σ : 𝓡 n), (σ : R) = (τ : R) ^ k → n = k • m →
        Function.Injective fun g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) =>
          g • ((L.tensorPow n).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op (ι n σ) :
            Γ(L.tensorPow n, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R))) := by
      intro n k σ hσ hn
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hn0 : n = 0 := by rw [hn, zero_smul]
        subst hn0
        have hσ1 : σ = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext (by rw [hσ, pow_zero])
        subst hσ1
        rw [hR.map_one]
        change Function.Injective fun g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) =>
          g • ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
            (Scheme.Modules.unitSection ⊤) : Γ((𝟙_ X.Modules : X.Modules), θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)))
        rw [Scheme.Modules.map_unitSection]
        exact Scheme.Modules.smul_unitSection_bijective.1
      · have hnpos : 0 < n := by rw [hn, smul_eq_mul]; exact Nat.mul_pos hk hm
        have hfr := hθ.isFrameOn n hnpos σ
        have hle : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by
          rw [hσ, Proj.basicOpen_pow 𝓡 (τ : R) k hk]
        exact (hfr.bijective le_top hle).1

    have hρ : ∀ (k : ℕ) (s : 𝓡 (k • m)),
        ((Proj.awayToSection 𝓡 (τ : R) ≫
            θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl).hom
              (Away.mk 𝓡 τ.2 k (s : R) s.2)) •
          (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
            (ι (k • m) ⟨(τ : R) ^ k, SetLike.pow_mem_graded k τ.2⟩) =
        (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op (ι (k • m) s) :=
      fun k s => hθ.appLE_awayToSection_smul m hm τ k s
    constructor
    ·
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨k, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓡 τ.2 z
      have h0 : (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
          (ι (k • m) ⟨s, hs⟩) = 0 := by
        rw [← hρ k ⟨s, hs⟩, hz, zero_smul]
      obtain ⟨j, hj⟩ :=
        P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.InjSol.main_of_charts
          hR hθ _ hcov (fun i => (haffs i).isCompact) τs
          (fun i => hθ.isFrameOn 1 one_pos (τs i)) hm τ ⟨s, hs⟩ h0
      apply HomogeneousLocalization.val_injective _
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
        IsLocalization.mk'_eq_zero_iff]
      exact ⟨⟨(τ : R) ^ j, j, rfl⟩, hj⟩
    ·
      intro g
      obtain ⟨k, t, hkt⟩ :=
        exists_local_fraction f L R 𝓡 ι hR θ hθ N τs hcov haffs m hm τ g
      refine ⟨Away.mk 𝓡 τ.2 k (t : R) t.2, ?_⟩
      apply aux (k • m) k ⟨(τ : R) ^ k, SetLike.pow_mem_graded k τ.2⟩ rfl rfl
      show _ • _ = _ • _
      rw [hρ k t, hkt]
  have happLE : IsIso (θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl) := by
    haveI : IsIso (Proj.awayToSection 𝓡 (τ : R) ≫
        θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact IsIso.of_isIso_comp_left (Proj.awayToSection 𝓡 (τ : R)) _

  have htop : IsIso ((θ ∣_ Proj.basicOpen 𝓡 (τ : R)).appTop) := by
    have main : ∀ (U' : (Proj 𝓡).Opens) (V' : X.Opens) (hU' : U' = Proj.basicOpen 𝓡 (τ : R))
        (hV' : V' = θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) (h : V' ≤ θ ⁻¹ᵁ U'), IsIso (θ.appLE U' V' h) := by
      rintro U' V' rfl rfl h
      exact happLE
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    exact main _ _ (Scheme.Opens.ι_image_top _) (Scheme.Opens.ι_image_top _) _
  have key : (MorphismProperty.isomorphisms Scheme) (θ ∣_ Proj.basicOpen 𝓡 (τ : R)) :=
    (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr ⟨haff, htop⟩
  exact (MorphismProperty.isomorphisms.iff _).mp key

#print axioms local_iso_of_affine_cover
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
end


/-! Scheme presentation: FrameLocus checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
lemma frame_disjoint_support {X : Scheme.{u}} {M : X.Modules}
    (hM : IsInvertible M) (s : Γ(M,⊤)) (U : X.Opens) (hs : IsFrameOn s U) :
    Disjoint (U : Set X) ((zeroSchemeIdeal (sectionHom s)).support : Set X) := by
  have hpre : U.ι ⁻¹ᵁ U=⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange U.ι
  have hf := (bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff M U).2
    (M.presheaf.map (homOfLE (le_top : U≤⊤)).op s)
  have hf' := hf.mpr (hs.map (homOfLE (le_top : U≤⊤)))
  rw [← map_pullbackLocalSection] at hf'
  have hf'' := P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj.K10F2.isFrameOn_of_restrict
    (pullbackLocalSection U.ι s) (show U.ι ⁻¹ᵁ U ≤ U.ι ⁻¹ᵁ ⊤ from le_top) (hf'.mono le_top)
  rw [hpre] at hf''
  have hd := disjoint_range_zeroSchemeIdeal_of_pullback_frame U.ι hM (sectionHom s) (by
    rw [sectionHom_app_one]
    exact hf'')
  simpa only [Scheme.Opens.range_ι] using hd

#print axioms frame_disjoint_support
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
end


/-! Scheme presentation: CanonicalLocus checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
open SectionFrames
variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of S)) (L : X.Modules)
variable (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
variable (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n,⊤))
variable (hR : GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
variable (θ : X ⟶ Proj 𝓡) (hθ : GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)

include hR hθ in
lemma frame_le_preimage (τ : 𝓡 1) (V : X.Opens) (hτ : IsFrameOn (ι 1 τ) V) :
    V ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ:R) := by
  let φ := P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol.φ hR τ V hτ
  have hφ : φ (τ:R)=1 := by
    have he := P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol.φ_coe hR τ V hτ 1 τ
    rw [he]
    symm
    apply P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol.eq_ψfun
    simp only [one_smul]
    have ht : P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol.τpow τ 1=τ := Subtype.ext (pow_one _)
    rw [ht]
  have hh := P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.InjSol.basicOpen_φ_le
    hR τ V hτ hθ one_pos τ
  change X.basicOpen (φ (τ:R)) ≤ _ at hh
  rwa [hφ,Scheme.basicOpen_one] at hh

include hR hθ in
lemma preimage_eq_frame_locus (hL : IsInvertible (L.tensorPow 1)) (τ : 𝓡 1) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ:R) = (zeroSchemeIdeal (sectionHom (ι 1 τ))).support.compl := by
  apply le_antisymm
  · intro x hx
    exact fun hh => Set.disjoint_left.mp
      (frame_disjoint_support hL (ι 1 τ) _ (hθ.isFrameOn 1 one_pos τ)) hx hh
  · apply frame_le_preimage f L 𝓡 ι hR θ hθ τ
    have hh := hL.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal (sectionHom (ι 1 τ))
      (zeroSchemeIdeal (sectionHom (ι 1 τ))).support.compl
      (Set.disjoint_left.mpr (fun _ ha hb => ha hb))
    change IsFrameOn ((sectionHom (ι 1 τ)).app ⊤ (unitSection ⊤)) _ at hh
    rwa [sectionHom_app_one] at hh

#print axioms preimage_eq_frame_locus
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CanonicalMap
end


/-! Scheme presentation: CubicCanonicalMap checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
open HomogeneousIdealQuotientGrading
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
open Scheme.Modules PlaneQuotient TensorGrouping PlaneSectionRing
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (L : X.Modules)
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (ι : ∀ n : ℕ, 𝓐 n → Γ(L.tensorPow n,⊤))
variable (hRing : GradedOAlgebra.IsSectionRing c L A 𝓐 ι)
variable (a : Fin 3 → 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial})
variable (hlift : ∀ n (b : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
  p.IsHomogeneous n ∧ MvPolynomial.aeval (fun i => (a i:A)) p=(b:A))

def coordinate (i : Fin 3) : WeierstrassProjModel.projModelGradingCR W.toProjective 1 :=
  ⟨Ideal.Quotient.mk _ (MvPolynomial.X i),mk_mem_quotGradingSubmodule _ _
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i))⟩

lemma degreeMap_coordinate (i : Fin 3) :
    degreeMap 𝓐 (fun i => (a i:A)) (fun i => (a i).2) W hk 1 (coordinate W i)=a i := by
  apply Subtype.ext
  exact MvPolynomial.aeval_X _ _

lemma coordinate_section (i : Fin 3) :
    sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk 1 (coordinate W i) =
      (grouping L 3 1).hom.app ⊤ (ι 3 (a i)) := by
  unfold sections
  rw [degreeMap_coordinate]

include hRing hlift in
lemma exists_canonical (𝔓 : ProjPresentation (L.tensorPow 3) c 2)
    (hσ : ∀ i, 𝔓.σ i=ι 3 (a i)) :
    ∃ θ : X ⟶ WeierstrassProjModel.projModelCR W.toProjective,
      GradedOAlgebra.IsCanonicalToProj c (L.tensorPow 3)
        (WeierstrassProjModel.ProjModelRingCR W.toProjective)
        (WeierstrassProjModel.projModelGradingCR W.toProjective)
        (sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk) θ := by
  let V : Fin 3 → X.Opens := fun i => 𝔓.toProj ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i)
  have hV : (⨆ i, V i)=⊤ := by
    exact 𝔓.toProj.iSup_preimage_eq_top (Proj.iSup_basicOpen_eq_top _
      (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X R 2))
  apply CanonicalMap.exists_canonical_of_frame_cover c (L.tensorPow 3)
    (WeierstrassProjModel.ProjModelRingCR W.toProjective)
    (WeierstrassProjModel.projModelGradingCR W.toProjective)
    (sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk)
    (isSectionRing c L 𝓐 ι hRing (fun i => (a i:A)) (fun i => (a i).2) W hk hlift)
    2 (coordinate W) V hV
  intro i
  rw [coordinate_section]
  have hf : IsFrameOn (ι 3 (a i)) (V i) := by
    rw [← hσ i]
    exact fun U _ hU => 𝔓.frame i U hU
  exact hf.map_iso (grouping L 3 1)

#print axioms exists_canonical
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
end


/-! Scheme presentation: ZeroSectionSupport checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
variable {X Y : Scheme.{u}} {M : X.Modules}
lemma zeroSchemeIdeal_zero : zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M)=⊥ := by
  apply bot_unique
  apply zeroSchemeIdeal_le
  intro U
  rw [coeffIdeal,Ideal.span_le]
  rintro _ ⟨φ,rfl⟩
  change U.1.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection (0 : 𝟙_ X.Modules ⟶ M) U.1)))=0
  have hz : restrictSection (0 : 𝟙_ X.Modules ⟶ M) U.1=0 := rfl
  rw [hz,map_zero]
  change U.1.topIso.hom (0 : Γ((U.1 : Scheme),⊤))=0
  exact map_zero _

lemma hom_eq_zero_of_top_unit (s : 𝟙_ X.Modules ⟶ M)
    (hs : s.app ⊤ (unitSection ⊤)=0) : s=0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  have hn := s.mapPresheaf.naturality (homOfLE (le_top : U≤⊤)).op
  have he := ConcreteCategory.congr_hom hn (unitSection ⊤)
  change s.app U ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U≤⊤)).op (unitSection ⊤)) =
    M.presheaf.map (homOfLE (le_top : U≤⊤)).op (s.app ⊤ (unitSection ⊤)) at he
  rw [map_unitSection,hs,map_zero] at he
  have ha : a=ofUnitSection U a • unitSection U := by
    apply ofUnitSection_injective
    change ofUnitSection U a=ofUnitSection U a*1
    rw [mul_one]
  rw [ha,Scheme.Modules.Hom.app_smul,he,smul_zero]
  rfl

lemma range_subset_support_of_pullback_zero (f : Y ⟶ X) (hM : IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M)
    (hs : pullbackLocalSection f (s.app ⊤ (unitSection ⊤))=0) :
    Set.range f ⊆ ((zeroSchemeIdeal s).support : Set X) := by
  have hz : pullbackSection f s=0 := hom_eq_zero_of_top_unit _ (by
    rw [pullbackSection_app_top]
    exact hs)
  have h := hM.comap_zeroSchemeIdeal f s
  rw [hz,zeroSchemeIdeal_zero] at h
  have hsup := congrArg Scheme.IdealSheafData.support h
  rw [Scheme.IdealSheafData.support_comap,Scheme.IdealSheafData.support_bot] at hsup
  rintro _ ⟨y,rfl⟩
  have hsup' := congrArg (fun T : TopologicalSpace.Closeds Y => (T : Set Y)) hsup
  change f ⁻¹' ((zeroSchemeIdeal s).support : Set X)=Set.univ at hsup'
  change y∈f ⁻¹' ((zeroSchemeIdeal s).support : Set X)
  rw [hsup']
  trivial

#print axioms range_subset_support_of_pullback_zero
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
end


/-! Scheme presentation: CoordinateLocus checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
lemma hom_eq_of_top_unit {X : Scheme.{u}} {M : X.Modules}
    (s t : 𝟙_ X.Modules ⟶ M) (h : s.app ⊤ (unitSection ⊤)=t.app ⊤ (unitSection ⊤)) : s=t := by
  apply sub_eq_zero.mp
  apply hom_eq_zero_of_top_unit
  change s.app ⊤ (unitSection ⊤)-t.app ⊤ (unitSection ⊤)=0
  exact sub_eq_zero.mpr h

lemma sectionHom_map {X : Scheme.{u}} {M N : X.Modules} (e : M ⟶ N) (s : Γ(M,⊤)) :
    sectionHom (e.app ⊤ s)=sectionHom s ≫ e := by
  apply hom_eq_of_top_unit
  rw [sectionHom_app_one]
  change e.app ⊤ s=e.app ⊤ ((sectionHom s).app ⊤ (unitSection ⊤))
  rw [sectionHom_app_one]
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
open SectionFrames PlaneSectionRing
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (L : X.Modules)
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (ι : ∀ n : ℕ, 𝓐 n → Γ(L.tensorPow n,⊤))
variable (hRing : GradedOAlgebra.IsSectionRing c L A 𝓐 ι)
variable (a : Fin 3 → 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial})
variable (hlift : ∀ n (b : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
  p.IsHomogeneous n ∧ MvPolynomial.aeval (fun i => (a i:A)) p=(b:A))
variable (θ : X ⟶ WeierstrassProjModel.projModelCR W.toProjective)
variable (hθ : GradedOAlgebra.IsCanonicalToProj c (L.tensorPow 3)
  (WeierstrassProjModel.ProjModelRingCR W.toProjective)
  (WeierstrassProjModel.projModelGradingCR W.toProjective)
  (sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk) θ)
include hRing hlift hθ in
lemma preimage_coordinate (hL : IsInvertible L) (i : Fin 3) :
    θ ⁻¹ᵁ Proj.basicOpen (WeierstrassProjModel.projModelGradingCR W.toProjective)
      (coordinate W i : WeierstrassProjModel.ProjModelRingCR W.toProjective) =
      (zeroSchemeIdeal (sectionHom (ι 3 (a i)))).support.compl := by
  rw [CanonicalMap.preimage_eq_frame_locus c (L.tensorPow 3) _ _
    (isSectionRing c L 𝓐 ι hRing (fun i => (a i:A)) (fun i => (a i).2) W hk hlift) θ hθ
    ((hL.tensorPow 3).tensorPow 1) (coordinate W i),coordinate_section,
    sectionHom_map,zeroSchemeIdeal_comp_eq_of_isIso]

#print axioms preimage_coordinate
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
end


/-! Scheme presentation: OriginCubicOpen checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open Filtration SectionFrames
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
lemma origin_support_eq_range : (Q.zero.ker.support : Set Q.target)=Set.range Q.zero := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  rw [Scheme.Hom.support_ker]
  exact Q.zero.isClosedEmbedding.isClosed_range.closure_eq

lemma pullback_zero_of_powerRestriction_zero (m : ℕ) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=0) : pullbackLocalSection Q.zero s=0 := by
  let e := pullbackTensorPowIso Q.zero Q.zero.ker.invModule m ≪≫ tensorPowMapIso (identityLineFrame R Q) m
  have h := congrArg (e.inv.app ⊤) hs
  change e.inv.app ⊤ (e.hom.app ⊤ (pullbackLocalSection Q.zero s))=e.inv.app ⊤ 0 at h
  change (e.hom ≫ e.inv).app ⊤ (pullbackLocalSection Q.zero s)=e.inv.app ⊤ 0 at h
  rw [e.hom_inv_id,map_zero] at h
  exact h

lemma normalized_affine_loci (m : ℕ) (hm : 1 ≤ m) (s : Γ(Q.zero.ker.invModule.tensorPow m,⊤))
    (hs : powerRestriction R Q m s=unitPower R m) :
    IsAffineOpen Q.zero.ker.support.compl ∧ IsAffineOpen (zeroSchemeIdeal (sectionHom s)).support.compl := by
  obtain ⟨U,V,hU,hV,_,heU,heV⟩ := normalized_affine_cover R Q m hm s hs
  have hUeq : U=Q.zero.ker.support.compl := by
    ext q
    change q ∈ U ↔ q ∉ (Q.zero.ker.support : Set Q.target)
    rw [origin_support_eq_range R Q]
    exact heU q
  have hVeq : V=(zeroSchemeIdeal (sectionHom s)).support.compl := by
    ext q
    exact heV q
  exact ⟨hUeq ▸ hU,hVeq ▸ hV⟩

variable (A : Type u) [CommRing A] [Algebra R A]
  (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
  (ι : ∀ m : ℕ, 𝓐 m → Γ(Q.zero.ker.invModule.tensorPow m,⊤))
  (hRing : GradedOAlgebra.IsSectionRing Q.structureMap Q.zero.ker.invModule A 𝓐 ι)
include hRing
lemma planeZ_frame_locus (z : 𝓐 1) (hz : ι 1 z=originDegreeOne R Q) :
    (zeroSchemeIdeal (sectionHom (ι 3 (planeZ R A 𝓐 z)))).support.compl=Q.zero.ker.support.compl := by
  have hzlead : GeometricCubic.gradedLead R Q A 𝓐 ι hRing 1 z=0 := by
    change leadingCoefficient R Q 1 (ι 1 z)=0
    rw [hz]
    exact (leadingCoefficient_eq_zero_iff R Q 1 _).mpr (originDegreeOne_restriction_zero R Q)
  have hzzz : powerRestriction R Q 3 (ι 3 (planeZ R A 𝓐 z))=0 := by
    apply (leadingCoefficient_eq_zero_iff R Q 3 _).mp
    let zz : 𝓐 2 := ⟨(z:A)*z,SetLike.mul_mem_graded z.2 z.2⟩
    change GeometricCubic.gradedLead R Q A 𝓐 ι hRing (2+1) ⟨(zz:A)*z,SetLike.mul_mem_graded zz.2 z.2⟩=0
    rw [GeometricCubic.gradedLead_mul R Q A 𝓐 ι hRing 2 1 zz z,hzlead,mul_zero]
  have hM := Q.zero_ideal_invertible.isInvertible_invModule.tensorPow 3
  have hsub := range_subset_support_of_pullback_zero Q.zero hM
    (sectionHom (ι 3 (planeZ R A 𝓐 z))) (by
      rw [sectionHom_app_one]
      exact pullback_zero_of_powerRestriction_zero R Q 3 _ hzzz)
  have hd := frame_disjoint_support hM (ι 3 (planeZ R A 𝓐 z)) Q.zero.ker.support.compl
    (planeZ_frame R Q A 𝓐 ι hRing z hz)
  ext q
  constructor
  · intro hq hqi
    apply hq
    exact hsub ((origin_support_eq_range R Q) ▸ hqi)
  · intro hq hqs
    exact Set.disjoint_left.mp hd hq hqs

#print axioms normalized_affine_loci
#print axioms planeZ_frame_locus
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
end


/-! Scheme presentation: CubicTwoCharts checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)
local notation "B" => WeierstrassProjModel.ProjModelRingCR W.toProjective
local notation "𝓑" => WeierstrassProjModel.projModelGradingCR W.toProjective

lemma coordinates_aeval (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval (fun i => (coordinate W i:B)) p = Ideal.Quotient.mk _ p := by
  have he : MvPolynomial.aeval (fun i => (coordinate W i:B)) = Ideal.Quotient.mkₐ R _ := by
    ext i
    exact MvPolynomial.aeval_X _ _
  rw [he]
  rfl

lemma coordinates_adjoin : Algebra.adjoin R (Set.range (fun i => (coordinate W i:B)))=⊤ := by
  rw [← MvPolynomial.aeval_range]
  apply top_unique
  intro b _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨p,coordinates_aeval R W p⟩

lemma coordinate_cover_generic {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (𝓣 : ℕ → Submodule S T) [GradedAlgebra 𝓣] (a : Fin 3 → 𝓣 1)
    (hgen : Algebra.adjoin S (Set.range (fun i => (a i:T)))=⊤) :
    (⨆ i : Fin 3,Proj.basicOpen 𝓣 (a i:T))=⊤ := by
  letI : IsScalarTower S (𝓣 0) T := ⟨fun r a b => by
    change (r • (a:T))*b=r • ((a:T)*b)
    exact smul_mul_assoc r (a:T) b⟩
  apply Proj.iSup_basicOpen_eq_top' 𝓣 (fun i => (a i:T)) (fun i => ⟨1,(a i).2⟩)
  have h : Algebra.adjoin S (Set.range (fun i => (a i:T))) ≤
      (Algebra.adjoin (𝓣 0) (Set.range (fun i => (a i:T)))).restrictScalars S :=
    Algebra.adjoin_le_iff.mpr Algebra.subset_adjoin
  rw [hgen] at h
  apply top_unique
  intro b _
  exact h (show b ∈ (⊤ : Subalgebra S T) from trivial)

lemma coordinate_cover : (⨆ i : Fin 3,Proj.basicOpen 𝓑 (coordinate W i:B))=⊤ :=
  coordinate_cover_generic 𝓑 (coordinate W) (coordinates_adjoin R W)

lemma coordinate_relation :
    (coordinate W 1:B)^2*(coordinate W 2:B) + algebraMap R B W.a₁*(coordinate W 0:B)*(coordinate W 1:B)*(coordinate W 2:B) +
      algebraMap R B W.a₃*(coordinate W 1:B)*(coordinate W 2:B)^2 =
    (coordinate W 0:B)^3 + algebraMap R B W.a₂*(coordinate W 0:B)^2*(coordinate W 2:B) +
      algebraMap R B W.a₄*(coordinate W 0:B)*(coordinate W 2:B)^2 + algebraMap R B W.a₆*(coordinate W 2:B)^3 := by
  have h : MvPolynomial.aeval (fun i => (coordinate W i:B)) W.toProjective.polynomial=0 := by
    rw [coordinates_aeval,Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa [WeierstrassCurve.Projective.polynomial,sub_eq_zero] using h

lemma two_chart_cover : Proj.basicOpen 𝓑 (coordinate W 1:B) ⊔ Proj.basicOpen 𝓑 (coordinate W 2:B)=⊤ := by
  apply top_unique
  intro p _
  by_contra hp
  have hy : (coordinate W 1:B) ∈ p.asHomogeneousIdeal := by
    exact not_not.mp (not_or.mp hp).1
  have hz : (coordinate W 2:B) ∈ p.asHomogeneousIdeal := by
    exact not_not.mp (not_or.mp hp).2
  let P := p.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := p.isPrime
  have hy0 : Ideal.Quotient.mk P (coordinate W 1:B)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hz0 : Ideal.Quotient.mk P (coordinate W 2:B)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have he := congrArg (Ideal.Quotient.mk P) (coordinate_relation R W)
  simp only [map_add,map_mul,map_pow,hy0,hz0,mul_zero,zero_mul,zero_add,add_zero,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0)] at he
  have hx0 : Ideal.Quotient.mk P (coordinate W 0:B)=0 := eq_zero_of_pow_eq_zero he.symm
  have hx : (coordinate W 0:B) ∈ p.asHomogeneousIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hx0
  have hc : p ∈ (⨆ i : Fin 3,Proj.basicOpen 𝓑 (coordinate W i:B)) := by
    rw [coordinate_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  fin_cases i
  · exact hi hx
  · exact hi hy
  · exact hi hz

#print axioms two_chart_cover
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
end


/-! Scheme presentation: CubicSchemeIso checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
open Scheme.Modules SectionFrames PlaneSectionRing
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (L : X.Modules)
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (ι : ∀ n : ℕ, 𝓐 n → Γ(L.tensorPow n,⊤))
variable (hRing : GradedOAlgebra.IsSectionRing c L A 𝓐 ι)
variable (a : Fin 3 → 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial})
variable (hlift : ∀ n (b : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
  p.IsHomogeneous n ∧ MvPolynomial.aeval (fun i => (a i:A)) p=(b:A))
variable (θ : X ⟶ WeierstrassProjModel.projModelCR W.toProjective)
variable (hθ : GradedOAlgebra.IsCanonicalToProj c (L.tensorPow 3)
  (WeierstrassProjModel.ProjModelRingCR W.toProjective)
  (WeierstrassProjModel.projModelGradingCR W.toProjective)
  (sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk) θ)
include hRing hlift hθ in
lemma isIso_of_affine_loci (hL : IsInvertible L)
    (h1 : IsAffineOpen (zeroSchemeIdeal (sectionHom (ι 3 (a 1)))).support.compl)
    (h2 : IsAffineOpen (zeroSchemeIdeal (sectionHom (ι 3 (a 2)))).support.compl) : IsIso θ := by
  let B := WeierstrassProjModel.ProjModelRingCR W.toProjective
  let 𝓑 := WeierstrassProjModel.projModelGradingCR W.toProjective
  let τs : Fin 2 → 𝓑 1 := ![coordinate W 1,coordinate W 2]
  let U : Fin 2 → (Proj 𝓑).Opens := fun i => Proj.basicOpen 𝓑 (τs i:B)
  have hU : (⨆ i,U i)=⊤ := by
    apply top_unique
    rw [← two_chart_cover R W]
    exact sup_le (le_iSup U (0:Fin 2)) (le_iSup U (1:Fin 2))
  have hcov : (⨆ i,θ ⁻¹ᵁ U i)=⊤ := θ.iSup_preimage_eq_top hU
  have haff : ∀ i,IsAffineOpen (θ ⁻¹ᵁ U i) := by
    intro i
    fin_cases i
    · change IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓑 (coordinate W 1:B))
      rw [preimage_coordinate c L 𝓐 ι hRing a W hk hlift θ hθ hL 1]
      exact h1
    · change IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓑 (coordinate W 2:B))
      rw [preimage_coordinate c L 𝓐 ι hRing a W hk hlift θ hθ hL 2]
      exact h2
  have hi : ∀ i,IsIso (θ ∣_ U i) := fun i => CanonicalMap.local_iso_of_affine_cover c (L.tensorPow 3)
    B 𝓑 (sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk)
    (isSectionRing c L 𝓐 ι hRing (fun i => (a i:A)) (fun i => (a i).2) W hk hlift)
    θ hθ 1 τs hcov haff 1 one_pos (τs i) (haff i)
  exact (MorphismProperty.isomorphisms.iff θ).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P:=MorphismProperty.isomorphisms Scheme) U hU
      (fun i => (MorphismProperty.isomorphisms.iff _).mpr (hi i)))

#print axioms isIso_of_affine_loci
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
end


/-! Scheme presentation: CubicBaseMap checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
lemma projZero_comp_algebraMap {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (𝓑 : ℕ → Submodule R B) [GradedAlgebra 𝓑] :
    (GradedRing.projZeroRingHom' 𝓑).comp (algebraMap R B) = algebraMap R (𝓑 0) := by
  ext r
  change (DirectSum.decompose 𝓑 (algebraMap R B r) 0 : B) = algebraMap R B r
  exact DirectSum.decompose_of_mem_same 𝓑 (SetLike.algebraMap_mem_graded 𝓑 r)

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (L : X.Modules)
variable (𝓐 : ℕ → Submodule R A) [GradedAlgebra 𝓐]
variable (ι : ∀ n : ℕ, 𝓐 n → Γ(L.tensorPow n,⊤))
variable (a : Fin 3 → 𝓐 3) (W : WeierstrassCurve R)
variable (hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial})
variable (θ : X ⟶ WeierstrassProjModel.projModelCR W.toProjective)
lemma canonical_over_base
    (hθ : GradedOAlgebra.IsCanonicalToProj c (L.tensorPow 3)
      (WeierstrassProjModel.ProjModelRingCR W.toProjective)
      (WeierstrassProjModel.projModelGradingCR W.toProjective)
      (PlaneSectionRing.sections L 𝓐 ι (fun i => (a i:A)) (fun i => (a i).2) W hk) θ) :
    θ ≫ WeierstrassProjModel.projModelStrCR W.toProjective = c := by
  have h := hθ.comp_toSpecZero
  rw [projZero_comp_algebraMap] at h
  exact h
#print axioms canonical_over_base
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.CubicCanonicalMap
end


/-! Scheme presentation: ActualCubicIso checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
open Filtration GeometricCubic CubicCanonicalMap
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
lemma exists_cubic_isomorphism :
    ∃ (W : WeierstrassCurve R) (e : Q.target ≅ WeierstrassProjModel.projModelCR W.toProjective),
      e.hom ≫ WeierstrassProjModel.projModelStrCR W.toProjective = Q.structureMap := by
  obtain ⟨A,hA,hRA,𝓐,h𝓐,ι,hRing⟩ := SectionRing.exists_origin_section_ring R Q
  letI := hA
  letI := hRA
  letI := h𝓐
  obtain ⟨z,x,y,W,b,hz,hx,hy,hb,hgen,hplane,hker⟩ := exists_plane_coordinate_data R Q A 𝓐 ι hRing
  let a : Fin 3 → 𝓐 3 := ![planeX R A 𝓐 z x,y,planeZ R A 𝓐 z]
  have ha : (fun i => (a i:A)) = ![(x:A)*z,(y:A),(z:A)^3] := by
    funext i
    fin_cases i <;> simp [a,planeX,planeZ,pow_succ]
  have hk : RingHom.ker (MvPolynomial.aeval (fun i => (a i:A))).toRingHom=Ideal.span {W.toProjective.polynomial} := by
    rw [ha]
    exact actual_plane_cubic_kernel R Q A 𝓐 ι hRing z x y W hz hx hy hplane
  have hlift : ∀ n (b : 𝓐 (3*n)), ∃ p : MvPolynomial (Fin 3) R,
      p.IsHomogeneous n ∧ MvPolynomial.aeval (fun i => (a i:A)) p=(b:A) := by
    rw [ha]
    exact actual_plane_homogeneous_lift R Q A 𝓐 ι hRing z x y hz hx hy
  obtain ⟨𝔓,hσ⟩ := exists_plane_projPresentation R Q A 𝓐 ι hRing z x y hz hy
  obtain ⟨θ,hθ⟩ := exists_canonical Q.structureMap Q.zero.ker.invModule 𝓐 ι hRing a W hk hlift 𝔓 (by
    intro i
    rw [hσ]
    fin_cases i <;> rfl)
  have haf := normalized_affine_loci R Q 3 (by decide) (ι 3 y) hy
  haveI : IsIso θ := isIso_of_affine_loci Q.structureMap Q.zero.ker.invModule 𝓐 ι hRing a W hk hlift θ hθ
    Q.zero_ideal_invertible.isInvertible_invModule haf.2 (by
      change IsAffineOpen (Scheme.Modules.zeroSchemeIdeal (SectionFrames.sectionHom (ι 3 (planeZ R A 𝓐 z)))).support.compl
      rw [planeZ_frame_locus R Q A 𝓐 ι hRing z hz]
      exact haf.1)
  exact ⟨W,asIso θ,canonical_over_base Q.structureMap Q.zero.ker.invModule 𝓐 ι a W hk θ hθ⟩
#print axioms exists_cubic_isomorphism
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.ProjectiveMap
end


/-! Scheme presentation: PointedCubicIso checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PointedIso
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of R)}
lemma adjust_identity (H : RelativeGroupLaw R p) (e : X ≅ Y)
    (he : e.hom ≫ q=p) (s : Spec (.of R) ⟶ Y) (hs : s ≫ q=𝟙 _) :
    ∃ e' : X ≅ Y, e'.hom ≫ q=p ∧ (H.one (𝟙 _)).val ≫ e'.hom=s := by
  have hie : e.inv ≫ p=q := by rw [← he,e.inv_hom_id_assoc]
  let x : SchemeHomOver (𝟙 (Spec (.of R))) p := ⟨s ≫ e.inv, by rw [Category.assoc,hie,hs]⟩
  let t : X ≅ X :=
    { hom := H.translate x
      inv := H.translate (H.inv (𝟙 _) x)
      hom_inv_id := by rw [← H.translate_mul,H.mul_inv_cancel,H.translate_one]
      inv_hom_id := by rw [← H.translate_mul,H.inv_mul_cancel,H.translate_one] }
  refine ⟨t ≪≫ e,?_,?_⟩
  · change H.translate x ≫ e.hom ≫ q=p
    rw [he,H.translate_over]
  · change ((H.one (𝟙 _)).val ≫ H.translate x) ≫ e.hom=s
    rw [H.comp_translate_eq_mul]
    have hx : schemeHomOverComp (𝟙 (Spec (.of R))) (Category.comp_id _) x=x := by
      apply Subtype.ext
      exact Category.id_comp _
    rw [hx,H.one_mul]
    change (s ≫ e.inv) ≫ e.hom=s
    simp only [Category.assoc,e.inv_hom_id,Category.comp_id]

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (Q : FramedCurve R)
lemma exists_pointed_cubic_isomorphism :
    ∃ (W : WeierstrassCurve R) (e : Q.target ≅ ArithmeticThetaRelativeKatoR0169.Curve R W),
      e.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W=Q.structureMap ∧
      Q.zero ≫ e.hom=ArithmeticThetaRelativeKatoR0169.origin R W := by
  obtain ⟨W,e,he⟩ := ProjectiveMap.exists_cubic_isomorphism R Q
  obtain ⟨e',he',hz⟩ := adjust_identity Q.law e he (WeierstrassProjModel.kwZeroSect R W).val
    (WeierstrassProjModel.kwZeroSect R W).property
  exact ⟨W,e',he',hz⟩
#print axioms exists_pointed_cubic_isomorphism
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PointedIso
end


/-! Smoothness and discriminant: SmoothHypersurface checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TensorProduct
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
variable {R P : Type u} [CommRing R] [CommRing P] [IsDomain P] [Algebra R P]
lemma exists_derivation_relation_one (f : P) (hf : f ≠ 0)
    [Algebra.FormallySmooth R P] [Algebra.FormallySmooth R (P ⧸ Ideal.span {f})] :
    ∃ D : Derivation R P (P ⧸ Ideal.span {f}), D f=1 := by
  let I : Ideal P := Ideal.span {f}
  let A := P ⧸ I
  let J := RingHom.ker (algebraMap P A)
  have hJ : J=I := Ideal.mk_ker
  let e : P ≃ₗ[P] I := LinearEquiv.toSpanNonzeroSingleton P P f hf
  let q : I →ₗ[P] A := I.mkQ ∘ₗ e.symm.toLinearMap
  have he (x : I) : e.symm x * f=(x:P) := e.symm_apply_apply (e.symm x) ▸
    (LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul P P f hf x)
  have hq (x y : I) : q (x*y)=0 := by
    have hxy : e.symm (x*y) = (x:P)*e.symm y := by
      apply mul_right_cancel₀ hf
      rw [he]
      change (x:P)*(y:P)=(x:P)*e.symm y*f
      rw [mul_assoc,he]
    change I.mkQ (e.symm (x*y))=0
    rw [hxy]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (I.mul_mem_right _ x.2)
  let φ : J.Cotangent →ₗ[P] A := (Ideal.Cotangent.lift q hq) ∘ₗ
    (Ideal.Cotangent.equivOfEq J I hJ).toLinearMap
  have hfJ : f ∈ J := hJ ▸ Ideal.subset_span (Set.mem_singleton f)
  have hφ : φ (J.toCotangent ⟨f,hfJ⟩)=1 := by
    change q (LinearEquiv.ofEq J I hJ ⟨f,hfJ⟩)=1
    change I.mkQ (e.symm ⟨f,_⟩)=1
    rw [show e.symm ⟨f,_⟩=1 from LinearEquiv.coord_self P P f hf]
    rfl
  obtain ⟨l,hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R:=R) (P:=P) (A:=A)
    (Ideal.Quotient.mk_surjective)).mp inferInstance
  let d : P →ₗ[P] A := 0
  let δ : Ω[P⁄R] →ₗ[P] A := φ ∘ₗ l ∘ₗ (TensorProduct.mk P A Ω[P⁄R] 1)
  refine ⟨δ.compDer (KaehlerDifferential.D R P),?_⟩
  change φ (l (1 ⊗ₜ[P] KaehlerDifferential.D R P f))=1
  rw [← KaehlerDifferential.kerCotangentToTensor_toCotangent (R:=R) (A:=P) (B:=A) ⟨f,hfJ⟩]
  have hl' := LinearMap.congr_fun hl (J.toCotangent ⟨f,hfJ⟩)
  change l (KaehlerDifferential.kerCotangentToTensor R P A (J.toCotangent ⟨f,hfJ⟩))=J.toCotangent ⟨f,hfJ⟩ at hl'
  rw [hl',hφ]
#print axioms exists_derivation_relation_one
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
end


/-! Smoothness and discriminant: WeierstrassDifferential checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Polynomial
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
variable {R A : Type u} [CommRing R] [CommRing A]
  [Algebra R A] [Algebra (Polynomial (Polynomial R)) A] [IsScalarTower R (Polynomial (Polynomial R)) A]
lemma derivation_polynomial (W : WeierstrassCurve R)
    (D : Derivation R (Polynomial (Polynomial R)) A) :
    D W.toAffine.polynomial =
      (2*algebraMap (Polynomial (Polynomial R)) A X + algebraMap R A W.a₁ * algebraMap (Polynomial (Polynomial R)) A (C X) + algebraMap R A W.a₃) * D X +
      (algebraMap R A W.a₁ * algebraMap (Polynomial (Polynomial R)) A X -
        (3*(algebraMap (Polynomial (Polynomial R)) A (C X))^2+2*algebraMap R A W.a₂*algebraMap (Polynomial (Polynomial R)) A (C X)+algebraMap R A W.a₄)) * D (C X) := by
  have hc (r : R) : D (C (C r))=0 := D.map_algebraMap r
  simp only [WeierstrassCurve.Affine.polynomial,map_add,map_sub,map_mul,map_pow,
    Derivation.leibniz,Derivation.leibniz_pow,hc,smul_zero,zero_add,add_zero,
    Algebra.smul_def,nsmul_eq_mul]
  simp only [show ∀ r : R, algebraMap (Polynomial (Polynomial R)) A (C (C r))=algebraMap R A r from fun r => (IsScalarTower.algebraMap_apply R (Polynomial (Polynomial R)) A r).symm]
  simp only [map_ofNat]
  ring
#print axioms derivation_polynomial
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
end


/-! Smoothness and discriminant: SingularCoordinates checked development. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
variable {K : Type u} [Field K] [CharZero K]
lemma singular_coordinates (W : WeierstrassCurve K) (hΔ : W.Δ=0) :
    ∃ x y : K,
      y^2+W.a₁*x*y+W.a₃*y-(x^3+W.a₂*x^2+W.a₄*x+W.a₆)=0 ∧
      2*y+W.a₁*x+W.a₃=0 ∧
      W.a₁*y-(3*x^2+2*W.a₂*x+W.a₄)=0 := by
  have hc : W.c₄^3=W.c₆^2 := by
    have h := W.c_relation
    rw [hΔ,mul_zero,eq_comm,sub_eq_zero] at h
    exact h
  have hshort (t : K) :
      (-(W.a₁*(t-W.b₂/12)+W.a₃)/2)^2 +
      W.a₁*(t-W.b₂/12)*(-(W.a₁*(t-W.b₂/12)+W.a₃)/2)+
      W.a₃*(-(W.a₁*(t-W.b₂/12)+W.a₃)/2)-
      ((t-W.b₂/12)^3+W.a₂*(t-W.b₂/12)^2+W.a₄*(t-W.b₂/12)+W.a₆) =
      -t^3+W.c₄/48*t+W.c₆/864 := by
    simp only [WeierstrassCurve.b₂,WeierstrassCurve.c₄,WeierstrassCurve.c₆,WeierstrassCurve.b₄,WeierstrassCurve.b₆]
    ring
  have hder (t : K) :
      W.a₁*(-(W.a₁*(t-W.b₂/12)+W.a₃)/2)-
      (3*(t-W.b₂/12)^2+2*W.a₂*(t-W.b₂/12)+W.a₄)= -3*t^2+W.c₄/48 := by
    simp only [WeierstrassCurve.b₂,WeierstrassCurve.c₄,WeierstrassCurve.b₄]
    ring
  suffices ∃ t : K, -t^3+W.c₄/48*t+W.c₆/864=0 ∧ -3*t^2+W.c₄/48=0 by
    obtain ⟨t,ht,ht'⟩ := this
    refine ⟨t-W.b₂/12,-(W.a₁*(t-W.b₂/12)+W.a₃)/2,?_,?_,?_⟩
    · rw [hshort,ht]
    · ring
    · rw [hder,ht']
  by_cases h4 : W.c₄=0
  · have h6 : W.c₆=0 := by
      exact eq_zero_of_pow_eq_zero (by simpa [h4] using hc.symm : W.c₆^2=0)
    refine ⟨0,?_,?_⟩ <;> simp [h4,h6]
  · refine ⟨-W.c₆/(12*W.c₄),?_,?_⟩
    · field_simp
      linear_combination -41472*W.c₆*hc
    · field_simp
      linear_combination 144*hc
#print axioms singular_coordinates
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
end


/-! Smoothness and discriminant: SmoothCubicChart checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
variable {R : Type u} [CommRing R]
lemma smooth_coordinateRing (W : WeierstrassCurve R)
    [Smooth (WeierstrassProjModel.projModelStrCR W.toProjective)] :
    Algebra.Smooth R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial}) := by
  let B := WeierstrassProjModel.ProjModelRingCR W.toProjective
  let 𝓑 := WeierstrassProjModel.projModelGradingCR W.toProjective
  let z : B := Ideal.Quotient.mk _ (MvPolynomial.X 2)
  have hz : z ∈ 𝓑 1 := HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
  obtain ⟨f,hf,hbase,_⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing W.toProjective
  let e := RingEquiv.ofBijective f hf
  haveI : IsIso e.toCommRingCatIso.hom := inferInstance
  let θ := Spec.map e.toCommRingCatIso.hom ≫ Proj.awayι 𝓑 z hz one_pos
  haveI : IsOpenImmersion θ := IsOpenImmersion.comp _ _
  have he : θ ≫ WeierstrassProjModel.projModelStrCR W.toProjective =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial}))) := by
    simp only [θ,WeierstrassProjModel.projModelStrCR,Category.assoc]
    rw [Proj.awayι_toSpecZero_assoc,← Spec.map_comp,← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hbase)
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial})))) :=
    he ▸ (inferInstance : Smooth (θ ≫ WeierstrassProjModel.projModelStrCR W.toProjective))
  apply (RingHom.smooth_algebraMap).mp
  exact (HasRingHomProperty.Spec_iff (P:=@Smooth) (φ:=CommRingCat.ofHom (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial})))).mp inferInstance
#print axioms smooth_coordinateRing
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
end


/-! Smoothness and discriminant: DiscriminantUnit checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
namespace ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
variable {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R]
lemma discriminant_unit_of_smooth_coordinateRing (W : WeierstrassCurve R)
    [Algebra.FormallySmooth R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial})] :
    IsUnit W.Δ := by
  letI : Algebra.FormallySmooth R (Polynomial (Polynomial R)) := Algebra.FormallySmooth.comp R (Polynomial R) (Polynomial (Polynomial R))
  obtain ⟨D,hD⟩ := exists_derivation_relation_one (R:=R) W.toAffine.polynomial W.toAffine.polynomial_ne_zero
  by_contra hΔ
  obtain ⟨m,hm,hmΔ⟩ := exists_max_ideal_of_mem_nonunits hΔ
  letI := hm
  let K := R ⧸ m
  letI : Field K := Ideal.Quotient.field m
  letI : Algebra ℚ K := inferInstanceAs (Algebra ℚ (R ⧸ m))
  letI : CharZero K := algebraRat.charZero K
  let ρ : R →+* K := Ideal.Quotient.mk m
  have hρΔ : (W.map ρ).Δ=0 := by
    rw [WeierstrassCurve.map_Δ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmΔ
  obtain ⟨x,y,hxy,hy,hx⟩ := singular_coordinates (W.map ρ) hρΔ
  let E : Polynomial (Polynomial R) →+* K :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom ρ x) y
  have hE : E W.toAffine.polynomial=0 := by
    simpa [E,WeierstrassCurve.Affine.polynomial,Polynomial.eval₂_pow,add_mul,add_assoc] using hxy
  let I : Ideal (Polynomial (Polynomial R)) := Ideal.span {W.toAffine.polynomial}
  let φ : (Polynomial (Polynomial R) ⧸ I) →+* K := Ideal.Quotient.lift I E (by
    change Ideal.span {W.toAffine.polynomial} ≤ RingHom.ker E
    rw [Ideal.span_le]
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact hE)
  have hX : φ (Ideal.Quotient.mk I (X : Polynomial (Polynomial R)))=y := by
    change E X=y
    simp [E]
  have hCX : φ (Ideal.Quotient.mk I (C X : Polynomial (Polynomial R)))=x := by
    change E (C X)=x
    simp [E]
  have hC (r : R) : φ (Ideal.Quotient.mk I (C (C r)))=ρ r := by
    change E (C (C r))=ρ r
    simp [E]
  have h := congrArg φ (derivation_polynomial W D)
  rw [hD,map_one] at h
  simp only [map_add,map_sub,map_mul,map_pow] at h
  change (1:K) = (φ 2 * φ (Ideal.Quotient.mk I X) + φ (Ideal.Quotient.mk I (C (C W.a₁))) * φ (Ideal.Quotient.mk I (C X)) + φ (Ideal.Quotient.mk I (C (C W.a₃)))) * φ (D X) +
    (φ (Ideal.Quotient.mk I (C (C W.a₁))) * φ (Ideal.Quotient.mk I X) - (φ 3 * φ (Ideal.Quotient.mk I (C X))^2 + φ 2 * φ (Ideal.Quotient.mk I (C (C W.a₂))) * φ (Ideal.Quotient.mk I (C X)) + φ (Ideal.Quotient.mk I (C (C W.a₄))))) * φ (D (C X)) at h
  rw [hX,hCX,hC,hC,hC,hC,show φ 2=2 from map_ofNat φ 2,show φ 3=3 from map_ofNat φ 3] at h
  change 2*y+ρ W.a₁*x+ρ W.a₃=0 at hy
  change ρ W.a₁*y-(3*x^2+2*ρ W.a₂*x+ρ W.a₄)=0 at hx
  rw [hy,hx,zero_mul,zero_mul,add_zero] at h
  exact one_ne_zero h
#print axioms discriminant_unit_of_smooth_coordinateRing
end ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface
end


/-! Smoothness and discriminant: FinalPresentation checked development. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaCyclicPresentationR0174
open RelativeWeierstrassPresentationR0174
/-- A relative one-dimensional abelian scheme with trivial identity Hodge line
has a pointed elliptic Weierstrass presentation over its original base. -/
theorem relative_weierstrass_presentation
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of R)) (H : GoodReductionJacobian.RelativeGroupLaw R p)
    (hX : GoodReductionJacobian.AbelianSchemePropertyBundle R p)
    (hdim : SmoothOfRelativeDimension 1 p)
    (hodge : Nonempty ((SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≅
      (Scheme.Modules.pullback (H.one (𝟙 (Spec (CommRingCat.of R)))).val).obj p.kaehler)) :
    ∃ (V : WeierstrassCurve R) (hV : V.IsElliptic)
      (e : X ≅ ArithmeticThetaRelativeKatoR0169.Curve R V),
      e.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R V=p ∧
      (H.one (𝟙 (Spec (CommRingCat.of R)))).val ≫ e.hom=ArithmeticThetaRelativeKatoR0169.origin R V := by
  let Q : FramedCurve R := ⟨X,p,H,hX,hdim,hodge⟩
  obtain ⟨W,e,he,hzero⟩ := PointedIso.exists_pointed_cubic_isomorphism R Q
  haveI : Smooth p := hX.smooth
  have hstr : WeierstrassProjModel.projModelStrCR W.toProjective = e.inv ≫ p := by
    change WeierstrassProjModel.projModelStrCR W.toProjective = e.inv ≫ Q.structureMap
    rw [← he,e.inv_hom_id_assoc]
    rfl
  haveI : Smooth (WeierstrassProjModel.projModelStrCR W.toProjective) := by
    rw [hstr]
    infer_instance
  haveI := SmoothHypersurface.smooth_coordinateRing W
  exact ⟨W,⟨SmoothHypersurface.discriminant_unit_of_smooth_coordinateRing W⟩,e,he,hzero⟩
#print axioms relative_weierstrass_presentation
end ArithmeticThetaCyclicPresentationR0174
end
