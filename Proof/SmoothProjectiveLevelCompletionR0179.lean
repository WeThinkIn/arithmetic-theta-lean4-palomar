module

public import LevelCompactificationDefinitionsR0179
public import Theorems.Thm_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
public import Definitions.Def_AlgebraicCurve_CurveModelConstruction
public import P2M.Sol.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
public import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso
public import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
public import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
public import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem
public import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
public import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
public import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
public import LegendreFamilyGeometryR0176

@[expose] public section

/-! Geometric prerequisites for compactifying the actual compatible quotient.
All scalar structures below are those of its specified structural morphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaLevelCompactificationR0179
namespace SmoothProjectiveLevelCompletionR0179

open CategoryTheory AlgebraicGeometry NeronModelInfra

variable (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)

theorem openStructure_smooth : SmoothOfRelativeDimension 1 (openStructure k L D) :=
  D.quotient.quotient.smooth

theorem openStructure_finiteType : LocallyOfFiniteType (openStructure k L D) := by
  let := openStructure_smooth k L D
  infer_instance

theorem openStructure_quasiCompact : QuasiCompact (openStructure k L D) := by
  unfold openStructure
  infer_instance

theorem openStructure_separated : IsSeparated (openStructure k L D) := by
  unfold openStructure
  infer_instance

theorem openBase_locallyNoetherian : IsLocallyNoetherian (OpenBase k L D) := by
  let := openStructure_finiteType k L D
  exact LocallyOfFiniteType.isLocallyNoetherian (openStructure k L D)

theorem quotientRing_smooth : Algebra.Smooth k D.quotient.quotient.ring := by
  have hs : Smooth (openStructure k L D) := by
    let := openStructure_smooth k L D
    infer_instance
  exact (RingHom.smooth_algebraMap).mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

theorem quotientRing_finiteType : Algebra.FiniteType k D.quotient.quotient.ring := by
  let := quotientRing_smooth k L D
  infer_instance

theorem quotientRing_noetherian : IsNoetherianRing D.quotient.quotient.ring := by
  let := quotientRing_finiteType k L D
  exact Algebra.FiniteType.isNoetherianRing k D.quotient.quotient.ring

/-- Normality is local on the possibly disconnected scheme; no global domain
instance is imposed on its coordinate ring. -/
theorem openBase_stalk_normal (x : OpenBase k L D) :
    IsDomain ((OpenBase k L D).presheaf.stalk x) ∧
      IsIntegrallyClosed ((OpenBase k L D).presheaf.stalk x) := by
  let := openStructure_smooth k L D
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
    MulEquiv.isDomain k e.symm.toMulEquiv
  let : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv e
  exact Smooth.isDomain_and_isIntegrallyClosed_stalk (openStructure k L D) x

theorem openBase_reduced : AlgebraicGeometry.IsReduced (OpenBase k L D) := by
  let : ∀ x : OpenBase k L D,
      IsDomain ((OpenBase k L D).presheaf.stalk x) :=
    fun x => (openBase_stalk_normal k L D x).1
  exact isReduced_of_isReduced_stalk (OpenBase k L D)

theorem openBase_finite_components :
    (irreducibleComponents (OpenBase k L D)).Finite := by
  let := quotientRing_noetherian k L D
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

theorem openBase_components_disjoint
    (Z W : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D))
    (hW : W ∈ irreducibleComponents (OpenBase k L D)) (hne : Z ≠ W) :
    Disjoint Z W := by
  rw [Set.disjoint_left]
  intro x hxZ hxW
  exact not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
    (OpenBase k L D) x Z W hZ hW hne hxZ hxW
    (openBase_stalk_normal k L D x).1

theorem openBase_component_isOpen (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) : IsOpen Z := by
  have heq : Zᶜ = ⋃ W ∈ irreducibleComponents (OpenBase k L D) \ {Z}, W := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion₂.mpr ⟨irreducibleComponent x, ?_, mem_irreducibleComponent⟩
      refine ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩
      intro he
      exact hx ((Set.mem_singleton_iff.mp he) ▸ mem_irreducibleComponent)
    · intro hx hxZ
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp
        (openBase_components_disjoint k L D W Z hW.1 hZ
          (by simpa only [Set.mem_singleton_iff] using hW.2)) hxW hxZ
  rw [← isClosed_compl_iff, heq]
  exact (openBase_finite_components k L D).sdiff.isClosed_biUnion
    (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)

/-- Each component is an actual open subscheme of the original quotient. -/
def componentOpen (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) : (OpenBase k L D).Opens :=
  ⟨Z, openBase_component_isOpen k L D Z hZ⟩

theorem component_integral (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    IsIntegral (componentOpen k L D Z hZ).toScheme := by
  let := openBase_reduced k L D
  let : IrreducibleSpace (componentOpen k L D Z hZ).toScheme :=
    Subtype.irreducibleSpace hZ.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem component_closedImmersion (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    IsClosedImmersion (componentOpen k L D Z hZ).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_of_mem_irreducibleComponents Z hZ

theorem component_affine (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    IsAffine (componentOpen k L D Z hZ).toScheme := by
  let := component_closedImmersion k L D Z hZ
  exact isAffine_of_isAffineHom (componentOpen k L D Z hZ).ι

theorem component_smooth (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    SmoothOfRelativeDimension 1 ((componentOpen k L D Z hZ).ι ≫ openStructure k L D) := by
  let := openStructure_smooth k L D
  exact smoothOfRelativeDimension_comp 0 1 _ _

namespace FunctionFieldConstruction

open AlgebraicCurve
open P2MW.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

/-- Extract the generator needed by the checked two-chart proper-curve
construction, with the field action supplied by the structural map. -/
theorem exists_generator (K F : Type u) [Field K] [CharZero K] [Field F]
    [Algebra K F] [Algebra.EssFiniteType K F]
    (hΩ : Module.rank F (KaehlerDifferential K F) = 1) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hr : (s : Set F) = Set.range ((↑) : s → F) := by ext; simp
  rw [hr] at hsep
  have hcard : (Fintype.card s : Cardinal.{u}) = 1 := by
    let : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
      Algebra.FormallyEtale.of_isSeparable _ F
    have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F).lift_rank_eq
    rw [Module.rank_baseChange, SmoothModelFunctionField.rank_kaehler_adjoin s hs.1, hΩ] at h1
    simpa using h1
  have hs1 : s.card = 1 := by
    rw [Fintype.card_coe] at hcard
    exact_mod_cast hcard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs1
  have hx : Set.range ((↑) : ({x} : Finset F) → F) = {x} := by ext; simp
  let : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := by
    have := hs.isAlgebraic_field
    rwa [hx] at this
  let : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.EssFiniteType.of_comp K _ F
  exact ⟨x, hs.1.transcendental ⟨x, Finset.mem_singleton_self x⟩,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩

theorem exists_proper_model (K : Type u) [Field K] [CharZero K]
    (C : Scheme.{u}) [IsIntegral C] (c : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    Nonempty (CurveModel K C.functionField) := by
  letI := (baseToFunctionField c).toAlgebra
  obtain ⟨hft, hΩ⟩ := SmoothModelFunctionField.stageA c
  let := hft
  obtain ⟨t, ht, hfin⟩ := exists_generator K C.functionField hΩ
  let := hfin
  let : Fact (t ≠ 0) := ⟨by intro hz; apply ht; rw [hz]; exact isAlgebraic_zero⟩
  let : FiniteDimensional (IntermediateField.adjoin K {t⁻¹}) C.functionField :=
    AlgebraicCurve.CurveModel.finiteDimensional_congr K
      (AlgebraicCurve.CurveModel.adjoin_simple_inv_eq K t).symm
  exact ⟨AlgebraicCurve.CurveModel.ofGenerator K t ht⟩

private theorem generic_structure (K : Type u) [Field K]
    (C : Scheme.{u}) [IsIntegral C] (c : C ⟶ Spec (.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) := by
  refine ext_of_isAffine ?_
  have h1 : (Spec.map (CommRingCat.ofHom (baseToFunctionField c))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (baseToFunctionField c) ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom (baseToFunctionField c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
        C.presheaf.germ ⊤ (genericPoint C) trivial := by
    ext a
    rfl
  have h3 : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3, Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Extend the generic identification over every point of the original smooth
curve by properness. The conclusion records its open-immersion restriction. -/
theorem exists_map_to_model (K : Type u) [Field K]
    (C : Scheme.{u}) [IsIntegral C] (c : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    ∀ M : CurveModel K C.functionField,
      ∃ g : C ⟶ M.C, g ≫ M.toBase = c ∧
        ∃ U : C.Opens, genericPoint C ∈ U ∧ IsOpenImmersion (U.ι ≫ g) := by
  letI := (baseToFunctionField c).toAlgebra
  intro M
  let ψ : C.functionField ≅ M.C.functionField := M.ffEquiv.toCommRingCatIso
  have hψ : Spec.map ψ.inv ≫ M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase =
      C.fromSpecStalk (genericPoint C) ≫ c := by
    rw [generic_structure, generic_structure, ← Spec.map_comp]
    congr 1
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = baseToFunctionField c a
    rw [← M.ffEquiv_algebraMap a, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨U, hη, j, hj, hover, _⟩ :=
    Scheme.exists_isOpenImmersion_of_functionField_iso c M.toBase ψ hψ
  let := hj
  let : Nonempty U.toScheme := ⟨⟨genericPoint C, hη⟩⟩
  have hreg : ∀ x : C, x ∉ Set.range U.ι.base →
      IsDiscreteValuationRing (C.presheaf.stalk x) := by
    intro x hx
    have hne : x ≠ genericPoint C := by
      intro heq
      apply hx
      rw [Scheme.Opens.range_ι, heq]
      exact hη
    exact SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x
      (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x hne)
  obtain ⟨g, hg, hgj⟩ :=
    exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
      c U.ι hreg M.toBase j hover
  exact ⟨g, hg, U, hη, hgj.symm ▸ hj⟩

theorem finite_complement (K : Type u) [Field K]
    (C : Scheme.{u}) [IsIntegral C] [CompactSpace C]
    (c : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hη : genericPoint C ∈ U) : (U : Set C)ᶜ.Finite := by
  let := LocallyOfFiniteType.isLocallyNoetherian c
  apply Scheme.finite_of_isClosed_of_genericPoint_notMem (X := C)
    (fun x => ?_) U.isOpen.isClosed_compl (by simpa using hη)
  by_cases hx : x = genericPoint C
  · subst x
    change ringKrullDim C.functionField ≤ 1
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one
  · rw [SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed K c 1 x
      (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x hx)]
    exact le_rfl

/-- A morphism of smooth integral curves which is an open immersion on a dense
open is quasi-finite: its fibers contain at most one interior point and finitely
many points in the complement. -/
theorem quasiFinite_of_open_restriction (K : Type u) [Field K]
    (C Y : Scheme.{u}) [IsIntegral C] [CompactSpace C]
    (c : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c]
    (p : Y ⟶ Spec (.of K)) (g : C ⟶ Y) (hg : g ≫ p = c)
    (U : C.Opens) (hη : genericPoint C ∈ U) [IsOpenImmersion (U.ι ≫ g)] :
    LocallyQuasiFinite g := by
  let : LocallyOfFiniteType (g ≫ p) := hg.symm ▸ inferInstance
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  let := LocallyOfFiniteType.isLocallyNoetherian c
  let : IsNoetherian C := {}
  apply (locallyQuasiFinite_iff_finite_preimage_singleton (f := g)).mpr
  intro y
  have hsmall : ((U : Set C) ∩ g.base ⁻¹' {y}).Subsingleton := by
    intro x hx z hz
    have h : (U.ι ≫ g) (⟨x, hx.1⟩ : U.toScheme) =
        (U.ι ≫ g) (⟨z, hz.1⟩ : U.toScheme) := hx.2.trans hz.2.symm
    exact congrArg Subtype.val ((U.ι ≫ g).injective h)
  apply ((finite_complement K C c U hη).union hsmall.finite).subset
  intro x hx
  by_cases hu : x ∈ U
  · exact Or.inr ⟨hu, hx⟩
  · exact Or.inl hu

/-- The birational extension embeds the entire original separated smooth curve,
not merely a dense open subset. -/
theorem exists_openImmersion_to_model (K : Type u) [Field K]
    (C : Scheme.{u}) [IsIntegral C] [CompactSpace C]
    (c : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c] [IsSeparated c] :
    letI := (baseToFunctionField c).toAlgebra
    ∀ M : CurveModel K C.functionField,
      ∃ g : C ⟶ M.C, g ≫ M.toBase = c ∧ IsOpenImmersion g ∧ DenseRange g.base := by
  letI := (baseToFunctionField c).toAlgebra
  intro M
  obtain ⟨g, hg, U, hη, hj⟩ := exists_map_to_model K C c M
  let := hj
  let : Nonempty U.toScheme := ⟨⟨genericPoint C, hη⟩⟩
  let j := U.ι ≫ g
  let V := j.opensRange
  let s : V.toScheme ⟶ C := j.isoOpensRange.inv ≫ U.ι
  have hs : s ≫ g = V.ι := by
    dsimp only [s, V, j]
    rw [Category.assoc]
    exact (U.ι ≫ g).isoOpensRange_inv_comp
  let : IsOpenImmersion s := by dsimp only [s]; infer_instance
  let : Nonempty V.toScheme := ⟨j.isoOpensRange.hom ⟨genericPoint C, hη⟩⟩
  have hV : Dense (V : Set M.C) := V.isOpen.dense (by
    exact ⟨j ⟨genericPoint C, hη⟩, ⟨⟨genericPoint C, hη⟩, rfl⟩⟩)
  have hsd : DenseRange s.base := s.isOpenMap.denseRange_of_isPreirreducibleSpace _
  let : LocallyQuasiFinite g := quasiFinite_of_open_restriction K C M.C c M.toBase g hg U hη
  let : LocallyOfFiniteType (g ≫ M.toBase) := hg.symm ▸ inferInstance
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g M.toBase
  let : IsSeparated (g ≫ M.toBase) := hg.symm ▸ inferInstance
  let : IsSeparated g := IsSeparated.of_comp g M.toBase
  let := LocallyOfFiniteType.isLocallyNoetherian c
  let := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  let : IsNoetherian C := {}
  have hnormal : ∀ y : M.C, IsDomain (M.C.presheaf.stalk y) ∧
      IsIntegrallyClosed (M.C.presheaf.stalk y) := by
    let e : K ≃+* Γ(Spec (.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
    let : IsDomain Γ(Spec (.of K), ⊤) := MulEquiv.isDomain K e.symm.toMulEquiv
    let : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv e
    exact fun y => Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase y
  let : IsOpenImmersion g :=
    isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
      g hnormal V hV s hs hsd
  exact ⟨g, hg, inferInstance, g.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩

end FunctionFieldConstruction

namespace Projectivity

open CategoryTheory.Limits
open ArithmeticThetaProjectiveEffectivityR0135

/-- A Chow modification of a smooth proper integral curve has a global section:
extend its inverse from the dense open by the valuative criterion. The section
is a closed immersion, which supplies projectivity of the curve itself. -/
theorem exists_embedding (K : Type u) [Field K]
    (C : Scheme.{u}) [IsIntegral C] (c : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c] :
    ∃ (n : ℕ) (e : C ⟶ projectiveSpace K (n+1)),
      IsClosedImmersion e ∧ e ≫ projectiveStructure K (n+1) = c := by
  obtain ⟨A⟩ := ChowDatumProj.nonempty_of c (ChowDatum.nonempty c)
  let s : A.U.toScheme ⟶ A.V' :=
    inv (pullback.snd A.p A.U.ι) ≫ pullback.fst A.p A.U.ι
  have hs : s ≫ A.p = A.U.ι := by
    dsimp only [s]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  obtain ⟨x, hx⟩ := A.hU_dense.nonempty
  have hη : genericPoint C ∈ A.U :=
    (genericPoint_specializes x).mem_open A.U.isOpen hx
  let : Nonempty A.U.toScheme := ⟨⟨x, hx⟩⟩
  have hreg : ∀ y : C, y ∉ Set.range A.U.ι.base →
      IsDiscreteValuationRing (C.presheaf.stalk y) := by
    intro y hy
    have hne : y ≠ genericPoint C := by
      intro heq
      apply hy
      rw [Scheme.Opens.range_ι, heq]
      exact hη
    exact SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c y
      (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c y hne)
  obtain ⟨g, hg, hsg⟩ :=
    exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
      c A.U.ι hreg (A.p ≫ c) s (by rw [← Category.assoc, hs])
  let : IsDominant A.U.ι := ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using A.hU_dense⟩
  have hgp : g ≫ A.p = 𝟙 C := by
    apply ext_of_isDominant_of_isSeparated c
      (by simpa only [Category.assoc, Category.id_comp] using hg) A.U.ι
    rw [← Category.assoc, hsg, hs, Category.comp_id]
  let : IsClosedImmersion (g ≫ A.p) := hgp.symm ▸ inferInstance
  let : IsClosedImmersion g := IsClosedImmersion.of_comp g A.p
  have hp : ProjSpace.π K A.Nd = projectiveStructure K (A.Nd+1) := by
    unfold ProjSpace.π projectiveStructure
    congr 2
  let := A.hιN_closed
  refine ⟨A.Nd, g ≫ A.ιN, inferInstance, ?_⟩
  rw [Category.assoc, ← hp, A.hoverN]
  exact hg

end Projectivity

/-- The intermediate completion keeps every geometric predicate and structural
equation used by the frozen `Compactification` target. It allows application to
each of the actual integral open-and-closed components. -/
structure CurveCompletion (K : Type u) [Field K] (C : Scheme.{u})
    (c : C ⟶ Spec (.of K)) where
  space : Scheme.{u}
  projection : space ⟶ Spec (.of K)
  inclusion : C ⟶ space
  over_eq : inclusion ≫ projection = c
  openImmersion : IsOpenImmersion inclusion
  dense : DenseRange inclusion.base
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  dimension : ℕ
  embedding : space ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace K (dimension+1)
  closedImmersion : IsClosedImmersion embedding
  embedding_over : embedding ≫
    ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure K (dimension+1) = projection

theorem integral_completion (K : Type u) [Field K] [CharZero K]
    (C : Scheme.{u}) [IsIntegral C] [CompactSpace C]
    (c : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c] [IsSeparated c] :
    Nonempty (CurveCompletion K C c) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  obtain ⟨M⟩ := FunctionFieldConstruction.exists_proper_model K C c
  obtain ⟨j, hj, hopen, hdense⟩ :=
    FunctionFieldConstruction.exists_openImmersion_to_model K C c M
  obtain ⟨n, e, hclosed, he⟩ := Projectivity.exists_embedding K M.C M.toBase
  exact ⟨{
    space := M.C
    projection := M.toBase
    inclusion := j
    over_eq := hj
    openImmersion := hopen
    dense := hdense
    proper := inferInstance
    smooth := inferInstance
    dimension := n
    embedding := e
    closedImmersion := hclosed
    embedding_over := he }⟩

theorem component_completion [CharZero k] (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    Nonempty (CurveCompletion k (componentOpen k L D Z hZ).toScheme
      ((componentOpen k L D Z hZ).ι ≫ openStructure k L D)) := by
  let := component_integral k L D Z hZ
  let := component_affine k L D Z hZ
  let := component_smooth k L D Z hZ
  let := openStructure_separated k L D
  exact integral_completion k _ _

/-- Each actual component has a proper smooth model of its function field.
The open immersion of the whole component and projective embedding remain
separate construction steps; this statement does not assert compactification. -/
theorem component_proper_model [CharZero k] (Z : Set (OpenBase k L D))
    (hZ : Z ∈ irreducibleComponents (OpenBase k L D)) :
    letI := component_integral k L D Z hZ
    let c := (componentOpen k L D Z hZ).ι ≫ openStructure k L D
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Nonempty (AlgebraicCurve.CurveModel k (componentOpen k L D Z hZ).toScheme.functionField) := by
  letI := component_integral k L D Z hZ
  letI := component_smooth k L D Z hZ
  exact FunctionFieldConstruction.exists_proper_model k _ _

/-- Nonemptiness is inherited from the actual compatible cover. This does not
assert that the quotient is integral or geometrically connected. -/
theorem openBase_nonempty [CharZero k] : Nonempty (OpenBase k L D) := by
  let := (ArithmeticThetaLegendreAtlasR0176.legendre_family_geometry k).1
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
      (ArithmeticThetaLegendreAtlasR0176.LegendreRing k))) := inferInstance
  obtain ⟨x, _⟩ := D.cover.surjective.surj z
  exact ⟨D.quotient.quotient.q x⟩

namespace FiniteAssembly

set_option maxHeartbeats 1600000

open CategoryTheory.Limits HomogeneousLocalization
open ArithmeticThetaProjectiveEffectivityR0135
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A split graded quotient is surjective on the degree-zero local rings. -/
theorem localRingHom_surjective_of_split
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (𝒜 : ℕ → Submodule k A) (ℬ : ℕ → Submodule k B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ b, f (g b) = b)
    (p : ProjectiveSpectrum ℬ) :
    Function.Surjective (HomogeneousLocalization.localRingHom f
      (p.asHomogeneousIdeal.toIdeal.comap f) p.asHomogeneousIdeal.toIdeal rfl) := by
  intro z
  obtain ⟨⟨n, a, b, hb⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  let w : NumDenSameDeg 𝒜 (p.asHomogeneousIdeal.toIdeal.comap f).primeCompl :=
    ⟨n, ⟨g a, g.map_mem a.2⟩, ⟨g b, g.map_mem b.2⟩, by
      change f (g b) ∉ p.asHomogeneousIdeal.toIdeal
      change (b : B) ∉ p.asHomogeneousIdeal.toIdeal at hb
      simpa only [hfg] using hb⟩
  refine ⟨HomogeneousLocalization.mk w, ?_⟩
  apply HomogeneousLocalization.val_injective
  simp [w, HomogeneousLocalization.val_localRingHom,
    HomogeneousLocalization.val_mk, Localization.localRingHom_mk, hfg]

variable {k}

/-- Retain exactly the coordinates in an injective block. -/
def blockQuotient {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e) :
    MvPolynomial.homogeneousSubmodule (Fin b) k →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin a) k where
  __ := (MvPolynomial.killCompl (R := k) he).toRingHom
  map_mem {i} {p} hp := by
    classical
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    let v : Fin b → MvPolynomial (Fin a) k := fun j =>
      if h : j ∈ Set.range e then MvPolynomial.X ((Equiv.ofInjective e he).symm ⟨j, h⟩) else 0
    have hv : ∀ j, (v j).IsHomogeneous 1 := by
      intro j
      dsimp only [v]
      split_ifs
      · exact MvPolynomial.isHomogeneous_X _ _
      · exact MvPolynomial.isHomogeneous_zero _ _ _
    change ((MvPolynomial.killCompl (R := k) he) p).IsHomogeneous i
    unfold MvPolynomial.killCompl
    convert hp.aeval v hv using 1
    · congr 2
      funext j
      dsimp only [v]
      split_ifs <;> rfl
    · exact (one_mul i).symm

def blockSection {a b : ℕ} (e : Fin a → Fin b) :
    MvPolynomial.homogeneousSubmodule (Fin a) k →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin b) k where
  __ := (MvPolynomial.rename e).toRingHom
  map_mem hp := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).rename_isHomogeneous

theorem block_split {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e)
    (p : MvPolynomial (Fin a) k) :
    blockQuotient e he (blockSection e p) = p :=
  MvPolynomial.killCompl_rename_app he p

theorem block_irrelevant {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin a) k) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin b) k)).map
        (blockQuotient e he) := by
  intro p hp
  rw [← block_split e he p]
  apply Ideal.mem_map_of_mem
  change blockSection e p ∈ HomogeneousIdeal.irrelevant _
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp ⊢
  change ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin b) k) (blockSection e p) 0).val) = 0
  rw [← GradedRingHom.map_directSumDecompose]
  change ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin a) k) p 0).val) = 0 at hp
  rw [hp, map_zero]

def blockMap {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e) :
    projectiveSpace k a ⟶ projectiveSpace k b :=
  Proj.map (blockQuotient e he) (block_irrelevant e he)


theorem blockMap_over {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e) :
    blockMap (k := k) e he ≫ projectiveStructure k b = projectiveStructure k a := by
  unfold blockMap
  refine (Proj.mapAffineOpenCover _ (block_irrelevant (k := k) e he)).openCover.hom_ext _ _ fun t => ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc _ _ t.1.2 _ t.2.2]
  unfold projectiveStructure
  simp only [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext r
  change (Away.map (blockQuotient (k := k) e he) t.2.1
    (HomogeneousLocalization.mk _)).val = (HomogeneousLocalization.mk _).val
  rw [Away.map, HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  · exact MvPolynomial.killCompl_C he r
  · exact Subtype.ext (map_one _)

theorem blockMap_injective {a b : ℕ} (e : Fin a → Fin b) (he : Function.Injective e) :
    Function.Injective (blockMap (k := k) e he) := by
  intro x y h
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  ext p
  have hh := congrArg (fun z : projectiveSpace k b =>
    blockSection (k := k) e p ∈ z.asHomogeneousIdeal) h
  change (blockQuotient e he (blockSection e p) ∈ x.asHomogeneousIdeal) =
    (blockQuotient e he (blockSection e p) ∈ y.asHomogeneousIdeal) at hh
  change p ∈ x.asHomogeneousIdeal ↔ p ∈ y.asHomogeneousIdeal
  simpa only [block_split] using Iff.of_eq hh

theorem blockMap_stalk_surjective {a b : ℕ} (e : Fin a → Fin b)
    (he : Function.Injective e) : SurjectiveOnStalks (blockMap (k := k) e he) := by
  constructor
  intro x
  change Function.Surjective ((Proj.sheafedSpaceMap (blockQuotient e he)
    (block_irrelevant (k := k) e he)).hom.stalkMap x)
  rw [← Proj.localRingHom_comp_stalkIso]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, CommRingCat.hom_ofHom]
  exact (ConcreteCategory.bijective_of_isIso (Proj.stalkIso _ x).inv).2.comp
    ((localRingHom_surjective_of_split k _ _ (blockQuotient e he) (blockSection e)
      (block_split e he) x).comp (ConcreteCategory.bijective_of_isIso
        (Proj.stalkIso _ (ProjectiveSpectrum.comap (blockQuotient e he) (block_irrelevant e he) x)).hom).2)

theorem blockMap_closedImmersion {a b : ℕ} (e : Fin (a+1) → Fin (b+1))
    (he : Function.Injective e) : IsClosedImmersion (blockMap (k := k) e he) := by
  have hπ (n : ℕ) : projectiveStructure k (n+1) = ProjSpace.π k n := by
    unfold projectiveStructure ProjSpace.π
    congr 2
  let : IsProper (projectiveStructure k (a+1)) := hπ a ▸ inferInstance
  let : IsSeparated (projectiveStructure k (b+1)) := hπ b ▸ inferInstance
  let : IsProper (blockMap (k := k) e he ≫ projectiveStructure k (b+1)) :=
    (blockMap_over (k := k) e he).symm ▸ inferInstance
  let : IsProper (blockMap (k := k) e he) := IsProper.of_comp _ (projectiveStructure k (b+1))
  let := blockMap_stalk_surjective (k := k) e he
  let : Mono (blockMap (k := k) e he) :=
    SurjectiveOnStalks.mono_of_injective (blockMap_injective e he)
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩


/-- Pairwise disjoint closed immersions form a closed immersion of the finite
coproduct. No connectedness hypothesis is needed. -/
theorem sigma_closedImmersion {I : Type u} [Finite I]
    {X : I → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    [∀ i, IsClosedImmersion (f i)]
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))) :
    IsClosedImmersion (Sigma.desc f) := by
  have hinj : Function.Injective (Sigma.desc f) := by
    intro x y h
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk X).surjective y
    simp only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc] at h ⊢
    obtain rfl : i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (hdisj hij) ⟨x, rfl⟩ ⟨y, h.symm⟩
    exact congrArg (Sigma.ι X i) ((f i).isClosedEmbedding.injective h)
  have hclosed : IsClosedMap (Sigma.desc f) := by
    intro S hS
    have heq : Sigma.desc f '' S = ⋃ i, f i '' ((Sigma.ι X i) ⁻¹' S) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
        simp only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
        exact Set.mem_iUnion.mpr ⟨i, x, by simpa only [Set.mem_preimage, sigmaMk_mk] using hx, rfl⟩
      · intro h
        obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp h
        exact ⟨Sigma.ι X i x, hx, by simp [← Scheme.Hom.comp_apply]⟩
    rw [heq]
    exact isClosed_iUnion_of_finite (fun i => (f i).isClosedEmbedding.isClosedMap _
      (hS.preimage (Sigma.ι X i).continuous))
  have hstalk : SurjectiveOnStalks (Sigma.desc f) := by
    apply IsZariskiLocalAtSource.of_openCover (sigmaOpenCover X)
    intro i
    simpa only [sigmaOpenCover_f, Sigma.ι_desc] using
      (inferInstance : SurjectiveOnStalks (f i))
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (Sigma.desc f).continuous hinj hclosed⟩

@[simp] theorem blockQuotient_X_image {a b : ℕ} (e : Fin a → Fin b)
    (he : Function.Injective e) (j : Fin a) :
    blockQuotient (k := k) e he (MvPolynomial.X (e j)) = MvPolynomial.X j := by
  change MvPolynomial.killCompl he (MvPolynomial.X (e j)) = MvPolynomial.X j
  simpa only [MvPolynomial.rename_X] using MvPolynomial.killCompl_rename_app he (MvPolynomial.X j)

theorem blockQuotient_X_outside {a b : ℕ} (e : Fin a → Fin b)
    (he : Function.Injective e) (j : Fin b) (hj : j ∉ Set.range e) :
    blockQuotient (k := k) e he (MvPolynomial.X j) = 0 := by
  classical
  change MvPolynomial.killCompl he (MvPolynomial.X j) = 0
  rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hj]

theorem blockMap_disjoint {a b n : ℕ} (e : Fin (a+1) → Fin (n+1))
    (f : Fin (b+1) → Fin (n+1)) (he : Function.Injective e) (hf : Function.Injective f)
    (hdisj : Disjoint (Set.range e) (Set.range f)) :
    Disjoint (Set.range (blockMap (k := k) e he)) (Set.range (blockMap (k := k) f hf)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hxy⟩
  have hx : ∃ j : Fin (a+1), MvPolynomial.X j ∉ x.asHomogeneousIdeal := by
    by_contra! h
    apply x.not_irrelevant_le
    exact (ProjSpace.irrelevant_le_span_X k a).trans
      (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j))
  obtain ⟨j, hj⟩ := hx
  have hnot : e j ∉ Set.range f := fun h => Set.disjoint_left.mp hdisj ⟨j, rfl⟩ h
  have hh := congrArg (fun z : projectiveSpace k (n+1) =>
    MvPolynomial.X (e j) ∈ z.asHomogeneousIdeal) hxy
  change (blockQuotient f hf (MvPolynomial.X (e j)) ∈ y.asHomogeneousIdeal) =
    (blockQuotient e he (MvPolynomial.X (e j)) ∈ x.asHomogeneousIdeal) at hh
  rw [blockQuotient_X_outside f hf _ hnot, blockQuotient_X_image] at hh
  exact hj (hh ▸ y.asHomogeneousIdeal.zero_mem)


/-- Embed all members of a finite family in disjoint coordinate blocks of one
finite-dimensional projective space, retaining their maps to the field. -/
theorem sigma_embedding {I : Type u} [Fintype I]
    (X : I → Scheme.{u}) (c : ∀ i, X i ⟶ Spec (.of k))
    (n : I → ℕ) (e : ∀ i, X i ⟶ projectiveSpace k (n i+1))
    [∀ i, IsClosedImmersion (e i)]
    (he : ∀ i, e i ≫ projectiveStructure k (n i+1) = c i) :
    ∃ (N : ℕ) (E : (∐ X) ⟶ projectiveSpace k (N+1)),
      IsClosedImmersion E ∧ E ≫ projectiveStructure k (N+1) = Sigma.desc c := by
  classical
  let N := Fintype.card (Σ i, Fin (n i+1))
  let a : ∀ i, Fin (n i+1) → Fin (N+1) := fun i j =>
    (Fintype.equivFin (Σ i, Fin (n i+1)) ⟨i, j⟩).castSucc
  have ha : ∀ i, Function.Injective (a i) := by
    intro i j l h
    have h' := (Fintype.equivFin _).injective (Fin.castSucc_injective N h)
    exact eq_of_heq (Sigma.mk.inj h').2
  let f : ∀ i, X i ⟶ projectiveSpace k (N+1) := fun i => e i ≫ blockMap (a i) (ha i)
  let : ∀ i, IsClosedImmersion (f i) := fun i => by
    let := blockMap_closedImmersion (k := k) (a i) (ha i)
    dsimp only [f]
    infer_instance
  have hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) := by
    intro i j hij
    have hab : Disjoint (Set.range (a i)) (Set.range (a j)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ ⟨y, h⟩
      have h' := (Fintype.equivFin _).injective (Fin.castSucc_injective N h)
      exact hij (congrArg Sigma.fst h').symm
    exact (blockMap_disjoint (k := k) (a i) (a j) (ha i) (ha j) hab).mono
      (by rintro _ ⟨x, rfl⟩; exact ⟨e i x, rfl⟩)
      (by rintro _ ⟨x, rfl⟩; exact ⟨e j x, rfl⟩)
  refine ⟨N, Sigma.desc f, sigma_closedImmersion f hdisj, ?_⟩
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
  dsimp only [f]
  rw [Category.assoc, blockMap_over, he]

/-- Density of each summand implies density of the induced coproduct map. -/
theorem sigma_dense {I : Type u} (X Y : I → Scheme.{u})
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, DenseRange (f i)) :
    DenseRange (Sigma.desc (fun i => f i ≫ Sigma.ι Y i)) := by
  intro y
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk Y).surjective y
  rw [sigmaMk_mk]
  apply closure_mono (s := Sigma.ι Y i '' Set.range (f i)) ?_
    (image_closure_subset_closure_image (Sigma.ι Y i).continuous ⟨y, hf i y, rfl⟩)
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨Sigma.ι X i x, ?_⟩
  change (Sigma.ι X i ≫ Sigma.desc _) x = (f i ≫ Sigma.ι Y i) x
  rw [Sigma.ι_desc]


/-- Complete the full finite disjoint union of actual components. -/
theorem complete_quotient (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (D : LevelData k L) : Nonempty (Compactification k L D) := by
  classical
  let I := {Z : Set (OpenBase k L D) // Z ∈ irreducibleComponents (OpenBase k L D)}
  let : Fintype I := (openBase_finite_components k L D).fintype
  let U : I → (OpenBase k L D).Opens := fun i => componentOpen k L D i.1 i.2
  let A : I → Scheme.{u} := fun i => (U i).toScheme
  let α : (∐ A) ⟶ OpenBase k L D := Sigma.desc (fun i => (U i).ι)
  have hdisjU : Pairwise (fun i j : I => Disjoint (Set.range (U i).ι) (Set.range (U j).ι)) := by
    intro i j hij
    simp only [Scheme.Opens.range_ι]
    change Disjoint i.1 j.1
    exact openBase_components_disjoint k L D i.1 j.1 i.2 j.2
      (fun h => hij (Subtype.ext h))
  let : IsOpenImmersion α := isOpenImmersion_sigmaDesc A _ hdisjU
  let : IsIso α := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply top_le_iff.mp
    intro x _
    let i : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let y : A i := ⟨x, mem_irreducibleComponent⟩
    refine ⟨Sigma.ι A i y, ?_⟩
    change (Sigma.ι A i ≫ α) y = x
    simp only [α, Sigma.ι_desc]
    rfl
  let C : ∀ i, CurveCompletion k (A i) ((U i).ι ≫ openStructure k L D) :=
    fun i => Classical.choice (component_completion k L D i.1 i.2)
  let X : I → Scheme.{u} := fun i => (C i).space
  let p : (∐ X) ⟶ Spec (.of k) := Sigma.desc (fun i => (C i).projection)
  let j : (∐ A) ⟶ (∐ X) := Sigma.desc (fun i => (C i).inclusion ≫ Sigma.ι X i)
  let : ∀ i, IsOpenImmersion (C i).inclusion := fun i => (C i).openImmersion
  let : ∀ i, IsClosedImmersion (C i).embedding := fun i => (C i).closedImmersion
  let : IsOpenImmersion j := by
    apply isOpenImmersion_sigmaDesc
    intro i l hil
    have h : Disjoint (Set.range (Sigma.ι X i)) (Set.range (Sigma.ι X l)) :=
      TopologicalSpace.Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι X i l hil)
    exact h.mono
      (by rintro _ ⟨x, rfl⟩; exact ⟨(C i).inclusion x, rfl⟩)
      (by rintro _ ⟨x, rfl⟩; exact ⟨(C l).inclusion x, rfl⟩)
  have hj : j ≫ p = α ≫ openStructure k L D := by
    apply Sigma.hom_ext
    intro i
    simp only [j, p, α, Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc, (C i).over_eq]
  have hdense : DenseRange j := sigma_dense A X (fun i => (C i).inclusion) (fun i => (C i).dense)
  obtain ⟨N, E, hE, hEp⟩ := sigma_embedding X (fun i => (C i).projection)
    (fun i => (C i).dimension) (fun i => (C i).embedding) (fun i => (C i).embedding_over)
  change E ≫ projectiveStructure k (N+1) = p at hEp
  let := hE
  let : SmoothOfRelativeDimension 1 p := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1) (sigmaOpenCover X)
    intro i
    simpa only [sigmaOpenCover_f, p, Sigma.ι_desc] using (C i).smooth
  have hπ : projectiveStructure k (N+1) = ProjSpace.π k N := by
    unfold projectiveStructure ProjSpace.π
    congr 2
  let : IsProper (projectiveStructure k (N+1)) := hπ ▸ inferInstance
  let : IsProper p := hEp ▸ inferInstanceAs (IsProper (E ≫ projectiveStructure k (N+1)))
  refine ⟨{
    space := ∐ X
    projection := p
    inclusion := inv α ≫ j
    over_eq := ?_
    openImmersion := inferInstance
    dense := ?_
    proper := inferInstance
    smooth := inferInstance
    dimension := N
    embedding := E
    closedImmersion := hE
    embedding_over := hEp }⟩
  · rw [Category.assoc, hj, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact hdense.comp (ConcreteCategory.bijective_of_isIso (inv α).base).2.denseRange j.continuous

end FiniteAssembly

end SmoothProjectiveLevelCompletionR0179

/-- The actual compatible full-level quotient admits a smooth projective
completion over every characteristic-zero field, with every component retained. -/
theorem smooth_projective_level_completion :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (D : LevelData k L), Nonempty (Compactification k L D) := by
  intro k _ _ L _ _ D
  exact SmoothProjectiveLevelCompletionR0179.FiniteAssembly.complete_quotient k L D

end ArithmeticThetaLevelCompactificationR0179

#print axioms ArithmeticThetaLevelCompactificationR0179.SmoothProjectiveLevelCompletionR0179.component_proper_model
#print axioms ArithmeticThetaLevelCompactificationR0179.SmoothProjectiveLevelCompletionR0179.openBase_component_isOpen
#print axioms ArithmeticThetaLevelCompactificationR0179.SmoothProjectiveLevelCompletionR0179.component_completion

#print axioms ArithmeticThetaLevelCompactificationR0179.smooth_projective_level_completion
