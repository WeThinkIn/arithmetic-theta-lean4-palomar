import ConstantExtensionDefinitionsR0225

/-! Descent of line morphisms over an arbitrary constant field.
The field-dependent constructions adapt the accepted r0221 proof; generic
frame, sheaf gluing, tensor and pullback-coherence providers are reused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base)
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms
open ArithmeticThetaLineRoot
open scoped TensorProduct
namespace LineHoms
variable {k : Type} [Field k]

theorem exists_finite_stage (K0 : (FieldStage k)) [FiniteDimensional k K0]
    (S : Finset (Omega k)) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧ ∀ x ∈ S, x ∈ K := by
  let F : (FieldStage k) := IntermediateField.adjoin k (S : Set (Omega k))
  have : FiniteDimensional k F := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x |>.isIntegral)
  refine ⟨K0 ⊔ F, inferInstance, le_sup_left, ?_⟩
  intro x hx
  exact (show F ≤ K0 ⊔ F from le_sup_right)
    (IntermediateField.subset_adjoin k (S : Set (Omega k)) hx)

theorem constantMap_extension {K K' : (FieldStage k)} (h : K ≤ K') :
    constantMap K' ≫ extensionMap h = constantMap K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

def enlargedCurve {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') : Curve K' where
  space := pullback M.curve.map (extensionMap h)
  map := pullback.snd _ _
  proper := by
    let := M.curve.proper
    infer_instance
  smooth := by
    let := M.curve.smooth
    let := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  geometricallyIntegral := by
    let := M.curve.geometricallyIntegral
    infer_instance

def enlargedProjection {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') : X.space ⟶ (enlargedCurve M h).space :=
  pullback.lift M.projection (X.map ≫ constantMap K') (by
    rw [Category.assoc, constantMap_extension]
    exact M.cartesian.w)

def enlargedModel {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') : Model X K' where
  curve := enlargedCurve M h
  projection := enlargedProjection M h
  cartesian := by
    apply IsPullback.of_right (h₁₂ := pullback.fst M.curve.map (extensionMap h))
      (h₂₂ := extensionMap h)
    · simpa only [enlargedProjection, pullback.lift_fst, constantMap_extension]
        using M.cartesian
    · exact pullback.lift_snd _ _ _
    · exact IsPullback.of_hasPullback _ _

def enlargement {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') : Refinement M (enlargedModel M h) where
  inclusion := h
  map := pullback.fst _ _
  cartesian := IsPullback.of_hasPullback _ _
  comparison := pullback.lift_fst _ _ _

abbrev stageAlgebra {K0 K : (FieldStage k)} (h : K0 ≤ K) : Algebra K0 K :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

def stageEmbedding {K0 K : (FieldStage k)} (h : K0 ≤ K) :
    letI := stageAlgebra h
    K →ₗ[K0] (Omega k) := by
  letI := stageAlgebra h
  exact { toFun := fun x => x.val
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }

open scoped TensorProduct

theorem extensionMap_refl (K : (FieldStage k)) : extensionMap (le_refl K) = 𝟙 (Base K) := by
  unfold extensionMap
  simp

def identityRefinement {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    Refinement M M where
  inclusion := le_refl K
  map := 𝟙 M.curve.space
  cartesian := by
    rw [extensionMap_refl]
    exact IsPullback.of_id_fst
  comparison := Category.comp_id _

theorem model_compact {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    CompactSpace M.curve.space := by
  let := M.curve.proper
  exact QuasiCompact.compactSpace_of_compactSpace M.curve.map

theorem model_pairFrameCover {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    (J H : M.curve.space.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space J)
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space H) :
    Nonempty (PairFrameCover M.curve.space J H) := by
  let := model_compact M
  exact exists_pairFrameCover M.curve.space J H hJ hH

theorem model_chart_pushout {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (chartConstants M.curve U)) (CommRingCat.ofHom K.subtype)
      (M.projection.app U)
      ((Scheme.ΓSpecIso (CommRingCat.of (Omega k))).inv ≫
        X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp)) := by
  exact curve_chart_pushout X M.curve K.subtype M.projection M.cartesian U hU

def modelChartTensorIso {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := (chartConstants M.curve U).toAlgebra
    CommRingCat.of ((Omega k) ⊗[K] Γ(M.curve.space, U)) ≅ Γ(X.space, M.projection ⁻¹ᵁ U) := by
  letI := (chartConstants M.curve U).toAlgebra
  exact (CommRingCat.isPushout_tensorProduct K (Omega k) Γ(M.curve.space, U)).flip.isoPushout ≪≫
    (model_chart_pushout M U hU).isoPushout.symm

theorem modelChartTensorIso_left {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    let := (chartConstants M.curve U).toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      (Omega k) →+* (Omega k) ⊗[K] Γ(M.curve.space, U)) ≫ (modelChartTensorIso M U hU).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (Omega k))).inv ≫
        X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp) := by
  let := (chartConstants M.curve U).toAlgebra
  exact ((CommRingCat.isPushout_tensorProduct K (Omega k) Γ(M.curve.space, U)).flip.inr_isoPushout_hom_assoc
    (model_chart_pushout M U hU).isoPushout.inv).trans
    (model_chart_pushout M U hU).inr_isoPushout_inv

theorem modelChartTensorIso_right {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    let := (chartConstants M.curve U).toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      Γ(M.curve.space, U) →+* (Omega k) ⊗[K] Γ(M.curve.space, U)) ≫
        (modelChartTensorIso M U hU).hom = M.projection.app U := by
  let := (chartConstants M.curve U).toAlgebra
  exact ((CommRingCat.isPushout_tensorProduct K (Omega k) Γ(M.curve.space, U)).flip.inl_isoPushout_hom_assoc
    (model_chart_pushout M U hU).isoPushout.inv).trans
    (model_chart_pushout M U hU).inl_isoPushout_inv

theorem modelChartTensorIso_tmul {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U)
    (c : (Omega k)) (r : Γ(M.curve.space, U)) :
    let := (chartConstants M.curve U).toAlgebra
    (modelChartTensorIso M U hU).hom (c ⊗ₜ[K] r) =
      X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp)
        ((Scheme.ΓSpecIso (CommRingCat.of (Omega k))).inv c) * M.projection.app U r := by
  let := (chartConstants M.curve U).toAlgebra
  have hl := ConcreteCategory.congr_hom (modelChartTensorIso_left M U hU) c
  have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
  change (modelChartTensorIso M U hU).hom (c ⊗ₜ[K] 1) = _ at hl
  change (modelChartTensorIso M U hU).hom (1 ⊗ₜ[K] r) = _ at hr
  rw [show c ⊗ₜ[K] r = (c ⊗ₜ[K] 1) * (1 ⊗ₜ[K] r) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, hl, hr]
  rfl

theorem model_projection_app_injective {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    Function.Injective (M.projection.app U) := by
  let := (chartConstants M.curve U).toAlgebra
  intro r t h
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := (Omega k))
    Γ(M.curve.space, U)
  apply (modelChartTensorIso M U hU).commRingCatIsoToRingEquiv.injective
  have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
  have ht := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) t
  exact hr.trans (h.trans ht.symm)

def stageChartMap {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) :
    Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U) ⟶
      Γ(X.space, M.projection ⁻¹ᵁ U) :=
  (enlargedModel M h).projection.appLE ((enlargement M h).map ⁻¹ᵁ U)
    (M.projection ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])

theorem stageChartMap_base {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) (r : Γ(M.curve.space, U)) :
    stageChartMap M h U ((enlargement M h).map.app U r) = M.projection.app U r := by
  have he := (enlargedModel M h).projection.appLE_comp_appLE (enlargement M h).map
    U ((enlargement M h).map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) le_rfl
    (by rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])
  simp only [(enlargement M h).comparison, Scheme.Hom.appLE_eq_app] at he
  exact ConcreteCategory.congr_hom he r

theorem stageChartMap_constant {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) (c : K') :
    stageChartMap M h U
      (chartConstants (enlargedModel M h).curve ((enlargement M h).map ⁻¹ᵁ U) c) =
      chartConstants X (M.projection ⁻¹ᵁ U) c.val :=
  chartConstants_comp X (enlargedModel M h).curve K'.subtype (enlargedModel M h).projection
    (enlargedModel M h).cartesian.w _ _ _ c

theorem finite_chart_functions {X : Curve (Omega k)} (K0 : (FieldStage k))
    [FiniteDimensional k K0] (M : Model X K0) (I : Type) [Fintype I]
    (U : I → M.curve.space.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : ℕ) (a : ∀ i, Fin s → Γ(X.space, M.projection ⁻¹ᵁ U i)) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ ∃ h : K0 ≤ K,
      ∃ b : ∀ i, Fin s → Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U i),
        ∀ i j, stageChartMap M h (U i) (b i j) = a i j := by
  classical
  let (i : I) : Algebra K0 Γ(M.curve.space, U i) := (chartConstants M.curve (U i)).toAlgebra
  choose T hT using fun i j => TensorProduct.exists_finset
    ((modelChartTensorIso M (U i) (hU i)).inv (a i j))
  let S : Finset (Omega k) := Finset.univ.biUnion
    (fun i => Finset.univ.biUnion (fun j => (T i j).image Prod.fst))
  obtain ⟨K, hK, h, hc⟩ := exists_finite_stage K0 S
  have hc' (i : I) (j : Fin s) (t : T i j) : t.val.1 ∈ K := by
    apply hc
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨t.val, t.property, rfl⟩⟩⟩
  refine ⟨K, hK, h, fun i j => ∑ t : T i j,
    chartConstants (enlargedModel M h).curve ((enlargement M h).map ⁻¹ᵁ U i)
      (⟨t.val.1, hc' i j t⟩ : K) * (enlargement M h).map.app (U i) t.val.2, ?_⟩
  intro i j
  simp only [map_sum, map_mul, stageChartMap_constant, stageChartMap_base]
  have he := congrArg (fun x => (modelChartTensorIso M (U i) (hU i)).hom x) (hT i j)
  have hid := ConcreteCategory.congr_hom (modelChartTensorIso M (U i) (hU i)).inv_hom_id (a i j)
  change (modelChartTensorIso M (U i) (hU i)).hom
    ((modelChartTensorIso M (U i) (hU i)).inv (a i j)) = a i j at hid
  rw [hid] at he
  simp only [map_sum] at he
  rw [Finset.sum_coe_sort (T i j)
    (fun t => chartConstants X (M.projection ⁻¹ᵁ U i) t.1 * M.projection.app (U i) t.2)]
  rw [he]
  apply Finset.sum_congr rfl
  intro t ht
  exact (modelChartTensorIso_tmul M (U i) (hU i) t.1 t.2).symm

theorem model_projection_app_injective_all {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) : Function.Injective (M.projection.app U) := by
  intro r t h
  let I := {V : M.curve.space.Opens // V ≤ U ∧ IsAffineOpen V}
  apply TopCat.Sheaf.eq_of_locally_eq' M.curve.space.sheaf
    (fun V : I => V.val) U (fun V => homOfLE V.property.1)
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hxV⟩
  · intro V
    apply model_projection_app_injective M V.val V.property.2
    have hn := M.projection.naturality (homOfLE V.property.1).op
    have hr := ConcreteCategory.congr_hom hn r
    have ht := ConcreteCategory.congr_hom hn t
    exact hr.trans ((congrArg
      (fun z => X.space.presheaf.map
        ((TopologicalSpace.Opens.map M.projection.base).map (homOfLE V.property.1)).op z) h).trans ht.symm)

theorem model_projection_isUnit_iff {X : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) (r : Γ(M.curve.space, U)) :
    IsUnit (M.projection.app U r) ↔ IsUnit r := by
  let := (chartConstants M.curve U).toAlgebra
  constructor
  · intro h
    let e := (modelChartTensorIso M U hU).commRingCatIsoToRingEquiv
    have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
    have ht : IsUnit ((1 : (Omega k)) ⊗ₜ[K] r) := by
      apply (isUnit_map_iff e _).mp
      exact hr.symm ▸ h
    have ht' := ht.map (Algebra.TensorProduct.comm K (Omega k) Γ(M.curve.space, U)).toRingHom
    change IsUnit (r ⊗ₜ[K] (1 : (Omega k))) at ht'
    exact (isUnit_map_iff (algebraMap Γ(M.curve.space, U)
      (Γ(M.curve.space, U) ⊗[K] (Omega k))) r).mp ht'
  · exact fun h => h.map (M.projection.app U).hom

theorem model_projection_affine {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    IsAffineHom M.projection :=
  MorphismProperty.of_isPullback M.cartesian.flip (inferInstance : IsAffineHom (constantMap K))

theorem enlargement_affine {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K) (h : K ≤ K') :
    IsAffineHom (enlargement M h).map :=
  MorphismProperty.of_isPullback (enlargement M h).cartesian.flip
    (inferInstance : IsAffineHom (extensionMap h))

theorem stageChartMap_injective {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') (U : M.curve.space.Opens) :
    Function.Injective (stageChartMap M h U) := by
  exact appLE_injective_of_preimage_eq (enlargedModel M h).projection
    ((enlargement M h).map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])
    (model_projection_app_injective_all (enlargedModel M h) _)

theorem stageChartMap_restrict {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') (U V : M.curve.space.Opens) (hVU : V ≤ U)
    (r : Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U)) :
    stageChartMap M h V
      ((enlargedModel M h).curve.space.presheaf.map
        (homOfLE ((enlargement M h).map.preimage_mono hVU)).op r) =
      X.space.presheaf.map (homOfLE (M.projection.preimage_mono hVU)).op
        (stageChartMap M h U r) := by
  have hV : M.projection ⁻¹ᵁ V ≤ (enlargedModel M h).projection ⁻¹ᵁ
      ((enlargement M h).map ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison]
  have hU : M.projection ⁻¹ᵁ U ≤ (enlargedModel M h).projection ⁻¹ᵁ
      ((enlargement M h).map ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison]
  have h₁ := (enlargedModel M h).projection.map_appLE hV
    (homOfLE ((enlargement M h).map.preimage_mono hVU)).op
  have h₂ := (enlargedModel M h).projection.appLE_map hU
    (homOfLE (M.projection.preimage_mono hVU)).op
  exact ConcreteCategory.congr_hom (h₁.trans h₂.symm) r

abbrev modelFrameCover {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    PairFrameCover X.space ((Scheme.Modules.pullback M.projection).obj J)
      ((Scheme.Modules.pullback M.projection).obj H) := by
  letI := model_projection_affine M
  exact C.pullback M.projection

abbrev stageFrameCover {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K) (h : K ≤ K')
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    PairFrameCover (enlargedModel M h).curve.space ((Scheme.Modules.pullback (enlargement M h).map).obj J)
      ((Scheme.Modules.pullback (enlargement M h).map).obj H) := by
  letI := enlargement_affine M h
  exact C.pullback (enlargement M h).map

theorem stageChartMap_transition {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K) (h : K ≤ K')
    {J : M.curve.space.Modules} {U U' : M.curve.space.Opens}
    (e : LocalFrame M.curve.space J U) (e' : LocalFrame M.curve.space J U')
    (V : M.curve.space.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    stageChartMap M h V
      (transition ((pulledFrame (enlargement M h).map e).equiv _ ((enlargement M h).map.preimage_mono hVU))
        ((pulledFrame (enlargement M h).map e').equiv _ ((enlargement M h).map.preimage_mono hVU'))) =
      transition ((pulledFrame M.projection e).equiv _ (M.projection.preimage_mono hVU))
        ((pulledFrame M.projection e').equiv _ (M.projection.preimage_mono hVU')) := by
  rw [← transition_pulledFrame (enlargement M h).map e e' V hVU hVU', stageChartMap_base,
    transition_pulledFrame M.projection e e' V hVU hVU']

def descendedCoefficients {X : Curve (Omega k)} {K K' : (FieldStage k)} (M : Model X K) (h : K ≤ K')
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H)
    (c : CompatibleCoefficients (modelFrameCover M C))
    (b : ∀ i : C.index, Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ C.opens i))
    (hb : ∀ i, stageChartMap M h (C.opens i) (b i) = c.value i) :
    CompatibleCoefficients (stageFrameCover M h C) where
  value := b
  overlap i j := by
    apply stageChartMap_injective M h (C.opens i ⊓ C.opens j)
    simp only [map_mul]
    change stageChartMap M h (C.opens i ⊓ C.opens j)
      (transition ((pulledFrame (enlargement M h).map (C.targetFrame i)).equiv _ _)
        ((pulledFrame (enlargement M h).map (C.targetFrame j)).equiv _ _)) * _ =
      stageChartMap M h (C.opens i ⊓ C.opens j)
      (transition ((pulledFrame (enlargement M h).map (C.sourceFrame i)).equiv _ _)
        ((pulledFrame (enlargement M h).map (C.sourceFrame j)).equiv _ _)) * _
    rw [stageChartMap_transition M h (C.targetFrame i) (C.targetFrame j)
      (C.opens i ⊓ C.opens j) inf_le_left inf_le_right,
      stageChartMap_transition M h (C.sourceFrame i) (C.sourceFrame j)
      (C.opens i ⊓ C.opens j) inf_le_left inf_le_right]
    erw [stageChartMap_restrict M h (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right (b j),
      stageChartMap_restrict M h (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left (b i)]
    rw [hb, hb]
    exact c.overlap i j

theorem refinement_preimage {X : Curve (Omega k)} {K K' : (FieldStage k)} {M : Model X K} {N : Model X K'}
    (E : Refinement M N) (U : M.curve.space.Opens) :
    M.projection ⁻¹ᵁ U = N.projection ⁻¹ᵁ (E.map ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, E.comparison]

theorem refinementComparison_unit {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N)
    (J : M.curve.space.Modules) (U : M.curve.space.Opens) (s : Γ(J, U)) :
    (refinementComparison E J).hom.app (M.projection ⁻¹ᵁ U)
      (pullbackSectionLE N.projection ((Scheme.Modules.pullback E.map).obj J)
        (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le
        (ArithmeticThetaNormalizedSections.pullbackLocalSection E.map J U s)) =
      ArithmeticThetaNormalizedSections.pullbackLocalSection M.projection J U s := by
  have h₁ := pullbackComp_hom_sectionLE N.projection E.map J U (E.map ⁻¹ᵁ U)
    (M.projection ⁻¹ᵁ U) le_rfl (refinement_preimage E U).le s
  simp only [pullbackSectionLE_full] at h₁
  have h₂ := pullbackCongr_sectionLE E.comparison J U (M.projection ⁻¹ᵁ U)
    (refinement_preimage E U).le s
  have h₃ := pullbackSectionLE_full M.projection J U s
  exact (congrArg (((Scheme.Modules.pullbackCongr E.comparison).app J).hom.app
    (M.projection ⁻¹ᵁ U)) h₁).trans (h₂.trans h₃)

theorem refinementComparison_frame {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N)
    {J : M.curve.space.Modules} {U : M.curve.space.Opens} (e : LocalFrame M.curve.space J U)
    (r : Γ(N.curve.space, E.map ⁻¹ᵁ U)) :
    (refinementComparison E J).hom.app (M.projection ⁻¹ᵁ U)
      (pullbackSectionLE N.projection ((Scheme.Modules.pullback E.map).obj J)
        (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le
        ((pulledFrame E.map e).equiv (E.map ⁻¹ᵁ U) le_rfl r)) =
      (pulledFrame M.projection e).equiv (M.projection ⁻¹ᵁ U) le_rfl
        (N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le r) := by
  have he : (pulledFrame E.map e).equiv (E.map ⁻¹ᵁ U) le_rfl r =
      r • ArithmeticThetaNormalizedSections.pullbackLocalSection E.map J U (e.equiv U le_rfl 1) := by
    rw [pulledFrame_compatible E.map e U le_rfl 1, map_one]
    simpa using ((pulledFrame E.map e).equiv (E.map ⁻¹ᵁ U) le_rfl).map_smul r 1
  rw [he, pullbackSectionLE_smul, Scheme.Modules.Hom.app_smul, refinementComparison_unit,
    pulledFrame_compatible M.projection e U le_rfl 1, map_one]
  simpa using (((pulledFrame M.projection e).equiv (M.projection ⁻¹ᵁ U) le_rfl).map_smul
    (N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le r) 1).symm

def refinedHom {X : Curve (Omega k)} {K K' : (FieldStage k)} {M : Model X K} {N : Model X K'}
    (E : Refinement M N) {J H : M.curve.space.Modules}
    (b : (Scheme.Modules.pullback E.map).obj J ⟶ (Scheme.Modules.pullback E.map).obj H) :
    (Scheme.Modules.pullback M.projection).obj J ⟶ (Scheme.Modules.pullback M.projection).obj H :=
  (refinementComparison E J).inv ≫ (Scheme.Modules.pullback N.projection).map b ≫
    (refinementComparison E H).hom

theorem homCoordinate_refinedHom {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N)
    {J H : M.curve.space.Modules} {U : M.curve.space.Opens}
    (e : LocalFrame M.curve.space J U) (f : LocalFrame M.curve.space H U)
    (b : (Scheme.Modules.pullback E.map).obj J ⟶ (Scheme.Modules.pullback E.map).obj H) :
    homCoordinate (pulledFrame M.projection e) (pulledFrame M.projection f)
      (refinedHom E b) (M.projection ⁻¹ᵁ U) le_rfl =
    N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le
      (homCoordinate (pulledFrame E.map e) (pulledFrame E.map f) b (E.map ⁻¹ᵁ U) le_rfl) := by
  apply ((pulledFrame M.projection f).equiv (M.projection ⁻¹ᵁ U) le_rfl).injective
  simp only [homCoordinate, LinearEquiv.apply_symm_apply]
  have he := refinementComparison_frame E e 1
  simp only [map_one] at he
  rw [← he]
  change (refinementComparison E H).hom.app (M.projection ⁻¹ᵁ U)
      (((Scheme.Modules.pullback N.projection).map b).app (M.projection ⁻¹ᵁ U)
        ((refinementComparison E J).inv.app (M.projection ⁻¹ᵁ U)
          ((refinementComparison E J).hom.app (M.projection ⁻¹ᵁ U) _))) = _
  have hid := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (M.projection ⁻¹ᵁ U)) (refinementComparison E J).hom_inv_id)
    (pullbackSectionLE N.projection ((Scheme.Modules.pullback E.map).obj J)
      (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) (refinement_preimage E U).le
      ((pulledFrame E.map e).equiv (E.map ⁻¹ᵁ U) le_rfl 1))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hid
  rw [hid, pullbackSectionLE_map,
    homCoordinate_apply (pulledFrame E.map e) (pulledFrame E.map f) b _ le_rfl 1, one_mul]
  simp only [LinearEquiv.symm_apply_apply]
  exact refinementComparison_frame E f _

theorem descendedCoefficients_refinedHom {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (h : K ≤ K') {J H : M.curve.space.Modules}
    (C : PairFrameCover M.curve.space J H) (c : CompatibleCoefficients (modelFrameCover M C))
    (b : ∀ i : C.index, Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ C.opens i))
    (hb : ∀ i, stageChartMap M h (C.opens i) (b i) = c.value i) :
    refinedHom (enlargement M h) (descendedCoefficients M h C c b hb).hom = c.hom := by
  apply pairFrameCover_hom_ext (modelFrameCover M C)
  intro i
  rw [c.hom_coordinate]
  change homCoordinate (pulledFrame M.projection (C.sourceFrame i))
    (pulledFrame M.projection (C.targetFrame i)) _ (M.projection ⁻¹ᵁ C.opens i) le_rfl = _
  rw [homCoordinate_refinedHom]
  have hd := (descendedCoefficients M h C c b hb).hom_coordinate i
  change homCoordinate (pulledFrame (enlargement M h).map (C.sourceFrame i))
    (pulledFrame (enlargement M h).map (C.targetFrame i)) _
      ((enlargement M h).map ⁻¹ᵁ C.opens i) le_rfl = b i at hd
  rw [hd]
  exact hb i

theorem model_pullback_hom_injective {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    Function.Injective (fun b : J ⟶ H => (Scheme.Modules.pullback M.projection).map b) := by
  intro b d hbd
  dsimp only at hbd
  apply pairFrameCover_hom_ext C
  intro i
  apply model_projection_app_injective_all M (C.opens i)
  rw [homCoordinate_pullback, homCoordinate_pullback, hbd]

theorem model_pullback_isIso_iff {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) (b : J ⟶ H) :
    IsIso ((Scheme.Modules.pullback M.projection).map b) ↔ IsIso b := by
  constructor
  · intro hb
    let := hb
    have hu (i : C.index) : IsUnit ((morphismCoefficients C b).value i) := by
      apply (model_projection_isUnit_iff M (C.opens i) (C.affine i) _).mp
      change IsUnit (M.projection.app (C.opens i)
        (homCoordinate (C.sourceFrame i) (C.targetFrame i) b (C.opens i) le_rfl))
      rw [homCoordinate_pullback]
      exact homCoordinate_isUnit _ _ _ _ _
    have hi := (morphismCoefficients C b).isIso_hom hu
    simpa only [morphismCoefficients_hom] using hi
  · intro hb
    let := hb
    infer_instance

theorem refinedHom_injective {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) {J H : M.curve.space.Modules}
    (C : PairFrameCover N.curve.space ((Scheme.Modules.pullback E.map).obj J)
      ((Scheme.Modules.pullback E.map).obj H)) :
    Function.Injective (fun b => refinedHom E (J := J) (H := H) b) := by
  intro b d hbd
  apply model_pullback_hom_injective N C
  apply (cancel_epi (refinementComparison E J).inv).mp
  apply (cancel_mono (refinementComparison E H).hom).mp
  simpa only [refinedHom, Category.assoc] using hbd

theorem refinedHom_isIso_iff {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) {J H : M.curve.space.Modules}
    (C : PairFrameCover N.curve.space ((Scheme.Modules.pullback E.map).obj J)
      ((Scheme.Modules.pullback E.map).obj H))
    (b : (Scheme.Modules.pullback E.map).obj J ⟶ (Scheme.Modules.pullback E.map).obj H) :
    IsIso (refinedHom E b) ↔ IsIso b := by
  simp only [refinedHom, isIso_comp_left_iff, isIso_comp_right_iff]
  exact model_pullback_isIso_iff N C b

end LineHoms
open LineHoms

theorem line_homs_constant_extension (k : Type) [Field k] [CharZero k] (X : Curve (Omega k)) (K0 : (FieldStage k))
    (hK0 : FiniteDimensional k K0) (M : Model X K0) (J H : M.curve.space.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space J)
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space H)
    (s : ℕ) (a : Fin s → ((Scheme.Modules.pullback M.projection).obj J ⟶
      (Scheme.Modules.pullback M.projection).obj H)) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ ∃ (M1 : Model X K) (E : Refinement M M1)
      (a0 : Fin s → ((Scheme.Modules.pullback E.map).obj J ⟶
        (Scheme.Modules.pullback E.map).obj H)),
      (∀ i, (Scheme.Modules.pullback M1.projection).map (a0 i) ≫
        (refinementComparison E H).hom = (refinementComparison E J).hom ≫ a i) ∧
      (∀ i, IsIso (a0 i) ↔ IsIso (a i)) ∧
      (∀ i j, a0 i = a0 j ↔ a i = a j) := by
  classical
  let := hK0
  obtain ⟨C⟩ := model_pairFrameCover M J H hJ hH
  let : Fintype C.index := C.finite
  let c (j : Fin s) := morphismCoefficients (modelFrameCover M C) (a j)
  obtain ⟨K, hK, h, b, hb⟩ := finite_chart_functions K0 M C.index C.opens C.affine s
    (fun i j => (c j).value i)
  let d (j : Fin s) := descendedCoefficients M h C (c j) (fun i => b i j) (fun i => hb i j)
  let a0 := fun j => (d j).hom
  have ha (j : Fin s) : refinedHom (enlargement M h) (a0 j) = a j :=
    (descendedCoefficients_refinedHom M h C (c j) (fun i => b i j) (fun i => hb i j)).trans
      (morphismCoefficients_hom (modelFrameCover M C) (a j))
  refine ⟨K, hK, enlargedModel M h, enlargement M h, a0, ?_, ?_, ?_⟩
  · intro j
    have hh := congrArg (fun t => (refinementComparison (enlargement M h) J).hom ≫ t) (ha j)
    simpa only [LineHoms.refinedHom, Iso.hom_inv_id_assoc] using hh
  · intro j
    have hi := (refinedHom_isIso_iff (enlargement M h) (stageFrameCover M h C) (a0 j)).symm
    rwa [ha j] at hi
  · intro i j
    constructor
    · intro hij
      rw [← ha i, ← ha j, hij]
    · intro hij
      apply refinedHom_injective (enlargement M h) (stageFrameCover M h C)
      exact (ha i).trans (hij.trans (ha j).symm)

end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.line_homs_constant_extension
