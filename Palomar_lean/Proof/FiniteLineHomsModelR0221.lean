module

public import FiniteFieldModelsDefinitionsR0221
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

/-! Finite-stage descent of finite families of actual line morphisms.
The construction retains the prescribed field, geometric refinement, canonical
pullback comparison, and equivalences for invertibility and equality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- A finite collection of algebraic coefficients fits in a finite extension
containing the prescribed initial field, with its actual rational action. -/
theorem exists_finite_stage (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (S : Finset Omega) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧ ∀ x ∈ S, x ∈ K := by
  let F : FieldStage := IntermediateField.adjoin ℚ (S : Set Omega)
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x |>.isIntegral)
  refine ⟨K0 ⊔ F, inferInstance, le_sup_left, ?_⟩
  intro x hx
  exact (show F ≤ K0 ⊔ F from le_sup_right)
    (IntermediateField.subset_adjoin ℚ (S : Set Omega) hx)

/-- Composition of the actual field-inclusion maps on spectra. -/
theorem constantMap_extension {K K' : FieldStage} (h : K ≤ K') :
    constantMap K' ≫ extensionMap h = constantMap K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The base change of an existing curve, retaining all geometric properties. -/
def enlargedCurve {X : Curve Omega} {K K' : FieldStage}
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

/-- Projection of the same algebraic-closure curve to the enlarged model. -/
def enlargedProjection {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (h : K ≤ K') : X.space ⟶ (enlargedCurve M h).space :=
  pullback.lift M.projection (X.map ≫ constantMap K') (by
    rw [Category.assoc, constantMap_extension]
    exact M.cartesian.w)

/-- The enlarged model has the required Cartesian scalar-extension square. -/
def enlargedModel {X : Curve Omega} {K K' : FieldStage}
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

/-- This is a refinement over the original model, with its literal comparison. -/
def enlargement {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (h : K ≤ K') : Refinement M (enlargedModel M h) where
  inclusion := h
  map := pullback.fst _ _
  cartesian := IsPullback.of_hasPullback _ _
  comparison := pullback.lift_fst _ _ _


/-- Scalars on an enlarged field come from the prescribed inclusion. -/
abbrev stageAlgebra {K0 K : FieldStage} (h : K0 ≤ K) : Algebra K0 K :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- The inclusion into the fixed algebraic closure as a linear map. -/
def stageEmbedding {K0 K : FieldStage} (h : K0 ≤ K) :
    letI := stageAlgebra h
    K →ₗ[K0] Omega := by
  letI := stageAlgebra h
  exact { toFun := fun x => x.val
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }

open scoped TensorProduct

/-- A finite family of actual tensors has preimages over one finite stage.
No finite-dimensionality of the coefficient module is assumed or needed. -/
theorem finite_tensor_family (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (V : Type) [AddCommGroup V] [Module K0 V] (s : ℕ)
    (a : Fin s → Omega ⊗[K0] V) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      letI := stageAlgebra h
      ∃ a0 : Fin s → K ⊗[K0] V,
        ∀ i, TensorProduct.map (stageEmbedding h) (LinearMap.id : V →ₗ[K0] V)
          (a0 i) = a i := by
  classical
  choose T hT using fun i => TensorProduct.exists_finset (a i)
  let S : Finset Omega := Finset.univ.biUnion (fun i => (T i).image Prod.fst)
  obtain ⟨K, hK, h, hS⟩ := exists_finite_stage K0 S
  refine ⟨K, hK, h, ?_⟩
  let := stageAlgebra h
  have hc (i : Fin s) (p : T i) : p.val.1 ∈ K := by
    apply hS
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
  refine ⟨fun i => ∑ p : T i, (⟨p.val.1, hc i p⟩ : K) ⊗ₜ[K0] p.val.2, ?_⟩
  intro i
  simp only [map_sum, TensorProduct.map_tmul, stageEmbedding, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_apply]
  exact (Finset.sum_coe_sort (T i)
    (fun p : Omega × V => p.1 ⊗ₜ[K0] p.2)).trans (hT i).symm


/-- The finite-stage coefficient map is injective, hence detects all equations. -/
theorem tensor_stage_injective {K0 K : FieldStage} (h : K0 ≤ K)
    (V : Type) [AddCommGroup V] [Module K0 V] :
    letI := stageAlgebra h
    Function.Injective (TensorProduct.map (stageEmbedding h) (LinearMap.id : V →ₗ[K0] V)) := by
  let := stageAlgebra h
  apply TensorProduct.map_injective_of_flat_flat
  · exact Subtype.val_injective
  · exact Function.injective_id

/-- The scalar extension map for the identity inclusion is the identity. -/
theorem extensionMap_refl (K : FieldStage) : extensionMap (le_refl K) = 𝟙 (Base K) := by
  unfold extensionMap
  simp

/-- The original model refines itself. -/
def identityRefinement {X : Curve Omega} {K : FieldStage} (M : Model X K) :
    Refinement M M where
  inclusion := le_refl K
  map := 𝟙 M.curve.space
  cartesian := by
    rw [extensionMap_refl]
    exact IsPullback.of_id_fst
  comparison := Category.comp_id _

/-- The empty-family boundary of the frozen obligation needs no enlargement. -/
theorem empty_family (X : Curve Omega) (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0)
    (M : Model X K0) (J H : M.curve.space.Modules)
    (a : Fin 0 → ((Scheme.Modules.pullback M.projection).obj J ⟶
      (Scheme.Modules.pullback M.projection).obj H)) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (M1 : Model X K) (E : Refinement M M1)
      (a0 : Fin 0 → ((Scheme.Modules.pullback E.map).obj J ⟶
        (Scheme.Modules.pullback E.map).obj H)),
      (∀ i, (Scheme.Modules.pullback M1.projection).map (a0 i) ≫
        (refinementComparison E H).hom = (refinementComparison E J).hom ≫ a i) ∧
      (∀ i, IsIso (a0 i) ↔ IsIso (a i)) ∧
      (∀ i j, a0 i = a0 j ↔ a i = a j) := by
  exact ⟨K0, hK0, M, identityRefinement M, Fin.elim0,
    (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩


open ArithmeticThetaLineRoot

/-- Coefficient of a genuine sheaf morphism in two given natural frames. -/
def homCoordinate {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a : J ⟶ H)
    (V : Y.Opens) (hVU : V ≤ U) : Γ(Y, V) :=
  (f.equiv V hVU).symm (a.app V (e.equiv V hVU 1))

/-- The coefficient determines the morphism on every section in that frame. -/
theorem homCoordinate_apply {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a : J ⟶ H)
    (V : Y.Opens) (hVU : V ≤ U) (r : Γ(Y, V)) :
    a.app V (e.equiv V hVU r) =
      f.equiv V hVU (r * homCoordinate e f a V hVU) := by
  have he : e.equiv V hVU r = r • e.equiv V hVU 1 := by
    simpa using (e.equiv V hVU).map_smul r (1 : Γ(Y, V))
  rw [he, Scheme.Modules.Hom.app_smul]
  change r • _ = f.equiv V hVU (r • homCoordinate e f a V hVU)
  rw [map_smul, homCoordinate, LinearEquiv.apply_symm_apply]

/-- These coefficients restrict along the actual structure-sheaf restriction. -/
theorem homCoordinate_restrict {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a : J ⟶ H)
    (V W : Y.Opens) (hWV : W ≤ V) (hVU : V ≤ U) :
    Y.presheaf.map (homOfLE hWV).op (homCoordinate e f a V hVU) =
      homCoordinate e f a W (hWV.trans hVU) := by
  apply (f.equiv W (hWV.trans hVU)).injective
  rw [← f.naturality V W hWV hVU, homCoordinate, LinearEquiv.apply_symm_apply,
    homCoordinate, LinearEquiv.apply_symm_apply]
  calc
    _ = a.app W (J.presheaf.map (homOfLE hWV).op (e.equiv V hVU 1)) :=
      (ConcreteCategory.congr_hom
        (a.mapPresheaf.naturality (homOfLE hWV).op) (e.equiv V hVU 1)).symm
    _ = _ := by rw [e.naturality]; simp


/-- Restrict an existing natural frame to a smaller open. -/
def restrictFrame {Y : Scheme} {J : Y.Modules} {U V : Y.Opens}
    (e : LocalFrame Y J U) (h : V ≤ U) : LocalFrame Y J V where
  equiv W hWV := e.equiv W (hWV.trans h)
  naturality W Z hZW hWV r := e.naturality W Z hZW (hWV.trans h) r

/-- Finite affine data on which both given lines have genuine natural frames. -/
structure PairFrameCover (Y : Scheme.{u}) (J H : Y.Modules) where
  index : Type u
  finite : Fintype index
  opens : index → Y.Opens
  covers : (⊤ : Y.Opens) ≤ iSup opens
  affine : ∀ i, IsAffineOpen (opens i)
  sourceFrame : ∀ i, LocalFrame Y J (opens i)
  targetFrame : ∀ i, LocalFrame Y H (opens i)

/-- Compactness reduces the two line conditions to finite simultaneous affine frames. -/
theorem exists_pairFrameCover (Y : Scheme) [CompactSpace Y] (J H : Y.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle Y J)
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle Y H) :
    Nonempty (PairFrameCover Y J H) := by
  classical
  have hx (x : Y) : ∃ U : Y.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (LocalFrame Y J U) ∧ Nonempty (LocalFrame Y H U) := by
    obtain ⟨UJ, hxJ, ⟨e⟩⟩ := hJ x
    obtain ⟨UH, hxH, ⟨f⟩⟩ := hH x
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ UJ ⊓ UH from ⟨hxJ, hxH⟩)
    exact ⟨U, hxU, hU,
      ⟨restrictFrame (localFrameOfIso Y J UJ e) (hle.trans inf_le_left)⟩,
      ⟨restrictFrame (localFrameOfIso Y H UH f) (hle.trans inf_le_right)⟩⟩
  choose U hmem haff he hf using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set Y)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  refine ⟨{
    index := ↥S
    finite := inferInstance
    opens := fun x => U x.val
    covers := ?_
    affine := fun x => haff x.val
    sourceFrame := fun x => Classical.choice (he x.val)
    targetFrame := fun x => Classical.choice (hf x.val) }⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩

/-- The required compactness follows from the actual proper structure map. -/
theorem model_compact {X : Curve Omega} {K : FieldStage} (M : Model X K) :
    CompactSpace M.curve.space := by
  let := M.curve.proper
  exact QuasiCompact.compactSpace_of_compactSpace M.curve.map

/-- Finite frames are therefore available for the exact sheaves in the obligation. -/
theorem model_pairFrameCover {X : Curve Omega} {K : FieldStage} (M : Model X K)
    (J H : M.curve.space.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space J)
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space H) :
    Nonempty (PairFrameCover M.curve.space J H) := by
  let := model_compact M
  exact exists_pairFrameCover M.curve.space J H hJ hH


/-- Section-level naturality in the scheme-module presentation used here. -/
theorem hom_restrict {Y : Scheme} {J H : Y.Modules} (a : J ⟶ H)
    (V W : Y.Opens) (hWV : W ≤ V) (t : Γ(J, V)) :
    H.presheaf.map (homOfLE hWV).op (a.app V t) =
      a.app W (J.presheaf.map (homOfLE hWV).op t) :=
  (ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE hWV).op) t).symm

/-- Equal coefficients in frames give equal maps on every section of the open. -/
theorem homCoordinate_ext {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a b : J ⟶ H)
    (V : Y.Opens) (hVU : V ≤ U)
    (h : homCoordinate e f a V hVU = homCoordinate e f b V hVU)
    (t : Γ(J, V)) : a.app V t = b.app V t := by
  obtain ⟨r, rfl⟩ := (e.equiv V hVU).surjective t
  rw [homCoordinate_apply, homCoordinate_apply, h]

/-- Finitely many coefficients on a simultaneous frame cover detect a morphism. -/
theorem pairFrameCover_hom_ext {Y : Scheme} {J H : Y.Modules}
    (C : PairFrameCover Y J H) (a b : J ⟶ H)
    (h : ∀ i, homCoordinate (C.sourceFrame i) (C.targetFrame i) a (C.opens i) le_rfl =
      homCoordinate (C.sourceFrame i) (C.targetFrame i) b (C.opens i) le_rfl) : a = b := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro t
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun i => V ⊓ C.opens i) V (fun _ => homOfLE inf_le_left)
  · intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (C.covers (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · intro i
    rw [hom_restrict, hom_restrict]
    apply homCoordinate_ext (C.sourceFrame i) (C.targetFrame i) a b
      (V ⊓ C.opens i) inf_le_right
    have heq := congrArg
      (fun r => Y.presheaf.map (homOfLE (inf_le_right : V ⊓ C.opens i ≤ C.opens i)).op r)
      (h i)
    simpa only [homCoordinate_restrict] using heq

/-- The exact transition equation for local coefficients of an actual morphism. -/
theorem homCoordinate_transition {Y : Scheme} {J H : Y.Modules} {U U' : Y.Opens}
    (e : LocalFrame Y J U) (e' : LocalFrame Y J U')
    (f : LocalFrame Y H U) (f' : LocalFrame Y H U') (a : J ⟶ H)
    (V : Y.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition (f.equiv V hVU) (f'.equiv V hVU') * homCoordinate e' f' a V hVU' =
      transition (e.equiv V hVU) (e'.equiv V hVU') * homCoordinate e f a V hVU := by
  apply (f.equiv V hVU).injective
  rw [← transition_apply]
  rw [homCoordinate, LinearEquiv.apply_symm_apply]
  rw [transition_apply (e.equiv V hVU) (e'.equiv V hVU'), mul_one,
    homCoordinate_apply]


/-- A global natural frame gives an isomorphism of actual module sheaves. -/
def globalFrameIso {Y : Scheme} {J : Y.Modules} (e : LocalFrame Y J ⊤) :
    SheafOfModules.unit Y.ringCatSheaf ≅ J :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (e.equiv V.unop le_top).toModuleIso)
      (fun {V W} g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        exact (e.naturality V.unop W.unop g.unop.le le_top r).symm))

/-- A natural frame on an open gives a global frame on the restricted scheme. -/
def frameOnOpen {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) : LocalFrame U.toScheme (J.restrict U.ι) ⊤ where
  equiv V _ := by
    refine { (e.equiv (U.ι ''ᵁ V) (U.ι_image_le V)).toAddEquiv with
      map_smul' := ?_ }
    intro r t
    change e.equiv (U.ι ''ᵁ V) (U.ι_image_le V) (r * t) =
      (U.ι.appIso V).inv r • (e.equiv (U.ι ''ᵁ V) (U.ι_image_le V) t : Γ(J, U.ι ''ᵁ V))
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact (e.equiv (U.ι ''ᵁ V) (U.ι_image_le V)).map_smul r t
  naturality V W hWV _ r := by
    exact e.naturality (U.ι ''ᵁ V) (U.ι ''ᵁ W) (U.ι.image_mono hWV)
      (U.ι_image_le V) r

/-- The local trivialization as an isomorphism on the actual open subscheme. -/
def frameOpenIso {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι :=
  globalFrameIso (frameOnOpen e)


/-- Restriction and pullback commute through the actual commuting square. -/
def pullbackRestrictionIso {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules) (U : Y.Opens) :
    (Scheme.Modules.pullback (p ∣_ U)).obj (J.restrict U.ι) ≅
      ((Scheme.Modules.pullback p).obj J).restrict (p ⁻¹ᵁ U).ι :=
  (Scheme.Modules.pullback (p ∣_ U)).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app J) ≪≫
    (Scheme.Modules.pullbackComp (p ∣_ U) U.ι).app J ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι p U)).app J ≪≫
    ((Scheme.Modules.pullbackComp (p ⁻¹ᵁ U).ι p).app J).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app
      ((Scheme.Modules.pullback p).obj J)).symm

/-- A local frame pulls back to an actual trivialization on the preimage subscheme. -/
def pullbackOpenFrameIso {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) :
    SheafOfModules.unit (p ⁻¹ᵁ U).toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback p).obj J).restrict (p ⁻¹ᵁ U).ι :=
  (ArithmeticThetaPullback.pullback_unit_iso _ _ (p ∣_ U)).symm ≪≫
    (Scheme.Modules.pullback (p ∣_ U)).mapIso (frameOpenIso e) ≪≫
    pullbackRestrictionIso p J U


/-- The canonical unit comparison sends every pulled local scalar to its actual image. -/
theorem pullback_unit_local {X Y : Scheme} (p : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    (ArithmeticThetaPullback.pullback_unit_iso X Y p).hom.app (p ⁻¹ᵁ U)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection p
        (SheafOfModules.unit Y.ringCatSheaf) U r) = p.app U r := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.val.app (Opposite.op U)) h)
    (show (SheafOfModules.unit Y.ringCatSheaf).val.obj (Opposite.op U) from r)

/-- Pullback of a genuine global trivialization using the canonical unit comparison. -/
def pullbackGlobalFrameIso {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ J) :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback p).obj J :=
  (ArithmeticThetaPullback.pullback_unit_iso X Y p).symm ≪≫
    (Scheme.Modules.pullback p).mapIso e

/-- The pulled frame is compatible with the literal adjunction-unit section map. -/
theorem pullbackGlobalFrameIso_unit {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ J) (U : Y.Opens) (r : Γ(Y, U)) :
    ArithmeticThetaNormalizedSections.pullbackLocalSection p J U (Scheme.Modules.Hom.app e.hom U r) =
      Scheme.Modules.Hom.app (pullbackGlobalFrameIso p e).hom (p ⁻¹ᵁ U) (p.app U r) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality e.hom
  have h' := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app U) h)
    (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from r)
  change ArithmeticThetaNormalizedSections.pullbackLocalSection p J U (Scheme.Modules.Hom.app e.hom U r) =
    ((Scheme.Modules.pullback p).map e.hom).app (p ⁻¹ᵁ U)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection p
        (SheafOfModules.unit Y.ringCatSheaf) U r) at h'
  rw [h']
  change _ = ((Scheme.Modules.pullback p).map e.hom).app (p ⁻¹ᵁ U)
    ((ArithmeticThetaPullback.pullback_unit_iso X Y p).inv.app (p ⁻¹ᵁ U) (p.app U r))
  congr 1
  rw [← pullback_unit_local p U r]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (p ⁻¹ᵁ U))
      (ArithmeticThetaPullback.pullback_unit_iso X Y p).hom_inv_id) _).symm

/-- The open-immersion comparison also retains the actual adjunction unit. -/
theorem restrictionComparison_unit {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i]
    (J : Y.Modules) (U : Y.Opens) (s : Γ(J, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app J).hom.app (i ⁻¹ᵁ U)
      (J.presheaf.map (homOfLE (i.image_preimage_le U)).op s) =
      ArithmeticThetaNormalizedSections.pullbackLocalSection i J U s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction i) J
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.app U) h) s


/-- Move a frame equivalence across equality of the actual opens. -/
def transportFrameEquiv {Y : Scheme} {J : Y.Modules} {V W : Y.Opens} (h : V = W)
    (e : Γ(Y, V) ≃ₗ[Γ(Y, V)] Γ(J, V)) : Γ(Y, W) ≃ₗ[Γ(Y, W)] Γ(J, W) := h ▸ e

theorem transportFrameEquiv_naturality {Y : Scheme} {J : Y.Modules}
    {A B A' B' : Y.Opens} (hA : A = A') (hB : B = B') (hBA : B ≤ A) (hBA' : B' ≤ A')
    (eA : Γ(Y, A) ≃ₗ[Γ(Y, A)] Γ(J, A)) (eB : Γ(Y, B) ≃ₗ[Γ(Y, B)] Γ(J, B))
    (hn : ∀ r, J.presheaf.map (homOfLE hBA).op (eA r) =
      eB (Y.presheaf.map (homOfLE hBA).op r)) (r : Γ(Y, A')) :
    J.presheaf.map (homOfLE hBA').op (transportFrameEquiv hA eA r) =
      transportFrameEquiv hB eB (Y.presheaf.map (homOfLE hBA').op r) := by
  subst A'
  subst B'
  exact hn r

/-- Evaluate a trivialization on an open subscheme using the original scalar action. -/
def openIsoEquiv {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι)
    (W : U.toScheme.Opens) : Γ(Y, U.ι ''ᵁ W) ≃ₗ[Γ(Y, U.ι ''ᵁ W)] Γ(J, U.ι ''ᵁ W) := by
  exact {
    toFun := fun r => Scheme.Modules.Hom.app e.hom W r
    invFun := fun t => Scheme.Modules.Hom.app e.inv W t
    left_inv := fun r => ConcreteCategory.congr_hom
      (congrArg (fun k => Scheme.Modules.Hom.app k W) e.hom_inv_id) r
    right_inv := fun t => ConcreteCategory.congr_hom
      (congrArg (fun k => Scheme.Modules.Hom.app k W) e.inv_hom_id) t
    map_add' := fun r t => map_add (Scheme.Modules.Hom.app e.hom W).hom r t
    map_smul' := by
      intro r t
      have h := Scheme.Modules.Hom.app_smul e.hom (U := W) r t
      change Scheme.Modules.Hom.app e.hom W (r * t) =
        (U.ι.appIso W).inv r • (show Γ(J, U.ι ''ᵁ W) from Scheme.Modules.Hom.app e.hom W t) at h
      rw [Scheme.Opens.ι_appIso] at h
      convert h using 1 <;> rfl }

theorem openIsoEquiv_naturality {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι)
    (V W : U.toScheme.Opens) (hWV : W ≤ V) (r : Γ(Y, U.ι ''ᵁ V)) :
    J.presheaf.map (homOfLE (U.ι.image_mono hWV)).op (openIsoEquiv e V r) =
      openIsoEquiv e W (Y.presheaf.map (homOfLE (U.ι.image_mono hWV)).op r) := by
  exact (ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf e.hom).naturality (homOfLE hWV).op) r).symm

/-- A trivialization on the actual open subscheme recovers a natural local frame. -/
def frameFromOpenIso {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι) : LocalFrame Y J U where
  equiv V hVU := transportFrameEquiv
    (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]) (openIsoEquiv e (U.ι ⁻¹ᵁ V))
  naturality V W hWV hVU r := by
    apply transportFrameEquiv_naturality
    exact openIsoEquiv_naturality e (U.ι ⁻¹ᵁ V) (U.ι ⁻¹ᵁ W) (U.ι.preimage_mono hWV)

/-- Construct the natural frame on the full preimage of the chosen open. -/
def pulledFrame {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) : LocalFrame X ((Scheme.Modules.pullback p).obj J) (p ⁻¹ᵁ U) :=
  frameFromOpenIso (pullbackOpenFrameIso p e)

/-- The supplied local line predicate is stable under the actual pullback. -/
theorem pullback_isLineBundle {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle Y J) :
    ArithmeticThetaNormalizedSections.IsLineBundle X ((Scheme.Modules.pullback p).obj J) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hJ (p x)
  refine ⟨p ⁻¹ᵁ U, hx, ?_⟩
  exact ⟨localFrameIso X _ _ (pulledFrame p (localFrameOfIso Y J U e))⟩


/-- The constant-field action on a chart comes from its actual structure map. -/
def chartConstants {k : Type} [Field k] (Y : Curve k) (U : Y.space.Opens) :
    k →+* Γ(Y.space, U) :=
  (Y.map.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- An abstract top-open identity avoids unfolding a concrete spectrum map. -/
theorem appLE_top_eq {A B : Scheme} (f : A ⟶ B) :
    f.appLE ⊤ ⊤ (by simp) = f.appTop := by
  exact Scheme.Hom.appLE_eq_app f

/-- Cartesian scalar extension along a specified field map is a pushout on chart rings. -/
theorem curve_chart_pushout {k l : Type} [Field k] [Field l]
    (X : Curve l) (Y : Curve k) (i : k →+* l) (p : X.space ⟶ Y.space)
    (hc : IsPullback p X.map Y.map (Spec.map (CommRingCat.ofHom i)))
    (U : Y.space.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (chartConstants Y U)) (CommRingCat.ofHom i)
      (p.app U)
      ((Scheme.ΓSpecIso (CommRingCat.of l)).inv ≫
        X.map.appLE ⊤ (p ⁻¹ᵁ U) (by simp)) := by
  have h := isIso_pushoutSection_of_isAffineOpen hc
    (UT := ⊤) (US := ⊤) (UX := U) (by simp) (by simp)
    (UY := p ⁻¹ᵁ U) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hp := (isIso_pushoutSection_iff hc
    (UT := ⊤) (US := ⊤) (UX := U) (by simp) (by simp)
    (UY := p ⁻¹ᵁ U) (by simp)).mp h
  rw [appLE_top_eq, Scheme.Hom.appLE_eq_app] at hp
  apply hp.of_iso (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of l)) (Iso.refl _)
  · change Y.map.appLE ⊤ U _ ≫ 𝟙 _ =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.map.appLE ⊤ U _)
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · change (Spec.map (CommRingCat.ofHom i)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of l)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom i
    exact Scheme.ΓSpecIso_naturality
      (R := CommRingCat.of k) (S := CommRingCat.of l) (CommRingCat.ofHom i)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Actual scalar extension is an affine pushout on section rings. -/
theorem model_chart_pushout {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (chartConstants M.curve U)) (CommRingCat.ofHom K.subtype)
      (M.projection.app U)
      ((Scheme.ΓSpecIso (CommRingCat.of Omega)).inv ≫
        X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp)) := by
  exact curve_chart_pushout X M.curve K.subtype M.projection M.cartesian U hU

/-- Tensor coordinates on a model chart, with the actual field action. -/
def modelChartTensorIso {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := (chartConstants M.curve U).toAlgebra
    CommRingCat.of (Omega ⊗[K] Γ(M.curve.space, U)) ≅ Γ(X.space, M.projection ⁻¹ᵁ U) := by
  letI := (chartConstants M.curve U).toAlgebra
  exact (CommRingCat.isPushout_tensorProduct K Omega Γ(M.curve.space, U)).flip.isoPushout ≪≫
    (model_chart_pushout M U hU).isoPushout.symm


/-- The tensor comparison sends the constant factor by the actual structure map. -/
theorem modelChartTensorIso_left {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    let := (chartConstants M.curve U).toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      Omega →+* Omega ⊗[K] Γ(M.curve.space, U)) ≫ (modelChartTensorIso M U hU).hom =
      (Scheme.ΓSpecIso (CommRingCat.of Omega)).inv ≫
        X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp) := by
  let := (chartConstants M.curve U).toAlgebra
  exact ((CommRingCat.isPushout_tensorProduct K Omega Γ(M.curve.space, U)).flip.inr_isoPushout_hom_assoc
    (model_chart_pushout M U hU).isoPushout.inv).trans
    (model_chart_pushout M U hU).inr_isoPushout_inv

/-- The other tensor factor maps by the given Cartesian projection. -/
theorem modelChartTensorIso_right {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    let := (chartConstants M.curve U).toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      Γ(M.curve.space, U) →+* Omega ⊗[K] Γ(M.curve.space, U)) ≫
        (modelChartTensorIso M U hU).hom = M.projection.app U := by
  let := (chartConstants M.curve U).toAlgebra
  exact ((CommRingCat.isPushout_tensorProduct K Omega Γ(M.curve.space, U)).flip.inl_isoPushout_hom_assoc
    (model_chart_pushout M U hU).isoPushout.inv).trans
    (model_chart_pushout M U hU).inl_isoPushout_inv

/-- Pure tensors have exactly the expected geometric image. -/
theorem modelChartTensorIso_tmul {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U)
    (c : Omega) (r : Γ(M.curve.space, U)) :
    let := (chartConstants M.curve U).toAlgebra
    (modelChartTensorIso M U hU).hom (c ⊗ₜ[K] r) =
      X.map.appLE ⊤ (M.projection ⁻¹ᵁ U) (by simp)
        ((Scheme.ΓSpecIso (CommRingCat.of Omega)).inv c) * M.projection.app U r := by
  let := (chartConstants M.curve U).toAlgebra
  have hl := ConcreteCategory.congr_hom (modelChartTensorIso_left M U hU) c
  have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
  change (modelChartTensorIso M U hU).hom (c ⊗ₜ[K] 1) = _ at hl
  change (modelChartTensorIso M U hU).hom (1 ⊗ₜ[K] r) = _ at hr
  rw [show c ⊗ₜ[K] r = (c ⊗ₜ[K] 1) * (1 ⊗ₜ[K] r) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, hl, hr]
  rfl


/-- Equality of chart functions is reflected by the actual model projection. -/
theorem model_projection_app_injective {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    Function.Injective (M.projection.app U) := by
  let := (chartConstants M.curve U).toAlgebra
  intro r t h
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := Omega)
    Γ(M.curve.space, U)
  apply (modelChartTensorIso M U hU).commRingCatIsoToRingEquiv.injective
  have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
  have ht := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) t
  exact hr.trans (h.trans ht.symm)


/-- Coordinate tensor comparison over an actual finite enlargement. -/
def stageChartTensorIso {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (h : K ≤ K') (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := (chartConstants M.curve U).toAlgebra
    letI := stageAlgebra h
    CommRingCat.of (K' ⊗[K] Γ(M.curve.space, U)) ≅
      Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U) := by
  letI := (chartConstants M.curve U).toAlgebra
  letI := stageAlgebra h
  exact (CommRingCat.isPushout_tensorProduct K K' Γ(M.curve.space, U)).flip.isoPushout ≪≫
    (curve_chart_pushout (enlargedModel M h).curve M.curve
      (IntermediateField.inclusion h).toRingHom (enlargement M h).map
      (enlargement M h).cartesian U hU).isoPushout.symm


/-- Pullback of constants follows the specified map of fields. -/
theorem chartConstants_comp {k l : Type} [Field k] [Field l]
    (X : Curve l) (Y : Curve k) (i : k →+* l) (p : X.space ⟶ Y.space)
    (hp : p ≫ Y.map = X.map ≫ Spec.map (CommRingCat.ofHom i))
    (U : Y.space.Opens) (V : X.space.Opens) (hVU : V ≤ p ⁻¹ᵁ U) (c : k) :
    p.appLE U V hVU (chartConstants Y U c) = chartConstants X V (i c) := by
  have h₁ := p.appLE_comp_appLE Y.map ⊤ U V (by simp) hVU
  have h₂ := X.map.appLE_comp_appLE (Spec.map (CommRingCat.ofHom i)) ⊤ ⊤ V
    (by simp) (by simp)
  rw [hp] at h₁
  rw [appLE_top_eq] at h₂
  have h₃ := Scheme.ΓSpecIso_inv_naturality
    (R := CommRingCat.of k) (S := CommRingCat.of l) (CommRingCat.ofHom i)
  have h := congrArg (fun f => f c)
    (show (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.map.appLE ⊤ U (by simp) ≫
        p.appLE U V hVU = CommRingCat.ofHom i ≫
          (Scheme.ΓSpecIso (CommRingCat.of l)).inv ≫ X.map.appLE ⊤ V (by simp) from by
      rw [h₁, ← h₂, ← Category.assoc, ← h₃, Category.assoc])
  exact h

/-- The map from the finite-stage chart to the algebraic-closure chart is the
actual projection, with the open-set inclusion proved from the refinement. -/
def stageChartMap {X : Curve Omega} {K K' : FieldStage} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) :
    Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U) ⟶
      Γ(X.space, M.projection ⁻¹ᵁ U) :=
  (enlargedModel M h).projection.appLE ((enlargement M h).map ⁻¹ᵁ U)
    (M.projection ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])

/-- The base-chart part of the finite-stage comparison is the original map. -/
theorem stageChartMap_base {X : Curve Omega} {K K' : FieldStage} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) (r : Γ(M.curve.space, U)) :
    stageChartMap M h U ((enlargement M h).map.app U r) = M.projection.app U r := by
  have he := (enlargedModel M h).projection.appLE_comp_appLE (enlargement M h).map
    U ((enlargement M h).map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U) le_rfl
    (by rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])
  simp only [(enlargement M h).comparison, Scheme.Hom.appLE_eq_app] at he
  exact ConcreteCategory.congr_hom he r

/-- The constant part of the finite-stage comparison is the given field inclusion. -/
theorem stageChartMap_constant {X : Curve Omega} {K K' : FieldStage} (M : Model X K)
    (h : K ≤ K') (U : M.curve.space.Opens) (c : K') :
    stageChartMap M h U
      (chartConstants (enlargedModel M h).curve ((enlargement M h).map ⁻¹ᵁ U) c) =
      chartConstants X (M.projection ⁻¹ᵁ U) c.val :=
  chartConstants_comp X (enlargedModel M h).curve K'.subtype (enlargedModel M h).projection
    (enlargedModel M h).cartesian.w _ _ _ c


/-- Finite families of actual affine-chart functions descend simultaneously,
with the comparison given by the actual refinement projection. -/
theorem finite_chart_functions {X : Curve Omega} (K0 : FieldStage)
    [FiniteDimensional ℚ K0] (M : Model X K0) (I : Type) [Fintype I]
    (U : I → M.curve.space.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : ℕ) (a : ∀ i, Fin s → Γ(X.space, M.projection ⁻¹ᵁ U i)) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      ∃ b : ∀ i, Fin s → Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U i),
        ∀ i j, stageChartMap M h (U i) (b i j) = a i j := by
  classical
  let (i : I) : Algebra K0 Γ(M.curve.space, U i) := (chartConstants M.curve (U i)).toAlgebra
  choose T hT using fun i j => TensorProduct.exists_finset
    ((modelChartTensorIso M (U i) (hU i)).inv (a i j))
  let S : Finset Omega := Finset.univ.biUnion
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

/-- Local linear maps, with actual restriction and overlap equations. -/
structure LocalHomFamily {Y : Scheme} (J H : Y.Modules) (I : Type)
    (U : I → Y.Opens) where
  covers : (⊤ : Y.Opens) ≤ iSup U
  map : ∀ i V, V ≤ U i → Γ(J, V) →ₗ[Γ(Y, V)] Γ(H, V)
  naturality : ∀ i V W (hWV : W ≤ V) (hVU : V ≤ U i) (t : Γ(J, V)),
    H.presheaf.map (homOfLE hWV).op (map i V hVU t) =
      map i W (hWV.trans hVU) (J.presheaf.map (homOfLE hWV).op t)
  overlap : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j) (t : Γ(J, V)),
    map i V hi t = map j V hj t

/-- Iterated restriction on a module sheaf is restriction to the composite inclusion. -/
theorem module_restrict_comp {Y : Scheme} (J : Y.Modules) {U V W : Y.Opens}
    (hWV : W ≤ V) (hVU : V ≤ U) (t : Γ(J, U)) :
    J.presheaf.map (homOfLE hWV).op (J.presheaf.map (homOfLE hVU).op t) =
      J.presheaf.map (homOfLE (hWV.trans hVU)).op t := by
  rw [← ConcreteCategory.comp_apply, ← J.presheaf.map_comp]
  rfl

namespace LocalHomFamily
variable {Y : Scheme} {J H : Y.Modules} {I : Type} {U : I → Y.Opens}
variable (D : LocalHomFamily J H I U)

include D in
/-- The chosen cover also covers each test open after intersection. -/
theorem cover_open (V : Y.Opens) : V ≤ ⨆ i, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (D.covers (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- Apply a local map to the restriction of the test section. -/
def localImage (V : Y.Opens) (t : Γ(J, V)) (i : I) : Γ(H, V ⊓ U i) :=
  D.map i (V ⊓ U i) inf_le_right (J.presheaf.map (homOfLE inf_le_left).op t)

/-- The local images satisfy the actual sheaf compatibility condition. -/
theorem localImage_compatible (V : Y.Opens) (t : Γ(J, V)) :
    TopCat.Presheaf.IsCompatible H.presheaf (fun i => V ⊓ U i) (D.localImage V t) := by
  intro i j
  change H.presheaf.map (homOfLE inf_le_left).op (D.localImage V t i) =
    H.presheaf.map (homOfLE inf_le_right).op (D.localImage V t j)
  dsimp [localImage]
  rw [D.naturality, D.naturality, module_restrict_comp, module_restrict_comp]
  exact D.overlap i j _ _ _ _

/-- Existence and uniqueness comes from the sheaf condition, with no gluing assumption. -/
theorem existsUnique_image (V : Y.Opens) (t : Γ(J, V)) :
    ∃! v : Γ(H, V), ∀ i, H.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op v =
      D.localImage V t i :=
  TopCat.Sheaf.existsUnique_gluing' ⟨H.presheaf, H.isSheaf⟩ (fun i => V ⊓ U i)
    V (fun _ => homOfLE inf_le_left) (D.cover_open V) _ (D.localImage_compatible V t)

/-- The image of a test section under the glued map. -/
def image (V : Y.Opens) (t : Γ(J, V)) : Γ(H, V) :=
  (D.existsUnique_image V t).choose

theorem image_restrict (V : Y.Opens) (t : Γ(J, V)) (i : I) :
    H.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (D.image V t) =
      D.localImage V t i := (D.existsUnique_image V t).choose_spec.1 i

/-- The glued action is additive, by local additivity and uniqueness. -/
theorem image_add (V : Y.Opens) (s t : Γ(J, V)) :
    D.image V (s + t) = D.image V s + D.image V t := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (D.cover_open V)
  intro i
  simp only [map_add, D.image_restrict, localImage]

/-- The scalar action is the original structure-sheaf action. -/
theorem image_smul (V : Y.Opens) (r : Γ(Y, V)) (t : Γ(J, V)) :
    D.image V (r • t) = r • D.image V t := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (D.cover_open V)
  intro i
  rw [Scheme.Modules.map_smul, D.image_restrict, D.image_restrict]
  simp only [localImage, Scheme.Modules.map_smul, map_smul]

/-- The glued images commute with restriction on arbitrary test opens. -/
theorem image_naturality (V W : Y.Opens) (hWV : W ≤ V) (t : Γ(J, V)) :
    H.presheaf.map (homOfLE hWV).op (D.image V t) =
      D.image W (J.presheaf.map (homOfLE hWV).op t) := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun i => W ⊓ U i) W (fun _ => homOfLE inf_le_left) (D.cover_open W)
  intro i
  rw [module_restrict_comp, D.image_restrict]
  have he := congrArg
    (fun v => H.presheaf.map (homOfLE (inf_le_inf_right (U i) hWV)).op v)
    (D.image_restrict V t i)
  rw [module_restrict_comp] at he
  rw [he]
  dsimp [localImage]
  rw [D.naturality, module_restrict_comp, module_restrict_comp]

/-- Compatible local linear maps glue to a genuine morphism of module sheaves. -/
def hom : J ⟶ H :=
  ⟨{ app := fun V => ModuleCat.ofHom
       { toFun := D.image V.unop
         map_add' := D.image_add V.unop
         map_smul' := D.image_smul V.unop }
     naturality := fun {V W} g => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro t
       exact (D.image_naturality V.unop W.unop g.unop.le t).symm }⟩

/-- On every covered subopen, the glued morphism equals the original local map. -/
theorem hom_app (i : I) (V : Y.Opens) (hVU : V ≤ U i) (t : Γ(J, V)) :
    D.hom.app V t = D.map i V hVU t := by
  change D.image V t = _
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun j => V ⊓ U j) V (fun _ => homOfLE inf_le_left) (D.cover_open V)
  intro j
  rw [D.image_restrict, D.naturality]
  exact D.overlap j i _ _ _ _

end LocalHomFamily

/-- The inverse frame coordinates commute with actual restriction maps. -/
theorem frame_symm_naturality {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (V W : Y.Opens) (hWV : W ≤ V) (hVU : V ≤ U)
    (t : Γ(J, V)) :
    Y.presheaf.map (homOfLE hWV).op ((e.equiv V hVU).symm t) =
      (e.equiv W (hWV.trans hVU)).symm (J.presheaf.map (homOfLE hWV).op t) := by
  apply (e.equiv W (hWV.trans hVU)).injective
  rw [← e.naturality V W hWV hVU, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Restriction of functions along a composite open inclusion. -/
theorem ring_restrict_comp {Y : Scheme} {U V W : Y.Opens}
    (hWV : W ≤ V) (hVU : V ≤ U) (r : Γ(Y, U)) :
    Y.presheaf.map (homOfLE hWV).op (Y.presheaf.map (homOfLE hVU).op r) =
      Y.presheaf.map (homOfLE (hWV.trans hVU)).op r := by
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

/-- A chart function defines a linear map in the given actual frames. -/
def coefficientMap {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (c : Γ(Y, U))
    (V : Y.Opens) (hVU : V ≤ U) : Γ(J, V) →ₗ[Γ(Y, V)] Γ(H, V) where
  toFun t := f.equiv V hVU ((e.equiv V hVU).symm t * Y.presheaf.map (homOfLE hVU).op c)
  map_add' s t := by simp only [map_add, add_mul]
  map_smul' r t := by
    simp only [map_smul, smul_eq_mul, mul_assoc]
    exact (f.equiv V hVU).map_smul r _

/-- The local map is natural on all smaller opens. -/
theorem coefficientMap_naturality {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (c : Γ(Y, U))
    (V W : Y.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (t : Γ(J, V)) :
    H.presheaf.map (homOfLE hWV).op (coefficientMap e f c V hVU t) =
      coefficientMap e f c W (hWV.trans hVU) (J.presheaf.map (homOfLE hWV).op t) := by
  change H.presheaf.map (homOfLE hWV).op (f.equiv V hVU _) = f.equiv W _ _
  rw [f.naturality, map_mul, frame_symm_naturality, ring_restrict_comp]

/-- Equality of the transition-scaled coefficients is exactly what is needed
for the two local formulas to agree. -/
theorem coefficientMap_overlap {Y : Scheme} {J H : Y.Modules} {U U' : Y.Opens}
    (e : LocalFrame Y J U) (e' : LocalFrame Y J U')
    (f : LocalFrame Y H U) (f' : LocalFrame Y H U')
    (c : Γ(Y, U)) (c' : Γ(Y, U')) (V : Y.Opens) (hVU : V ≤ U) (hVU' : V ≤ U')
    (hc : transition (f.equiv V hVU) (f'.equiv V hVU') *
        Y.presheaf.map (homOfLE hVU').op c' =
      transition (e.equiv V hVU) (e'.equiv V hVU') *
        Y.presheaf.map (homOfLE hVU).op c) (t : Γ(J, V)) :
    coefficientMap e f c V hVU t = coefficientMap e' f' c' V hVU' t := by
  change f.equiv V hVU _ = f'.equiv V hVU' _
  rw [transition_apply (f.equiv V hVU) (f'.equiv V hVU')]
  congr 1
  have he : (e.equiv V hVU).symm t =
      transition (e.equiv V hVU) (e'.equiv V hVU') * (e'.equiv V hVU').symm t := by
    apply (e.equiv V hVU).injective
    rw [← transition_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [he]
  calc
    _ = (e'.equiv V hVU').symm t *
        (transition (e.equiv V hVU) (e'.equiv V hVU') *
          Y.presheaf.map (homOfLE hVU).op c) := by ring
    _ = _ := by rw [← hc]; ring

/-- Compatible coefficients on a finite frame cover, expressed only on actual overlaps. -/
structure CompatibleCoefficients {Y : Scheme} {J H : Y.Modules} (C : PairFrameCover Y J H) where
  value : ∀ i, Γ(Y, C.opens i)
  overlap : ∀ i j,
    transition ((C.targetFrame i).equiv _ inf_le_left) ((C.targetFrame j).equiv _ inf_le_right) *
        Y.presheaf.map (homOfLE inf_le_right).op (value j) =
      transition ((C.sourceFrame i).equiv _ inf_le_left) ((C.sourceFrame j).equiv _ inf_le_right) *
        Y.presheaf.map (homOfLE inf_le_left).op (value i)

namespace CompatibleCoefficients
variable {Y : Scheme} {J H : Y.Modules} {C : PairFrameCover Y J H}
variable (c : CompatibleCoefficients C)

/-- The transition relation on the overlap restricts to every common subopen. -/
theorem overlap_on (i j : C.index) (V : Y.Opens) (hi : V ≤ C.opens i) (hj : V ≤ C.opens j) :
    transition ((C.targetFrame i).equiv V hi) ((C.targetFrame j).equiv V hj) *
        Y.presheaf.map (homOfLE hj).op (c.value j) =
      transition ((C.sourceFrame i).equiv V hi) ((C.sourceFrame j).equiv V hj) *
        Y.presheaf.map (homOfLE hi).op (c.value i) := by
  have h := congrArg (fun r => Y.presheaf.map (homOfLE (le_inf hi hj)).op r) (c.overlap i j)
  simpa only [map_mul, transition_restrict, ring_restrict_comp] using h

/-- The coefficient formulas provide the input to the proved sheaf-gluing construction. -/
def localFamily : LocalHomFamily J H C.index C.opens where
  covers := C.covers
  map i := coefficientMap (C.sourceFrame i) (C.targetFrame i) (c.value i)
  naturality i := coefficientMap_naturality (C.sourceFrame i) (C.targetFrame i) (c.value i)
  overlap i j V hi hj t := coefficientMap_overlap _ _ _ _ _ _ V hi hj (c.overlap_on i j V hi hj) t

/-- The actual sheaf morphism constructed from compatible chart functions. -/
def hom : J ⟶ H := c.localFamily.hom

/-- The constructed morphism has the prescribed coefficient on each chart. -/
theorem hom_coordinate (i : C.index) :
    homCoordinate (C.sourceFrame i) (C.targetFrame i) c.hom (C.opens i) le_rfl = c.value i := by
  unfold homCoordinate
  rw [show c.hom = c.localFamily.hom from rfl, LocalHomFamily.hom_app]
  change ((C.targetFrame i).equiv (C.opens i) le_rfl).symm
    ((C.targetFrame i).equiv (C.opens i) le_rfl
      (((C.sourceFrame i).equiv (C.opens i) le_rfl).symm
        ((C.sourceFrame i).equiv (C.opens i) le_rfl 1) *
          Y.presheaf.map (homOfLE le_rfl).op (c.value i))) = _
  simp

end CompatibleCoefficients

/-- The canonical pullback composition comparison preserves the nested unit sections. -/
theorem pullbackComp_inv_unit {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (U : Z.Opens) (s : Γ(J, U)) :
    ((Scheme.Modules.pullbackComp p q).app J).inv.app ((p ≫ q) ⁻¹ᵁ U)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection (p ≫ q) J U s) =
    ArithmeticThetaNormalizedSections.pullbackLocalSection p ((Scheme.Modules.pullback q).obj J)
      (q ⁻¹ᵁ U) (ArithmeticThetaNormalizedSections.pullbackLocalSection q J U s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q))
    (Scheme.Modules.pullbackComp p q).inv J
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  exact (ConcreteCategory.congr_hom (congrArg (fun k => k.app U) h) s).symm

/-- Actual scalar extension reflects equality of functions on every open,
by affine-local detection and the sheaf condition. -/
theorem model_projection_app_injective_all {X : Curve Omega} {K : FieldStage}
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

/-- Restriction after a pullback unit, retaining the explicitly specified subopen. -/
def pullbackSectionLE {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ p ⁻¹ᵁ U) (s : Γ(J, U)) :
    Γ((Scheme.Modules.pullback p).obj J, V) :=
  ((Scheme.Modules.pullback p).obj J).presheaf.map (homOfLE h).op
    (ArithmeticThetaNormalizedSections.pullbackLocalSection p J U s)

/-- The section pullback for the full preimage is literally the adjunction-unit map. -/
theorem pullbackSectionLE_full {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U : Y.Opens) (s : Γ(J, U)) :
    pullbackSectionLE p J U (p ⁻¹ᵁ U) le_rfl s =
      ArithmeticThetaNormalizedSections.pullbackLocalSection p J U s := by
  simp [pullbackSectionLE]

/-- Restricting a pulled section changes only the target subopen. -/
theorem pullbackSectionLE_restrict {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U : Y.Opens) (V W : X.Opens) (hV : V ≤ p ⁻¹ᵁ U) (hWV : W ≤ V) (s : Γ(J, U)) :
    ((Scheme.Modules.pullback p).obj J).presheaf.map (homOfLE hWV).op
      (pullbackSectionLE p J U V hV s) = pullbackSectionLE p J U W (hWV.trans hV) s :=
  module_restrict_comp _ hWV hV _

/-- Naturality of the adjunction unit on local sections. -/
theorem pullbackLocalSection_restrict {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U V : Y.Opens) (hVU : V ≤ U) (s : Γ(J, U)) :
    ArithmeticThetaNormalizedSections.pullbackLocalSection p J V
      (J.presheaf.map (homOfLE hVU).op s) =
    ((Scheme.Modules.pullback p).obj J).presheaf.map (homOfLE (p.preimage_mono hVU)).op
      (ArithmeticThetaNormalizedSections.pullbackLocalSection p J U s) := by
  exact (hom_restrict ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app J)
    U V hVU s).symm

/-- Pulling back a restriction and then restricting to a specified subopen
is the same as pulling the original section to that subopen. -/
theorem pullbackSectionLE_source_restrict {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U V : Y.Opens) (hVU : V ≤ U) (W : X.Opens) (hW : W ≤ p ⁻¹ᵁ V) (s : Γ(J, U)) :
    pullbackSectionLE p J V W hW (J.presheaf.map (homOfLE hVU).op s) =
      pullbackSectionLE p J U W (hW.trans (p.preimage_mono hVU)) s := by
  unfold pullbackSectionLE
  rw [pullbackLocalSection_restrict, module_restrict_comp]

/-- The forward composition comparison preserves the actual composite unit. -/
theorem pullbackComp_hom_unit {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (U : Z.Opens) (s : Γ(J, U)) :
    ((Scheme.Modules.pullbackComp p q).app J).hom.app ((p ≫ q) ⁻¹ᵁ U)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection p ((Scheme.Modules.pullback q).obj J)
        (q ⁻¹ᵁ U) (ArithmeticThetaNormalizedSections.pullbackLocalSection q J U s)) =
    ArithmeticThetaNormalizedSections.pullbackLocalSection (p ≫ q) J U s := by
  rw [← pullbackComp_inv_unit]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app ((p ≫ q) ⁻¹ᵁ U)) ((Scheme.Modules.pullbackComp p q).app J).inv_hom_id) _

/-- Composition of pullback units, with arbitrary source and target subopens. -/
theorem pullbackComp_hom_sectionLE {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ q ⁻¹ᵁ U) (hW : W ≤ p ⁻¹ᵁ V) (s : Γ(J, U)) :
    ((Scheme.Modules.pullbackComp p q).app J).hom.app W
      (pullbackSectionLE p ((Scheme.Modules.pullback q).obj J) V W hW
        (pullbackSectionLE q J U V hV s)) =
      pullbackSectionLE (p ≫ q) J U W (hW.trans (p.preimage_mono hV)) s := by
  unfold pullbackSectionLE
  rw [pullbackLocalSection_restrict, module_restrict_comp]
  exact (hom_restrict ((Scheme.Modules.pullbackComp p q).app J).hom
    ((p ≫ q) ⁻¹ᵁ U) W (hW.trans (p.preimage_mono hV)) _).symm.trans
    (congrArg (fun t => ((Scheme.Modules.pullback (p ≫ q)).obj J).presheaf.map
      (homOfLE (hW.trans (p.preimage_mono hV))).op t) (pullbackComp_hom_unit p q J U s))

/-- Equality of scheme maps transports their canonical pulled sections. -/
theorem pullbackCongr_sectionLE {X Y : Scheme} {p q : X ⟶ Y} (hpq : p = q)
    (J : Y.Modules) (U : Y.Opens) (V : X.Opens) (h : V ≤ p ⁻¹ᵁ U) (s : Γ(J, U)) :
    ((Scheme.Modules.pullbackCongr hpq).app J).hom.app V (pullbackSectionLE p J U V h s) =
      pullbackSectionLE q J U V (hpq ▸ h) s := by
  subst q
  rfl

/-- Pullback of a sheaf morphism acts naturally on canonical section pullbacks. -/
theorem pullbackLocalSection_map {X Y : Scheme} (p : X ⟶ Y) {J H : Y.Modules}
    (a : J ⟶ H) (U : Y.Opens) (s : Γ(J, U)) :
    ((Scheme.Modules.pullback p).map a).app (p ⁻¹ᵁ U)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection p J U s) =
      ArithmeticThetaNormalizedSections.pullbackLocalSection p H U (a.app U s) := by
  exact (ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality a)) s).symm

/-- Naturality also holds after restriction to any specified target open. -/
theorem pullbackSectionLE_map {X Y : Scheme} (p : X ⟶ Y) {J H : Y.Modules}
    (a : J ⟶ H) (U : Y.Opens) (V : X.Opens) (h : V ≤ p ⁻¹ᵁ U) (s : Γ(J, U)) :
    ((Scheme.Modules.pullback p).map a).app V (pullbackSectionLE p J U V h s) =
      pullbackSectionLE p H U V h (a.app U s) := by
  unfold pullbackSectionLE
  rw [← hom_restrict, pullbackLocalSection_map]

/-- The open-immersion comparison preserves unit sections on arbitrary subopens. -/
theorem restrictionComparison_sectionLE {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i]
    (J : Y.Modules) (U : Y.Opens) (V : X.Opens) (h : V ≤ i ⁻¹ᵁ U) (s : Γ(J, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app J).hom.app V
      (J.presheaf.map (homOfLE ((i.image_mono h).trans (i.image_preimage_le U))).op s) =
      pullbackSectionLE i J U V h s := by
  have he := congrArg (fun t => ((Scheme.Modules.pullback i).obj J).presheaf.map
    (homOfLE h).op t) (restrictionComparison_unit i J U s)
  rw [hom_restrict] at he
  change ((Scheme.Modules.restrictFunctorIsoPullback i).app J).hom.app V
    (J.presheaf.map (homOfLE (i.image_mono h)).op
      (J.presheaf.map (homOfLE (i.image_preimage_le U)).op s)) = _ at he
  rw [module_restrict_comp] at he
  exact he

/-- On a section already over the image open, the restriction comparison is canonical pullback. -/
theorem restrictionComparison_image {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i]
    (J : Y.Modules) (V : X.Opens) (s : Γ(J, i ''ᵁ V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app J).hom.app V s =
      pullbackSectionLE i J (i ''ᵁ V) V (i.preimage_image_eq V).ge s := by
  simpa using restrictionComparison_sectionLE i J (i ''ᵁ V) V (i.preimage_image_eq V).ge s

/-- The inverse composition comparison also preserves restricted canonical sections. -/
theorem pullbackComp_inv_sectionLE {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ q ⁻¹ᵁ U) (hW : W ≤ p ⁻¹ᵁ V) (s : Γ(J, U)) :
    ((Scheme.Modules.pullbackComp p q).app J).inv.app W
      (pullbackSectionLE (p ≫ q) J U W (hW.trans (p.preimage_mono hV)) s) =
      pullbackSectionLE p ((Scheme.Modules.pullback q).obj J) V W hW
        (pullbackSectionLE q J U V hV s) := by
  rw [← pullbackComp_hom_sectionLE p q J U V W hV hW s]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app W) ((Scheme.Modules.pullbackComp p q).app J).hom_inv_id) _

/-- The actual restriction/pullback comparison carries the restricted unit section
to the original unit section on the same geometric preimage open. -/
theorem pullbackRestrictionIso_unit {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U : Y.Opens) (V : U.toScheme.Opens) (s : Γ(J.restrict U.ι, V)) :
    (pullbackRestrictionIso p J U).hom.app ((p ∣_ U) ⁻¹ᵁ V)
      (ArithmeticThetaNormalizedSections.pullbackLocalSection (p ∣_ U) (J.restrict U.ι) V s) =
      pullbackSectionLE p J (U.ι ''ᵁ V) ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V))
        (image_morphismRestrict_preimage p U V).le s := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app
      ((Scheme.Modules.pullback p).obj J) ≪≫
    (Scheme.Modules.pullbackComp (p ⁻¹ᵁ U).ι p).app J
  have he : (pullbackRestrictionIso p J U).hom ≫ e.hom =
      (Scheme.Modules.pullback (p ∣_ U)).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app J).hom ≫
      ((Scheme.Modules.pullbackComp (p ∣_ U) U.ι).app J).hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι p U)).app J).hom := by
    simp [e, pullbackRestrictionIso, Category.assoc]
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ((p ∣_ U) ⁻¹ᵁ V))).injective
  change ((pullbackRestrictionIso p J U).hom ≫ e.hom).app ((p ∣_ U) ⁻¹ᵁ V) _ = _
  rw [he]
  simp only [e, Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackLocalSection_map, restrictionComparison_image]
  rw [← pullbackSectionLE_full (p ∣_ U) ((Scheme.Modules.pullback U.ι).obj J)]
  have h₁ := pullbackComp_hom_sectionLE (p ∣_ U) U.ι J (U.ι ''ᵁ V) V
    ((p ∣_ U) ⁻¹ᵁ V) (U.ι.preimage_image_eq V).ge le_rfl s
  have h₂ := pullbackCongr_sectionLE (morphismRestrict_ι p U) J (U.ι ''ᵁ V)
    ((p ∣_ U) ⁻¹ᵁ V) ((p ∣_ U).preimage_mono (U.ι.preimage_image_eq V).ge) s
  have h₃ := restrictionComparison_image (p ⁻¹ᵁ U).ι ((Scheme.Modules.pullback p).obj J)
    ((p ∣_ U) ⁻¹ᵁ V)
    (pullbackSectionLE p J (U.ι ''ᵁ V) ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V))
      (image_morphismRestrict_preimage p U V).le s)
  have h₄ := pullbackComp_hom_sectionLE (p ⁻¹ᵁ U).ι p J (U.ι ''ᵁ V)
    ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V)) ((p ∣_ U) ⁻¹ᵁ V)
    (image_morphismRestrict_preimage p U V).le ((p ⁻¹ᵁ U).ι.preimage_image_eq _).ge s
  exact (congrArg (((Scheme.Modules.pullbackCongr (morphismRestrict_ι p U)).app J).hom.app
    ((p ∣_ U) ⁻¹ᵁ V)) h₁).trans (h₂.trans
      ((congrArg (((Scheme.Modules.pullbackComp (p ⁻¹ᵁ U).ι p).app J).hom.app
        ((p ∣_ U) ⁻¹ᵁ V)) h₃).trans h₄).symm)

/-- Units are reflected on affine charts by the actual scalar extension map. -/
theorem model_projection_isUnit_iff {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) (r : Γ(M.curve.space, U)) :
    IsUnit (M.projection.app U r) ↔ IsUnit r := by
  let := (chartConstants M.curve U).toAlgebra
  constructor
  · intro h
    let e := (modelChartTensorIso M U hU).commRingCatIsoToRingEquiv
    have hr := ConcreteCategory.congr_hom (modelChartTensorIso_right M U hU) r
    have ht : IsUnit ((1 : Omega) ⊗ₜ[K] r) := by
      apply (isUnit_map_iff e _).mp
      exact hr.symm ▸ h
    have ht' := ht.map (Algebra.TensorProduct.comm K Omega Γ(M.curve.space, U)).toRingHom
    change IsUnit (r ⊗ₜ[K] (1 : Omega)) at ht'
    exact (isUnit_map_iff (algebraMap Γ(M.curve.space, U)
      (Γ(M.curve.space, U) ⊗[K] Omega)) r).mp ht'
  · exact fun h => h.map (M.projection.app U).hom

/-- Equality of open-scheme indices transports evaluation of the same isomorphism. -/
theorem openIsoEquiv_transport {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι)
    {V W : U.toScheme.Opens} (hVW : V = W) (h : U.ι ''ᵁ V = U.ι ''ᵁ W)
    (r : Γ(Y, U.ι ''ᵁ W)) :
    transportFrameEquiv h (openIsoEquiv e V) r = openIsoEquiv e W r := by
  subst W
  rfl

/-- Evaluation of the recovered frame on an image open is the original open-scheme isomorphism. -/
theorem frameFromOpenIso_image {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ J.restrict U.ι)
    (V : U.toScheme.Opens) (r : Γ(Y, U.ι ''ᵁ V)) :
    (frameFromOpenIso e).equiv (U.ι ''ᵁ V) (U.ι_image_le V) r =
      Scheme.Modules.Hom.app e.hom V r := by
  change transportFrameEquiv _ (openIsoEquiv e (U.ι ⁻¹ᵁ U.ι ''ᵁ V)) r = openIsoEquiv e V r
  exact openIsoEquiv_transport e (U.ι.preimage_image_eq V) _ r

/-- The open-scheme pulled trivialization carries actual chart scalars to
canonical pulled sections of the original line. -/
theorem pullbackOpenFrameIso_unit {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) :
    Scheme.Modules.Hom.app (pullbackOpenFrameIso p e).hom ((p ∣_ U) ⁻¹ᵁ V)
      ((p ∣_ U).app V r) =
      pullbackSectionLE p J (U.ι ''ᵁ V) ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V))
        (image_morphismRestrict_preimage p U V).le (e.equiv (U.ι ''ᵁ V) (U.ι_image_le V) r) := by
  have h₁ := pullbackGlobalFrameIso_unit (p ∣_ U) (frameOpenIso e) V r
  have h₂ := pullbackRestrictionIso_unit p J U V
    (Scheme.Modules.Hom.app (frameOpenIso e).hom V r)
  exact (congrArg ((pullbackRestrictionIso p J U).hom.app ((p ∣_ U) ⁻¹ᵁ V)) h₁.symm).trans h₂

/-- Transporting a frame equivalence along equal opens agrees with actual restrictions. -/
theorem transportFrameEquiv_apply {Y : Scheme} {J : Y.Modules} {V W : Y.Opens} (h : V = W)
    (e : Γ(Y, V) ≃ₗ[Γ(Y, V)] Γ(J, V)) (r : Γ(Y, W)) :
    transportFrameEquiv h e r =
      J.presheaf.map (eqToHom h.symm).op (e (Y.presheaf.map (eqToHom h).op r)) := by
  subst W
  simp [transportFrameEquiv]

/-- Compatibility with the unit on opens presented in the original frame chart. -/
theorem pulledFrame_unit_image {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (V : U.toScheme.Opens) (r : Γ(Y, U.ι ''ᵁ V)) :
    ArithmeticThetaNormalizedSections.pullbackLocalSection p J (U.ι ''ᵁ V)
      (e.equiv (U.ι ''ᵁ V) (U.ι_image_le V) r) =
      (pulledFrame p e).equiv (p ⁻¹ᵁ (U.ι ''ᵁ V)) (p.preimage_mono (U.ι_image_le V))
        (p.app (U.ι ''ᵁ V) r) := by
  let h := image_morphismRestrict_preimage p U V
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback p).obj J).presheaf.map (eqToHom h).op)).injective
  have hnat := (pulledFrame p e).naturality (p ⁻¹ᵁ (U.ι ''ᵁ V))
    ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V)) h.le (p.preimage_mono (U.ι_image_le V))
    (p.app (U.ι ''ᵁ V) r)
  rw [show (eqToHom h).op = (homOfLE h.le).op from rfl, hnat]
  change pullbackSectionLE p J (U.ι ''ᵁ V) ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V)) h.le _ =
    (frameFromOpenIso (pullbackOpenFrameIso p e)).equiv
      ((p ⁻¹ᵁ U).ι ''ᵁ ((p ∣_ U) ⁻¹ᵁ V)) _ _
  rw [frameFromOpenIso_image]
  have hr := ConcreteCategory.congr_hom (morphismRestrict_app p U V) r
  exact (pullbackOpenFrameIso_unit p e V r).symm.trans
    (congrArg (Scheme.Modules.Hom.app (pullbackOpenFrameIso p e).hom ((p ∣_ U) ⁻¹ᵁ V)) hr)

/-- The constructed pulled frame satisfies the precise accepted compatibility predicate. -/
theorem pulledFrame_compatible {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) :
    ArithmeticThetaNormalizedSections.FramePullbackCompatible p J U e (pulledFrame p e) := by
  intro V hVU r
  obtain ⟨W, hW⟩ : ∃ W : U.toScheme.Opens, U.ι ''ᵁ W = V := by
    refine ⟨U.ι ⁻¹ᵁ V, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  subst V
  exact pulledFrame_unit_image p e W r

/-- Pulling back a simultaneous affine frame cover keeps the actual preimage charts. -/
abbrev PairFrameCover.pullback {X Y : Scheme} (p : X ⟶ Y) [IsAffineHom p]
    {J H : Y.Modules} (C : PairFrameCover Y J H) :
    PairFrameCover X ((Scheme.Modules.pullback p).obj J) ((Scheme.Modules.pullback p).obj H) where
  index := C.index
  finite := C.finite
  opens i := p ⁻¹ᵁ C.opens i
  covers := by
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (C.covers (Set.mem_univ (p x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  affine i := (C.affine i).preimage p
  sourceFrame i := pulledFrame p (C.sourceFrame i)
  targetFrame i := pulledFrame p (C.targetFrame i)

/-- Every actual model projection is affine, as the base change of a map of spectra. -/
theorem model_projection_affine {X : Curve Omega} {K : FieldStage} (M : Model X K) :
    IsAffineHom M.projection :=
  MorphismProperty.of_isPullback M.cartesian.flip (inferInstance : IsAffineHom (constantMap K))

/-- The actual enlargement map is affine for the same reason. -/
theorem enlargement_affine {X : Curve Omega} {K K' : FieldStage} (M : Model X K) (h : K ≤ K') :
    IsAffineHom (enlargement M h).map :=
  MorphismProperty.of_isPullback (enlargement M h).cartesian.flip
    (inferInstance : IsAffineHom (extensionMap h))

/-- Transition functions pull back by the actual structure-sheaf ring map. -/
theorem transition_pulledFrame {X Y : Scheme} (p : X ⟶ Y) {J : Y.Modules} {U U' : Y.Opens}
    (e : LocalFrame Y J U) (e' : LocalFrame Y J U')
    (V : Y.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    p.app V (transition (e.equiv V hVU) (e'.equiv V hVU')) =
      transition ((pulledFrame p e).equiv (p ⁻¹ᵁ V) (p.preimage_mono hVU))
        ((pulledFrame p e').equiv (p ⁻¹ᵁ V) (p.preimage_mono hVU')) := by
  apply ((pulledFrame p e).equiv (p ⁻¹ᵁ V) (p.preimage_mono hVU)).injective
  rw [← pulledFrame_compatible p e V hVU]
  simp only [transition, LinearEquiv.apply_symm_apply]
  simpa only [map_one] using pulledFrame_compatible p e' V hVU' 1

/-- The coefficient of a pulled morphism is the actual pullback of its coefficient. -/
theorem homCoordinate_pullback {X Y : Scheme} (p : X ⟶ Y) {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a : J ⟶ H)
    (V : Y.Opens) (hVU : V ≤ U) :
    p.app V (homCoordinate e f a V hVU) =
      homCoordinate (pulledFrame p e) (pulledFrame p f) ((Scheme.Modules.pullback p).map a)
        (p ⁻¹ᵁ V) (p.preimage_mono hVU) := by
  apply ((pulledFrame p f).equiv (p ⁻¹ᵁ V) (p.preimage_mono hVU)).injective
  rw [← pulledFrame_compatible p f V hVU]
  simp only [homCoordinate, LinearEquiv.apply_symm_apply]
  rw [← pullbackLocalSection_map]
  congr 1
  simpa only [map_one] using pulledFrame_compatible p e V hVU 1

/-- Coefficients multiply under composition of actual line maps. -/
theorem homCoordinate_comp {Y : Scheme} {J H L : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (g : LocalFrame Y L U)
    (a : J ⟶ H) (b : H ⟶ L) (V : Y.Opens) (hVU : V ≤ U) :
    homCoordinate e g (a ≫ b) V hVU =
      homCoordinate e f a V hVU * homCoordinate f g b V hVU := by
  unfold homCoordinate
  change (g.equiv V hVU).symm (b.app V (a.app V (e.equiv V hVU 1))) = _
  rw [homCoordinate_apply e f a V hVU 1, one_mul, homCoordinate_apply f g b,
    LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

/-- The identity map has coefficient one in the same source and target frame. -/
theorem homCoordinate_id {Y : Scheme} {J : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (V : Y.Opens) (hVU : V ≤ U) :
    homCoordinate e e (𝟙 J) V hVU = 1 := by
  simp [homCoordinate]

/-- An isomorphism of actual lines has a unit coefficient in any two frames. -/
theorem homCoordinate_isUnit {Y : Scheme} {J H : Y.Modules} {U : Y.Opens}
    (e : LocalFrame Y J U) (f : LocalFrame Y H U) (a : J ⟶ H) [IsIso a]
    (V : Y.Opens) (hVU : V ≤ U) : IsUnit (homCoordinate e f a V hVU) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨homCoordinate f e (inv a) V hVU, ?_⟩
  rw [← homCoordinate_comp e f e a (inv a), IsIso.hom_inv_id, homCoordinate_id]

/-- An equal-open presentation does not change injectivity of a section map. -/
theorem appLE_injective_of_preimage_eq {X Y : Scheme} (p : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V = p ⁻¹ᵁ U) (hp : Function.Injective (p.app U)) :
    Function.Injective (p.appLE U V h.le) := by
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using hp

/-- The stage comparison reflects all equations on the specified base preimage charts. -/
theorem stageChartMap_injective {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (h : K ≤ K') (U : M.curve.space.Opens) :
    Function.Injective (stageChartMap M h U) := by
  exact appLE_injective_of_preimage_eq (enlargedModel M h).projection
    ((enlargement M h).map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison])
    (model_projection_app_injective_all (enlargedModel M h) _)

/-- Restriction of descended chart functions commutes with the actual stage comparison. -/
theorem stageChartMap_restrict {X : Curve Omega} {K K' : FieldStage}
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

/-- Compatible coefficients of the given morphism on a pulled affine frame cover. -/
def morphismCoefficients {Y : Scheme} {J H : Y.Modules}
    (C : PairFrameCover Y J H) (a : J ⟶ H) : CompatibleCoefficients C where
  value i := homCoordinate (C.sourceFrame i) (C.targetFrame i) a (C.opens i) le_rfl
  overlap i j := by
    rw [homCoordinate_restrict, homCoordinate_restrict]
    exact homCoordinate_transition (C.sourceFrame i) (C.sourceFrame j)
      (C.targetFrame i) (C.targetFrame j) a _ inf_le_left inf_le_right

/-- The coefficient construction recovers the original morphism. -/
theorem morphismCoefficients_hom {Y : Scheme} {J H : Y.Modules}
    (C : PairFrameCover Y J H) (a : J ⟶ H) : (morphismCoefficients C a).hom = a := by
  apply pairFrameCover_hom_ext C
  intro i
  exact (morphismCoefficients C a).hom_coordinate i

/-- Reverse the source and target frames on the same affine cover. -/
abbrev PairFrameCover.swap {Y : Scheme} {J H : Y.Modules} (C : PairFrameCover Y J H) :
    PairFrameCover Y H J where
  index := C.index
  finite := C.finite
  opens := C.opens
  covers := C.covers
  affine := C.affine
  sourceFrame := C.targetFrame
  targetFrame := C.sourceFrame

namespace CompatibleCoefficients
variable {Y : Scheme} {J H : Y.Modules} {C : PairFrameCover Y J H}
variable (c : CompatibleCoefficients C) (hc : ∀ i, IsUnit (c.value i))

/-- Invert unit coefficients on the same opens. Their overlap equation is proved
from the original transition relation, rather than assumed. -/
def inverse : CompatibleCoefficients C.swap where
  value i := (↑((hc i).unit⁻¹) : Γ(Y, C.opens i))
  overlap i j := by
    have hi : Y.presheaf.map (homOfLE (inf_le_left : C.opens i ⊓ C.opens j ≤ C.opens i)).op
        (c.value i) * Y.presheaf.map (homOfLE inf_le_left).op (↑((hc i).unit⁻¹)) = 1 := by
      rw [← map_mul, (hc i).mul_val_inv, map_one]
    have hj : Y.presheaf.map (homOfLE (inf_le_right : C.opens i ⊓ C.opens j ≤ C.opens j)).op
        (c.value j) * Y.presheaf.map (homOfLE inf_le_right).op (↑((hc j).unit⁻¹)) = 1 := by
      rw [← map_mul, (hc j).mul_val_inv, map_one]
    change transition ((C.sourceFrame i).equiv _ inf_le_left) ((C.sourceFrame j).equiv _ inf_le_right) *
        Y.presheaf.map (homOfLE inf_le_right).op (↑((hc j).unit⁻¹)) =
      transition ((C.targetFrame i).equiv _ inf_le_left) ((C.targetFrame j).equiv _ inf_le_right) *
        Y.presheaf.map (homOfLE inf_le_left).op (↑((hc i).unit⁻¹))
    calc
      _ = (_ * Y.presheaf.map (homOfLE inf_le_right).op (↑((hc j).unit⁻¹))) *
          (Y.presheaf.map (homOfLE inf_le_left).op (c.value i) *
            Y.presheaf.map (homOfLE inf_le_left).op (↑((hc i).unit⁻¹))) := by rw [hi, mul_one]
      _ = (transition ((C.sourceFrame i).equiv _ inf_le_left) ((C.sourceFrame j).equiv _ inf_le_right) *
          Y.presheaf.map (homOfLE inf_le_left).op (c.value i)) *
          (Y.presheaf.map (homOfLE inf_le_left).op (↑((hc i).unit⁻¹)) *
            Y.presheaf.map (homOfLE inf_le_right).op (↑((hc j).unit⁻¹))) := by ring
      _ = _ := by
        rw [← c.overlap i j]
        calc
          _ = (transition ((C.targetFrame i).equiv _ inf_le_left) ((C.targetFrame j).equiv _ inf_le_right) *
              Y.presheaf.map (homOfLE inf_le_left).op (↑((hc i).unit⁻¹))) *
              (Y.presheaf.map (homOfLE inf_le_right).op (c.value j) *
                Y.presheaf.map (homOfLE inf_le_right).op (↑((hc j).unit⁻¹))) := by ring
          _ = _ := by rw [hj, mul_one]

include hc in
/-- Unit chart coefficients give an isomorphism of the actual sheaves. -/
theorem isIso_hom : IsIso c.hom := by
  let d := c.inverse hc
  let CJ : PairFrameCover Y J J := { C with targetFrame := C.sourceFrame }
  let CH : PairFrameCover Y H H := { C.swap with targetFrame := C.targetFrame }
  have hd (i : C.index) : c.value i * d.value i = 1 := by
    change c.value i * ↑((hc i).unit⁻¹) = 1
    exact (hc i).mul_val_inv
  have hJ : c.hom ≫ d.hom = 𝟙 J := by
    apply pairFrameCover_hom_ext CJ
    intro i
    change homCoordinate (C.sourceFrame i) (C.sourceFrame i) (c.hom ≫ d.hom) (C.opens i) le_rfl =
      homCoordinate (C.sourceFrame i) (C.sourceFrame i) (𝟙 J) (C.opens i) le_rfl
    rw [homCoordinate_comp (C.sourceFrame i) (C.targetFrame i) (C.sourceFrame i),
      c.hom_coordinate, d.hom_coordinate, homCoordinate_id]
    exact hd i
  have hH : d.hom ≫ c.hom = 𝟙 H := by
    apply pairFrameCover_hom_ext CH
    intro i
    change homCoordinate (C.targetFrame i) (C.targetFrame i) (d.hom ≫ c.hom) (C.opens i) le_rfl =
      homCoordinate (C.targetFrame i) (C.targetFrame i) (𝟙 H) (C.opens i) le_rfl
    rw [homCoordinate_comp (C.targetFrame i) (C.sourceFrame i) (C.targetFrame i),
      d.hom_coordinate, c.hom_coordinate, homCoordinate_id, mul_comm]
    exact hd i
  exact ⟨⟨d.hom, hJ, hH⟩⟩

end CompatibleCoefficients

/-- The supplied finite frame cover after the actual model projection. -/
abbrev modelFrameCover {X : Curve Omega} {K : FieldStage} (M : Model X K)
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    PairFrameCover X.space ((Scheme.Modules.pullback M.projection).obj J)
      ((Scheme.Modules.pullback M.projection).obj H) := by
  letI := model_projection_affine M
  exact C.pullback M.projection

/-- The same cover over an actual finite enlargement. -/
abbrev stageFrameCover {X : Curve Omega} {K K' : FieldStage} (M : Model X K) (h : K ≤ K')
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    PairFrameCover (enlargedModel M h).curve.space ((Scheme.Modules.pullback (enlargement M h).map).obj J)
      ((Scheme.Modules.pullback (enlargement M h).map).obj H) := by
  letI := enlargement_affine M h
  exact C.pullback (enlargement M h).map

/-- Stage transition functions compare to the original ones, through the prescribed maps. -/
theorem stageChartMap_transition {X : Curve Omega} {K K' : FieldStage} (M : Model X K) (h : K ≤ K')
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

/-- Reflecting the original overlap equations proves compatibility of the descended functions. -/
def descendedCoefficients {X : Curve Omega} {K K' : FieldStage} (M : Model X K) (h : K ≤ K')
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

/-- Presenting the same preimage open differently does not change reflection of units. -/
theorem model_projection_appLE_isUnit_iff {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U)
    (V : X.space.Opens) (h : V = M.projection ⁻¹ᵁ U) (r : Γ(M.curve.space, U)) :
    IsUnit (M.projection.appLE U V h.le r) ↔ IsUnit r := by
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using model_projection_isUnit_iff M U hU r

/-- The stage comparison preserves and reflects units on the descended affine charts. -/
theorem stageChartMap_isUnit_iff {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (h : K ≤ K') (U : M.curve.space.Opens) (hU : IsAffineOpen U)
    (r : Γ((enlargedModel M h).curve.space, (enlargement M h).map ⁻¹ᵁ U)) :
    IsUnit (stageChartMap M h U r) ↔ IsUnit r := by
  let := enlargement_affine M h
  exact model_projection_appLE_isUnit_iff (enlargedModel M h) _ (hU.preimage (enlargement M h).map)
    _ (by rw [← Scheme.Hom.comp_preimage, (enlargement M h).comparison]) r

/-- Scalar compatibility of the actual section pullback, including target restriction. -/
theorem pullbackSectionLE_smul {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ p ⁻¹ᵁ U) (r : Γ(Y, U)) (s : Γ(J, U)) :
    pullbackSectionLE p J U V h (r • s) = p.appLE U V h r • pullbackSectionLE p J U V h s := by
  unfold pullbackSectionLE ArithmeticThetaNormalizedSections.pullbackLocalSection
  rw [Scheme.Modules.Hom.app_smul]
  change ((Scheme.Modules.pullback p).obj J).presheaf.map (homOfLE h).op
      (p.app U r • (show Γ((Scheme.Modules.pullback p).obj J, p ⁻¹ᵁ U) from
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app J).app U s)) = _
  rw [Scheme.Modules.map_smul]
  rfl

/-- The refinement triangle identifies the relevant preimage opens exactly. -/
theorem refinement_preimage {X : Curve Omega} {K K' : FieldStage} {M : Model X K} {N : Model X K'}
    (E : Refinement M N) (U : M.curve.space.Opens) :
    M.projection ⁻¹ᵁ U = N.projection ⁻¹ᵁ (E.map ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, E.comparison]

/-- The exact frozen refinement comparison preserves the iterated adjunction-unit section. -/
theorem refinementComparison_unit {X : Curve Omega} {K K' : FieldStage}
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

/-- The canonical refinement comparison has the expected coefficient action in the proved frames. -/
theorem refinementComparison_frame {X : Curve Omega} {K K' : FieldStage}
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

/-- Transport an actual finite-stage morphism through the frozen canonical comparisons. -/
def refinedHom {X : Curve Omega} {K K' : FieldStage} {M : Model X K} {N : Model X K'}
    (E : Refinement M N) {J H : M.curve.space.Modules}
    (b : (Scheme.Modules.pullback E.map).obj J ⟶ (Scheme.Modules.pullback E.map).obj H) :
    (Scheme.Modules.pullback M.projection).obj J ⟶ (Scheme.Modules.pullback M.projection).obj H :=
  (refinementComparison E J).inv ≫ (Scheme.Modules.pullback N.projection).map b ≫
    (refinementComparison E H).hom

/-- Transported morphisms have exactly the projected chart coefficients. -/
theorem homCoordinate_refinedHom {X : Curve Omega} {K K' : FieldStage}
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

/-- The glued descended coefficients recover the original morphism through the exact comparisons. -/
theorem descendedCoefficients_refinedHom {X : Curve Omega} {K K' : FieldStage}
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

/-- Actual model pullback detects equality of morphisms between framed lines. -/
theorem model_pullback_hom_injective {X : Curve Omega} {K : FieldStage} (M : Model X K)
    {J H : M.curve.space.Modules} (C : PairFrameCover M.curve.space J H) :
    Function.Injective (fun b : J ⟶ H => (Scheme.Modules.pullback M.projection).map b) := by
  intro b d hbd
  dsimp only at hbd
  apply pairFrameCover_hom_ext C
  intro i
  apply model_projection_app_injective_all M (C.opens i)
  rw [homCoordinate_pullback, homCoordinate_pullback, hbd]

/-- Actual model pullback also detects invertibility of morphisms between framed lines. -/
theorem model_pullback_isIso_iff {X : Curve Omega} {K : FieldStage} (M : Model X K)
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

/-- Canonical comparison isomorphisms do not lose equality information. -/
theorem refinedHom_injective {X : Curve Omega} {K K' : FieldStage}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) {J H : M.curve.space.Modules}
    (C : PairFrameCover N.curve.space ((Scheme.Modules.pullback E.map).obj J)
      ((Scheme.Modules.pullback E.map).obj H)) :
    Function.Injective (fun b => refinedHom E (J := J) (H := H) b) := by
  intro b d hbd
  apply model_pullback_hom_injective N C
  apply (cancel_epi (refinementComparison E J).inv).mp
  apply (cancel_mono (refinementComparison E H).hom).mp
  simpa only [refinedHom, Category.assoc] using hbd

/-- Canonical comparison isomorphisms preserve the precise invertibility criterion. -/
theorem refinedHom_isIso_iff {X : Curve Omega} {K K' : FieldStage}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) {J H : M.curve.space.Modules}
    (C : PairFrameCover N.curve.space ((Scheme.Modules.pullback E.map).obj J)
      ((Scheme.Modules.pullback E.map).obj H))
    (b : (Scheme.Modules.pullback E.map).obj J ⟶ (Scheme.Modules.pullback E.map).obj H) :
    IsIso (refinedHom E b) ↔ IsIso b := by
  simp only [refinedHom, isIso_comp_left_iff, isIso_comp_right_iff]
  exact model_pullback_isIso_iff N C b

end ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.exists_finite_stage
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.enlargedModel
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.enlargement

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.finite_tensor_family

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.tensor_stage_injective
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.empty_family

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.homCoordinate_apply
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.homCoordinate_restrict

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.model_pairFrameCover

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pairFrameCover_hom_ext
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.homCoordinate_transition

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.frameOpenIso

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackOpenFrameIso

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackGlobalFrameIso_unit
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.restrictionComparison_unit

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pulledFrame
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullback_isLineBundle

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.modelChartTensorIso

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.modelChartTensorIso_tmul

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.model_projection_app_injective

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartTensorIso

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartMap_base
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartMap_constant

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.finite_chart_functions

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.LocalHomFamily.hom
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.LocalHomFamily.hom_app

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.CompatibleCoefficients.hom_coordinate

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackComp_inv_unit

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.model_projection_app_injective_all
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackComp_hom_sectionLE
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackCongr_sectionLE

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.restrictionComparison_image
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackComp_inv_sectionLE

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullbackRestrictionIso_unit

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.model_projection_isUnit_iff

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pulledFrame_compatible

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.transition_pulledFrame
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.homCoordinate_pullback
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartMap_injective
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartMap_restrict

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.CompatibleCoefficients.isIso_hom

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.descendedCoefficients
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.stageChartMap_isUnit_iff

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.refinementComparison_unit
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.homCoordinate_refinedHom

namespace ArithmeticThetaFiniteFieldModelsR0221
open CategoryTheory AlgebraicGeometry FiniteLineHoms

/-- A finite family of actual line morphisms descends to one finite constant-field enlargement,
with the canonical comparison and exact preservation of isomorphisms and equality. -/
theorem finite_line_homs_model (X : Curve Omega) (K0 : FieldStage)
    (hK0 : FiniteDimensional ℚ K0) (M : Model X K0) (J H : M.curve.space.Modules)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space J)
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle M.curve.space H)
    (s : ℕ) (a : Fin s → ((Scheme.Modules.pullback M.projection).obj J ⟶
      (Scheme.Modules.pullback M.projection).obj H)) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (M1 : Model X K) (E : Refinement M M1)
      (a0 : Fin s → ((Scheme.Modules.pullback E.map).obj J ⟶
        (Scheme.Modules.pullback E.map).obj H)),
      (∀ i, (Scheme.Modules.pullback M1.projection).map (a0 i) ≫
        (refinementComparison E H).hom = (refinementComparison E J).hom ≫ a i) ∧
      (∀ i, IsIso (a0 i) ↔ IsIso (a i)) ∧
      (∀ i j, a0 i = a0 j ↔ a i = a j) := by
  classical
  let := hK0
  obtain ⟨C⟩ := model_pairFrameCover M J H hJ hH
  letI : Fintype C.index := C.finite
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
    simpa only [refinedHom, Iso.hom_inv_id_assoc] using hh
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

end ArithmeticThetaFiniteFieldModelsR0221

#print axioms ArithmeticThetaFiniteFieldModelsR0221.finite_line_homs_model
