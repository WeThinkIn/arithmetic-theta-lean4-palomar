import ConstantExtensionDefinitionsR0225

/-! Finite maps over the algebraic closure of any constant field: finite-stage
morphism descent, Cartesian refinements, and preservation of ramified rank. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base)
namespace FiniteMapExtension
variable {k : Type} [Field k]

theorem constantMap_flat (K : (FieldStage k)) : Flat (constantMap K) := by
  unfold constantMap Base
  infer_instance

theorem constantMap_surjective (K : (FieldStage k)) : Surjective (constantMap K) := by
  unfold constantMap Base
  infer_instance

theorem constantMap_quasiCompact (K : (FieldStage k)) : QuasiCompact (constantMap K) := by
  unfold constantMap Base
  infer_instance

/-- The actual model projection is faithfully flat and quasi-compact. -/
theorem projection_fpqc {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    Surjective M.projection ∧ Flat M.projection ∧ QuasiCompact M.projection := by
  exact ⟨MorphismProperty.of_isPullback M.cartesian.flip (constantMap_surjective K),
    MorphismProperty.of_isPullback M.cartesian.flip (constantMap_flat K),
    MorphismProperty.of_isPullback M.cartesian.flip (constantMap_quasiCompact K)⟩

@[simp] theorem constantMap_extensionMap {K L : (FieldStage k)} (h : K ≤ L) :
    constantMap L ≫ extensionMap h = constantMap K := by
  unfold constantMap extensionMap
  rw [← Spec.map_comp]
  rfl

/-- Base extension retains all the curve predicates by their genuine
base-change theorems. -/
def extendCurve {X : Curve (Omega k)} {K L : (FieldStage k)} (M : Model X K) (h : K ≤ L) :
    Curve L where
  space := pullback M.curve.map (extensionMap h)
  map := pullback.snd _ _
  proper := by
    have := M.curve.proper
    infer_instance
  smooth := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ M.curve.smooth
  geometricallyIntegral := by
    have := M.curve.geometricallyIntegral
    infer_instance

def extendProjection {X : Curve (Omega k)} {K L : (FieldStage k)} (M : Model X K) (h : K ≤ L) :
    X.space ⟶ (extendCurve M h).space :=
  pullback.lift M.projection (X.map ≫ constantMap L) (by
    rw [Category.assoc, constantMap_extensionMap]
    exact M.cartesian.w)

/-- The extended model uses the original projection, with its defining equation. -/
def extendModel {X : Curve (Omega k)} {K L : (FieldStage k)} (M : Model X K) (h : K ≤ L) :
    Model X L where
  curve := extendCurve M h
  projection := extendProjection M h
  cartesian := by
    have hc : IsPullback M.projection X.map M.curve.map
        (constantMap L ≫ extensionMap h) := by
      simpa only [constantMap_extensionMap] using M.cartesian
    have he : extendProjection M h ≫ pullback.fst M.curve.map (extensionMap h) =
        M.projection := pullback.lift_fst _ _ _
    rw [← he] at hc
    exact hc.of_right (pullback.lift_snd _ _ _)
      (.of_hasPullback M.curve.map (extensionMap h))

def extendRefinement {X : Curve (Omega k)} {K L : (FieldStage k)} (M : Model X K) (h : K ≤ L) :
    Refinement M (extendModel M h) where
  inclusion := h
  map := pullback.fst _ _
  cartesian := .of_hasPullback _ _
  comparison := pullback.lift_fst _ _ _

set_option maxHeartbeats 100000

/-- A concrete directed family; the empty coefficient set retains the input field. -/
def stage (K0 : (FieldStage k)) (s : Finset (Omega k)) : (FieldStage k) :=
  K0 ⊔ IntermediateField.adjoin k (s : Set (Omega k))

theorem stage_mono (K0 : (FieldStage k)) {s t : Finset (Omega k)} (h : s ≤ t) :
    stage K0 s ≤ stage K0 t :=
  sup_le_sup_left (IntermediateField.adjoin.mono k _ _ h) K0

theorem stage_finite (K0 : (FieldStage k)) [FiniteDimensional k K0] (s : Finset (Omega k)) :
    FiniteDimensional k (stage K0 s) := by
  have : FiniteDimensional k (IntermediateField.adjoin k (s : Set (Omega k))) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  change FiniteDimensional k ↥(K0 ⊔ IntermediateField.adjoin k (s : Set (Omega k)))
  infer_instance

theorem mem_stage (K0 : (FieldStage k)) (s : Finset (Omega k)) {x : (Omega k)} (hx : x ∈ s) :
    x ∈ stage K0 s :=
  (show IntermediateField.adjoin k (s : Set (Omega k)) ≤ stage K0 s from le_sup_right)
    (IntermediateField.subset_adjoin k _ hx)

def fieldInclusion {K L : (FieldStage k)} (h : K ≤ L) :
    CommRingCat.of K ⟶ CommRingCat.of L :=
  CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom

@[simp] theorem fieldInclusion_self (K : (FieldStage k)) :
    fieldInclusion (le_refl K) = 𝟙 (CommRingCat.of K) := by
  ext x; rfl

@[simp] theorem fieldInclusion_comp {K L M : (FieldStage k)} (h : K ≤ L) (h' : L ≤ M) :
    fieldInclusion h ≫ fieldInclusion h' = fieldInclusion (h.trans h') := by
  ext x; rfl

@[simp] theorem fieldInclusion_subtype {K L : (FieldStage k)} (h : K ≤ L) :
    fieldInclusion h ≫ CommRingCat.ofHom L.subtype = CommRingCat.ofHom K.subtype := by
  ext x; rfl

def fieldDiagram (K0 : (FieldStage k)) : Finset (Omega k) ⥤ CommRingCat where
  obj s := CommRingCat.of (stage K0 s)
  map h := fieldInclusion (stage_mono K0 (leOfHom h))
  map_id _ := fieldInclusion_self _
  map_comp _ _ := (fieldInclusion_comp _ _).symm

def fieldCocone (K0 : (FieldStage k)) : Cocone (fieldDiagram K0) where
  pt := CommRingCat.of (Omega k)
  ι :=
    { app s := CommRingCat.ofHom (stage K0 s).subtype
      naturality _ _ h := (fieldInclusion_subtype (stage_mono K0 (leOfHom h))).trans
        (Category.comp_id _).symm }

/-- The algebraic closure is the actual colimit of the finite fields, with
inclusion maps and the usual scalar structure. -/
def fieldColimit (K0 : (FieldStage k)) : IsColimit (fieldCocone K0) := by
  have : ReflectsColimit (fieldDiagram K0) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf' _
  · intro x
    exact ⟨{x}, ⟨x, mem_stage K0 {x} (Finset.mem_singleton_self x)⟩, rfl⟩
  · intro i x y h
    refine ⟨i, 𝟙 i, ?_⟩
    exact Subtype.ext h

def baseDiagram (K0 : (FieldStage k)) : (Finset (Omega k))ᵒᵖ ⥤ Scheme :=
  (fieldDiagram K0).op ⋙ Scheme.Spec

def baseCone (K0 : (FieldStage k)) : Cone (baseDiagram K0) :=
  Scheme.Spec.mapCone (fieldCocone K0).op

def baseLimit (K0 : (FieldStage k)) : IsLimit (baseCone K0) :=
  isLimitOfPreserves Scheme.Spec (fieldColimit K0).op

@[simp] theorem extensionMap_comp {K L M : (FieldStage k)} (h : K ≤ L) (h' : L ≤ M) :
    extensionMap h' ≫ extensionMap h = extensionMap (h.trans h') := by
  unfold extensionMap
  rw [← Spec.map_comp]
  rfl

@[simp] theorem extensionMap_self (K : (FieldStage k)) : extensionMap (le_refl K) = 𝟙 (Base K) := by
  unfold extensionMap
  change Spec.map (𝟙 (CommRingCat.of K)) = _
  simp

theorem extensionMap_affine {K L : (FieldStage k)} (h : K ≤ L) : IsAffineHom (extensionMap h) := by
  unfold extensionMap
  infer_instance

/-- Actual scalar-extension transition morphisms. -/
def modelTransition {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {s t : Finset (Omega k)} (h : t ≤ s) :
    (extendCurve M (show K ≤ stage K s from le_sup_left)).space ⟶
      (extendCurve M (show K ≤ stage K t from le_sup_left)).space :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ extensionMap (stage_mono K h)) (by
      rw [Category.assoc, extensionMap_comp]
      exact pullback.condition)

@[simp, reassoc] theorem modelTransition_fst {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {s t : Finset (Omega k)} (h : t ≤ s) :
    modelTransition M h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[simp, reassoc] theorem modelTransition_snd {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {s t : Finset (Omega k)} (h : t ≤ s) :
    modelTransition M h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ extensionMap (stage_mono K h) := pullback.lift_snd _ _ _

def modelDiagram {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    (Finset (Omega k))ᵒᵖ ⥤ Scheme where
  obj s := (extendCurve M (show K ≤ stage K s.unop from le_sup_left)).space
  map h := modelTransition M (leOfHom h.unop)
  map_id s := by
    apply pullback.hom_ext <;> simp
  map_comp h h' := by
    apply pullback.hom_ext <;> simp [Category.assoc, modelTransition_snd_assoc]

def modelBase {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    modelDiagram M ⟶ baseDiagram K where
  app _ := pullback.snd _ _
  naturality _ _ h := by
    exact modelTransition_snd M (leOfHom h.unop)

def modelCone {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) : Cone (modelDiagram M) where
  pt := X.space
  π :=
    { app s := extendProjection M (show K ≤ stage K s.unop from le_sup_left)
      naturality _ _ h := by
        apply pullback.hom_ext <;>
          simp [modelDiagram, extendProjection, Category.assoc] }

def modelLimit {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    IsLimit (modelCone M) := by
  have : IsConnected (Finset (Omega k))ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfIsPullbackOfIsConnected (modelBase M) (modelCone M) (baseCone K)
    { hom := X.map
      w := fun _ => (pullback.lift_snd _ _ _).symm }
    (fun s => (extendModel M (show K ≤ stage K s.unop from le_sup_left)).cartesian)
    (baseLimit K)

theorem pullback_fst_extension_affine {S : Scheme} {K L : (FieldStage k)}
    (f : S ⟶ Base K) (h : K ≤ L) : IsAffineHom (pullback.fst f (extensionMap h)) :=
  MorphismProperty.pullback_fst _ _ (extensionMap_affine h)

attribute [local instance] extensionMap_affine pullback_fst_extension_affine

@[simp, reassoc] theorem extendProjection_fst {X : Curve (Omega k)} {K L : (FieldStage k)}
    (M : Model X K) (h : K ≤ L) :
    extendProjection M h ≫ pullback.fst M.curve.map (extensionMap h) = M.projection :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem extendProjection_snd {X : Curve (Omega k)} {K L : (FieldStage k)}
    (M : Model X K) (h : K ≤ L) :
    extendProjection M h ≫ pullback.snd M.curve.map (extensionMap h) = X.map ≫ constantMap L :=
  pullback.lift_snd _ _ _

instance modelDiagram_affine {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    {s t : (Finset (Omega k))ᵒᵖ} (h : s ⟶ t) : IsAffineHom ((modelDiagram M).map h) := by
  have : IsAffineHom ((modelDiagram M).map h ≫
      pullback.fst M.curve.map (extensionMap (show K ≤ stage K t.unop from le_sup_left))) := by
    change IsAffineHom (modelTransition M (leOfHom h.unop) ≫ _)
    rw [modelTransition_fst]
    infer_instance
  exact IsAffineHom.of_comp _ (pullback.fst _ _)

instance modelDiagram_compact {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    (s : (Finset (Omega k))ᵒᵖ) : CompactSpace ((modelDiagram M).obj s) := by
  have := (extendCurve M (show K ≤ stage K s.unop from le_sup_left)).proper
  exact QuasiCompact.compactSpace_of_compactSpace
    (extendCurve M (show K ≤ stage K s.unop from le_sup_left)).map

instance modelDiagram_quasiSeparated {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
    (s : (Finset (Omega k))ᵒᵖ) : QuasiSeparatedSpace ((modelDiagram M).obj s) := by
  have := (extendCurve M (show K ≤ stage K s.unop from le_sup_left)).proper
  exact quasiSeparatedSpace_of_quasiSeparated
    (extendCurve M (show K ≤ stage K s.unop from le_sup_left)).map

def modelOver {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K) :
    modelDiagram M ⟶ (Functor.const _).obj (Base K) where
  app _ := pullback.fst _ _ ≫ M.curve.map
  naturality _ _ h := by
    simp only [Functor.const_obj_map]
    exact modelTransition_fst_assoc M (leOfHom h.unop) M.curve.map

/-- Finite presentation descends the actual map to the original target model.
No finite-stage morphism or coefficient-descent assertion is assumed. -/
theorem exists_stage_map {X Y : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (N : Model Y K) (f : X.space ⟶ Y.space)
    (hf : f ≫ Y.map = X.map) :
    ∃ (s : Finset (Omega k))
      (a : (extendCurve M (show K ≤ stage K s from le_sup_left)).space ⟶ N.curve.space),
      extendProjection M (show K ≤ stage K s from le_sup_left) ≫ a = f ≫ N.projection ∧
      a ≫ N.curve.map = pullback.fst _ _ ≫ M.curve.map := by
  have : SmoothOfRelativeDimension 1 N.curve.map := N.curve.smooth
  have : Smooth N.curve.map := SmoothOfRelativeDimension.smooth 1 N.curve.map
  obtain ⟨i, a, ha, hb⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (modelDiagram M) (modelOver M) N.curve.map (modelCone M) (modelLimit M)
    (f ≫ N.projection) (by
      ext s
      change extendProjection M _ ≫ (pullback.fst _ _ ≫ M.curve.map) =
        (f ≫ N.projection) ≫ N.curve.map
      rw [← Category.assoc, extendProjection_fst, M.cartesian.w,
        Category.assoc, N.cartesian.w, ← Category.assoc, hf])
  exact ⟨i.unop, a, ha, hb⟩

/-- A morphism over the base between two scalar-extension models has a Cartesian
comparison square whenever it is the prescribed map after extension. -/
theorem cartesian_of_comparison {X Y : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (N : Model Y K) (f : X.space ⟶ Y.space)
    (hf : f ≫ Y.map = X.map) (g : M.curve.space ⟶ N.curve.space)
    (hg : g ≫ N.curve.map = M.curve.map)
    (he : M.projection ≫ g = f ≫ N.projection) :
    IsPullback M.projection f g N.projection := by
  have hc := M.cartesian.flip
  rw [← hf, ← hg] at hc
  exact (hc.of_right he.symm N.cartesian.flip).flip

/-- Finite fibers descend through the actual Cartesian square. Properness of
both curve models then promotes quasi-finiteness to finiteness. -/
theorem properties_of_cartesian {X Y : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (N : Model Y K) (f : X.space ⟶ Y.space)
    [IsFinite f] [Surjective f] (g : M.curve.space ⟶ N.curve.space)
    (hg : g ≫ N.curve.map = M.curve.map)
    (hc : IsPullback M.projection f g N.projection) :
    IsFinite g ∧ Surjective g ∧
      ∀ y : Y.space, g.finrank (N.projection y) = f.finrank y := by
  have : Surjective N.projection := (projection_fpqc N).1
  have : IsProper N.curve.map := N.curve.proper
  have : IsProper (g ≫ N.curve.map) := hg.symm ▸ M.curve.proper
  have : IsProper g := IsProper.of_comp g N.curve.map
  have : LocallyQuasiFinite g := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro z
    obtain ⟨y, rfl⟩ := N.projection.surjective z
    have he : M.projection '' (f ⁻¹' {y}) = g ⁻¹' {N.projection y} := by
      simpa only [Set.image_singleton] using
        Scheme.image_preimage_eq_of_isPullback hc.flip {y}
    rw [← he]
    exact (f.finite_preimage_singleton y).image M.projection
  have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  have : Surjective (f ≫ N.projection) := inferInstance
  have : Surjective (M.projection ≫ g) := hc.w.symm ▸ inferInstance
  have : Surjective g := Surjective.of_comp M.projection g
  have : Flat N.projection := (projection_fpqc N).2.1
  have : GeometricallyIntegral Y.map := Y.geometricallyIntegral
  have : IsIntegral Y.space := GeometricallyIntegral.isIntegral_of_subsingleton Y.map
  have : GeometricallyIntegral N.curve.map := N.curve.geometricallyIntegral
  have : IsIntegral N.curve.space :=
    GeometricallyIntegral.isIntegral_of_subsingleton N.curve.map
  exact ⟨inferInstance, inferInstance, fun y =>
    (ArithmeticThetaRamifiedRootModelsR0222.RamifiedFiniteMap.finrank_cartesian M.projection f g N.projection hc y).symm⟩


end FiniteMapExtension
open FiniteMapExtension

/-- The prescribed finite surjective map descends over a common finite extension. -/
theorem finite_map_constant_extension :
    ∀ (k : Type) [Field k] [CharZero k], ∀ (X Y : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (K0 : (ArithmeticThetaConstantExtensionR0225.FieldStage k)), FiniteDimensional k K0 → ∀ (M : ArithmeticThetaConstantExtensionR0225.Model X K0) (N : ArithmeticThetaConstantExtensionR0225.Model Y K0) (f : Quiver.Hom X.space Y.space), CategoryTheory.CategoryStruct.comp f Y.map = X.map → AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Surjective f → ∃ K : (ArithmeticThetaConstantExtensionR0225.FieldStage k), FiniteDimensional k K ∧ ∃ (M1 : ArithmeticThetaConstantExtensionR0225.Model X K) (N1 : ArithmeticThetaConstantExtensionR0225.Model Y K) (_ : ArithmeticThetaConstantExtensionR0225.Refinement M M1) (_ : ArithmeticThetaConstantExtensionR0225.Refinement N N1) (g : Quiver.Hom M1.curve.space N1.curve.space), CategoryTheory.CategoryStruct.comp g N1.curve.map = M1.curve.map ∧ CategoryTheory.IsPullback M1.projection f g N1.projection ∧ AlgebraicGeometry.IsFinite g ∧ AlgebraicGeometry.Surjective g ∧ ∀ y : Y.space, AlgebraicGeometry.Scheme.Hom.finrank g (N1.projection y) = AlgebraicGeometry.Scheme.Hom.finrank f y := by
  intro k _ _ X Y K0 hK M N f hf hfinite hsurjective
  have : FiniteDimensional k K0 := hK
  have : IsFinite f := hfinite
  have : Surjective f := hsurjective
  obtain ⟨s, a, ha, hb⟩ := exists_stage_map M N f hf
  let K := stage K0 s
  have h : K0 ≤ K := le_sup_left
  let M1 := extendModel M h
  let N1 := extendModel N h
  let g : M1.curve.space ⟶ N1.curve.space :=
    pullback.lift a (pullback.snd M.curve.map (extensionMap h))
      (hb.trans pullback.condition)
  have hg : g ≫ N1.curve.map = M1.curve.map := pullback.lift_snd _ _ _
  have he : M1.projection ≫ g = f ≫ N1.projection := by
    apply pullback.hom_ext
    · change extendProjection M h ≫ g ≫ pullback.fst _ _ =
        (f ≫ extendProjection N h) ≫ pullback.fst _ _
      dsimp only [g]
      rw [pullback.lift_fst, Category.assoc, extendProjection_fst]
      exact ha
    · change extendProjection M h ≫ g ≫ pullback.snd _ _ =
        (f ≫ extendProjection N h) ≫ pullback.snd _ _
      dsimp only [g]
      rw [pullback.lift_snd, extendProjection_snd, Category.assoc,
        extendProjection_snd, ← Category.assoc, hf]
  have hc : IsPullback M1.projection f g N1.projection :=
    cartesian_of_comparison M1 N1 f hf g hg he
  exact ⟨K, stage_finite K0 s, M1, N1, extendRefinement M h, extendRefinement N h,
    g, hg, hc, FiniteMapExtension.properties_of_cartesian M1 N1 f g hg hc⟩

end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.finite_map_constant_extension
