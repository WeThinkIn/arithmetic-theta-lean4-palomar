import ConstantExtensionDefinitionsR0225

/-! Descent of an invertible sheaf after finite extension of the given constant field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ArithmeticThetaNormalizedSections
open ArithmeticThetaFiniteFieldModelsR0221 (Curve)
open ArithmeticThetaFiniteFieldModelsR0221.LineFiniteModel (isLineBundle_iff_isInvertible)

namespace ArithmeticThetaConstantExtensionR0225
namespace LineConstantExtension
variable {k : Type} [Field k]

/-- Scalar-extension maps compose using the given intermediate-field inclusion. -/
theorem constantMap_extensionMap {K0 K : (FieldStage k)} (h : K0 ≤ K) :
    constantMap K ≫ extensionMap h = constantMap K0 := by
  unfold constantMap extensionMap
  rw [← Spec.map_comp]
  rfl

/-- Enlarge the given curve model by its actual scheme fiber product. -/
def enlargedCurve {X : Curve (Omega k)} {K0 K : (FieldStage k)}
    (M : Model X K0) (h : K0 ≤ K) : Curve K where
  space := pullback M.curve.map (extensionMap h)
  map := pullback.snd M.curve.map (extensionMap h)
  proper := MorphismProperty.pullback_snd _ _ M.curve.proper
  smooth := by
    let := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd _ _ M.curve.smooth
  geometricallyIntegral := MorphismProperty.pullback_snd _ _ M.curve.geometricallyIntegral

/-- The original `Omega`-curve is the scalar extension of the enlarged model. -/
def enlargedModel {X : Curve (Omega k)} {K0 K : (FieldStage k)}
    (M : Model X K0) (h : K0 ≤ K) : Model X K := by
  let t := IsPullback.of_hasPullback M.curve.map (extensionMap h)
  have s : IsPullback M.projection X.map M.curve.map
      (constantMap K ≫ extensionMap h) := by
    rw [constantMap_extensionMap h]
    exact M.cartesian
  exact {
    curve := enlargedCurve M h
    projection := t.lift M.projection (X.map ≫ constantMap K)
      (by rw [s.w, Category.assoc])
    cartesian := s.of_right' t }

/-- The enlargement satisfies every comparison field of the frozen refinement record. -/
def modelRefinement {X : Curve (Omega k)} {K0 K : (FieldStage k)}
    (M : Model X K0) (h : K0 ≤ K) : Refinement M (enlargedModel M h) where
  inclusion := h
  map := pullback.fst M.curve.map (extensionMap h)
  cartesian := IsPullback.of_hasPullback M.curve.map (extensionMap h)
  comparison := (IsPullback.of_hasPullback M.curve.map (extensionMap h)).lift_fst _ _ _


end LineConstantExtension
open LineConstantExtension

/-- A line on a prescribed finite model descends after a finite enlargement. -/
theorem line_constant_extension (k : Type) [Field k] [CharZero k] (X : Curve (Omega k)) (K0 : (FieldStage k))
    (hK0 : FiniteDimensional k K0) (M : Model X K0) (J : X.space.Modules)
    (hJ : IsLineBundle X.space J) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧
      ∃ (M1 : Model X K) (_ : Refinement M M1) (J0 : M1.curve.space.Modules),
        IsLineBundle M1.curve.space J0 ∧
        Nonempty ((Scheme.Modules.pullback M1.projection).obj J0 ≅ J) := by
  letI := hK0
  letI := M.curve.proper
  let e := M.cartesian.isoPullback
  let L := (Scheme.Modules.pullback e.inv).obj J
  have hL : Scheme.Modules.IsInvertible L :=
    ((isLineBundle_iff_isInvertible X.space J).mp hJ).pullback e.inv
  obtain ⟨F, hF, J0, hJ0, hc⟩ :=
    Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
      K0 (Omega k) M.curve.map L hL
  let K : (FieldStage k) := F.restrictScalars k
  have h : K0 ≤ K := by
    intro x hx
    exact F.algebraMap_mem (⟨x, hx⟩ : K0)
  letI := hF
  have hK : FiniteDimensional k K := FiniteDimensional.trans k K0 F
  let N := enlargedModel M h
  let E := modelRefinement M h
  let c := e.inv ≫ N.projection
  have hc₁ : c ≫ pullback.fst M.curve.map
      (Spec.map (CommRingCat.ofHom (algebraMap K0 F))) =
      pullback.fst M.curve.map (constantMap K0) := by
    change e.inv ≫ N.projection ≫ E.map = _
    rw [E.comparison]
    exact M.cartesian.isoPullback_inv_fst
  have hc₂ : c ≫ pullback.snd M.curve.map
      (Spec.map (CommRingCat.ofHom (algebraMap K0 F))) =
      pullback.snd M.curve.map (constantMap K0) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F (Omega k))) := by
    change e.inv ≫ N.projection ≫ N.curve.map = _
    rw [N.cartesian.w, ← Category.assoc]
    rw [M.cartesian.isoPullback_inv_snd]
    rfl
  obtain ⟨d⟩ := hc c hc₁ hc₂
  refine ⟨K, hK, N, E, J0, (isLineBundle_iff_isInvertible _ _).mpr hJ0, ⟨?_⟩⟩
  have hec : e.hom ≫ c = N.projection := by simp [c]
  exact ((Scheme.Modules.pullbackCongr hec).app J0).symm ≪≫
    ((Scheme.Modules.pullbackComp e.hom c).app J0).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso d ≪≫
    (Scheme.Modules.pullbackComp e.hom e.inv).app J ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app J ≪≫
    (Scheme.Modules.pullbackId X.space).app J


end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.line_constant_extension
