module

public import FiniteModelFramedRootValuesR0224
public import SmoothProjectiveLevelCompletionR0179
public import PointedRamifiedRootModelR0222
public import ValuativeSimultaneousSectionsR0223
public import ValuativeRootIntegralityR0223

@[expose] public section

-- Preserve original field inference without overriding specialized local-ring instances.
attribute [local instance 999] HenselianLocalRing.toIsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaPrescribedRootModelsR0224
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaValuativeRootsR0223

namespace PrescribedProjectiveRootFiniteModelR0224

lemma projective (k : Type) [Field k] (X : Curve k) :
    Nonempty (ProjectivePresentation k X.space X.map) := by
  letI := X.proper
  letI := X.smooth
  letI := X.geometricallyIntegral
  letI := GeometricallyIntegral.isIntegral_of_subsingleton X.map
  obtain ⟨d, e, he, hb⟩ :=
    ArithmeticThetaLevelCompactificationR0179.SmoothProjectiveLevelCompletionR0179.Projectivity.exists_embedding
      k X.space X.map
  exact ⟨⟨d, e, he, hb⟩⟩

end PrescribedProjectiveRootFiniteModelR0224

/-- Construct the prescribed valuative roots, and descend their finite algebraic
 data to one number field while retaining the original whole-section values. -/
theorem prescribed_projective_root_finite_model :
∀ (X : ArithmeticThetaFiniteFieldModelsR0221.Curve ArithmeticThetaFiniteFieldModelsR0221.Omega) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (E : Type) [Field E] (A : ValuationSubring E) (f : Quiver.Hom (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A) X.space), AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaValuativeRootsR0223.genericInclusion E A) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (r : Fin s → E), (∀ j, ArithmeticThetaValuativeRootsR0223.FieldEquation E A f J n (F j) h (r j)) → ∀ (c : Quiver.Hom (ArithmeticThetaFiniteFieldModelsR0221.Base ArithmeticThetaFiniteFieldModelsR0221.Omega) (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A)), c (IsLocalRing.closedPoint ArithmeticThetaFiniteFieldModelsR0221.Omega) = IsLocalRing.closedPoint A → CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp c f) X.map = CategoryTheory.CategoryStruct.id _ → ∀ K0 : ArithmeticThetaFiniteFieldModelsR0221.FieldStage, FiniteDimensional ℚ K0 → ∃ T : ArithmeticThetaPrescribedRootModelsR0224.RootRealization X J n s F E A f h r c, Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation ArithmeticThetaFiniteFieldModelsR0221.Omega X.space X.map) ∧ Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation ArithmeticThetaFiniteFieldModelsR0221.Omega T.cover.space (CategoryTheory.CategoryStruct.comp T.cover.map X.map)) ∧ ArithmeticThetaPrescribedRootModelsR0224.FiniteRealization T K0 := by
  intro X J hJ n s hn F hF E _ A f hdom h hh r hr c _hc hcf K0 hK0
  classical
  letI := X.proper
  letI := X.smooth
  letI := X.geometricallyIntegral
  letI := GeometricallyIntegral.isIntegral_of_subsingleton X.map
  have hi (j : Fin s) := valuative_root_integrality E A X.space f J n hn
    (F j) h hh (r j) (hr j)
  choose a ha using fun j => (hi j).exists
  obtain ⟨R, g, hg, hgd, t, ht⟩ := valuative_simultaneous_sections
    Omega X.space X.map J hJ n s hn F hF E A f hdom h hh a (fun j => (ha j).2)
  letI := R.integral
  letI := R.smooth
  have hgeom : GeometricallyIntegral (R.map ≫ X.map) :=
    geometricallyIntegral_of_isAlgClosed (R.map ≫ X.map)
  have hcentre : (c ≫ g) ≫ (R.map ≫ X.map) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc g, hg, ← Category.assoc]
    exact hcf
  let T : RootRealization X J n s F E A f h r c := {
    cover := R
    geometric := hgeom
    line := ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187.line_of_invertible J hJ
    powers_nonzero := hF
    coefficients := a
    coefficients_eq := fun j => (ha j).1
    lift := g
    lift_eq := hg
    dominant := hgd
    roots := t
    roots_nonzero := fun j => (ht j).1
    equation := fun j => (ht j).2.1
    values := fun j => (ht j).2.2
    centre_over := hcentre }
  obtain ⟨K, hK, h0K, ⟨M⟩⟩ :=
    ArithmeticThetaRamifiedRootModelsR0222.pointed_ramified_root_model s n hn T.data K0 hK0
  refine ⟨T, PrescribedProjectiveRootFiniteModelR0224.projective Omega X,
    PrescribedProjectiveRootFiniteModelR0224.projective Omega T.data.cover,
    K, hK, h0K, M,
    PrescribedProjectiveRootFiniteModelR0224.projective K M.base.curve,
    PrescribedProjectiveRootFiniteModelR0224.projective K M.cover.curve, ?_⟩
  exact finite_model_framed_root_values s n T.data K M E A f h hh
    T.coefficients T.lift T.lift_eq T.values

#print axioms prescribed_projective_root_finite_model
end ArithmeticThetaPrescribedRootModelsR0224
