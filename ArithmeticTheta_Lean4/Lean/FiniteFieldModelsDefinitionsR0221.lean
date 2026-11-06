import PullbackTensorSections
import NormalizedSectionDefinitions
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Finite constant-field models, with actual Cartesian maps and sheaf comparisons.
These records describe construction outputs, not assumed descent data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFiniteFieldModelsR0221
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaNormalizedSections

abbrev Omega := AlgebraicClosure ℚ
abbrev FieldStage := IntermediateField ℚ Omega
abbrev Base (k : Type) [CommRing k] := Spec (CommRingCat.of k)
def constantMap (K : FieldStage) : Base Omega ⟶ Base K :=
  Spec.map (CommRingCat.ofHom K.subtype)
def extensionMap {K K' : FieldStage} (h : K ≤ K') : Base K' ⟶ Base K :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

/-- Proper smooth geometrically integral curves with their actual structure map. -/
structure Curve (k : Type) [Field k] where
  space : Scheme
  map : space ⟶ Base k
  proper : IsProper map
  smooth : SmoothOfRelativeDimension 1 map
  geometricallyIntegral : GeometricallyIntegral map

/-- A model is related by a Cartesian square, not by a freely chosen expansion. -/
structure Model (X : Curve Omega) (K : FieldStage) where
  curve : Curve K
  projection : X.space ⟶ curve.space
  cartesian : IsPullback projection X.map curve.map (constantMap K)

/-- Enlargement keeps the original finite-field model and its actual map. -/
structure Refinement {X : Curve Omega} {K K' : FieldStage}
    (M : Model X K) (N : Model X K') where
  inclusion : K ≤ K'
  map : N.curve.space ⟶ M.curve.space
  cartesian : IsPullback map N.curve.map M.curve.map (extensionMap inclusion)
  comparison : N.projection ≫ map = M.projection

abbrev Sections {X : Scheme} (H : X.Modules) := H.presheaf.obj (Opposite.op ⊤)

/-- The recursively induced tensor comparison, including tensor exponent zero. -/
def powerIso {X : Scheme} {H J : X.Modules} (e : H ≅ J) :
    (n : ℕ) → tensorPower X H n ≅ tensorPower X J n
  | 0 => Iso.refl _
  | n+1 => sheafTensorCongr X (powerIso e n) e

def powerComparison {X Y : Scheme} (p : X ⟶ Y) (H : Y.Modules)
    {J : X.Modules} (e : (Scheme.Modules.pullback p).obj H ≅ J) (n : ℕ) :
    (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X J n :=
  pullback_tensorPower_iso X Y p H n ≪≫ powerIso e n

/-- This uses exactly the commuting triangle of the refinement. -/
def refinementComparison {X : Curve Omega} {K K' : FieldStage}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) (H : M.curve.space.Modules) :
    (Scheme.Modules.pullback N.projection).obj ((Scheme.Modules.pullback E.map).obj H) ≅
      (Scheme.Modules.pullback M.projection).obj H :=
  (Scheme.Modules.pullbackComp N.projection E.map).app H ≪≫
    (Scheme.Modules.pullbackCongr E.comparison).app H

/-- Finite algebraic data of the compact square-root cover. The source's complete
formal disk and its power series are deliberately not claimed to be finite data. -/
structure RootData (s n b : ℕ) where
  base : Curve Omega
  cover : Curve Omega
  map : cover.space ⟶ base.space
  over_eq : map ≫ base.map = cover.map
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  degree : ∀ x : base.space, 0 < map.finrank x ∧ map.finrank x ≤ b
  cusp : Base Omega ⟶ cover.space
  cusp_over : cusp ≫ cover.map = 𝟙 _
  weight : base.space.Modules
  weight_line : IsLineBundle base.space weight
  half : cover.space.Modules
  half_line : IsLineBundle cover.space half
  square : tensorPower cover.space half 2 ≅ (Scheme.Modules.pullback map).obj weight
  sections : Fin s → Sections (tensorPower cover.space half n)

/-- Transport along the exact square of the two finite-field models. -/
def squareTargetComparison {s n b : ℕ} (D : RootData s n b) {K : FieldStage}
    (X : Model D.base K) (Y : Model D.cover K)
    (f : Y.curve.space ⟶ X.curve.space)
    (hf : Y.projection ≫ f = D.map ≫ X.projection)
    (W : X.curve.space.Modules)
    (e : (Scheme.Modules.pullback X.projection).obj W ≅ D.weight) :
    (Scheme.Modules.pullback Y.projection).obj ((Scheme.Modules.pullback f).obj W) ≅
      (Scheme.Modules.pullback D.map).obj D.weight :=
  (Scheme.Modules.pullbackComp Y.projection f).app W ≪≫
    (Scheme.Modules.pullbackCongr hf).app W ≪≫
    ((Scheme.Modules.pullbackComp D.map X.projection).app W).symm ≪≫
    (Scheme.Modules.pullback D.map).mapIso e

/-- A simultaneous finite-field model of the SAME cover, cusp, square and sections.
Every geometric property and equality below is an output to be constructed. -/
structure RootModel {s n b : ℕ} (D : RootData s n b) (K : FieldStage) where
  base : Model D.base K
  cover : Model D.cover K
  map : cover.curve.space ⟶ base.curve.space
  over_eq : map ≫ base.curve.map = cover.curve.map
  comparison : cover.projection ≫ map = D.map ≫ base.projection
  cartesian : IsPullback cover.projection D.map map base.projection
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  degree : ∀ x : base.curve.space, 0 < map.finrank x ∧ map.finrank x ≤ b
  cusp : Base K ⟶ cover.curve.space
  cusp_over : cusp ≫ cover.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.projection
  weight : base.curve.space.Modules
  weight_line : IsLineBundle base.curve.space weight
  weightComparison : (Scheme.Modules.pullback base.projection).obj weight ≅ D.weight
  half : cover.curve.space.Modules
  half_line : IsLineBundle cover.curve.space half
  halfComparison : (Scheme.Modules.pullback cover.projection).obj half ≅ D.half
  square : tensorPower cover.curve.space half 2 ≅ (Scheme.Modules.pullback map).obj weight
  square_comparison :
    (Scheme.Modules.pullback cover.projection).mapIso square ≪≫
      squareTargetComparison D base cover map comparison weight weightComparison =
    powerComparison cover.projection half halfComparison 2 ≪≫ D.square
  sections : Fin s → Sections (tensorPower cover.curve.space half n)
  sections_comparison : ∀ i,
    (powerComparison cover.projection half halfComparison n).hom.app ⊤
      (pullbackGlobalSection cover.projection (tensorPower cover.curve.space half n)
        (sections i)) = D.sections i

end ArithmeticThetaFiniteFieldModelsR0221
