module

public import PointedSquareCoverFiniteModelR0221

@[expose] public section

/-! Finite constant-field models of an existing ramified Kth-root family.
The algebraic cover and its sections are inputs over Qbar. All finite-field
models and root equations on those models are construction outputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRamifiedRootModelsR0222
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaNormalizedSections

/-- Actual tensor pullback of a global section. -/
def pulledPower {X Y : Scheme} (p : Y ⟶ X) (H : X.Modules) (n : ℕ)
    (F : Sections (tensorPower X H n)) :
    Sections (tensorPower Y ((Scheme.Modules.pullback p).obj H) n) :=
  (pullback_tensorPower_iso Y X p H n).hom.app ⊤
    (pullbackGlobalSection p (tensorPower X H n) F)

/-- The regular Kth-root equation in the actual pulled-back line. -/
def RootEquation {X Y : Scheme} (p : Y ⟶ X) (H : X.Modules) (n : ℕ)
    (F : Sections (tensorPower X H n))
    (r : Sections ((Scheme.Modules.pullback p).obj H)) : Prop :=
  tensorPowerSection Y ((Scheme.Modules.pullback p).obj H) n ⊤ r = pulledPower p H n F

/-- The same four scheme maps and the given base-line comparison. -/
def coverLineComparison {X Y : Curve Omega} {K : FieldStage}
    (M : Model X K) (N : Model Y K) (f : Y.space ⟶ X.space)
    (g : N.curve.space ⟶ M.curve.space)
    (hc : N.projection ≫ g = f ≫ M.projection)
    (H0 : M.curve.space.Modules) {H : X.space.Modules}
    (e : (Scheme.Modules.pullback M.projection).obj H0 ≅ H) :
    (Scheme.Modules.pullback N.projection).obj ((Scheme.Modules.pullback g).obj H0) ≅
      (Scheme.Modules.pullback f).obj H :=
  PointedSquareCover.squareComparison N.projection g f M.projection hc H0 ≪≫
    (Scheme.Modules.pullback f).mapIso e

/-- Algebraic data after normalization in one chosen root field. No etaleness
is required: zeros of F may ramify. No finite constant-field model is assumed. -/
structure RootData (s n : ℕ) where
  base : Curve Omega
  cover : Curve Omega
  map : cover.space ⟶ base.space
  over_eq : map ≫ base.map = cover.map
  finite : IsFinite map
  surjective : Surjective map
  degree : ∀ x : base.space, 0 < map.finrank x ∧ map.finrank x ≤ n^s
  cusp : Base Omega ⟶ cover.space
  cusp_over : cusp ≫ cover.map = 𝟙 _
  line : base.space.Modules
  isLine : IsLineBundle base.space line
  powers : Fin s → Sections (tensorPower base.space line n)
  powers_nonzero : ∀ i, powers i ≠ 0
  roots : Fin s → Sections ((Scheme.Modules.pullback map).obj line)
  equation : ∀ i, RootEquation map line n (powers i) (roots i)

/-- Simultaneous descent of the original finite map, cusp, line, power sections
and chosen roots; every field below is required output, including the equations. -/
structure RootModel {s n : ℕ} (D : RootData s n) (K : FieldStage) where
  base : Model D.base K
  cover : Model D.cover K
  map : cover.curve.space ⟶ base.curve.space
  over_eq : map ≫ base.curve.map = cover.curve.map
  comparison : cover.projection ≫ map = D.map ≫ base.projection
  cartesian : IsPullback cover.projection D.map map base.projection
  finite : IsFinite map
  surjective : Surjective map
  degree_comparison : ∀ x : D.base.space,
    map.finrank (base.projection x) = D.map.finrank x
  degree : ∀ x : base.curve.space, 0 < map.finrank x ∧ map.finrank x ≤ n^s
  cusp : Base K ⟶ cover.curve.space
  cusp_over : cusp ≫ cover.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.projection
  line : base.curve.space.Modules
  isLine : IsLineBundle base.curve.space line
  lineComparison : (Scheme.Modules.pullback base.projection).obj line ≅ D.line
  powers : Fin s → Sections (tensorPower base.curve.space line n)
  powers_nonzero : ∀ i, powers i ≠ 0
  powers_comparison : ∀ i,
    (powerComparison base.projection line lineComparison n).hom.app ⊤
      (pullbackGlobalSection base.projection (tensorPower base.curve.space line n)
        (powers i)) = D.powers i
  roots : Fin s → Sections ((Scheme.Modules.pullback map).obj line)
  roots_comparison : ∀ i,
    (coverLineComparison base cover D.map map comparison line lineComparison).hom.app ⊤
      (pullbackGlobalSection cover.projection ((Scheme.Modules.pullback map).obj line)
        (roots i)) = D.roots i
  equation : ∀ i, RootEquation map line n (powers i) (roots i)

end ArithmeticThetaRamifiedRootModelsR0222
