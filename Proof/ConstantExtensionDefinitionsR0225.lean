module

public import PrescribedProjectiveRootFiniteModelR0224
public import PrescribedRootModelsDefinitionsR0224

@[expose] public section

/-! Finite extensions of an arbitrary characteristic-zero constant field.
All model and realization records are construction outputs. Accepted generic
curve, tensor, root-equation and projectivity definitions are reused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections powerIso powerComparison)
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171 (IsFrame)
open ArithmeticThetaValuativeRootsR0223
open ArithmeticThetaRamifiedRootModelsR0222 (RootEquation)
open ArithmeticThetaPrescribedRootModelsR0224 (ProjectivePresentation)

abbrev Omega (k : Type) [Field k] := AlgebraicClosure k
abbrev FieldStage (k : Type) [Field k] := IntermediateField k (Omega k)
variable {k : Type} [Field k]

def constantMap (K : FieldStage k) : Base (Omega k) ⟶ Base K :=
  Spec.map (CommRingCat.ofHom K.subtype)
def extensionMap {K K' : FieldStage k} (h : K ≤ K') : Base K' ⟶ Base K :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

/-- A model is related by a Cartesian square, not by a freely chosen expansion. -/
structure Model (X : Curve (Omega k)) (K : (FieldStage k)) where
  curve : Curve K
  projection : X.space ⟶ curve.space
  cartesian : IsPullback projection X.map curve.map (constantMap K)

/-- Enlargement keeps the original finite-field model and its actual map. -/
structure Refinement {X : Curve (Omega k)} {K K' : (FieldStage k)}
    (M : Model X K) (N : Model X K') where
  inclusion : K ≤ K'
  map : N.curve.space ⟶ M.curve.space
  cartesian : IsPullback map N.curve.map M.curve.map (extensionMap inclusion)
  comparison : N.projection ≫ map = M.projection

/-- This uses exactly the commuting triangle of the refinement. -/
def refinementComparison {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) (H : M.curve.space.Modules) :
    (Scheme.Modules.pullback N.projection).obj ((Scheme.Modules.pullback E.map).obj H) ≅
      (Scheme.Modules.pullback M.projection).obj H :=
  (Scheme.Modules.pullbackComp N.projection E.map).app H ≪≫
    (Scheme.Modules.pullbackCongr E.comparison).app H

/-- The same four scheme maps and the given base-line comparison. -/
def coverLineComparison {X Y : Curve (Omega k)} {K : (FieldStage k)}
    (M : Model X K) (N : Model Y K) (f : Y.space ⟶ X.space)
    (g : N.curve.space ⟶ M.curve.space)
    (hc : N.projection ≫ g = f ≫ M.projection)
    (H0 : M.curve.space.Modules) {H : X.space.Modules}
    (e : (Scheme.Modules.pullback M.projection).obj H0 ≅ H) :
    (Scheme.Modules.pullback N.projection).obj ((Scheme.Modules.pullback g).obj H0) ≅
      (Scheme.Modules.pullback f).obj H :=
  ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover.squareComparison N.projection g f M.projection hc H0 ≪≫
    (Scheme.Modules.pullback f).mapIso e

/-- Algebraic data after normalization in one chosen root field. No etaleness
is required: zeros of F may ramify. No finite constant-field model is assumed. -/
structure RootData (k : Type) [Field k] (s n : ℕ) where
  base : Curve (Omega k)
  cover : Curve (Omega k)
  map : cover.space ⟶ base.space
  over_eq : map ≫ base.map = cover.map
  finite : IsFinite map
  surjective : Surjective map
  degree : ∀ x : base.space, 0 < map.finrank x ∧ map.finrank x ≤ n^s
  cusp : Base (Omega k) ⟶ cover.space
  cusp_over : cusp ≫ cover.map = 𝟙 _
  line : base.space.Modules
  isLine : IsLineBundle base.space line
  powers : Fin s → Sections (tensorPower base.space line n)
  powers_nonzero : ∀ i, powers i ≠ 0
  roots : Fin s → Sections ((Scheme.Modules.pullback map).obj line)
  equation : ∀ i, RootEquation map line n (powers i) (roots i)

/-- Simultaneous descent of the original finite map, cusp, line, power sections
and chosen roots; every field below is required output, including the equations. -/
structure RootModel {s n : ℕ} (D : RootData k s n) (K : (FieldStage k)) where
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

/-- Comparison on the SAME valuation scheme through the finite model projection. -/
def modelFrameComparison {s n : ℕ} {D : RootData k s n}
    {K : (FieldStage k)} (M : RootModel D K)
    {V : Scheme.{0}} (f : V ⟶ D.base.space) :
    (Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line ≅
      (Scheme.Modules.pullback f).obj D.line :=
  ((Scheme.Modules.pullbackComp f M.base.projection).app M.line).symm ≪≫
    (Scheme.Modules.pullback f).mapIso M.lineComparison

def modelFrame {s n : ℕ} {D : RootData k s n}
    {K : (FieldStage k)} (M : RootModel D K)
    {V : Scheme.{0}} (f : V ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line)) :
    Sections ((Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line) :=
  (modelFrameComparison M f).inv.app ⊤ h

/-- Equality of whole regular sections, through the actual branch and frame. -/
def BranchValues {s n : ℕ} (D : RootData k s n)
    (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line)) (a : Fin s → A)
    (g : ValuationPoint E A ⟶ D.cover.space) (hg : g ≫ D.map = f) : Prop :=
  ∀ j, (ArithmeticThetaCommonHalfHodgeR0185.along g D.map f hg D.line).hom.app ⊤
    (pullbackGlobalSection g ((Scheme.Modules.pullback D.map).obj D.line) (D.roots j)) =
      ArithmeticThetaOpenHodgeR0180.scalar A (a j) • h

/-- The model branch is g followed by the fixed model projection. The frame is
the inverse image of the ORIGINAL h, not an independently chosen trivialization. -/
def ModelBranchValues {s n : ℕ}
    {D : RootData k s n} {K : (FieldStage k)}
    (M : RootModel D K)
    (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line)) (a : Fin s → A)
    (g : ValuationPoint E A ⟶ D.cover.space) : Prop :=
  IsFrame ((Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line) ⊤
      (modelFrame M f h) ∧
    ∃ hg : (g ≫ M.cover.projection) ≫ M.map = f ≫ M.base.projection,
      ∀ j, (ArithmeticThetaCommonHalfHodgeR0185.along (g ≫ M.cover.projection)
        M.map (f ≫ M.base.projection) hg M.line).hom.app ⊤
          (pullbackGlobalSection (g ≫ M.cover.projection)
            ((Scheme.Modules.pullback M.map).obj M.line) (M.roots j)) =
          ArithmeticThetaOpenHodgeR0180.scalar A (a j) • modelFrame M f h

/-- A constructed single root cover, its actual prescribed branch and rational
centre. No root section, cover or finite model is assumed by the final theorem. -/
structure RootRealization (X : Curve (Omega k)) (J : X.space.Modules) (n s : ℕ)
    (F : Fin s → Sections (tensorPower X.space J n))
    (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ X.space)
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : Fin s → E)
    (c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A) where
  cover : ArithmeticThetaSimultaneousUnaryR0187.RootCover (Omega k) X.space X.map (n^s)
  geometric : GeometricallyIntegral (cover.map ≫ X.map)
  line : IsLineBundle X.space J
  powers_nonzero : ∀ j, F j ≠ 0
  coefficients : Fin s → A
  coefficients_eq : ∀ j, algebraMap A E (coefficients j) = r j
  lift : ValuationPoint E A ⟶ cover.space
  lift_eq : lift ≫ cover.map = f
  dominant : IsDominant (genericInclusion E A ≫ lift)
  roots : Fin s → Sections ((Scheme.Modules.pullback cover.map).obj J)
  roots_nonzero : ∀ j, roots j ≠ 0
  equation : ∀ j, RootEquation cover.map J n (F j) (roots j)
  values : ∀ j,
    (ArithmeticThetaCommonHalfHodgeR0185.along lift cover.map f lift_eq J).hom.app ⊤
      (pullbackGlobalSection lift ((Scheme.Modules.pullback cover.map).obj J) (roots j)) =
        ArithmeticThetaOpenHodgeR0180.scalar A (coefficients j) • h
  centre_over : (c ≫ lift) ≫ (cover.map ≫ X.map) = 𝟙 _

/-- Forget only the infinite valuative data when invoking finite algebraic descent. -/
def RootRealization.data {X : Curve (Omega k)} {J : X.space.Modules} {n s : ℕ}
    {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E}
    {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E}
    {c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) :
    RootData k s n where
  base := X
  cover := ⟨T.cover.space, T.cover.map ≫ X.map, T.cover.proper, T.cover.smooth, T.geometric⟩
  map := T.cover.map
  over_eq := rfl
  finite := T.cover.finite
  surjective := T.cover.surjective
  degree := T.cover.degree
  cusp := c ≫ T.lift
  cusp_over := T.centre_over
  line := J
  isLine := T.line
  powers := F
  powers_nonzero := T.powers_nonzero
  roots := T.roots
  equation := T.equation

/-- One finite constant-field model retains the entire branch comparison over A.
It does not assert that an arbitrary formal frame has finitely many coefficients. -/
def FiniteRealization {X : Curve (Omega k)} {J : X.space.Modules} {n s : ℕ}
    {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E}
    {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E}
    {c : ArithmeticThetaFiniteFieldModelsR0221.Base (Omega k) ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) (K0 : (FieldStage k)) : Prop :=
  ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧
    ∃ M : RootModel T.data K,
      Nonempty (ProjectivePresentation K M.base.curve.space M.base.curve.map) ∧
      Nonempty (ProjectivePresentation K M.cover.curve.space M.cover.curve.map) ∧
      ModelBranchValues M E A f h T.coefficients T.lift


end ArithmeticThetaConstantExtensionR0225
