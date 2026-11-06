module

public import ValuedExtensionPrescribedRootsR0223
public import PointedRamifiedRootModelR0222
public import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
public import RamifiedRootModelsDefinitionsR0222
public import ValuativeRootSectionsDefinitionsR0223

@[expose] public section

/-! Actual finite models and the unchanged valuative frame of prescribed roots.
All geometric records in the final existence statement are outputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaPrescribedRootModelsR0224
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRamifiedRootModelsR0222 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaValuativeRootsR0223

/-- A projective presentation over the specified field, including its base map. -/
structure ProjectivePresentation (k : Type) [Field k] (X : Scheme.{0})
    (b : X ⟶ ArithmeticThetaFiniteFieldModelsR0221.Base k) where
  dimension : ℕ
  embedding : X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)
  closed : IsClosedImmersion embedding
  over_eq : embedding ≫
    ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = b

/-- Comparison on the SAME valuation scheme through the finite model projection. -/
def modelFrameComparison {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K : FieldStage} (M : ArithmeticThetaRamifiedRootModelsR0222.RootModel D K)
    {V : Scheme.{0}} (f : V ⟶ D.base.space) :
    (Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line ≅
      (Scheme.Modules.pullback f).obj D.line :=
  ((Scheme.Modules.pullbackComp f M.base.projection).app M.line).symm ≪≫
    (Scheme.Modules.pullback f).mapIso M.lineComparison

def modelFrame {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K : FieldStage} (M : ArithmeticThetaRamifiedRootModelsR0222.RootModel D K)
    {V : Scheme.{0}} (f : V ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line)) :
    Sections ((Scheme.Modules.pullback (f ≫ M.base.projection)).obj M.line) :=
  (modelFrameComparison M f).inv.app ⊤ h

/-- Equality of whole regular sections, through the actual branch and frame. -/
def BranchValues {s n : ℕ} (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
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
    {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n} {K : FieldStage}
    (M : ArithmeticThetaRamifiedRootModelsR0222.RootModel D K)
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
structure RootRealization (X : Curve Omega) (J : X.space.Modules) (n s : ℕ)
    (F : Fin s → Sections (tensorPower X.space J n))
    (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ X.space)
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : Fin s → E)
    (c : ArithmeticThetaFiniteFieldModelsR0221.Base Omega ⟶ ValuationPoint E A) where
  cover : ArithmeticThetaSimultaneousUnaryR0187.RootCover Omega X.space X.map (n^s)
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
def RootRealization.data {X : Curve Omega} {J : X.space.Modules} {n s : ℕ}
    {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E}
    {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E}
    {c : ArithmeticThetaFiniteFieldModelsR0221.Base Omega ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) :
    ArithmeticThetaRamifiedRootModelsR0222.RootData s n where
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

/-- One finite number-field model retains the entire branch comparison over A.
It does not assert that an arbitrary formal frame has finitely many coefficients. -/
def FiniteRealization {X : Curve Omega} {J : X.space.Modules} {n s : ℕ}
    {F : Fin s → Sections (tensorPower X.space J n)}
    {E : Type} [Field E] {A : ValuationSubring E}
    {f : ValuationPoint E A ⟶ X.space}
    {h : Sections ((Scheme.Modules.pullback f).obj J)} {r : Fin s → E}
    {c : ArithmeticThetaFiniteFieldModelsR0221.Base Omega ⟶ ValuationPoint E A}
    (T : RootRealization X J n s F E A f h r c) (K0 : FieldStage) : Prop :=
  ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧
    ∃ M : ArithmeticThetaRamifiedRootModelsR0222.RootModel T.data K,
      Nonempty (ProjectivePresentation K M.base.curve.space M.base.curve.map) ∧
      Nonempty (ProjectivePresentation K M.cover.curve.space M.cover.curve.map) ∧
      ModelBranchValues M E A f h T.coefficients T.lift

end ArithmeticThetaPrescribedRootModelsR0224
