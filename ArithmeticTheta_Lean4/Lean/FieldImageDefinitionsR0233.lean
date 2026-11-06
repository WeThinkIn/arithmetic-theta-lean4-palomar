import ArithmeticMatrixFiniteModelR0232
import CompactThetaSectionImageR0209

/-! Source-facing image predicates over coefficient fields and actual descended
compact sections. All scalars use the displayed structural morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFieldImageR0233
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaTensorPower ArithmeticThetaPullback

abbrev pivotCount {n h : ℕ} (A : Matrices n h) (B : ℕ) :=
  (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length

def seriesCombination (k : Type) [Field k] {n h : ℕ}
    (A : Matrices n h) (c : Fin h → k) : PowerSeries k :=
  ∑ i, c i • ArithmeticThetaArithmeticFieldR0231.theta k (A i)

def seriesPivot (k : Type) [Field k] {n h : ℕ}
    (A : Matrices n h) (B : ℕ) (d : Fin (pivotCount A B) → k) : PowerSeries k :=
  ∑ t, d t • ArithmeticThetaArithmeticFieldR0231.theta k
    (A (ArithmeticThetaComputed.selectedIndex A B t))

/-- The prefix is the actual computed rational matrix under its canonical map. -/
def Kernel (k : Type) [Field k] [CharZero k] {n h : ℕ}
    (A : Matrices n h) (B : ℕ) : Prop :=
  ∀ c : Fin h → k, seriesCombination k A c = 0 ↔
    ((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ k)).mulVec c = 0

/-- The SAME rational elimination output supplies all full-series coordinates. -/
def SeriesImage (k : Type) [Field k] [CharZero k] {n h : ℕ}
    (A : Matrices n h) (B : ℕ) : Prop :=
  Kernel k A B ∧
  (∀ d : Fin (pivotCount A B) → k, seriesPivot k A B d = 0 → d = 0) ∧
  (∀ c : Fin h → k, ∃! d : Fin (pivotCount A B) → k,
    seriesCombination k A c = seriesPivot k A B d) ∧
  (∀ j : Fin h, ArithmeticThetaArithmeticFieldR0231.theta k (A j) =
    seriesPivot k A B (fun t => algebraMap ℚ k
      (ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t))) ∧
  (∀ (j : Fin h) (d : Fin (pivotCount A B) → ℚ),
    ArithmeticThetaArithmeticFieldR0231.theta k (A j) =
      seriesPivot k A B (fun t => algebraMap ℚ k (d t)) →
    d = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j)

abbrev Sections {X : Scheme.{0}} (J : X.Modules) := J.presheaf.obj (Opposite.op ⊤)

def combination (k : Type) [Field k] {h : ℕ} {X : Scheme.{0}}
    (b : X ⟶ Spec (CommRingCat.of k)) {J : X.Modules}
    (s : Fin h → Sections J) (c : Fin h → k) : Sections J :=
  ∑ i, baseScalar k b (c i) • s i

def pivotCombination (k : Type) [Field k] {n h : ℕ} (A : Matrices n h) (B : ℕ)
    {X : Scheme.{0}} (b : X ⟶ Spec (CommRingCat.of k)) {J : X.Modules}
    (s : Fin h → Sections J) (d : Fin (pivotCount A B) → k) : Sections J :=
  ∑ t, baseScalar k b (d t) • s (ArithmeticThetaComputed.selectedIndex A B t)

/-- Exact relations, independence, spanning and rational coordinates of actual
sections. No freely chosen k-module action is used on their carrier. -/
def SectionImage (k : Type) [Field k] [CharZero k] {n h : ℕ} (A : Matrices n h) (B : ℕ)
    {X : Scheme.{0}} (b : X ⟶ Spec (CommRingCat.of k)) {J : X.Modules}
    (s : Fin h → Sections J) : Prop :=
  (∀ c : Fin h → k, combination k b s c = 0 ↔ seriesCombination k A c = 0) ∧
  (∀ c : Fin h → k, combination k b s c = 0 ↔
    ((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ k)).mulVec c = 0) ∧
  (∀ d : Fin (pivotCount A B) → k, pivotCombination k A B b s d = 0 → d = 0) ∧
  (∀ c : Fin h → k, ∃! d : Fin (pivotCount A B) → k,
    combination k b s c = pivotCombination k A B b s d) ∧
  (∀ j : Fin h, s j = pivotCombination k A B b s
    (fun t => algebraMap ℚ k
      (ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t))) ∧
  (∀ (j : Fin h) (d : Fin (pivotCount A B) → ℚ),
    s j = pivotCombination k A B b s (fun t => algebraMap ℚ k (d t)) →
    d = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j)

/-- The accepted actual pullback comparison, with every map retained. -/
def modelTransport {s n b : ℕ} {D : ArithmeticThetaFiniteFieldModelsR0221.RootData s n b}
    {K : ArithmeticThetaFiniteFieldModelsR0221.FieldStage}
    (M : ArithmeticThetaFiniteFieldModelsR0221.RootModel D K)
    (v : Sections (tensorPower M.cover.curve.space M.half n)) :
    Sections (tensorPower D.cover.space D.half n) :=
  (ArithmeticThetaFiniteFieldModelsR0221.powerComparison M.cover.projection M.half
    M.halfComparison n).hom.app ⊤
      (pullbackGlobalSection M.cover.projection (tensorPower M.cover.curve.space M.half n) v)

end ArithmeticThetaFieldImageR0233
