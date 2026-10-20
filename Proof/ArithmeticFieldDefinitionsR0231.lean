module

public import MatrixArithmeticModularityR0209
public import PointedSquareCoverFiniteModelR0221

@[expose] public section

/-! Algebraic coefficient fields for the actual sharp theta family.
The new construction and descent instances are separate worker obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticFieldR0231
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195 ArithmeticThetaTateCuspsR0181


open ArithmeticThetaCompactModularityR0209

/-- The integer shell-count series, before any coefficient-field embedding. -/
def integralTheta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℤ))

def theta (k : Type) [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries k :=
  PowerSeries.map (Int.castRingHom k) (integralTheta A)

def expanded (k : Type) [Field k] {n h : ℕ} (A : Matrices n h) (c : Fin h → k) : PowerSeries k :=
  PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (∑ i, c i • theta k (A i))

def FormalIdentity (k : Type) [Field k] {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
  ∀ c : Fin h → k, expanded k A c =
    ∑ i, c i • (∑ a : Cosets A i, ∏ j : Fin n,
      unarySeries k (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2)

structure MatrixData (k : Type) [Field k] [CharZero k] {n h : ℕ} (A : Matrices n h) where
  indexing : Indexing A
  indexed : Indexed A indexing
  formal : FormalIdentity k A indexing
  data : LevelData k (level (commonN A))
  compact : Compactification k (level (commonN A)) data
  hodge : Extension k (level (commonN A)) data compact
  canonical : Canonical k (level (commonN A)) hodge
  test : DiskTest k (level (commonN A)) data compact
  half : SquareLine (Component k (level (commonN A)) data compact (test.disk (closedPoint k)))
    (ArithmeticThetaComponentDegreeR0184.hodge k (level (commonN A)) data compact
      (test.disk (closedPoint k)) hodge)
  cover : RootCover k (Component k (level (commonN A)) data compact (test.disk (closedPoint k)))
    (projection k (level (commonN A)) data compact (test.disk (closedPoint k))) (2^(normCount A-1))
  etale : Etale cover.map
  oneNorm : normCount A = 1 → IsIso cover.map
  degree : ArithmeticThetaSharpCoverR0194.SquareCoverDegree k (level (commonN A)) data compact
    hodge (test.disk (closedPoint k)) half (2^(normCount A-1)) n cover
  frame : CoverFrame k (commonN A) hodge test half (2^(normCount A-1)) cover
  unary : Fin indexing.count → Sections cover.space ((Scheme.Modules.pullback cover.map).obj half.line)
  sections : Fin h → Sections cover.space (tensorPower cover.space
    ((Scheme.Modules.pullback cover.map).obj half.line) n)
  unary_expansion : ∀ j, unary j ≠ 0 ∧
    pullbackGlobalSection frame.disk ((Scheme.Modules.pullback cover.map).obj half.line) (unary j) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (unarySeries k (commonN A) (indexing.pair j).1 (indexing.pair j).2) • frame.frame
  coset_eq : ∀ i, sections i = ∑ a : Cosets A i,
    tensorProductSection cover.space ((Scheme.Modules.pullback cover.map).obj half.line) n ⊤
      (fun j => unary (indexing.index i a j))
  expansion : ∀ c : Fin h → k,
    pullbackPowerSection frame.disk ((Scheme.Modules.pullback cover.map).obj half.line) n
      (∑ i : Fin h, baseScalar k (cover.map ≫ projection k (level (commonN A)) data compact
        (test.disk (closedPoint k))) (c i) • sections i) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (expanded k A c) •
        tensorPowerSection (Disk k) ((Scheme.Modules.pullback frame.disk).obj
          ((Scheme.Modules.pullback cover.map).obj half.line)) n ⊤ frame.frame

variable {k : Type} [Field k] [CharZero k] {n h : ℕ} {A : Matrices n h}

def MatrixData.root (G : MatrixData k A) : CompactRoot k (level (commonN A)) (2^(normCount A-1)) :=
  ⟨G.data, G.compact, G.hodge, G.test.disk (closedPoint k), G.half, G.cover⟩

abbrev baseSpace (G : MatrixData k A) :=
  Component k (level (commonN A)) G.data G.compact (G.test.disk (closedPoint k))
abbrev baseMap (G : MatrixData k A) :=
  projection k (level (commonN A)) G.data G.compact (G.test.disk (closedPoint k))
abbrev weight (G : MatrixData k A) :=
  ArithmeticThetaComponentDegreeR0184.hodge k (level (commonN A)) G.data G.compact
    (G.test.disk (closedPoint k)) G.hodge
abbrev half (G : MatrixData k A) := (Scheme.Modules.pullback G.cover.map).obj G.half.line
abbrev structureMap (G : MatrixData k A) := G.cover.map ≫ baseMap G

def cusp (G : MatrixData k A) : Spec (CommRingCat.of k) ⟶ G.cover.space :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k)) ≫ G.frame.disk

/-- Exact geometric facts needed to apply the already proved finite-model theorem.
They refer to these actual maps, sheaves, and the centre of this very disk. -/
def DescentGeometry (G : MatrixData k A) : Prop :=
  IsProper (baseMap G) ∧ SmoothOfRelativeDimension 1 (baseMap G) ∧
  GeometricallyIntegral (baseMap G) ∧ GeometricallyIntegral (structureMap G) ∧
  ArithmeticThetaNormalizedSections.IsLineBundle (baseSpace G) (weight G) ∧
  ArithmeticThetaNormalizedSections.IsLineBundle G.cover.space (half G) ∧
  cusp G ≫ structureMap G = 𝟙 _

/-- No new cover, point, line or section is selected in this conversion. -/
def rootData (G : MatrixData (AlgebraicClosure ℚ) A) (hg : DescentGeometry G) :
    ArithmeticThetaFiniteFieldModelsR0221.RootData h n (2^(normCount A-1)) where
  base := ⟨baseSpace G, baseMap G, hg.1, hg.2.1, hg.2.2.1⟩
  cover := ⟨G.cover.space, structureMap G, G.cover.proper, G.cover.smooth, hg.2.2.2.1⟩
  map := G.cover.map
  over_eq := rfl
  finite := G.cover.finite
  etale := G.etale
  surjective := G.cover.surjective
  degree := G.cover.degree
  cusp := cusp G
  cusp_over := hg.2.2.2.2.2.2
  weight := weight G
  weight_line := hg.2.2.2.2.1
  half := half G
  half_line := hg.2.2.2.2.2.1
  square := squarePull G.cover.map G.half
  sections := G.sections

end ArithmeticThetaArithmeticFieldR0231
