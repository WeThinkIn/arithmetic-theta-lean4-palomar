module

public import StandardActualMetaplecticLevelR0208
public import SharpExactImageDataR0195
public import ActualLevelDefinitionsR0208

@[expose] public section

/-! The same compact sharp theta cover as a level in the actual family stack.
Only ordinary definitions; construction and source consumers are future proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCompactModularityR0209
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195 ArithmeticThetaTateCuspsR0181

/-- Input geometric data on the actual compact component. The later existence
consumer constructs these from the original matrix family using accepted proofs. -/
structure CompactRoot (k : Type) [Field k] [CharZero k] (L b : ℕ) where
  data : LevelData k L
  compact : Compactification k L data
  hodge : Extension k L data compact
  point : compact.space
  half : SquareLine (Component k L data compact point)
    (ArithmeticThetaComponentDegreeR0184.hodge k L data compact point hodge)
  cover : RootCover k (Component k L data compact point)
    (projection k L data compact point) b

variable {k : Type} [Field k] [CharZero k] {L b : ℕ}

abbrev compactMap (K : CompactRoot k L b) :=
  K.cover.map ≫ inclusion k L K.data K.compact K.point
abbrev line (K : CompactRoot k L b) :=
  (Scheme.Modules.pullback K.cover.map).obj K.half.line

def compactSquare (K : CompactRoot k L b) :
    tensorPower K.cover.space (line K) 2 ≅
      (Scheme.Modules.pullback (compactMap K)).obj K.hodge.line :=
  squarePull K.cover.map K.half ≪≫
    (Scheme.Modules.pullbackComp K.cover.map
      (inclusion k L K.data K.compact K.point)).app K.hodge.line

/-- This is the categorical inverse image of the original open full-level base. -/
abbrev Interior (K : CompactRoot k L b) := pullback (compactMap K) K.compact.inclusion
abbrev interiorInclusion (K : CompactRoot k L b) : Interior K ⟶ K.cover.space :=
  pullback.fst (compactMap K) K.compact.inclusion
abbrev interiorMap (K : CompactRoot k L b) : Interior K ⟶ OpenBase k L K.data :=
  pullback.snd (compactMap K) K.compact.inclusion

def openSquare (K : CompactRoot k L b) :
    SquareLine (Interior K) ((Scheme.Modules.pullback (interiorMap K)).obj
      (openHodge k L K.data)) where
  line := (Scheme.Modules.pullback (interiorInclusion K)).obj (line K)
  invertible := (K.half.invertible.pullback K.cover.map).pullback (interiorInclusion K)
  square := (pullback_tensorPower_iso _ _ (interiorInclusion K) (line K) 2).symm ≪≫
    (Scheme.Modules.pullback (interiorInclusion K)).mapIso (compactSquare K) ≪≫
    (Scheme.Modules.pullbackComp (interiorInclusion K) (compactMap K)).app K.hodge.line ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := compactMap K) (g := K.compact.inclusion))).app K.hodge.line ≪≫
    ((Scheme.Modules.pullbackComp (interiorMap K) K.compact.inclusion).app K.hodge.line).symm ≪≫
    (Scheme.Modules.pullback (interiorMap K)).mapIso K.hodge.onOpen

/-- No replacement of the existing quotient is allowed. -/
def Universal (K : CompactRoot k L b) : Prop :=
  ArithmeticThetaSchemeHodgeR0205.HodgeUniversal k L K.data.atlas K.data.two
    K.data.cover K.data.quotient

def provider (K : CompactRoot k L b) (h : Universal K) :
    ArithmeticThetaActualLevelR0208.Provider k L :=
  ⟨K.data.atlas, K.data.two, K.data.canonical, K.data.cover, K.data.quotient, h⟩

def interiorBase (K : CompactRoot k L b) :
    Over (ArithmeticThetaLocalWeierstrassR0203.Base k) :=
  Over.mk (interiorMap K ≫ openStructure k L K.data)

def levelMap (K : CompactRoot k L b) (h : Universal K) :
    interiorBase K ⟶ ArithmeticThetaActualLevelR0208.base (provider K h) :=
  Over.homMk (interiorMap K) rfl

/-- Density identifies this with an open part of the SAME compact cover.
The rank is allowed to vanish on other components of the full-level base. -/
def InteriorGeometry (K : CompactRoot k L b) : Prop :=
  IsOpenImmersion (interiorInclusion K) ∧ DenseRange (interiorInclusion K).base ∧
  IsFinite (interiorMap K) ∧ Etale (interiorMap K) ∧
  ∀ z : OpenBase k L K.data, (interiorMap K).finrank z ≤ b

/-- The level uses actual marked families, not only roots on a fixed Hodge base.
The open root is the explicit restriction of the compact square above. -/
def ActualLevel (K : CompactRoot k L b) : Prop :=
  InteriorGeometry K ∧ ∃ (h : Universal K)
    (C : ArithmeticThetaMetaplecticStackR0207.Coherence L
      (ArithmeticThetaLocalWeierstrassR0203.Base k)),
    Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L
      (ArithmeticThetaLocalWeierstrassR0203.Base k) C) ∧
    CategoryTheory.Pseudofunctor.IsStack C.functor
      (ArithmeticThetaRootStackR0198.rootTopology (ArithmeticThetaLocalWeierstrassR0203.Base k)) ∧
    Nonempty (ArithmeticThetaActualLevelR0208.PullbackComparison
      (ArithmeticThetaActualLevelR0208.canonicalMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))) ∧
    ArithmeticThetaActualLevelR0208.FiniteEtaleLevel (provider K h) (levelMap K h) (openSquare K)
      (ArithmeticThetaActualLevelR0208.canonicalMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))

/-- All accepted sharp-family witnesses, with the same sections retained for
modularity and exact image statements. No modularity or basis conclusion is a field. -/
structure MatrixData {n h : ℕ} (A : Matrices n h) where
  indexing : Indexing A
  indexed : Indexed A indexing
  formal : FormalIdentity A indexing
  data : LevelData ℂ (level (commonN A))
  compact : Compactification ℂ (level (commonN A)) data
  hodge : Extension ℂ (level (commonN A)) data compact
  canonical : Canonical ℂ (level (commonN A)) hodge
  test : DiskTest ℂ (level (commonN A)) data compact
  half : SquareLine (Component ℂ (level (commonN A)) data compact (test.disk (closedPoint ℂ)))
    (ArithmeticThetaComponentDegreeR0184.hodge ℂ (level (commonN A)) data compact
      (test.disk (closedPoint ℂ)) hodge)
  cover : RootCover ℂ (Component ℂ (level (commonN A)) data compact (test.disk (closedPoint ℂ)))
    (projection ℂ (level (commonN A)) data compact (test.disk (closedPoint ℂ))) (2^(normCount A-1))
  etale : Etale cover.map
  oneNorm : normCount A = 1 → IsIso cover.map
  degree : ArithmeticThetaSharpCoverR0194.SquareCoverDegree ℂ (level (commonN A)) data compact
    hodge (test.disk (closedPoint ℂ)) half (2^(normCount A-1)) n cover
  frame : CoverFrame ℂ (commonN A) hodge test half (2^(normCount A-1)) cover
  unary : Fin indexing.count → Sections cover.space ((Scheme.Modules.pullback cover.map).obj half.line)
  sections : Fin h → Sections cover.space (tensorPower cover.space
    ((Scheme.Modules.pullback cover.map).obj half.line) n)
  unary_expansion : ∀ j, unary j ≠ 0 ∧
    pullbackGlobalSection frame.disk ((Scheme.Modules.pullback cover.map).obj half.line) (unary j) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ)
        (unarySeries ℂ (commonN A) (indexing.pair j).1 (indexing.pair j).2) • frame.frame
  coset_eq : ∀ i, sections i = ∑ a : Cosets A i,
    tensorProductSection cover.space ((Scheme.Modules.pullback cover.map).obj half.line) n ⊤
      (fun j => unary (indexing.index i a j))
  expansion : ∀ c : Fin h → ℂ,
    pullbackPowerSection frame.disk ((Scheme.Modules.pullback cover.map).obj half.line) n
      (∑ i : Fin h, baseScalar ℂ (cover.map ≫ projection ℂ (level (commonN A)) data compact
        (test.disk (closedPoint ℂ))) (c i) • sections i) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (expanded A c) •
        tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback frame.disk).obj
          ((Scheme.Modules.pullback cover.map).obj half.line)) n ⊤ frame.frame

variable {n h : ℕ} {A : Matrices n h}

def MatrixData.root (G : MatrixData A) : CompactRoot ℂ (level (commonN A)) (2^(normCount A-1)) :=
  ⟨G.data, G.compact, G.hodge, G.test.disk (closedPoint ℂ), G.half, G.cover⟩

abbrev weightSections (G : MatrixData A) :=
  Sections G.cover.space (tensorPower G.cover.space (line G.root) n)
abbrev structureMap (G : MatrixData A) :=
  G.cover.map ≫ projection ℂ (level (commonN A)) G.data G.compact (G.test.disk (closedPoint ℂ))
def combination (G : MatrixData A) (c : Fin h → ℂ) : weightSections G :=
  ∑ i, baseScalar ℂ (structureMap G) (c i) • G.sections i
abbrev pivotCount (B : ℕ) := (ArithmeticThetaElimination.run
  (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length
def pivotCombination (G : MatrixData A) (B : ℕ) (c : Fin (pivotCount (A := A) B) → ℂ) :
    weightSections G :=
  ∑ t, baseScalar ℂ (structureMap G) (c t) •
    G.sections (ArithmeticThetaComputed.selectedIndex A B t)

/-- Linear independence, spanning and exact rational coordinates of the ACTUAL
compact sections, written with their structural scalar action. -/
def SectionImage (G : MatrixData A) (B : ℕ) : Prop :=
  (∀ c : Fin h → ℂ, combination G c = 0 ↔ ArithmeticThetaComputed.thetaMap A c = 0) ∧
  (∀ c : Fin (pivotCount (A := A) B) → ℂ, pivotCombination G B c = 0 → c = 0) ∧
  (∀ c : Fin h → ℂ, ∃! d : Fin (pivotCount (A := A) B) → ℂ,
    combination G c = pivotCombination G B d) ∧
  (∀ j : Fin h, G.sections j = pivotCombination G B
    (fun t => ((ArithmeticThetaElimination.columnCoordinates
      (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ))) ∧
  (∀ (j : Fin h) (c : Fin (pivotCount (A := A) B) → ℚ),
    G.sections j = pivotCombination G B (fun t => ((c t : ℚ) : ℂ)) →
    c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j)

/-- Regularity is encoded by global sections on the compact curve, and the
same weight line restricts to the tautological line at the actual finite level. -/
def ArithmeticModularFamily (G : MatrixData A) : Prop :=
  ActualLevel G.root ∧ ∀ B : ℕ, cutoff A ≤ B → SectionImage G B ∧ ImageData A B

end ArithmeticThetaCompactModularityR0209
