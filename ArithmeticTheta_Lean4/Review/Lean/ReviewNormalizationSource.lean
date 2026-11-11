import ReviewNormalizationDefinitions
import ArithmeticFieldDefinitionsR0231

/-! Extraction of the original Tate test and frame into the generic interface.
Every scheme, map, line, marking, differential and generator is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaReview.Normalization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCompactModularityR0209
open ArithmeticThetaLatticeSectionsR0188 (Matrices commonN)
open ArithmeticThetaCompactUnaryR0183 (level)
open ArithmeticThetaCoverComparison

/-- The very pointed Cartesian test used by the original `testIso`. -/
def sourceTest {k : Type} [Field k] [CharZero k] {L : ℕ}
    {D : LevelData k L} (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring
      D.atlas.descent.family (LaurentSeries k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k L) T.level.law := by
  let ι : D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
  have hmap : baseMap D.atlas.quotient.ring (LaurentSeries k) ι =
      T.base ≫ D.quotient.inclusion := Spec.map_preimage _
  exact
    { scalar := ι
      map := T.map
      cartesian := by rw [hmap]; exact T.classifies.2.1
      origin_eq := by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq := T.nsmul_eq }

/-- Forget only the atlas bookkeeping, retaining all maps in the canonical
disk-to-Hodge comparison and the original full marking and differential. -/
def sourceChart {k : Type} [Field k] [CharZero k] {L : ℕ}
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    TateChart k L X.space H.line where
  ring := D.atlas.quotient.ring
  family := D.atlas.descent.family
  marking := D.atlas.marking
  openSpace := OpenBase k L D
  inclusion := X.inclusion
  openImmersion := X.openImmersion
  toFamily := D.quotient.inclusion
  onOpen := H.onOpen
  level := T.level
  test := sourceTest T.toTest
  puncture := T.base
  base_eq := (Spec.map_preimage (T.base ≫ D.quotient.inclusion)).symm
  marking_x := T.classifies.2.2.2.1
  marking_y := T.classifies.2.2.2.2
  disk := T.disk
  extends_eq := T.extends_eq.2.1
  differential := T.differential
  normalized := T.normalized

/-- The marked interior/root link depends only on a compact root and its
canonical universal-family witness; no matrix construction enters the proof. -/
def sourceInteriorLink {k : Type} [Field k] [CharZero k] {L b : ℕ}
    (K : CompactRoot k L b) (u : Universal K) (V : DiskTest k L K.data K.compact) :
    InteriorLink (sourceChart K.hodge V) (line K) (compactMap K) (compactSquare K)
      (interiorInclusion K)
      (ArithmeticThetaActualLevelR0208.object (provider K u) (levelMap K u)
        (openSquare K)) rfl := by
  let M := ArithmeticThetaActualLevelR0208.model (provider K u) (levelMap K u)
  exact
    { base := interiorMap K
      triangle := pullback.condition
      curve := M.curve
      cartesian := M.classifies.2.1
      zero_eq := M.classifies.2.2.1
      marking_x := M.classifies.2.2.2.1
      marking_y := M.classifies.2.2.2.2.1
      multiplicative := M.classifies.2.2.2.2.2
      hodge := M.hodge
      canonical := M.canonical
      square_eq := by
        simp only [eqToHom_refl, tensorPowerMap_id, Category.id_comp]
        rfl }

/-- The same marked interior object and root, now with its compact square and
normalized Tate frame connected through the generic normalization interface. -/
def sourceNormalization {k : Type} [Field k] [CharZero k] {n h : ℕ}
    {A : Matrices n h} (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : Universal G.root) :
    FrameNormalization (level (commonN A))
      (ArithmeticThetaArithmeticFieldR0231.half G) (interiorInclusion G.root)
      (ArithmeticThetaActualLevelR0208.object (provider G.root u) (levelMap G.root u)
        (openSquare G.root)) rfl G.frame.disk G.frame.frame where
  base := G.compact.space
  weight := G.hodge.line
  map := compactMap G.root
  square := compactSquare G.root
  chart := sourceChart G.hodge G.test
  triangle := G.frame.triangle
  interior := sourceInteriorLink G.root u G.test
  normalized :=
    { generator := G.frame.generator
      isFrame := G.frame.extendsGenerator.1
      generic_eq := G.frame.extendsGenerator.2
      square_eq := G.frame.square_eq }

end ArithmeticThetaReview.Normalization
