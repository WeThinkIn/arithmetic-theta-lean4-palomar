import ReviewGeometryBridges
import ReviewNormalizationSource

/-! A field-by-field view of the original normalized family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaReview.Geometry
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195 (normCount)
open ArithmeticThetaCompactModularityR0209
open ArithmeticThetaMetaplecticStackR0207 (Coherence ForgetData)
open ArithmeticThetaActualLevelR0208
open ArithmeticThetaLocalWeierstrassR0203 (Base)
open ArithmeticThetaComponentDegreeR0184 (projection)

/-- Nothing is selected again: the curve, line, disk, frame, normalization,
and sections are the fields of the supplied original family. The same
universality witness `u` is used for the finite level and the square comparison. -/
def familyOfData {k : Type} [Field k] [CharZero k] {n h : ℕ}
    {A : Matrices n h} (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (hgeometry : InteriorGeometry G.root) (u : Universal G.root)
    (C : Coherence (level (commonN A)) (Base k))
    (hforget : Nonempty (ForgetData (level (commonN A)) (Base k) C))
    (hstack : Pseudofunctor.IsStack C.functor
      (ArithmeticThetaRootStackR0198.rootTopology (Base k)))
    (hcomparison : Nonempty (PullbackComparison
      (canonicalMap C (interiorBase G.root)
        (object (provider G.root u) (levelMap G.root u) (openSquare G.root)))))
    (hlevel : FiniteEtaleLevel (provider G.root u) (levelMap G.root u) (openSquare G.root)
      (canonicalMap C (interiorBase G.root)
        (object (provider G.root u) (levelMap G.root u) (openSquare G.root)))) :
    FramedFamily k (level (commonN A)) (2 * 2 ^ (normCount A - 1)) n h where
  curve := curveOfRoot G.root hgeometry u C hforget hstack hcomparison hlevel
  disk := G.frame.disk
  disk_over := by
    have he := congrArg (fun f => f ≫ G.compact.projection) G.frame.triangle
    have he' := he.trans G.test.extends_eq.1
    simpa only [curveOfRoot, ArithmeticThetaArithmeticFieldR0231.MatrixData.root,
      projection, Category.assoc] using he'
  dominant := G.frame.dominant
  frame := G.frame.frame
  isFrame := G.frame.isFrame
  normalization := ArithmeticThetaReview.Normalization.sourceNormalization G u
  sections := G.sections

end ArithmeticThetaReview.Geometry
