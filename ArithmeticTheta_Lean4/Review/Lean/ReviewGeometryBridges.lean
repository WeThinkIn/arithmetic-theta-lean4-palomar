import ReviewFiniteLevel
import ConservativeImageConsumerR0268

/-! Preserve the original geometric witnesses while projecting their interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaReview.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaCompactModularityR0209
open ArithmeticThetaMetaplecticStackR0207 (Coherence ForgetData)
open ArithmeticThetaActualLevelR0208
open ArithmeticThetaLocalWeierstrassR0203 (Base)
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaComponentDegreeR0184

/-- The same compact curve, the same restricted root and the same classifying
map. The proof arguments supply already proved properties of those maps. -/
def curveOfRoot {k : Type} [Field k] [CharZero k] {L b : ℕ}
    (K : CompactRoot k L b) (hgeometry : InteriorGeometry K)
    (h : Universal K) (C : Coherence L (Base k))
    (hforget : Nonempty (ForgetData L (Base k) C))
    (hstack : Pseudofunctor.IsStack C.functor
      (ArithmeticThetaRootStackR0198.rootTopology (Base k)))
    (hcomparison : Nonempty (PullbackComparison
      (canonicalMap C (interiorBase K)
        (object (provider K h) (levelMap K h) (openSquare K)))))
    (hlevel : FiniteEtaleLevel (provider K h) (levelMap K h) (openSquare K)
      (canonicalMap C (interiorBase K)
        (object (provider K h) (levelMap K h) (openSquare K)))) :
    CompactCurve k L (2 * b) where
  space := K.cover.space
  structureMap := K.cover.map ≫ projection k L K.data K.compact K.point
  integral := K.cover.integral
  proper := K.cover.proper
  smooth := K.cover.smooth
  half := line K
  invertible := K.half.invertible.pullback K.cover.map
  interior := interiorBase K
  inclusion := interiorInclusion K
  over_eq := by
    have he := congrArg (fun f => f ≫ K.compact.projection)
      (pullback.condition (f := compactMap K) (g := K.compact.inclusion))
    simpa only [interiorInclusion, interiorBase, interiorMap, Over.mk_hom,
      compactMap, projection, Category.assoc, K.compact.over_eq] using he
  openImmersion := hgeometry.1
  dense := hgeometry.2.1
  object := object (provider K h) (levelMap K h) (openSquare K)
  root_eq := rfl
  coherence := C
  tautological := hforget
  stack := hstack
  classifying := canonicalMap C (interiorBase K)
    (object (provider K h) (levelMap K h) (openSquare K))
  finiteLevel := finite_level_of_original k L (provider K h) C (interiorBase K)
    (levelMap K h) (openSquare K) _ hcomparison hlevel b hgeometry.2.2.2.2

end ArithmeticThetaReview.Geometry
