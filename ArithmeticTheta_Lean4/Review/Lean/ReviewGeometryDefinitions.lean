import ActualLevelDefinitionsR0208
import FieldImageDefinitionsR0233
import ReviewNormalizationDefinitions

/-!
# Geometry needed to read the modularity conclusion

The objects and arrows of the metaplectic stack are the original marked elliptic
families with a square root of their actual cotangent line. This interface does
not include a choice of atlas, quotient presentation, or root-cover algorithm.
The adapter in `ReviewGeometryBridges` constructs it from the original witnesses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaReview.Geometry
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 (Base)
open ArithmeticThetaMetaplecticStackR0207 (Coherence ForgetData group)
open ArithmeticThetaActualLevelR0208 (AnchoredMap PullbackComparison FiberPresentation)
open ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaTateCuspsR0181 (Disk genericInclusion)

/-- Every base change to a scheme is represented by a finite étale scheme.
The bound concerns the actual projection to that test scheme; zero rank on
other components is allowed. Both projections and naturality are retained by
`FiberPresentation`. This predicate makes no reference to an atlas/provider. -/
def FiniteLevel {k : Type} [Field k] [CharZero k] {L : ℕ}
    {C : Coherence L (Base k)} {Y : Over (Base k)}
    {X : (group L Y.left).Objects} (j : AnchoredMap C Y X) (bound : ℕ) : Prop :=
  Nonempty (PullbackComparison j) ∧
  ∀ (T : Over (Base k))
    (r : Pseudofunctor.StrongTrans (ArithmeticThetaStackLevelR0199.representable T)
      C.functor),
    ∃ F : FiberPresentation j.map r,
      IsFinite F.toTest.left ∧ Etale F.toTest.left ∧
      ∀ t : T.left, F.toTest.left.finrank t ≤ bound

/-- A compact curve, its half-weight line, and the actual finite level on a
dense open. The line on the level is literally the restriction of this line,
not an unrelated line with an arbitrarily chosen expansion map. -/
structure CompactCurve (k : Type) [Field k] [CharZero k] (L bound : ℕ) where
  space : Scheme.{0}
  structureMap : space ⟶ Base k
  integral : IsIntegral space
  proper : IsProper structureMap
  smooth : SmoothOfRelativeDimension 1 structureMap
  half : space.Modules
  invertible : Scheme.Modules.IsInvertible half
  interior : Over (Base k)
  inclusion : interior.left ⟶ space
  over_eq : inclusion ≫ structureMap = interior.hom
  openImmersion : IsOpenImmersion inclusion
  dense : DenseRange inclusion.base
  object : ArithmeticThetaMetaplecticComparisonR0206.Object L interior.left
  root_eq : object.root.line = (Scheme.Modules.pullback inclusion).obj half
  coherence : Coherence L (Base k)
  tautological : Nonempty (ForgetData L (Base k) coherence)
  stack : Pseudofunctor.IsStack coherence.functor
    (ArithmeticThetaRootStackR0198.rootTopology (Base k))
  classifying : AnchoredMap coherence interior object
  finiteLevel : FiniteLevel classifying bound

/-- A specified dominant formal disk and its genuine line-bundle frame.
These are geometric pullbacks and global sections, not abstract linear
functionals. The normalization bridge identifies the original Tate frame. -/
structure FramedFamily (k : Type) [Field k] [CharZero k] (L bound n h : ℕ) where
  curve : CompactCurve k L bound
  disk : Disk k ⟶ curve.space
  disk_over : disk ≫ curve.structureMap = ArithmeticThetaTateCuspsR0181.diskStructure k
  dominant : IsDominant (genericInclusion k ≫ disk)
  frame : ArithmeticThetaFieldImageR0233.Sections
    ((Scheme.Modules.pullback disk).obj curve.half)
  isFrame : ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ frame
  normalization : ArithmeticThetaReview.Normalization.FrameNormalization L
    curve.half curve.inclusion curve.object curve.root_eq disk frame
  sections : Fin h → ArithmeticThetaFieldImageR0233.Sections
    (tensorPower curve.space curve.half n)

/-- Complete theta expansions in the displayed frame, with the literal
substitution `q = t^L` and the scalar action of the actual structure morphism. -/
def Realizes {k : Type} [Field k] [CharZero k] {L bound n h : ℕ}
    (F : FramedFamily k L bound n h)
    (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h) : Prop :=
  ∀ c : Fin h → k,
    ArithmeticThetaNormalizedSections.pullbackPowerSection F.disk F.curve.half n
      (ArithmeticThetaFieldImageR0233.combination k F.curve.structureMap F.sections c) =
    ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
      (PowerSeries.subst (PowerSeries.X ^ L)
        (ArithmeticThetaFieldImageR0233.seriesCombination k A c)) •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback F.disk).obj F.curve.half)
        n ⊤ F.frame

end ArithmeticThetaReview.Geometry
