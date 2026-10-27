import ActualMetaplecticFPQCStackR0207
import CategoricalRootFiberR0199
import RootClassifyingMapR0199

/-! Finite levels in the actual elliptic-family stack, over all field-base tests.
Only definitions and accepted constructions occur here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaActualLevelR0208
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaMetaplecticComparisonR0206 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
open ArithmeticThetaStackLevelR0199
attribute [local instance] CategoryTheory.uliftCategory

abbrev Provider := ActualFamilyFPQCDescentProof.Provider

variable {k : Type} [Field k] [CharZero k] {L : ℕ}

abbrev base (P : Provider k L) : Over (Base k) :=
  Over.mk (ActualFamilyFPQCDescentProof.quotientStructure (Q := P.quotient))

abbrev hodge (P : Provider k L) :=
  ModularHodge k L P.atlas P.two P.cover P.quotient

/-- The accepted model is constructed from the actual map to the quotient. -/
def model (P : Provider k L) {Y : Over (Base k)} (p : Y ⟶ base P) :=
  FiberEquivalenceProof.model P.universal
    (⟨p.left, Over.w p⟩ : BaseMap k L P.atlas P.two P.cover P.quotient Y)

def object (P : Provider k L) {Y : Over (Base k)} (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P))) :
    (group L Y.left).Objects := FiberEquivalenceProof.obj (model P p) H

/-- A classifying map with an actual family isomorphism at its identity test. -/
structure AnchoredMap (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (group L Y.left).Objects) where
  map : Pseudofunctor.StrongTrans (representable Y) C.functor
  anchor : (map.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y)) ≅ X

/-- Reuse the accepted generic categorical Yoneda construction and unit map. -/
def canonicalMap (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (group L Y.left).Objects) : AnchoredMap C Y X where
  map := RootClassifyingMapR0199.classify C.functor Y X
  anchor := (Cat.Hom.toNatIso (C.unit (.op Y))).app X

/-- Actual family/root comparison, natural in every test morphism and normalized
at identity. Its arrows retain the marked curve, cotangent and full square map. -/
structure PullbackComparison {C : Coherence L (Base k)} {Y : Over (Base k)}
    {X : (group L Y.left).Objects} (j : AnchoredMap C Y X) where
  component : ∀ (S : Over (Base k)) (f : S ⟶ Y),
    (j.map.app (.mk (.op S))).toFunctor.obj (point f) ≅ (pull L f.left).functor.obj X
  identity : (component Y (𝟙 Y)).hom ≫
    (Cat.Hom.toNatIso (C.unit (.op Y))).hom.app X = j.anchor.hom
  natural : ∀ (S T : Over (Base k)) (a : T ⟶ S) (f : S ⟶ Y),
    (component T (a ≫ f)).hom ≫
      (Cat.Hom.toNatIso (C.comp f.op a.op)).hom.app X =
    (j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f) ≫
      (pull L a.left).functor.map (component S f).hom

/-- All arrows in the categorical fiber of actual family maps over Spec k. -/
abbrev TestFiber {C : Coherence L (Base k)} {Y T : Over (Base k)}
    (j : Pseudofunctor.StrongTrans (representable Y) C.functor)
    (r : Pseudofunctor.StrongTrans (representable T) C.functor) (S : Over (Base k)) :=
  Comma ((j.app (.mk (.op S))).toFunctor) ((r.app (.mk (.op S))).toFunctor)

def fiberPull {C : Coherence L (Base k)} {Y T S S' : Over (Base k)}
    (j : Pseudofunctor.StrongTrans (representable Y) C.functor)
    (r : Pseudofunctor.StrongTrans (representable T) C.functor) (a : S' ⟶ S) :
    TestFiber j r S ⥤ TestFiber j r S' :=
  Comma.map (j.naturality a.op.toLoc).hom.toNatTrans (r.naturality a.op.toLoc).inv.toNatTrans

/-- Representability on all field-base tests, with both projections and naturality. -/
structure FiberPresentation {C : Coherence L (Base k)} {Y T : Over (Base k)}
    (j : Pseudofunctor.StrongTrans (representable Y) C.functor)
    (r : Pseudofunctor.StrongTrans (representable T) C.functor) where
  space : Over (Base k)
  toLevel : space ⟶ Y
  toTest : space ⟶ T
  equiv : ∀ S : Over (Base k), Points S space ≌ TestFiber j r S
  left_eq : ∀ (S : Over (Base k)) (f : S ⟶ space),
    ((equiv S).functor.obj (point f)).left = point (f ≫ toLevel)
  right_eq : ∀ (S : Over (Base k)) (f : S ⟶ space),
    ((equiv S).functor.obj (point f)).right = point (f ≫ toTest)
  natural : ∀ (S S' : Over (Base k)) (a : S' ⟶ S),
    Nonempty (precompose space a ⋙ (equiv S').functor ≅ (equiv S).functor ⋙ fiberPull j r a)

/-- The actual categorical fiber is the accepted geometric square-isometry
scheme, up to an isomorphism preserving both original projection maps. -/
def UsesFiber {P : Provider k L} {C : Coherence L (Base k)} {Y T : Over (Base k)}
    {p : Y ⟶ base P}
    {H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P))}
    {R : RootObject (base P).left (hodge P) T.left}
    {j : Pseudofunctor.StrongTrans (representable Y) C.functor}
    {r : Pseudofunctor.StrongTrans (representable T) C.functor}
    (F : Fiber p.left H R) (G : FiberPresentation j r) : Prop :=
  ∃ e : G.space.left ≅ F.space,
    e.hom ≫ F.universal.toLevel = G.toLevel.left ∧
    e.hom ≫ F.universal.toTest = G.toTest.left

/-- The classifier and root of an ARBITRARY stack-valued test map at identity,
using the actual accepted Hodge comparison of its elliptic family. -/
def testRoot (P : Provider k L) {C : Coherence L (Base k)} {T : Over (Base k)}
    (r : Pseudofunctor.StrongTrans (representable T) C.functor) :
    RootObject (base P).left (hodge P) T.left :=
  let X : (group L T.left).Objects := (r.app (.mk (.op T))).toFunctor.obj (point (𝟙 T))
  ⟨(ActualFamilyFPQCDescentProof.classifier P.universal X).val,
    ActualFamilyFPQCDescentProof.classifiedRoot P.universal X⟩

/-- Finite etale representability in the actual family stack. No surjectivity
of p is silently assumed: outside its image the degree can be zero. -/
def FiniteEtaleLevel (P : Provider k L) {C : Coherence L (Base k)}
    {Y : Over (Base k)} (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (j : AnchoredMap C Y (object P p H)) : Prop :=
  ∀ (T : Over (Base k)) (r : Pseudofunctor.StrongTrans (representable T) C.functor),
    ∃ (F : Fiber p.left H (testRoot P r)) (G : FiberPresentation j.map r),
      Represents F ∧ PairTorsor F ∧ UsesFiber F G ∧
      IsFinite G.toTest.left ∧ Etale G.toTest.left ∧
      (Surjective p.left → Surjective G.toTest.left) ∧
      ∀ t : T.left, G.toTest.left.finrank t = 2 * p.left.finrank ((testRoot P r).map t)

end ArithmeticThetaActualLevelR0208
