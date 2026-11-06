module

public import SchemeHodgeUniversalR0205
public import RootModuliPseudofunctorR0198
public import Mathlib.CategoryTheory.Sigma.Basic
public import SchemeHodgeDefinitionsR0205

@[expose] public section

/-! Actual elliptic-family root objects and their categorical comparison.
The data below specify constructions; no existence theorem is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaCoverComparison

/-- An arbitrary marked elliptic family and a root of its ACTUAL cotangent.
There is no chosen classifier, equation, frame or Hodge comparison in this input. -/
structure Object (L : ℕ) (S : Scheme.{0}) where
  family : Family S
  marking : FullLevel family L
  root : SquareLine S (Cotangent family)

/-- Actual isomorphisms, including the inclusion-normalized cotangent map.
The cotangent map points forward, the inverse of differential pullback. -/
structure Arrow {L : ℕ} {S : Scheme.{0}} (X Y : Object L S) where
  curve : X.family.curve ≅ Y.family.curve
  marked : MarkedCartesian Y.family X.family Y.marking X.marking (𝟙 S) curve.hom
  cotangent : Cotangent X.family ≅ Cotangent Y.family
  canonical : CotangentCompatible Y.family X.family (𝟙 S) curve.hom marked.2.1
    ((Scheme.Modules.pullbackId S).app (Cotangent Y.family) ≪≫ cotangent.symm)
  line : X.root.line ≅ Y.root.line
  square : tensorPowerMap line.hom 2 ≫ Y.root.square.hom =
    X.root.square.hom ≫ cotangent.hom

/-- The category must have exactly these arrows, and the actual curve/line
composition laws. This is construction output, not an input category of classes. -/
structure GroupoidData (L : ℕ) (S : Scheme.{0}) where
  groupoid : Groupoid.{0} (Object L S)
  arrow : ∀ X Y, (@Quiver.Hom _ groupoid.toCategory.toCategoryStruct.toQuiver X Y) ≃ Arrow X Y
  curve_id : ∀ X, (arrow X X (@CategoryStruct.id _ groupoid.toCategory.toCategoryStruct X)).curve.hom = 𝟙 X.family.curve
  line_id : ∀ X, (arrow X X (@CategoryStruct.id _ groupoid.toCategory.toCategoryStruct X)).line.hom = 𝟙 X.root.line
  curve_comp : ∀ X Y Z f g,
    (arrow X Z (@CategoryStruct.comp _ groupoid.toCategory.toCategoryStruct X Y Z f g)).curve.hom =
      (arrow X Y f).curve.hom ≫ (arrow Y Z g).curve.hom
  line_comp : ∀ X Y Z f g,
    (arrow X Z (@CategoryStruct.comp _ groupoid.toCategory.toCategoryStruct X Y Z f g)).line.hom =
      (arrow X Y f).line.hom ≫ (arrow Y Z g).line.hom

def GroupoidData.Objects {L : ℕ} {S : Scheme.{0}} (_G : GroupoidData L S) := Object L S

instance {L : ℕ} {S : Scheme.{0}} (G : GroupoidData L S) : Groupoid.{0} G.Objects := G.groupoid

def lineForget {L : ℕ} {S : Scheme.{0}} (G : GroupoidData L S) : G.Objects ⥤ S.Modules where
  obj X := X.root.line
  map f := (G.arrow _ _ f).line.hom
  map_id X := G.line_id X
  map_comp f g := G.line_comp _ _ _ f g

/-- A functorial pullback of the actual families with their actual roots.
Both curve and line squares commute for every arrow, not only geometric points. -/
structure PullbackData {L : ℕ} {S T : Scheme.{0}}
    (GS : GroupoidData L S) (GT : GroupoidData L T) (a : T ⟶ S) where
  functor : GS.Objects ⥤ GT.Objects
  curve : ∀ X, (functor.obj X).family.curve ⟶ X.family.curve
  marked : ∀ X, MarkedCartesian X.family (functor.obj X).family
    X.marking (functor.obj X).marking a (curve X)
  cotangent : ∀ X, (Scheme.Modules.pullback a).obj (Cotangent X.family) ≅ Cotangent (functor.obj X).family
  canonical : ∀ X, CotangentCompatible X.family (functor.obj X).family a (curve X)
    (marked X).2.1 (cotangent X)
  line : ∀ X, (functor.obj X).root.line ≅ (Scheme.Modules.pullback a).obj X.root.line
  square : ∀ X, tensorPowerMap (line X).hom 2 ≫ (squarePull a X.root).hom ≫
    (cotangent X).hom = (functor.obj X).root.square.hom
  curve_natural : ∀ X Y (f : X ⟶ Y),
    (GT.arrow _ _ (functor.map f)).curve.hom ≫ curve Y = curve X ≫ (GS.arrow _ _ f).curve.hom
  line_natural : ∀ X Y (f : X ⟶ Y),
    (GT.arrow _ _ (functor.map f)).line.hom ≫ (line Y).hom =
      (line X).hom ≫ (Scheme.Modules.pullback a).map (GS.arrow _ _ f).line.hom

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)

abbrev BaseMap (S : Over (Base k)) :=
  {b : S.left ⟶ Base Q.quotient.ring //
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = S.hom}

/-- The disjoint union retains all square-root arrows over each classifying map. -/
abbrev RootFiber (S : Over (Base k)) :=
  Σ b : BaseMap k L A B C Q S,
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
      (ModularHodge k L A B C Q) (Over.mk b.val)

def rootForget (S : Over (Base k)) : RootFiber k L A B C Q S ⥤ S.left.Modules :=
  CategoryTheory.Sigma.desc (fun b =>
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.forget
      (W := ModularHodge k L A B C Q) (Over.mk b.val))

def mapBase {S T : Over (Base k)} (a : T ⟶ S) (b : BaseMap k L A B C Q S) :
    BaseMap k L A B C Q T :=
  ⟨a.left ≫ b.val, by rw [Category.assoc, b.property]; exact Over.w a⟩

/-- Reuse the accepted root pullback on the same actual sheaves. -/
def rootReindex {S T : Over (Base k)} (a : T ⟶ S) :
    RootFiber k L A B C Q S ⥤ RootFiber k L A B C Q T :=
  CategoryTheory.Sigma.desc (fun b =>
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.pull
      (W := ModularHodge k L A B C Q)
      (Over.homMk a.left (by rfl) : Over.mk (mapBase k L A B C Q a b).val ⟶ Over.mk b.val) ⋙
    CategoryTheory.Sigma.incl (C := fun c : BaseMap k L A B C Q T =>
      ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
        (ModularHodge k L A B C Q) (Over.mk c.val)) (mapBase k L A B C Q a b))

/-- A genuine equivalence of categories, with the same marked family classifier
and a NATURAL tautological line isomorphism preserving the exact square maps. -/
structure FiberComparison (S : Over (Base k)) (G : GroupoidData L S.left) where
  equiv : RootFiber k L A B C Q S ≌ G.Objects
  line : rootForget k L A B C Q S ≅ equiv.functor ⋙ lineForget G
  curve : ∀ r, (equiv.functor.obj r).family.curve ⟶ A.descent.family.curve
  classifies : ∀ r, Classifies k L A B C Q S.hom (equiv.functor.obj r).family
    (equiv.functor.obj r).marking r.1.val (curve r)
  cotangent : ∀ r, (Scheme.Modules.pullback r.1.val).obj (ModularHodge k L A B C Q) ≅
    Cotangent (equiv.functor.obj r).family
  canonical : ∀ r, ClassifierHodge k L A B C Q (equiv.functor.obj r).family
    r.1.val (curve r) (cotangent r)
  square : ∀ r, tensorPowerMap (line.hom.app r) 2 ≫ (equiv.functor.obj r).root.square.hom =
    r.2.square.hom ≫ (cotangent r).hom

/-- Canonical comparison of both actual base-change routes. The equation
fixes the tautological line map and thus excludes an unspecified sign. -/
def BaseChangeCompatible {S T : Over (Base k)}
    {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (ES : FiberComparison k L A B C Q S GS) (ET : FiberComparison k L A B C Q T GT)
    (a : T ⟶ S) (P : PullbackData GS GT a.left)
    (e : rootReindex k L A B C Q a ⋙ ET.equiv.functor ≅ ES.equiv.functor ⋙ P.functor) : Prop :=
  ∀ r, (GT.arrow _ _ (e.hom.app r)).line.hom =
    ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫
      (Scheme.Modules.pullback a.left).map (ES.line.hom.app r) ≫
        (P.line (ES.equiv.functor.obj r)).inv

/-- One quotient, all actual test-family groupoids, all fiber equivalences,
and their normalized natural comparison along EVERY base morphism.
Stack-level pseudofunctor packaging and finite-level transfer remain consumers. -/
def ComparisonSystem : Prop :=
  ∃ (G : ∀ S : Over (Base k), GroupoidData L S.left)
    (E : ∀ S : Over (Base k), FiberComparison k L A B C Q S (G S)),
    ∀ (S T : Over (Base k)) (a : T ⟶ S),
      ∃ P : PullbackData (G S) (G T) a.left,
        ∃! e : rootReindex k L A B C Q a ⋙ (E T).equiv.functor ≅ (E S).equiv.functor ⋙ P.functor,
          BaseChangeCompatible k L A B C Q (E S) (E T) a P e

end ArithmeticThetaMetaplecticComparisonR0206
