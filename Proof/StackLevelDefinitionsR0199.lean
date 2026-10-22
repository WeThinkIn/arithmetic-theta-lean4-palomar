module

public import FPQCRootStackR0198
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Yoneda
public import RootModuliPseudofunctorR0198

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaStackLevelR0199
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRootStackR0198 ArithmeticThetaMetaplecticTestsR0196
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower
attribute [local instance] CategoryTheory.uliftCategory

/-- A universe lift of the discrete functor of points; arrows remain small. -/
abbrev Points {B : Scheme.{0}} (S Y : Over B) := ULift.{1} (Discrete (S ⟶ Y))

def point {B : Scheme.{0}} {S Y : Over B} (f : S ⟶ Y) : Points S Y := ⟨⟨f⟩⟩

def precompose {B : Scheme.{0}} {S T : Over B} (Y : Over B) (a : S ⟶ T) :
    Points T Y ⥤ Points S Y :=
  ULift.downFunctor ⋙ Discrete.functor (fun f : T ⟶ Y => point (a ≫ f))

/-- The representable presheaf as a category-valued functor. -/
def pointsFunctor {B : Scheme.{0}} (Y : Over B) : (Over B)ᵒᵖ ⥤ Cat.{0,1} where
  obj S := Cat.of (Points S.unop Y)
  map a := (precompose Y a.unop).toCatHom
  map_id S := by
    apply Cat.Hom.ext
    fapply CategoryTheory.Functor.ext
    · intro f
      change point (𝟙 S.unop ≫ f.down.as) = f
      cases f with
      | up f => cases f; simp [point]
    · change ∀ X Y f, _
      intro X Z f
      exact congrArg Discrete.Hom.mk rfl
  map_comp a b := by
    apply Cat.Hom.ext
    fapply CategoryTheory.Functor.ext
    · intro f
      change point ((b.unop ≫ a.unop) ≫ f.down.as) = point (b.unop ≫ (a.unop ≫ f.down.as))
      simp only [Category.assoc]
    · change ∀ X Y f, _
      intro X Z f
      exact congrArg Discrete.Hom.mk rfl

abbrev representable {B : Scheme.{0}} (Y : Over B) := (pointsFunctor Y).toPseudofunctor'

/-- A genuine morphism into the root stack, with the specified value at identity. -/
structure ClassifiedMap {B : Scheme.{0}} {W : B.Modules} (P : Presentation B W)
    (Y : Over B) (H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)) where
  map : Pseudofunctor.StrongTrans (representable Y) P.functor
  anchor : SquareIso
    (root P.toRootDiagram Y ((map.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y)))) H

/-- The actual categorical two-fiber: target arrows are invertible because P
has groupoid fibers. It retains all square-root arrows, not isomorphism classes. -/
abbrev TestFiber {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
    {Y T : Over B} (j : Pseudofunctor.StrongTrans (representable Y) P.functor)
    (r : Pseudofunctor.StrongTrans (representable T) P.functor) (S : Over B) :=
  Comma ((j.app (.mk (.op S))).toFunctor) ((r.app (.mk (.op S))).toFunctor)

/-- Canonical reindexing of the actual comma category, using the SAME strong
naturality isomorphisms as the two classifying maps. -/
def fiberPull {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
    {Y T S S' : Over B}
    (j : Pseudofunctor.StrongTrans (representable Y) P.functor)
    (r : Pseudofunctor.StrongTrans (representable T) P.functor) (a : S' ⟶ S) :
    TestFiber j r S ⥤ TestFiber j r S' :=
  Comma.map (j.naturality a.op.toLoc).hom.toNatTrans
    (r.naturality a.op.toLoc).inv.toNatTrans

/-- Scheme representability with all-test categorical equivalences, both
projections and naturality under every base-change map. -/
structure FiberPresentation {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
    {Y T : Over B}
    (j : Pseudofunctor.StrongTrans (representable Y) P.functor)
    (r : Pseudofunctor.StrongTrans (representable T) P.functor) where
  space : Over B
  toLevel : space ⟶ Y
  toTest : space ⟶ T
  equiv : ∀ S : Over B, Points S space ≌ TestFiber j r S
  left_eq : ∀ (S : Over B) (f : S ⟶ space),
    ((equiv S).functor.obj (point f)).left = point (f ≫ toLevel)
  right_eq : ∀ (S : Over B) (f : S ⟶ space),
    ((equiv S).functor.obj (point f)).right = point (f ≫ toTest)
  natural : ∀ (S S' : Over B) (a : S' ⟶ S),
    Nonempty (precompose space a ⋙ (equiv S').functor ≅ (equiv S).functor ⋙ fiberPull j r a)

/-- Finite etale representability for every actual stack-valued test map.
The rank is measured over the original level morphism, not an unrelated scalar action. -/
def FiniteEtaleLevel {B : Scheme.{0}} {W : B.Modules} (P : Presentation B W)
    (Y : Over B) (j : Pseudofunctor.StrongTrans (representable Y) P.functor) : Prop :=
  ∀ (T : Over B) (r : Pseudofunctor.StrongTrans (representable T) P.functor),
    ∃ F : FiberPresentation j r,
      IsFinite F.toTest.left ∧ Etale F.toTest.left ∧ Surjective F.toTest.left ∧
        ∀ t : T.left, Scheme.Hom.finrank F.toTest.left t = 2 * Scheme.Hom.finrank Y.hom (T.hom t)

/-- The tautological line comparison includes the full square equation (in
SquareIso) and the same strong pullback maps on every test morphism. -/
structure TautologicalComparison {B : Scheme.{0}} {W : B.Modules}
    {P : Presentation B W} {Y : Over B}
    {H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)}
    (j : ClassifiedMap P Y H) where
  component : ∀ (S : Over B) (f : S ⟶ Y), SquareIso
    (root P.toRootDiagram S ((j.map.app (.mk (.op S))).toFunctor.obj (point f)))
    (ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.pullObj f H)
  natural : ∀ (S S' : Over B) (a : S' ⟶ S) (f : S ⟶ Y),
    (component S' (a ≫ f)).val.hom =
      (P.forget.app (.mk (.op S'))).toFunctor.map
        ((j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f)) ≫
      (P.forget.naturality a.op.toLoc).hom.toNatTrans.app
        ((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ≫
      (Scheme.Modules.pullback a.left).map (component S f).val.hom ≫
      (Scheme.Modules.pullbackComp a.left f.left).hom.app H.line

/-- The represented categorical fiber uses the same scheme and projection
maps as the already accepted geometric fiber, up to a checked isomorphism. -/
def UsesFiber {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
    {Y T : Over B} {H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)}
    {R : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W)}
    (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (F : Fiber Y.hom H (⟨T.hom, R⟩ : RootObject B W T.left))
    (G : FiberPresentation j.map r.map) : Prop :=
  ∃ e : G.space.left ≅ F.space,
    e.hom ≫ F.universal.toLevel = G.toLevel.left ∧
    e.hom ≫ F.universal.toTest = G.toTest.left

end ArithmeticThetaStackLevelR0199
