import FPQCSquareRootDescentR0197
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Groupoid

/-! A categorical presentation of the specified root moduli problem.
All construction and stack assertions are proof-worker outputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRootStackR0198
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196

/-- The actual sheaf pullback pseudofunctor on schemes over B. -/
abbrev modulesOver (B : Scheme.{0}) :=
  (Over.forget B).op.toPseudofunctor.comp ArithmeticThetaRootDescentR0197.moduleFunctor

/-- A pseudofunctor equipped with its actual underlying line sheaves and
specified square maps. The strong transformation retains unit/composition
coherence with the canonical sheaf pullback. -/
structure RootDiagram (B : Scheme.{0}) (W : B.Modules) where
  functor : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1}
  forget : Pseudofunctor.StrongTrans functor (modulesOver B)
  invertible : ∀ (T : Over B) (x : functor.obj (.mk (.op T))),
    Scheme.Modules.IsInvertible ((forget.app (.mk (.op T))).toFunctor.obj x)
  square : ∀ (T : Over B) (x : functor.obj (.mk (.op T))),
    tensorPower T.left ((forget.app (.mk (.op T))).toFunctor.obj x) 2 ≅
      (Scheme.Modules.pullback T.hom).obj W

/-- The actual square-root object underlying a categorical object. -/
def root {B : Scheme.{0}} {W : B.Modules} (D : RootDiagram B W)
    (T : Over B) (x : D.functor.obj (.mk (.op T))) :
    SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W) :=
  ⟨(D.forget.app (.mk (.op T))).toFunctor.obj x, D.invertible T x, D.square T x⟩

/-- Square compatibility for the same strong pullback comparison, on every
scheme map over B; equality of full sheaf maps, including nonreduced tests. -/
def SquareNatural {B : Scheme.{0}} {W : B.Modules} (D : RootDiagram B W) : Prop :=
  ∀ (S T : Over B) (f : S ⟶ T) (x : D.functor.obj (.mk (.op T))),
    tensorPowerMap ((D.forget.naturality f.op.toLoc).hom.toNatTrans.app x) 2 ≫
      (squarePull f.left (root D T x)).hom ≫
      ((Scheme.Modules.pullbackComp f.left T.hom).app W).hom ≫
      ((Scheme.Modules.pullbackCongr (Over.w f)).app W).hom =
    (D.square S ((D.functor.map f.op.toLoc).toFunctor.obj x)).hom

/-- A presentation is equivalent, fiber by fiber, to ALL genuine square roots,
with EXACTLY the square-compatible sheaf isomorphisms as arrows. These are
construction output data, not assumed descent or stack properties. -/
structure Presentation (B : Scheme.{0}) (W : B.Modules) extends RootDiagram B W where
  groupoid : ∀ T : Over B, IsGroupoid (functor.obj (.mk (.op T)))
  square_natural : SquareNatural toRootDiagram
  homEquiv : ∀ (T : Over B) (x y : functor.obj (.mk (.op T))),
    (x ⟶ y) ≃ SquareIso (root toRootDiagram T x) (root toRootDiagram T y)
  hom_eq : ∀ (T : Over B) (x y : functor.obj (.mk (.op T))) (f : x ⟶ y),
    (homEquiv T x y f).val.hom = (forget.app (.mk (.op T))).toFunctor.map f
  essentially_surjective : ∀ (T : Over B)
    (J : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W)),
    ∃ x : functor.obj (.mk (.op T)), Nonempty (SquareIso (root toRootDiagram T x) J)

/-- The standard big fpqc topology on schemes over the specified base. -/
abbrev rootTopology (B : Scheme.{0}) := Scheme.fpqcTopology.over B

/-- Categorical descent along every single quasicompact faithfully flat cover.
This predicate is an input only to the general site criterion, and an output
of the root-specific comparison theorem. -/
def SingletonDescent {B : Scheme.{0}}
    (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1}) : Prop :=
  ∀ (T V : Over B) (q : V ⟶ T),
    QuasiCompact q.left → Flat q.left → Surjective q.left →
      (F.toDescentData (fun _ : Unit => q)).IsEquivalence

/-- Categorical descent for every open covering family in the site universe,
including infinite covers and the empty cover of the empty scheme. -/
def OpenDescent {B : Scheme.{0}}
    (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1}) : Prop :=
  ∀ (T : Over B) (ι : Type 1) (V : ι → Over B) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i).left) →
    (∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) →
      (F.toDescentData f).IsEquivalence

end ArithmeticThetaRootStackR0198
