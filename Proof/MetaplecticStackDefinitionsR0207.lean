module

public import NaturalMetaplecticComparisonR0206
public import FPQCRootStackR0198

@[expose] public section

/-! Coherent pullback of actual root-bearing elliptic families.
All existence and coherence results are assigned to proof workers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticStackR0207
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open ArithmeticThetaMetaplecticComparisonR0206

/-- Fix already constructed actual groupoids, without changing their objects or arrows. -/
def group (L : ℕ) (S : Scheme.{0}) : GroupoidData L S :=
  Classical.choice (actual_metaplectic_groupoid L S)

/-- Use the accepted geometric pullback and all its curve, cotangent and line equations. -/
def pull (L : ℕ) {S T : Scheme.{0}} (a : T ⟶ S) :
    PullbackData (group L S) (group L T) a :=
  ActualPullbackProof.pullData (group L S) (group L T) a

/-- Both geometric components of the unit comparison are fixed. -/
def UnitNormalized {L : ℕ} {S : Scheme.{0}} {G : GroupoidData L S}
    (P : PullbackData G G (𝟙 S)) (e : P.functor ≅ 𝟭 G.Objects) : Prop :=
  ∀ X, (G.arrow _ _ (e.hom.app X)).curve.hom = P.curve X ∧
    (G.arrow _ _ (e.hom.app X)).line.hom =
      (P.line X).hom ≫ (Scheme.Modules.pullbackId S).hom.app X.root.line

/-- Both geometric components of composition are fixed, including the original
Cartesion projections and the canonical sheaf pullback associativity map. -/
def CompNormalized {L : ℕ} {S T U : Scheme.{0}}
    {GS : GroupoidData L S} {GT : GroupoidData L T} {GU : GroupoidData L U}
    {a : T ⟶ S} {b : U ⟶ T}
    (P : PullbackData GS GT a) (Q : PullbackData GT GU b)
    (R : PullbackData GS GU (b ≫ a))
    (e : R.functor ≅ P.functor ⋙ Q.functor) : Prop :=
  ∀ X,
    (GU.arrow _ _ (e.hom.app X)).curve.hom ≫ Q.curve (P.functor.obj X) ≫ P.curve X =
      R.curve X ∧
    (GU.arrow _ _ (e.hom.app X)).line.hom ≫ (Q.line (P.functor.obj X)).hom ≫
      (Scheme.Modules.pullback b).map (P.line X).hom =
      (R.line X).hom ≫ (Scheme.Modules.pullbackComp b a).inv.app X.root.line

variable (L : ℕ) (B : Scheme.{0})

def fiber (S : (Over B)ᵒᵖ) : Cat.{0, 1} := Cat.of (group L S.unop.left).Objects

def reindex {S T : (Over B)ᵒᵖ} (f : S ⟶ T) : fiber L B S ⟶ fiber L B T :=
  (pull L f.unop.left).functor.toCatHom

/-- Actual unit and composition isomorphisms with pentagon and both triangle
laws. These are required outputs, not hypotheses of the construction theorem. -/
structure Coherence where
  unit : ∀ S, reindex L B (𝟙 S) ≅ 𝟙 (fiber L B S)
  comp : ∀ {S T U : (Over B)ᵒᵖ} (f : S ⟶ T) (g : T ⟶ U),
    reindex L B (f ≫ g) ≅ reindex L B f ≫ reindex L B g
  unit_normalized : ∀ S : Over B,
    UnitNormalized (pull L (𝟙 S.left)) (Cat.Hom.toNatIso (unit (.op S)))
  comp_normalized : ∀ (S T U : Over B) (a : T ⟶ S) (b : U ⟶ T),
    CompNormalized (pull L a.left) (pull L b.left) (pull L (b.left ≫ a.left))
      (Cat.Hom.toNatIso (comp a.op b.op))
  associativity : ∀ {S T U V : (Over B)ᵒᵖ} (f : S ⟶ T) (g : T ⟶ U) (h : U ⟶ V),
    (comp (f ≫ g) h).hom ≫ (comp f g).hom ▷ reindex L B h ≫
      (α_ (reindex L B f) (reindex L B g) (reindex L B h)).hom ≫
      reindex L B f ◁ (comp g h).inv ≫ (comp f (g ≫ h)).inv = eqToHom (by simp)
  left_unit : ∀ {S T : (Over B)ᵒᵖ} (f : S ⟶ T),
    (comp (𝟙 S) f).hom ≫ (unit S).hom ▷ reindex L B f ≫
      (λ_ (reindex L B f)).hom = eqToHom (by simp)
  right_unit : ∀ {S T : (Over B)ᵒᵖ} (f : S ⟶ T),
    (comp f (𝟙 T)).hom ≫ reindex L B f ◁ (unit T).hom ≫
      (ρ_ (reindex L B f)).hom = eqToHom (by simp)

/-- Standard categorical packaging of the required coherence laws. -/
def Coherence.functor (C : Coherence L B) :
    Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1} :=
  LocallyDiscrete.mkPseudofunctor (fiber L B) (reindex L B)
    C.unit C.comp C.associativity C.left_unit C.right_unit

/-- The already proved line-naturality equation, presented as a natural iso. -/
def linePull {S T : Over B} (a : T ⟶ S) :
    (pull L a.left).functor ⋙ lineForget (group L T.left) ≅
      lineForget (group L S.left) ⋙ Scheme.Modules.pullback a.left :=
  NatIso.ofComponents (fun X => (pull L a.left).line X)
    (fun f => (pull L a.left).line_natural _ _ f)

/-- A coherent tautological line, with the specified actual pullback map.
HEq only compares the dependent functor hom types after app_eq; it does not
weaken either map or permit an arbitrary scalar. -/
structure ForgetData (C : Coherence L B) where
  transformation : Pseudofunctor.StrongTrans C.functor
    (ArithmeticThetaRootStackR0198.modulesOver B)
  app_eq : ∀ S : Over B, transformation.app (.mk (.op S)) =
    (lineForget (group L S.left)).toCatHom
  naturality_eq : ∀ (S T : Over B) (a : T ⟶ S),
    HEq (transformation.naturality a.op.toLoc) (Cat.Hom.isoMk (linePull L B a))

end ArithmeticThetaMetaplecticStackR0207
