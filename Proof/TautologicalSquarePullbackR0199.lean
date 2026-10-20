module

public import StackLevelDefinitionsR0199

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaStackLevelR0199
namespace TautologicalSquarePullbackR0199
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRootStackR0198 ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
open ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198
attribute [local instance] CategoryTheory.uliftCategory

variable {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
  {Y : Over B} {H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)}

def pointId {S : Over B} (f : S ⟶ Y) :
    point f ≅ (precompose Y f).obj (point (𝟙 Y)) :=
  eqToIso (by change point f = point (f ≫ 𝟙 Y); rw [Category.comp_id])

def rootArrow (j : ClassifiedMap P Y H) {S : Over B} (f : S ⟶ Y) :=
  (j.map.app (.mk (.op S))).toFunctor.map (pointId f).hom ≫
    (j.map.naturality f.op.toLoc).hom.toNatTrans.app (point (𝟙 Y))

def pullComparison {S T : Over B} (f : S ⟶ T)
    (x : P.functor.obj (.mk (.op T))) : SquareIso
    (root P.toRootDiagram S ((P.functor.map f.op.toLoc).toFunctor.obj x))
    (pullObj f (root P.toRootDiagram T x)) :=
  ⟨(Cat.Hom.toNatIso (P.forget.naturality f.op.toLoc)).app x,
    P.square_natural S T f x⟩

def component (j : ClassifiedMap P Y H) (S : Over B) (f : S ⟶ Y) : SquareIso
    (root P.toRootDiagram S ((j.map.app (.mk (.op S))).toFunctor.obj (point f)))
    (pullObj f H) :=
  trans (P.homEquiv S _ _ (rootArrow j f))
    (trans (pullComparison f _) ((pull f).map j.anchor))

/-- The tautological module transformation, with its actual strong coherence. -/
def underlying (j : ClassifiedMap P Y H) := j.map.vcomp P.forget

lemma underlying_naturality (j : ClassifiedMap P Y H) {S T : Over B}
    (f : S ⟶ T) (x : Points T Y) :
    ((underlying j).naturality f.op.toLoc).hom.toNatTrans.app x =
      (P.forget.app (.mk (.op S))).toFunctor.map
        ((j.map.naturality f.op.toLoc).hom.toNatTrans.app x) ≫
      (P.forget.naturality f.op.toLoc).hom.toNatTrans.app
        ((j.map.app (.mk (.op T))).toFunctor.obj x) := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

def yonedaHom (τ : Pseudofunctor.StrongTrans (representable Y) (modulesOver B))
    {S : Over B} (f : S ⟶ Y) :=
  (τ.app (.mk (.op S))).toFunctor.map (pointId f).hom ≫
    (τ.naturality f.op.toLoc).hom.toNatTrans.app (point (𝟙 Y))

lemma yonedaHom_natural
    (τ : Pseudofunctor.StrongTrans (representable Y) (modulesOver B))
    {S S' : Over B} (a : S' ⟶ S) (f : S ⟶ Y) :
    yonedaHom τ (a ≫ f) =
      (τ.naturality a.op.toLoc).hom.toNatTrans.app (point f) ≫
      (Scheme.Modules.pullback a.left).map (yonedaHom τ f) ≫
      (Scheme.Modules.pullbackComp a.left f.left).hom.app
        ((τ.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y))) := by
  have h := congrArg (fun k => k.toNatTrans.app (point (𝟙 Y)))
    (τ.naturality_comp f.op.toLoc a.op.toLoc)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app] at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  change (τ.naturality (a ≫ f).op.toLoc).hom.toNatTrans.app (point (𝟙 Y)) ≫
      (Scheme.Modules.pullbackComp a.left f.left).inv.app
        ((τ.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y))) = _ at h
  have h' := congrArg (fun k => k ≫ (Scheme.Modules.pullbackComp a.left f.left).hom.app
    ((τ.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y)))) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h'
  erw [Category.comp_id] at h'
  have hp : (pointId (a ≫ f)).hom ≫
      ((representable Y).mapComp f.op.toLoc a.op.toLoc).hom.toNatTrans.app
        (point (𝟙 Y)) = (precompose Y a).map (pointId f).hom := by
    apply ULift.ext
    apply Subsingleton.elim
  have hn := ((τ.naturality a.op.toLoc).hom.toNatTrans).naturality (pointId f).hom
  dsimp only [yonedaHom]
  erw [h']
  simp only [← Category.assoc]
  rw [← Functor.map_comp, hp]
  erw [hn]
  simp only [Category.assoc, Functor.map_comp]
  rfl


lemma component_hom (j : ClassifiedMap P Y H) (S : Over B) (f : S ⟶ Y) :
    (component j S f).val.hom = yonedaHom (underlying j) f ≫
      (Scheme.Modules.pullback f.left).map j.anchor.val.hom := by
  dsimp only [component, RootModuliPseudofunctorR0198.trans, Iso.trans_hom]
  rw [P.hom_eq]
  dsimp only [rootArrow, yonedaHom]
  rw [underlying_naturality]
  simp only [Functor.map_comp, Category.assoc]
  rfl

lemma component_natural (j : ClassifiedMap P Y H) (S S' : Over B)
    (a : S' ⟶ S) (f : S ⟶ Y) :
    (component j S' (a ≫ f)).val.hom =
      (P.forget.app (.mk (.op S'))).toFunctor.map
        ((j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f)) ≫
      (P.forget.naturality a.op.toLoc).hom.toNatTrans.app
        ((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ≫
      (Scheme.Modules.pullback a.left).map (component j S f).val.hom ≫
      (Scheme.Modules.pullbackComp a.left f.left).hom.app H.line := by
  rw [component_hom, component_hom, yonedaHom_natural, underlying_naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.pullbackComp a.left f.left).hom.naturality j.anchor.val.hom
  erw [← hn]
  rfl

end TautologicalSquarePullbackR0199

/-- The tautological square line pulls back to the specified line, naturally
on every test, for any anchored strong classifying transformation. -/
theorem tautological_square_pullback
    (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (P : ArithmeticThetaRootStackR0198.Presentation B W)
    (Y : CategoryTheory.Over B)
    (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left
      ((AlgebraicGeometry.Scheme.Modules.pullback Y.hom).obj W))
    (j : ClassifiedMap P Y H) : Nonempty (TautologicalComparison j) :=
  ⟨{ component := TautologicalSquarePullbackR0199.component j,
      natural := TautologicalSquarePullbackR0199.component_natural j }⟩

end ArithmeticThetaStackLevelR0199

#print axioms ArithmeticThetaStackLevelR0199.tautological_square_pullback
