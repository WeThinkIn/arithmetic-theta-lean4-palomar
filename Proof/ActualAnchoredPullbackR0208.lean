module

public import ActualLevelDefinitionsR0208

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaActualLevelR0208
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaStackLevelR0199
attribute [local instance] CategoryTheory.uliftCategory

namespace ActualAnchoredPullbackProof
variable {k : Type} [Field k] [CharZero k] {L : ℕ}
  {C : Coherence L (Base k)} {Y : Over (Base k)}
  {X : (group L Y.left).Objects} (j : AnchoredMap C Y X)

/-- The representable identity point, transported along its right unit law. -/
def pointId {S : Over (Base k)} (f : S ⟶ Y) :
    point f ≅ (precompose Y f).obj (point (𝟙 Y)) :=
  eqToIso (by change point f = point (f ≫ 𝟙 Y); rw [Category.comp_id])

/-- Evaluate strong naturality at the identity and then pull back the anchor.
Every factor is an isomorphism in the actual family/root groupoid. -/
def component (S : Over (Base k)) (f : S ⟶ Y) :
    (j.map.app (.mk (.op S))).toFunctor.obj (point f) ≅ (pull L f.left).functor.obj X :=
  (j.map.app (.mk (.op S))).toFunctor.mapIso (pointId f) ≪≫
    (Cat.Hom.toNatIso (j.map.naturality f.op.toLoc)).app (point (𝟙 Y)) ≪≫
    (pull L f.left).functor.mapIso j.anchor

def yonedaHom {S : Over (Base k)} (f : S ⟶ Y) :=
  (j.map.app (.mk (.op S))).toFunctor.map (pointId f).hom ≫
    (j.map.naturality f.op.toLoc).hom.toNatTrans.app (point (𝟙 Y))

lemma component_hom (S : Over (Base k)) (f : S ⟶ Y) :
    (component j S f).hom = yonedaHom j f ≫ (pull L f.left).functor.map j.anchor.hom := by
  simp only [component, yonedaHom, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Cat.Hom.toNatIso_hom, Category.assoc]

lemma yonedaHom_natural {S T : Over (Base k)} (a : T ⟶ S) (f : S ⟶ Y) :
    yonedaHom j (a ≫ f) ≫
      (Cat.Hom.toNatIso (C.comp f.op a.op)).hom.app
        ((j.map.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y))) =
    (j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f) ≫
      (pull L a.left).functor.map (yonedaHom j f) := by
  have h := congrArg (fun z => z.toNatTrans.app (point (𝟙 Y)))
    (j.map.naturality_comp f.op.toLoc a.op.toLoc)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app] at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  have hp : (pointId (a ≫ f)).hom ≫
      ((representable Y).mapComp f.op.toLoc a.op.toLoc).hom.toNatTrans.app
        (point (𝟙 Y)) = (precompose Y a).map (pointId f).hom := by
    apply ULift.ext
    apply Subsingleton.elim
  have hn := ((j.map.naturality a.op.toLoc).hom.toNatTrans).naturality (pointId f).hom
  dsimp only [yonedaHom]
  rw [Category.assoc]
  erw [h]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, hp]
  erw [hn]
  simp only [Category.assoc, Functor.map_comp]
  rfl

lemma component_natural (S T : Over (Base k)) (a : T ⟶ S) (f : S ⟶ Y) :
    (component j T (a ≫ f)).hom ≫
      (Cat.Hom.toNatIso (C.comp f.op a.op)).hom.app X =
    (j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f) ≫
      (pull L a.left).functor.map (component j S f).hom := by
  rw [component_hom, component_hom, Category.assoc]
  have hn := (Cat.Hom.toNatIso (C.comp f.op a.op)).hom.naturality j.anchor.hom
  erw [hn]
  rw [← Category.assoc, yonedaHom_natural]
  simp only [Category.assoc, Functor.map_comp]
  rfl

lemma component_identity : (component j Y (𝟙 Y)).hom ≫
    (Cat.Hom.toNatIso (C.unit (.op Y))).hom.app X = j.anchor.hom := by
  have h := congrArg (fun z => z.toNatTrans.app (point (𝟙 Y)))
    (j.map.naturality_id (.mk (.op Y)))
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app] at h
  rw [component_hom, Category.assoc]
  have hn := (Cat.Hom.toNatIso (C.unit (.op Y))).hom.naturality j.anchor.hom
  erw [hn]
  dsimp only [yonedaHom]
  simp only [Category.assoc]
  have hh := congrArg (fun z =>
    (j.map.app (.mk (.op Y))).toFunctor.map (pointId (𝟙 Y)).hom ≫ z ≫ j.anchor.hom) h
  simp [pointId, representable, Category.assoc, ← Functor.map_comp] at hh
  erw [Category.id_comp] at hh
  simpa [pointId, Category.assoc, Coherence.functor] using hh

end ActualAnchoredPullbackProof

/-- Anchored normalization on every test, with actual arrows and both coherence laws. -/
theorem actual_anchored_pullback
    (k : Type) [Field k] [CharZero k] (L : ℕ)
    (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (group L Y.left).Objects) (j : AnchoredMap C Y X) :
    Nonempty (PullbackComparison j) :=
  ⟨{ component := ActualAnchoredPullbackProof.component j,
       identity := ActualAnchoredPullbackProof.component_identity j,
       natural := ActualAnchoredPullbackProof.component_natural j }⟩

end ArithmeticThetaActualLevelR0208
#print axioms ArithmeticThetaActualLevelR0208.actual_anchored_pullback
