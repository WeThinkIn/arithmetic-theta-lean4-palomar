module

public import StackLevelDefinitionsR0199

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaStackLevelR0199
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRootStackR0198 ArithmeticThetaSquareLinesR0192
open Bicategory
attribute [local instance] CategoryTheory.uliftCategory

namespace RootClassifyingMapR0199
variable {B : Scheme.{0}} (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0,1})
  (Y : Over B) (x : F.obj (.mk (.op Y)))

/-- Evaluation of pullback at a fixed object. -/
def component (S : Over B) : Points S Y ⥤ F.obj (.mk (.op S)) :=
  ULift.downFunctor ⋙ Discrete.functor (fun f : S ⟶ Y =>
    (F.map f.op.toLoc).toFunctor.obj x)

/-- The comparison is precisely the pseudofunctor's composition isomorphism. -/
def comparison {S T : Over B} (a : S ⟶ T) :
    precompose Y a ⋙ component F Y x S ≅
      component F Y x T ⋙ (F.map a.op.toLoc).toFunctor :=
  NatIso.ofComponents (fun f => (Cat.Hom.toNatIso
    (F.mapComp f.down.as.op.toLoc a.op.toLoc)).app x)
    (fun {f g} e => by
      have h : f = g := ULift.ext (Discrete.ext (Discrete.eq_of_hom e))
      subst g
      have he : e = 𝟙 f := by exact congrArg Discrete.Hom.mk rfl
      subst e
      simp)

/-- The categorical Yoneda construction, retaining its unit and composition laws. -/
def classify : Pseudofunctor.StrongTrans (representable Y) F where
  app S := (component F Y x S.as.unop).toCatHom
  naturality a := Cat.Hom.isoMk (comparison F Y x a.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext f
    have h := congrArg (fun η => η.toNatTrans.app x)
      (F.map₂_right_unitor f.down.as.op.toLoc)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
      Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
      Cat.eqToHom_app, eqToIso.hom, eqToHom_refl, Category.comp_id] at h
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, comparison,
      Cat.Hom.isoMk_hom, NatIso.ofComponents_hom_app, Cat.Hom.toNatIso_hom,
      NatTrans.toCatHom₂_toNatTrans, Iso.app_hom, representable,
      Functor.toPseudofunctor'_mapId, eqToIso.hom, Cat.eqToHom_app,
      eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id]
    simp only [F.map₂_id, Cat.Hom₂.id_app, Functor.map_id, Category.id_comp] at h ⊢
    exact h.symm
  naturality_comp a b := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext f
    have h := congrArg (fun η => η.toNatTrans.app x)
      (F.mapComp_assoc_right_hom f.down.as.op.toLoc a b)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Strict.associator_eqToIso, eqToIso.inv,
      PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app, eqToIso.hom, eqToHom_refl, Category.comp_id] at h
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app, comparison,
      Cat.Hom.isoMk_hom, NatIso.ofComponents_hom_app, Cat.Hom.toNatIso_hom,
      NatTrans.toCatHom₂_toNatTrans, Iso.app_hom, representable,
      Functor.toPseudofunctor'_mapComp, eqToIso.hom, Cat.eqToHom_app,
      eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp]
    simp only [F.map₂_id, Cat.Hom₂.id_app, Functor.map_id, Category.id_comp] at h ⊢
    change _ = (component F Y x _).map (𝟙 _) ≫ _
    rw [(component F Y x _).map_id, Category.id_comp]
    exact h

end RootClassifyingMapR0199

/-- Every specified square line defines a strong classifying map to every root presentation. -/
theorem root_classifying_map (B : Scheme.{0}) (W : B.Modules) (P : Presentation B W)
    (Y : Over B) (H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)) :
    Nonempty (ClassifiedMap P Y H) := by
  obtain ⟨x, ⟨e⟩⟩ := P.essentially_surjective Y H
  refine ⟨⟨RootClassifyingMapR0199.classify P.functor Y x, ?_⟩⟩
  exact RootModuliPseudofunctorR0198.trans
    (P.homEquiv Y _ x ((P.functor.mapId (.mk (.op Y))).hom.toNatTrans.app x)) e

#print axioms root_classifying_map
end ArithmeticThetaStackLevelR0199
