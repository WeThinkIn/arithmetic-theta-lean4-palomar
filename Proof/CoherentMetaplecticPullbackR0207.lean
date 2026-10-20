module

public import GeometricPullbackUnitR0207
public import GeometricPullbackCompositionR0207

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticStackR0207
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open ArithmeticThetaMetaplecticComparisonR0206

namespace CoherentPullbackProof
variable (L : ℕ)
local instance (S : Scheme.{0}) : Groupoid (Object L S) := (group L S).groupoid

def unit (S : Scheme.{0}) : (pull L (𝟙 S)).functor ≅ 𝟭 (group L S).Objects :=
  Classical.choose (geometric_pullback_unit L S (group L S) (pull L (𝟙 S)))

lemma unit_normalized (S : Scheme.{0}) : UnitNormalized (pull L (𝟙 S)) (unit L S) :=
  (Classical.choose_spec (geometric_pullback_unit L S (group L S) (pull L (𝟙 S)))).1

def comp {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T) :
    (pull L (b ≫ a)).functor ≅ (pull L a).functor ⋙ (pull L b).functor :=
  Classical.choose (geometric_pullback_composition L S T U
    (group L S) (group L T) (group L U) a b (pull L a) (pull L b) (pull L (b ≫ a)))

lemma comp_normalized {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T) :
    CompNormalized (pull L a) (pull L b) (pull L (b ≫ a)) (comp L a b) :=
  (Classical.choose_spec (geometric_pullback_composition L S T U
    (group L S) (group L T) (group L U) a b (pull L a) (pull L b) (pull L (b ≫ a)))).1

@[reassoc] lemma comp_curve {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T)
    (X : (group L S).Objects) :
    ((group L U).arrow _ _ ((comp L a b).hom.app X)).curve.hom ≫
      (pull L b).curve ((pull L a).functor.obj X) ≫ (pull L a).curve X =
      (pull L (b ≫ a)).curve X := (comp_normalized L a b X).1

@[reassoc] lemma comp_inv_curve {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T)
    (X : (group L S).Objects) :
    ((group L U).arrow _ _ ((comp L a b).inv.app X)).curve.hom ≫
      (pull L (b ≫ a)).curve X =
      (pull L b).curve ((pull L a).functor.obj X) ≫ (pull L a).curve X := by
  rw [← comp_curve L a b X, ← Category.assoc]
  have h := congrArg (fun q => ((group L U).arrow _ _ q).curve.hom)
    ((comp L a b).inv_hom_id_app X)
  rw [(group L U).curve_comp, (group L U).curve_id] at h
  rw [h, Category.id_comp]

@[reassoc] lemma unit_curve {S : Scheme.{0}} (X : (group L S).Objects) :
    ((group L S).arrow _ _ ((unit L S).hom.app X)).curve.hom =
      (pull L (𝟙 S)).curve X := (unit_normalized L S X).1

lemma map_line {S T : Scheme.{0}} (a : T ⟶ S)
    {X Y : (group L S).Objects} (f : X ⟶ Y) :
    ((group L T).arrow _ _ ((pull L a).functor.map f)).line.hom =
      ((pull L a).line X).hom ≫
      (Scheme.Modules.pullback a).map ((group L S).arrow _ _ f).line.hom ≫
      ((pull L a).line Y).inv := by
  apply (cancel_mono ((pull L a).line Y).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (pull L a).line_natural X Y f

lemma comp_line {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T)
    (X : (group L S).Objects) :
    ((group L U).arrow _ _ ((comp L a b).hom.app X)).line.hom =
      ((pull L (b ≫ a)).line X).hom ≫
      (Scheme.Modules.pullbackComp b a).inv.app X.root.line ≫
      (Scheme.Modules.pullback b).map ((pull L a).line X).inv ≫
      ((pull L b).line ((pull L a).functor.obj X)).inv := by
  apply (cancel_mono (((pull L b).line ((pull L a).functor.obj X)).hom ≫
    (Scheme.Modules.pullback b).map ((pull L a).line X).hom)).mp
  simpa [Category.assoc, ← Functor.map_comp] using (comp_normalized L a b X).2

lemma comp_inv_line {S T U : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T)
    (X : (group L S).Objects) :
    ((group L U).arrow _ _ ((comp L a b).inv.app X)).line.hom =
      ((pull L b).line ((pull L a).functor.obj X)).hom ≫
      (Scheme.Modules.pullback b).map ((pull L a).line X).hom ≫
      (Scheme.Modules.pullbackComp b a).hom.app X.root.line ≫
      ((pull L (b ≫ a)).line X).inv := by
  have h := congrArg (fun q => ((group L U).arrow _ _ q).line.hom)
    ((comp L a b).hom_inv_id_app X)
  rw [(group L U).line_comp, (group L U).line_id] at h
  apply (cancel_epi (((group L U).arrow _ _ ((comp L a b).hom.app X)).line.hom)).mp
  rw [h, comp_line]
  simp [Category.assoc, ← Functor.map_comp]

lemma unit_line {S : Scheme.{0}} (X : (group L S).Objects) :
    ((group L S).arrow _ _ ((unit L S).hom.app X)).line.hom =
      ((pull L (𝟙 S)).line X).hom ≫ (Scheme.Modules.pullbackId S).hom.app X.root.line :=
  (unit_normalized L S X).2

@[reassoc] lemma transport_curve {S T : Scheme.{0}} {a b : T ⟶ S} (h : a = b)
    (X : (group L S).Objects) :
    ((group L T).arrow _ _ (eqToHom (congrArg (fun q => (pull L q).functor.obj X) h))).curve.hom ≫
      (pull L b).curve X = (pull L a).curve X := by
  subst b
  simp only [eqToHom_refl, (group L T).curve_id, Category.id_comp]

lemma transport_line {S T : Scheme.{0}} {a b : T ⟶ S} (h : a = b)
    (X : (group L S).Objects) :
    ((group L T).arrow _ _ (eqToHom (congrArg (fun q => (pull L q).functor.obj X) h))).line.hom =
      ((pull L a).line X).hom ≫
      eqToHom (congrArg (fun q => (Scheme.Modules.pullback q).obj X.root.line) h) ≫
      ((pull L b).line X).inv := by
  subst b
  simp only [eqToHom_refl, (group L T).line_id, Category.id_comp, Iso.hom_inv_id]

/-- Cartesian uniqueness controls the curve; the specified line controls the root arrow. -/
lemma arrow_ext_pull {S T : Scheme.{0}} (a : T ⟶ S)
    (X : (group L S).Objects) {Y : (group L T).Objects}
    (f g : Y ⟶ (pull L a).functor.obj X)
    (hc : ((group L T).arrow _ _ f).curve.hom ≫ (pull L a).curve X =
      ((group L T).arrow _ _ g).curve.hom ≫ (pull L a).curve X)
    (hl : ((group L T).arrow _ _ f).line.hom = ((group L T).arrow _ _ g).line.hom) :
    f = g := by
  apply ((group L T).arrow _ _).injective
  apply ActualGroupoidProof.arrow_ext
  · apply ((pull L a).marked X).1.hom_ext
    · exact hc
    · exact ((group L T).arrow _ _ f).marked.1.w.trans
        ((group L T).arrow _ _ g).marked.1.w.symm
  · exact hl

lemma left_triangle {S T : Scheme.{0}} (a : T ⟶ S) (X : (group L S).Objects) :
    (comp L (𝟙 S) a).hom.app X ≫ (pull L a).functor.map ((unit L S).hom.app X) =
      eqToHom (congrArg (fun q => (pull L q).functor.obj X) (Category.comp_id a)) := by
  apply arrow_ext_pull L a X
  · simp only [(group L T).curve_comp, Category.assoc, transport_curve]
    erw [(pull L a).curve_natural, unit_curve, comp_curve,
      transport_curve L (Category.comp_id a) X]
  · rw [(group L T).line_comp, comp_line]
    erw [map_line L a ((unit L S).hom.app X), unit_line L X,
      transport_line L (Category.comp_id a) X]
    simp only [Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.comp_obj, Functor.id_obj, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    have h := congrArg (fun q => q.app X.root.line)
      (Scheme.Modules.pseudofunctor_left_unitality a)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Functor.id_obj, eqToHom_refl, Category.comp_id] at h
    rw [reassoc_of% h]
    rfl

lemma right_triangle {S T : Scheme.{0}} (a : T ⟶ S) (X : (group L S).Objects) :
    (comp L a (𝟙 T)).hom.app X ≫ (unit L T).hom.app ((pull L a).functor.obj X) =
      eqToHom (congrArg (fun q => (pull L q).functor.obj X) (Category.id_comp a)) := by
  apply arrow_ext_pull L a X
  · rw [(group L T).curve_comp]
    erw [unit_curve L ((pull L a).functor.obj X)]
    rw [Category.assoc, comp_curve]
    erw [transport_curve L (Category.id_comp a) X]
  · rw [(group L T).line_comp, comp_line]
    erw [unit_line L ((pull L a).functor.obj X), transport_line L (Category.id_comp a) X]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [(Scheme.Modules.pullbackId T).hom.naturality]
    simp only [Functor.id_map]
    have h := congrArg (fun q => q.app X.root.line)
      (Scheme.Modules.pseudofunctor_right_unitality a)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, eqToHom_app, Functor.id_obj, Category.comp_id] at h
    rw [reassoc_of% h]

lemma pentagon {S T U V : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ T) (c : V ⟶ U)
    (X : (group L S).Objects) :
    (comp L (b ≫ a) c).hom.app X ≫
      (pull L c).functor.map ((comp L a b).hom.app X) ≫
      (comp L b c).inv.app ((pull L a).functor.obj X) ≫
      (comp L a (c ≫ b)).inv.app X =
      eqToHom (congrArg (fun q => (pull L q).functor.obj X) (Category.assoc c b a).symm) := by
  apply arrow_ext_pull L ((c ≫ b) ≫ a) X
  · simp only [(group L V).curve_comp, Category.assoc]
    erw [comp_inv_curve L a (c ≫ b) X,
      comp_inv_curve_assoc L b c ((pull L a).functor.obj X)]
    erw [reassoc_of% ((pull L c).curve_natural _ _ ((comp L a b).hom.app X))]
    erw [comp_curve L a b X, comp_curve L (b ≫ a) c X]
    erw [transport_curve L (Category.assoc c b a).symm X]
  · simp only [(group L V).line_comp]
    erw [comp_line L (b ≫ a) c X,
      map_line L c ((comp L a b).hom.app X),
      comp_inv_line L b c ((pull L a).functor.obj X),
      comp_inv_line L a (c ≫ b) X,
      comp_line L a b X,
      transport_line L (Category.assoc c b a).symm X]
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.comp_obj, Functor.id_obj, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Functor.map_id, Category.id_comp]
    erw [(Scheme.Modules.pullback c).map_id]
    rw [Category.id_comp]
    erw [reassoc_of% ((Scheme.Modules.pullbackComp c b).hom.naturality
      ((pull L a).line X).inv)]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    erw [(Scheme.Modules.pullback (c ≫ b)).map_id]
    rw [Category.id_comp]
    have h := congrArg (fun q => q.app X.root.line)
      (Scheme.Modules.pseudofunctor_associativity c b a)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id, eqToHom_app,
      eqToHom_refl] at h
    rw [reassoc_of% h]
    rfl

/-- Package the geometric component identities as genuine Cat coherence laws. -/
def coherence (B : Scheme.{0}) : Coherence L B where
  unit S := Cat.Hom.isoMk (unit L S.unop.left)
  comp f g := Cat.Hom.isoMk (comp L f.unop.left g.unop.left)
  unit_normalized S := unit_normalized L S.left
  comp_normalized S T U a b := comp_normalized L a.left b.left
  associativity f g h := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Cat.eqToHom_app]
    change (comp L (g.unop.left ≫ f.unop.left) h.unop.left).hom.app X ≫
      (pull L h.unop.left).functor.map ((comp L f.unop.left g.unop.left).hom.app X) ≫
      𝟙 _ ≫ (comp L g.unop.left h.unop.left).inv.app ((pull L f.unop.left).functor.obj X) ≫
      (comp L f.unop.left (h.unop.left ≫ g.unop.left)).inv.app X = _
    rw [Category.id_comp]
    exact pentagon L f.unop.left g.unop.left h.unop.left X
  left_unit f := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
      Cat.eqToHom_app]
    change (comp L (𝟙 _) f.unop.left).hom.app X ≫
      (pull L f.unop.left).functor.map ((unit L _).hom.app X) ≫ 𝟙 _ = _
    erw [Category.comp_id ((pull L f.unop.left).functor.map ((unit L _).hom.app X))]
    exact left_triangle L f.unop.left X
  right_unit f := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
      Cat.eqToHom_app]
    change (comp L f.unop.left (𝟙 _)).hom.app X ≫
      (unit L _).hom.app ((pull L f.unop.left).functor.obj X) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact right_triangle L f.unop.left X

end CoherentPullbackProof

/-- Actual marked elliptic families with specified cotangent roots have coherent
pullback on every slice of small schemes, at every natural level. -/
theorem coherent_metaplectic_pullback :
    ∀ (L : ℕ) (B : AlgebraicGeometry.Scheme.{0}),
      Nonempty (ArithmeticThetaMetaplecticStackR0207.Coherence L B) := by
  intro L B
  exact ⟨CoherentPullbackProof.coherence L B⟩

#print axioms coherent_metaplectic_pullback
end ArithmeticThetaMetaplecticStackR0207
