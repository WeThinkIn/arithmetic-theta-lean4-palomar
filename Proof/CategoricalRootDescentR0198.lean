module

public import RootStackDefinitionsR0198

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe v
namespace ArithmeticThetaRootStackR0198
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
namespace CategoricalRootDescentR0198

variable {B : Scheme.{0}} {W : B.Modules} (P : Presentation B W)

lemma forget_faithful (T : Over B) :
    (P.forget.app (.mk (.op T))).toFunctor.Faithful where
  map_injective {x y} a b h := by
    apply (P.homEquiv T x y).injective
    apply Subtype.ext
    apply Iso.ext
    simpa only [P.hom_eq] using h

lemma map_square (T : Over B) {x y : P.functor.obj (.mk (.op T))} (a : x ⟶ y) :
    tensorPowerMap ((P.forget.app (.mk (.op T))).toFunctor.map a) 2 ≫
      (P.square T y).hom = (P.square T x).hom := by
  have h := (P.homEquiv T x y a).property
  change tensorPowerMap _ 2 ≫ (P.square T y).hom = (P.square T x).hom at h
  rw [P.hom_eq] at h
  exact h

/-- Lift an actual square-compatible sheaf isomorphism through the presentation. -/
def liftIso (T : Over B) {x y : P.functor.obj (.mk (.op T))}
    (e : SquareIso (root P.toRootDiagram T x) (root P.toRootDiagram T y)) : x ≅ y := by
  letI := P.groupoid T
  exact asIso ((P.homEquiv T x y).symm e)

@[simp] lemma liftIso_hom (T : Over B) {x y : P.functor.obj (.mk (.op T))}
    (e : SquareIso (root P.toRootDiagram T x) (root P.toRootDiagram T y)) :
    (P.forget.app (.mk (.op T))).toFunctor.map (liftIso P T e).hom = e.val.hom := by
  rw [← P.hom_eq]
  simp [liftIso]

section Strong
universe u₀ v₀ u₁ v₁ u₂ v₂
variable {C : Type u₀} [Category.{v₀} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁,u₁}}
  {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁,u₁}}
  (η : Pseudofunctor.StrongTrans F G)
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- Transport a transition using the same strong comparison on its two ends. -/
def transition {X Y S : C} (a : S ⟶ X) (b : S ⟶ Y)
    {x : F.obj (.mk (.op X))} {y : F.obj (.mk (.op Y))}
    (t : (F.map a.op.toLoc).toFunctor.obj x ⟶ (F.map b.op.toLoc).toFunctor.obj y) :
    (G.map a.op.toLoc).toFunctor.obj ((η.app (.mk (.op X))).toFunctor.obj x) ⟶
      (G.map b.op.toLoc).toFunctor.obj ((η.app (.mk (.op Y))).toFunctor.obj y) :=
  (η.naturality a.op.toLoc).inv.toNatTrans.app x ≫
    (η.app (.mk (.op S))).toFunctor.map t ≫
    (η.naturality b.op.toLoc).hom.toNatTrans.app y

lemma transition_id {X S : C} (a : S ⟶ X) (x : F.obj (.mk (.op X))) :
    transition η a a (𝟙 ((F.map a.op.toLoc).toFunctor.obj x)) = 𝟙 _ := by
  simp [transition, ← Cat.Hom₂.comp_app]

lemma transition_comp {X Y Z S : C} (a : S ⟶ X) (b : S ⟶ Y) (c : S ⟶ Z)
    {x : F.obj (.mk (.op X))} {y : F.obj (.mk (.op Y))} {z : F.obj (.mk (.op Z))}
    (s : (F.map a.op.toLoc).toFunctor.obj x ⟶ (F.map b.op.toLoc).toFunctor.obj y)
    (t : (F.map b.op.toLoc).toFunctor.obj y ⟶ (F.map c.op.toLoc).toFunctor.obj z) :
    transition η a b s ≫ transition η b c t = transition η a c (s ≫ t) := by
  simp [transition, Category.assoc, ← Cat.Hom₂.comp_app, ← reassoc_of% Cat.Hom₂.comp_app]

lemma comparison_comp_hom {X Y Z : C} (a : Y ⟶ X) (g : Z ⟶ Y)
    (x : F.obj (.mk (.op X))) :
    (η.naturality (a.op.toLoc ≫ g.op.toLoc)).hom.toNatTrans.app x ≫
      (G.mapComp a.op.toLoc g.op.toLoc).hom.toNatTrans.app _ =
    (η.app (.mk (.op Z))).toFunctor.map
      ((F.mapComp a.op.toLoc g.op.toLoc).hom.toNatTrans.app x) ≫
      (η.naturality g.op.toLoc).hom.toNatTrans.app _ ≫
      (G.map g.op.toLoc).toFunctor.map ((η.naturality a.op.toLoc).hom.toNatTrans.app x) := by
  have h := congrArg (fun t => t.toNatTrans.app x) (η.naturality_comp a.op.toLoc g.op.toLoc)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app, Category.comp_id,
    Category.id_comp, Category.assoc, Cat.Hom.comp_toFunctor, Functor.comp_obj, eqToHom_refl] using h

lemma transition_pull {X Y S S' : C} (a : S ⟶ X) (b : S ⟶ Y) (g : S' ⟶ S)
    {x : F.obj (.mk (.op X))} {y : F.obj (.mk (.op Y))}
    (t : (F.map a.op.toLoc).toFunctor.obj x ⟶ (F.map b.op.toLoc).toFunctor.obj y)
    (ga : S' ⟶ X) (gb : S' ⟶ Y) (ha : g ≫ a = ga) (hb : g ≫ b = gb) :
    pullHom (transition η a b t) g ga gb ha hb =
      transition η ga gb (pullHom t g ga gb ha hb) := by
  subst ga gb
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  dsimp [transition]
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi ((η.naturality (a.op.toLoc ≫ g.op.toLoc)).hom.toNatTrans.app x)).1
  simp only [← Category.assoc]
  rw [comparison_comp_hom]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app]
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  erw [(G.map g.op.toLoc).toFunctor.map_id]
  simp only [Category.id_comp]
  have ht := (η.naturality g.op.toLoc).hom.toNatTrans.naturality t
  change (η.app (.mk (.op S'))).toFunctor.map ((F.map g.op.toLoc).toFunctor.map t) ≫ _ =
    _ ≫ (G.map g.op.toLoc).toFunctor.map ((η.app (.mk (.op S))).toFunctor.map t) at ht
  rw [← reassoc_of% ht]
  congr 1
  congr 1
  apply (cancel_mono ((G.mapComp b.op.toLoc g.op.toLoc).hom.toNatTrans.app _)).1
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id]
  rw [comparison_comp_hom]
  simp only [← Category.assoc, ← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app,
    Functor.map_id, Category.id_comp]

  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  simp

/-- The functor on full all-test descent data induced by a strong transformation. -/
def strongData {T : C} {ι : Type v} {V : ι → C} (f : ∀ i, V i ⟶ T) :
    F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj := fun i => (η.app (.mk (.op (V i)))).toFunctor.obj (D.obj i)
      hom := fun {_} p {_ _} a b ha hb => transition η a b (D.hom p a b ha hb)
      pullHom_hom := by
        intro S' S g p p' hp i j a b ha hb ga gb hga hgb
        rw [transition_pull, D.pullHom_hom g p p' hp a b ha hb ga gb hga hgb]
      hom_self := by
        intro S p i a ha
        rw [D.hom_self p a ha, transition_id]
      hom_comp := by
        intro S p i j k a b c ha hb hc
        rw [transition_comp, D.hom_comp p a b c ha hb hc] }
  map φ :=
    { hom := fun i => (η.app (.mk (.op (V i)))).toFunctor.map (φ.hom i)
      comm := by
        intro S p i j a b ha hb
        dsimp [transition]
        have h := congrArg ((η.app (.mk (.op S))).toFunctor.map) (φ.comm p a b ha hb)
        simp only [Functor.map_comp] at h
        have ha' := (η.naturality a.op.toLoc).inv.toNatTrans.naturality (φ.hom i)
        have hb' := (η.naturality b.op.toLoc).hom.toNatTrans.naturality (φ.hom j)
        dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at ha' hb'
        simp only [Category.assoc]
        rw [reassoc_of% ha', reassoc_of% h, hb'] }
  map_id D := by ext i; exact (η.app (.mk (.op (V i)))).toFunctor.map_id _
  map_comp φ ψ := by ext i; exact (η.app (.mk (.op (V i)))).toFunctor.map_comp _ _

lemma comparison_comp'_hom {X Y Z : C} (f : Y ⟶ X) (a : Z ⟶ Y)
    (p : Z ⟶ X) (h : a ≫ f = p) (x : F.obj (.mk (.op X))) :
    (η.naturality p.op.toLoc).hom.toNatTrans.app x ≫
      (G.mapComp' f.op.toLoc a.op.toLoc p.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app _ =
    (η.app (.mk (.op Z))).toFunctor.map
      ((F.mapComp' f.op.toLoc a.op.toLoc p.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app x) ≫
      (η.naturality a.op.toLoc).hom.toNatTrans.app _ ≫
      (G.map a.op.toLoc).toFunctor.map ((η.naturality f.op.toLoc).hom.toNatTrans.app x) := by
  subst p
  simpa [Pseudofunctor.mapComp'] using comparison_comp_hom η f a x

/-- The same strong comparisons identify the two canonical descent data. -/
def strongCanonicalIso {T : C} {ι : Type v} {V : ι → C} (f : ∀ i, V i ⟶ T)
    (x : F.obj (.mk (.op T))) :
    (strongData η f).obj ((F.toDescentData f).obj x) ≅
      (G.toDescentData f).obj ((η.app (.mk (.op T))).toFunctor.obj x) :=
  Pseudofunctor.DescentData.isoMk
    (fun i => (Cat.Hom.toNatIso (η.naturality (f i).op.toLoc)).app x) (by
      intro S p i j a b ha hb
      change (G.map a.op.toLoc).toFunctor.map ((η.naturality (f i).op.toLoc).hom.toNatTrans.app x) ≫
        ((G.toDescentData f).obj _).hom p a b ha hb =
        transition η a b (((F.toDescentData f).obj x).hom p a b ha hb) ≫
          (G.map b.op.toLoc).toFunctor.map ((η.naturality (f j).op.toLoc).hom.toNatTrans.app x)
      let d := F.mapComp' (f i).op.toLoc a.op.toLoc p.op.toLoc (by rw [← ha]; rfl)
      apply (cancel_epi ((η.app (.mk (.op S))).toFunctor.map (d.hom.toNatTrans.app x) ≫
        (η.naturality a.op.toLoc).hom.toNatTrans.app _)).1
      dsimp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, transition, d]
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% (comparison_comp'_hom η (f i) a p ha x)]
      simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      rw [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app]
      dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
      erw [(η.app (.mk (.op S))).toFunctor.map_id]
      simp only [Category.id_comp]
      exact comparison_comp'_hom η (f j) b p hb x)

/-- Faithful fiber functors reflect the commutation of descent morphisms. -/
def liftStrongHom (hη : ∀ X : C, (η.app (.mk (.op X))).toFunctor.Faithful)
    {T : C} {ι : Type v} {V : ι → C} {f : ∀ i, V i ⟶ T}
    {D E : F.DescentData f}
    (φ : ∀ i, D.obj i ⟶ E.obj i)
    (ψ : (strongData η f).obj D ⟶ (strongData η f).obj E)
    (hφ : ∀ i, (η.app (.mk (.op (V i)))).toFunctor.map (φ i) = ψ.hom i) : D ⟶ E where
  hom := φ
  comm S p i j a b ha hb := by
    letI := hη S
    apply (η.app (.mk (.op S))).toFunctor.map_injective
    have h := ψ.comm p a b ha hb
    dsimp only [strongData, transition] at h
    rw [← hφ i, ← hφ j] at h
    have hn₁ := (η.naturality a.op.toLoc).inv.toNatTrans.naturality (φ i)
    have hn₂ := (η.naturality b.op.toLoc).hom.toNatTrans.naturality (φ j)
    dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn₁ hn₂
    simp only [Category.assoc] at h
    rw [reassoc_of% hn₁, ← hn₂] at h
    have h' := (cancel_epi ((η.naturality a.op.toLoc).inv.toNatTrans.app (D.obj i))).1 h
    simp only [← Category.assoc] at h'
    have h'' := (cancel_mono ((η.naturality b.op.toLoc).hom.toNatTrans.app (E.obj j))).1
      h'
    simpa only [Functor.map_comp] using h''

end Strong
open ArithmeticThetaRootDescentR0197
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- The test scheme with its structural map to the original base. -/
abbrev testOver {T : Over B} {S : Scheme.{0}} (p : S ⟶ T.left) : Over B :=
  Over.mk (p ≫ T.hom)

/-- Lift a leg of a test diagram to the slice, retaining the original map. -/
def testLeg {T V : Over B} (f : V ⟶ T) {S : Scheme.{0}}
    (p : S ⟶ T.left) (a : S ⟶ V.left) (ha : a ≫ f.left = p) :
    testOver p ⟶ V :=
  Over.homMk a (by dsimp [testOver]; rw [← ha, Category.assoc, Over.w f])

lemma testLeg_comp {T V : Over B} (f : V ⟶ T) {S : Scheme.{0}}
    (p : S ⟶ T.left) (a : S ⟶ V.left) (ha : a ≫ f.left = p) :
    testLeg f p a ha ≫ f = Over.homMk p rfl := by
  apply Over.OverMorphism.ext
  exact ha


section Precompose
universe u₀ v₀ u₁ v₁ u₂ v₂
variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
  (H : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v₂,u₂})
lemma precompose_comp_hom {X Y Z : C} (f : Y ⟶ X) (a : Z ⟶ Y) (p : Z ⟶ X)
    (h : a ≫ f = p) (x : F.obj (.mk (.op (H.obj X)))) :
    ((H.op.toPseudofunctor.comp F).mapComp' f.op.toLoc a.op.toLoc p.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app x =
    (F.mapComp' (H.map f).op.toLoc (H.map a).op.toLoc (H.map p).op.toLoc
      (by rw [← h, H.map_comp]; rfl)).hom.toNatTrans.app x := by
  subst p
  simp [Pseudofunctor.mapComp', Pseudofunctor.comp_mapComp,
    Functor.toPseudofunctor_mapComp]
  rfl
lemma precompose_comp_inv {X Y Z : C} (f : Y ⟶ X) (a : Z ⟶ Y) (p : Z ⟶ X)
    (h : a ≫ f = p) (x : F.obj (.mk (.op (H.obj X)))) :
    ((H.op.toPseudofunctor.comp F).mapComp' f.op.toLoc a.op.toLoc p.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app x =
    (F.mapComp' (H.map f).op.toLoc (H.map a).op.toLoc (H.map p).op.toLoc
      (by rw [← h, H.map_comp]; rfl)).inv.toNatTrans.app x := by
  subst p
  simp [Pseudofunctor.mapComp', Pseudofunctor.comp_mapComp,
    Functor.toPseudofunctor_mapComp]
  rfl
lemma precompose_transition {T S : C} {ι : Type*} {V : ι → C} (f : ∀ i, V i ⟶ T)
    (x : F.obj (.mk (.op (H.obj T)))) (p : S ⟶ T) {i j : ι}
    (a : S ⟶ V i) (b : S ⟶ V j) (ha : a ≫ f i = p) (hb : b ≫ f j = p) :
    (((H.op.toPseudofunctor.comp F).toDescentData f).obj x).hom p a b ha hb =
    ((F.toDescentData (fun i => H.map (f i))).obj x).hom (H.map p) (H.map a) (H.map b)
      (by rw [← H.map_comp, ha]) (by rw [← H.map_comp, hb]) := by
  change ((H.op.toPseudofunctor.comp F).mapComp' (f i).op.toLoc a.op.toLoc p.op.toLoc _).inv.toNatTrans.app x ≫
    ((H.op.toPseudofunctor.comp F).mapComp' (f j).op.toLoc b.op.toLoc p.op.toLoc _).hom.toNatTrans.app x = _
  rw [precompose_comp_inv H F (f i) a p ha, precompose_comp_hom H F (f j) b p hb]
  rfl

end Precompose
section GenericSlice
universe uₛ vₛ uₜ vₜ tₛ
variable {C : Type uₛ} [Category.{vₛ} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vₜ,uₜ}) {B : C}
abbrev overFunctor := (Over.forget B).op.toPseudofunctor.comp F
abbrev genericTest {T : Over B} {S : C} (p : S ⟶ T.left) : Over B := Over.mk (p ≫ T.hom)
def genericLeg {T V : Over B} (f : V ⟶ T) {S : C} (p : S ⟶ T.left)
    (a : S ⟶ V.left) (ha : a ≫ f.left = p) : genericTest p ⟶ V :=
  Over.homMk a (by dsimp [genericTest]; rw [← ha, Category.assoc, Over.w f])
lemma genericLeg_comp {T V : Over B} (f : V ⟶ T) {S : C} (p : S ⟶ T.left)
    (a : S ⟶ V.left) (ha : a ≫ f.left = p) :
    genericLeg f p a ha ≫ f = Over.homMk p rfl := by ext; exact ha

def genericUnslice {T : Over B} {ι : Type tₛ} {V : ι → Over B} (f : ∀ i, V i ⟶ T)
    (D : (overFunctor F).DescentData f) : F.DescentData (fun i => (f i).left) where
  obj i := D.obj i
  hom S p i j a b ha hb := D.hom (Over.homMk p rfl)
    (genericLeg (f i) p a ha) (genericLeg (f j) p b hb)
    (genericLeg_comp (f i) p a ha) (genericLeg_comp (f j) p b hb)
  hom_self S p i a ha := D.hom_self (Over.homMk p rfl) (genericLeg (f i) p a ha)
    (genericLeg_comp (f i) p a ha)
  hom_comp S p i j k a b c ha hb hc := D.hom_comp (Over.homMk p rfl)
    (genericLeg (f i) p a ha) (genericLeg (f j) p b hb) (genericLeg (f k) p c hc)
    (genericLeg_comp (f i) p a ha) (genericLeg_comp (f j) p b hb) (genericLeg_comp (f k) p c hc)
  pullHom_hom S' S g p p' hp i j a b ha hb ga gb hga hgb := by
    let g' : genericTest p' ⟶ genericTest p := Over.homMk g (by
      dsimp [genericTest]; rw [← Category.assoc, hp])
    have h := D.pullHom_hom g' (Over.homMk p rfl) (Over.homMk p' rfl)
      (by ext; exact hp)
      (genericLeg (f i) p a ha) (genericLeg (f j) p b hb)
      (genericLeg_comp (f i) p a ha) (genericLeg_comp (f j) p b hb)
      (genericLeg (f i) p' ga (by rw [← hga, Category.assoc, ha, hp]))
      (genericLeg (f j) p' gb (by rw [← hgb, Category.assoc, hb, hp]))
      (by ext; exact hga) (by ext; exact hgb)
    dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at h ⊢
    rw [precompose_comp_hom (Over.forget B) F _ _ _ (by ext; exact hga),
      precompose_comp_inv (Over.forget B) F _ _ _ (by ext; exact hgb)] at h
    exact h

def genericUnsliceCanonical {T : Over B} {ι : Type tₛ} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (M : F.obj (.mk (.op T.left))) :
    genericUnslice F f (((overFunctor F).toDescentData f).obj M) ≅
      (F.toDescentData (fun i => (f i).left)).obj M :=
  Pseudofunctor.DescentData.isoMk (fun i => Iso.refl _) (by
    intro S p i j a b ha hb
    simp only [Iso.refl_hom]
    rw [(F.map a.op.toLoc).toFunctor.map_id, (F.map b.op.toLoc).toFunctor.map_id,
      Category.id_comp, Category.comp_id]
    exact (precompose_transition (Over.forget B) F f M
      (Over.homMk (U := genericTest (T := T) p) (V := T) p rfl)
      (genericLeg (f i) p a ha) (genericLeg (f j) p b hb)
      (genericLeg_comp (f i) p a ha) (genericLeg_comp (f j) p b hb)).symm)

end GenericSlice
/-- Forget the slice using the generic construction with the actual module pseudofunctor. -/
abbrev unsliceData {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T)
    (D : (modulesOver B).DescentData f) := genericUnslice moduleFunctor f D

open OpenSquareRootEffectivityR0197

/-- Associativity with all structural-map equalities retained explicitly. -/
lemma compare_comp {S V T B : Scheme.{0}}
    (a : S ⟶ V) (f : V ⟶ T) (t : T ⟶ B)
    (p : S ⟶ T) (s : V ⟶ B) (r : S ⟶ B)
    (ha : a ≫ f = p) (hf : f ≫ t = s) (hp : p ≫ t = r)
    (hs : a ≫ s = r) (W : B.Modules) :
    (compare a f p ha ((Scheme.Modules.pullback t).obj W)).hom ≫
      (compare p t r hp W).hom =
    (Scheme.Modules.pullback a).map (compare f t s hf W).hom ≫
      (compare a s r hs W).hom := by
  subst p s r
  dsimp [OpenSquareRootEffectivityR0197.compare]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.app, Iso.trans_hom,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.map_comp]
  have h := RootTestPullbackCoherenceR0196.comp_assoc_reverse a f t W
  simpa [Scheme.Modules.pullbackCongr] using h

/-- An arbitrary categorical root datum gives the accepted concrete module datum. -/
def concreteDatum {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T)
    (D : P.functor.DescentData f) :
    RootDatum ((Scheme.Modules.pullback T.hom).obj W) (fun i => (f i).left) where
  data := unsliceData f ((strongData P.forget f).obj D)
  invertible i := P.invertible (V i) (D.obj i)
  square i := P.square (V i) (D.obj i) ≪≫
    (compare (f i).left T.hom (V i).hom (Over.w (f i)) W).symm

lemma concrete_square_test {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f)
    {S : Scheme.{0}} (p : S ⟶ T.left) (i : ι) (a : S ⟶ (V i).left)
    (ha : a ≫ (f i).left = p) :
    (squarePull a (localRoot (concreteDatum P f D) i)).hom ≫
      (compare a (f i).left p ha ((Scheme.Modules.pullback T.hom).obj W)).hom ≫
      (compare p T.hom (p ≫ T.hom) rfl W).hom =
    (squarePull a (root P.toRootDiagram (V i) (D.obj i))).hom ≫
      (compare a (V i).hom (p ≫ T.hom) (Over.w (testLeg (f i) p a ha)) W).hom := by
  have hc := compare_comp a (f i).left T.hom p (V i).hom (p ≫ T.hom)
    ha (Over.w (f i)) rfl (Over.w (testLeg (f i) p a ha)) W
  rw [hc]
  dsimp [squarePull, localRoot, concreteDatum, root]
  dsimp only [unsliceData, genericUnslice, strongData]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]

lemma concrete_square_natural {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f)
    {S : Scheme.{0}} (p : S ⟶ T.left) (i : ι) (a : S ⟶ (V i).left)
    (ha : a ≫ (f i).left = p) :
    tensorPowerMap ((P.forget.naturality (testLeg (f i) p a ha).op.toLoc).hom.toNatTrans.app (D.obj i)) 2 ≫
      (squarePull a (localRoot (concreteDatum P f D) i)).hom ≫
      (compare a (f i).left p ha ((Scheme.Modules.pullback T.hom).obj W)).hom ≫
      (compare p T.hom (p ≫ T.hom) rfl W).hom =
    (P.square (testOver p) ((P.functor.map (testLeg (f i) p a ha).op.toLoc).toFunctor.obj (D.obj i))).hom := by
  rw [concrete_square_test]
  exact P.square_natural (testOver p) (V i) (testLeg (f i) p a ha) (D.obj i)

lemma square_conjugate {S : Scheme.{0}} {A A' K K' R : S.Modules}
    (a : A ≅ A') (b : K ≅ K') (t : A ⟶ K)
    (sA : tensorPower S A 2 ⟶ R) (sK : tensorPower S K 2 ⟶ R)
    (sA' : tensorPower S A' 2 ⟶ R) (sK' : tensorPower S K' 2 ⟶ R)
    (ha : tensorPowerMap a.hom 2 ≫ sA' = sA)
    (hb : tensorPowerMap b.hom 2 ≫ sK' = sK)
    (ht : tensorPowerMap t 2 ≫ sK = sA) :
    tensorPowerMap (a.inv ≫ t ≫ b.hom) 2 ≫ sK' = sA' := by
  apply (cancel_epi (tensorPowerIso a 2).hom).1
  change tensorPowerMap a.hom 2 ≫ _ = tensorPowerMap a.hom 2 ≫ _
  simp only [tensorPowerMap_comp, Category.assoc]
  rw [hb, ht, ← ha, ← Category.assoc, ← tensorPowerMap_comp,
    a.hom_inv_id, tensorPowerMap_id, Category.id_comp]

/-- All-test square compatibility survives the same strong comparison. -/
lemma concrete_compatible {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f) :
    CompatibleSquares (concreteDatum P f D) := by
  intro S p i j a b ha hb
  let a' := testLeg (f i) p a ha
  let b' := testLeg (f j) p b hb
  let p' : testOver p ⟶ T := Over.homMk p rfl
  let ca := (Cat.Hom.toNatIso (P.forget.naturality a'.op.toLoc)).app (D.obj i)
  have hn₁ := concrete_square_natural P f D p i a ha
  have hn₂ := concrete_square_natural P f D p j b hb
  change tensorPowerMap (transition P.forget a' b'
      (D.hom p' a' b' (testLeg_comp (f i) p a ha) (testLeg_comp (f j) p b hb))) 2 ≫
      (squarePull b (localRoot (concreteDatum P f D) j)).hom ≫
      (compare b (f j).left p hb ((Scheme.Modules.pullback T.hom).obj W)).hom =
    (squarePull a (localRoot (concreteDatum P f D) i)).hom ≫
      (compare a (f i).left p ha ((Scheme.Modules.pullback T.hom).obj W)).hom
  apply (cancel_mono (compare p T.hom (p ≫ T.hom) rfl W).hom).1
  simp only [Category.assoc]
  exact square_conjugate ca
    ((Cat.Hom.toNatIso (P.forget.naturality b'.op.toLoc)).app (D.obj j))
    ((P.forget.app (.mk (.op (testOver p)))).toFunctor.map
      (D.hom p' a' b' (testLeg_comp (f i) p a ha) (testLeg_comp (f j) p b hb)))
    _ _ _ _ hn₁ hn₂ (map_square P (testOver p) _)

/-- Accepted fpqc effectivity applies to every categorical datum after comparison. -/
lemma concrete_effective_fpqc (hW : Scheme.Modules.IsInvertible W)
    (T V : Over B) (q : V ⟶ T) (hq : QuasiCompact q.left)
    (hf : Flat q.left) (hs : Surjective q.left)
    (D : P.functor.DescentData (fun _ : Unit => q)) :
    Effective (concreteDatum P (fun _ : Unit => q) D) :=
  (fpqc_square_root_descent T.left V.left q.left hq hf hs
    ((Scheme.Modules.pullback T.hom).obj W) (hW.pullback T.hom)).1
      _ (concrete_compatible P _ D)

/-- Accepted open-cover effectivity applies with an arbitrary index universe. -/
lemma concrete_effective_open (hW : Scheme.Modules.IsInvertible W)
    (T : Over B) (ι : Type v) (V : ι → Over B) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (f i).left)
    (hcover : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base)
    (D : P.functor.DescentData f) : Effective (concreteDatum P f D) :=
  open_square_root_effectivity T.left ι (fun i => (V i).left) (fun i => (f i).left)
    hf hcover ((Scheme.Modules.pullback T.hom).obj W) (hW.pullback T.hom)
    _ (concrete_compatible P f D)

lemma pull_square_iso {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Modules}
    (J K : SquareLine Y W) (e : SquareIso J K) :
    tensorPowerMap ((Scheme.Modules.pullback f).map e.val.hom) 2 ≫
      (squarePull f K).hom = (squarePull f J).hom := by
  dsimp [squarePull]
  rw [← Category.assoc, RootTestPullbackCoherenceR0196.power_natural_inv f J.invertible e.val.hom 2,
    Category.assoc, ← Functor.map_comp, e.property]

lemma square_chain_transport {S : Scheme.{0}} {A K L M U V : S.Modules}
    (c : A ≅ K) (d : K ≅ L) (e : L ≅ M) (b : U ≅ V)
    (sA : tensorPower S A 2 ⟶ V) (sK : tensorPower S K 2 ⟶ U)
    (sL : tensorPower S L 2 ⟶ U) (sM : tensorPower S M 2 ⟶ U)
    (hc : tensorPowerMap c.hom 2 ≫ sK ≫ b.hom = sA)
    (hd : tensorPowerMap d.hom 2 ≫ sL = sK)
    (he : tensorPowerMap e.hom 2 ≫ sM = sL) :
    tensorPowerMap (c ≪≫ d ≪≫ e).hom 2 ≫ (sM ≫ b.hom) = sA := by
  simp only [Iso.trans_hom, tensorPowerMap_comp, Category.assoc]
  rw [reassoc_of% he, reassoc_of% hd, hc]

/-- Local isomorphisms back in the original categorical presentation,
using the actual effective descent isomorphism and its specified squares. -/
def effectiveLocalIso {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f)
    (J : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W))
    (e : (descent (fun i => (f i).left)).obj J.line ≅ (concreteDatum P f D).data)
    (he : Realizes (concreteDatum P f D) J e)
    (x : P.functor.obj (.mk (.op T))) (k : SquareIso (root P.toRootDiagram T x) J)
    (i : ι) : (P.functor.map (f i).op.toLoc).toFunctor.obj x ≅ D.obj i := by
  let c := (Cat.Hom.toNatIso (P.forget.naturality (f i).op.toLoc)).app x
  let z := c ≪≫ (Scheme.Modules.pullback (f i).left).mapIso k.val ≪≫
    componentIso (concreteDatum P f D) e i
  apply liftIso P (V i) (x := (P.functor.map (f i).op.toLoc).toFunctor.obj x)
    (y := D.obj i) ⟨z, ?_⟩
  change tensorPowerMap z.hom 2 ≫ (P.square (V i) (D.obj i)).hom = _
  have hs : (P.square (V i) (D.obj i)).hom =
      ((concreteDatum P f D).square i).hom ≫
      (compare (f i).left T.hom (V i).hom (Over.w (f i)) W).hom := by
    simp [concreteDatum]
  rw [hs]
  exact square_chain_transport (S := (V i).left) c
    ((Scheme.Modules.pullback (f i).left).mapIso k.val)
    (componentIso (concreteDatum P f D) e i)
    (compare (f i).left T.hom (V i).hom (Over.w (f i)) W)
    _ _ _ _ (P.square_natural (V i) T (f i) x)
    (pull_square_iso (f i).left (root P.toRootDiagram T x) J k) (he i)

/-- Forgetting the slice on module descent data also preserves all arrows. -/
def unsliceFunctor {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T) :
    (modulesOver B).DescentData f ⥤ moduleFunctor.DescentData (fun i => (f i).left) where
  obj := unsliceData f
  map φ :=
    { hom := φ.hom
      comm := fun S p i j a b ha hb => φ.comm (Over.homMk (U := testOver (T := T) p) (V := T) p rfl)
        (testLeg (f i) p a ha) (testLeg (f j) p b hb)
        (testLeg_comp (f i) p a ha) (testLeg_comp (f j) p b hb) }

/-- Every underlying module-descent arrow is already compatible in the slice. -/
def liftUnsliceHom {T : Over B} {ι : Type v} {V : ι → Over B} {f : ∀ i, V i ⟶ T}
    {D E : (modulesOver B).DescentData f}
    (φ : unsliceData f D ⟶ unsliceData f E) : D ⟶ E where
  hom := φ.hom
  comm S p i j a b ha hb := by
    obtain ⟨S, s, rfl⟩ := CostructuredArrow.mk_surjective S
    rcases p with ⟨p, pr, pw⟩
    have hp : p ≫ T.hom = s := by simpa using pw
    dsimp at p pr pw hp
    subst s
    exact φ.comm p a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb)

def unsliceFullyFaithful {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T) :
    (unsliceFunctor f).FullyFaithful where
  preimage := liftUnsliceHom
  map_preimage := by intros; rfl
  preimage_map := by intros; rfl

def unsliceCanonical {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T)
    (M : T.left.Modules) :
    unsliceData f (((modulesOver B).toDescentData f).obj M) ≅
      (descent (fun i => (f i).left)).obj M :=
  genericUnsliceCanonical moduleFunctor f M

open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
lemma root_iso_descent_family {T : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    (f : ∀ i, V i ⟶ T)
    (hff : ∀ (M N : T.Modules), Scheme.Modules.IsInvertible M →
      Scheme.Modules.IsInvertible N → Function.Bijective ((descent f).map : (M ⟶ N) → _))
    (W : T.Modules) (hW : Scheme.Modules.IsInvertible W) : RootIsoDescent W f := by
  intro J K e he
  obtain ⟨a, ha⟩ := (hff J.line K.line J.invertible K.invertible).2 e.hom
  obtain ⟨b, hb⟩ := (hff K.line J.line K.invertible J.invertible).2 e.inv
  have hab : a ≫ b = 𝟙 J.line := by
    apply (hff J.line J.line J.invertible J.invertible).1
    rw [(descent f).map_comp, ha, hb, e.hom_inv_id]
    exact ((descent f).map_id _).symm
  have hba : b ≫ a = 𝟙 K.line := by
    apply (hff K.line K.line K.invertible K.invertible).1
    rw [(descent f).map_comp, hb, ha, e.inv_hom_id]
    exact ((descent f).map_id _).symm
  let z : J.line ≅ K.line := ⟨a, b, hab, hba⟩
  have hz : tensorPowerMap z.hom 2 ≫ K.square.hom = J.square.hom := by
    apply (hff (tensorPower T J.line 2) W (tensorPower_invertible J.line J.invertible 2) hW).1
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    have hi := he i
    have hai : (Scheme.Modules.pullback (f i)).map a = e.hom.hom i :=
      congrArg (fun t => t.hom i) ha
    rw [← hai] at hi
    change tensorPowerMap ((Scheme.Modules.pullback (f i)).map a) 2 ≫
      (pullback_tensorPower_iso (V i) T (f i) K.line 2).inv ≫
        (Scheme.Modules.pullback (f i)).map K.square.hom =
      (pullback_tensorPower_iso (V i) T (f i) J.line 2).inv ≫
        (Scheme.Modules.pullback (f i)).map J.square.hom at hi
    rw [← Category.assoc, RootTestPullbackCoherenceR0196.power_natural_inv (f i) J.invertible a 2,
      Category.assoc, ← Functor.map_comp] at hi
    exact (cancel_epi (pullback_tensorPower_iso (V i) T (f i) J.line 2).inv).1 hi
  refine ⟨⟨z, hz⟩, ?_, ?_⟩
  · apply Iso.ext
    exact ha
  · intro w hw
    apply Subtype.ext
    apply Iso.ext
    apply (hff J.line K.line J.invertible K.invertible).1
    exact (congrArg Iso.hom hw).trans ha.symm

variable {B : Scheme.{0}} {W : B.Modules} (P : Presentation B W)

/-- A categorical arrow between pulled-back objects gives a compatible
isomorphism between the actual pulled-back sheaves. -/
lemma local_arrow_square {T V : Over B} (f : V ⟶ T)
    (x y : P.functor.obj (.mk (.op T)))
    (t : (P.functor.map f.op.toLoc).toFunctor.obj x ⟶ (P.functor.map f.op.toLoc).toFunctor.obj y) :
    tensorPowerMap
      ((P.forget.naturality f.op.toLoc).inv.toNatTrans.app x ≫
        (P.forget.app (.mk (.op V))).toFunctor.map t ≫
        (P.forget.naturality f.op.toLoc).hom.toNatTrans.app y) 2 ≫
      (squarePull f.left (root P.toRootDiagram T y)).hom =
    (squarePull f.left (root P.toRootDiagram T x)).hom := by
  apply (cancel_mono
    (OpenSquareRootEffectivityR0197.compare f.left T.hom V.hom (Over.w f) W).hom).1
  simp only [Category.assoc]
  exact square_conjugate
    ((Cat.Hom.toNatIso (P.forget.naturality f.op.toLoc)).app x)
    ((Cat.Hom.toNatIso (P.forget.naturality f.op.toLoc)).app y)
    ((P.forget.app (.mk (.op V))).toFunctor.map t)
    _ _ _ _ (P.square_natural V T f x) (P.square_natural V T f y) (map_square P V t)

/-- Every arrow in the descent category of groupoid fibers is an isomorphism. -/
def descentArrowIso {T : Over B} {ι : Type v} {V : ι → Over B} {f : ∀ i, V i ⟶ T}
    {D E : P.functor.DescentData f} (t : D ⟶ E) : D ≅ E := by
  letI : ∀ i, IsGroupoid (P.functor.obj (.mk (.op (V i)))) := fun i => P.groupoid (V i)
  exact Pseudofunctor.DescentData.isoMk (fun i => asIso (t.hom i))
    (fun {_} p {_ _} a b ha hb => t.comm p a b ha hb)

lemma descentArrowIso_hom {T : Over B} {ι : Type v} {V : ι → Over B} {f : ∀ i, V i ⟶ T}
    {D E : P.functor.DescentData f} (t : D ⟶ E) : (descentArrowIso P t).hom = t := rfl

lemma categorical_faithful {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T)
    (hff : ∀ (M N : T.left.Modules), Scheme.Modules.IsInvertible M →
      Scheme.Modules.IsInvertible N →
      Function.Bijective ((descent (fun i => (f i).left)).map : (M ⟶ N) → _)) :
    (P.functor.toDescentData f).Faithful where
  map_injective {x y} a b hab := by
    letI := forget_faithful P T
    apply (P.forget.app (.mk (.op T))).toFunctor.map_injective
    apply (hff _ _ (P.invertible T x) (P.invertible T y)).1
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    have hi := congrArg (fun t => t.hom i) hab
    have ha := (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.naturality a
    have hb := (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.naturality b
    dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at ha hb
    change (P.functor.map (f i).op.toLoc).toFunctor.map a =
      (P.functor.map (f i).op.toLoc).toFunctor.map b at hi
    rw [hi] at ha
    apply (cancel_epi ((P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app x)).1
    exact ha.symm.trans hb

/-- The underlying all-test module descent functor. -/
def concreteFunctor {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T) :=
  strongData P.forget f ⋙ unsliceFunctor f

def concreteCanonicalIso {T : Over B} {ι : Type v} {V : ι → Over B} (f : ∀ i, V i ⟶ T)
    (x : P.functor.obj (.mk (.op T))) :
    (concreteFunctor P f).obj ((P.functor.toDescentData f).obj x) ≅
      (descent (fun i => (f i).left)).obj ((P.forget.app (.mk (.op T))).toFunctor.obj x) :=
  (unsliceFunctor f).mapIso (strongCanonicalIso P.forget f x) ≪≫
    unsliceCanonical f _

/-- Reflect a module descent arrow whose components lift to the presentation. -/
def liftConcreteHom {T : Over B} {ι : Type v} {V : ι → Over B} {f : ∀ i, V i ⟶ T}
    {D E : P.functor.DescentData f}
    (φ : ∀ i, D.obj i ⟶ E.obj i)
    (ψ : (concreteFunctor P f).obj D ⟶ (concreteFunctor P f).obj E)
    (hφ : ∀ i, (P.forget.app (.mk (.op (V i)))).toFunctor.map (φ i) = ψ.hom i) : D ⟶ E :=
  liftStrongHom P.forget (forget_faithful P) φ (liftUnsliceHom ψ) hφ

open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196

@[simp] lemma concreteCanonicalIso_hom {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (x : P.functor.obj (.mk (.op T))) (i : ι) :
    (concreteCanonicalIso P f x).hom.hom i =
      (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app x := by
  simp [concreteCanonicalIso, unsliceFunctor, strongCanonicalIso, unsliceCanonical,
    genericUnsliceCanonical, Pseudofunctor.DescentData.isoMk]

@[simp] lemma concreteCanonicalIso_inv {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (x : P.functor.obj (.mk (.op T))) (i : ι) :
    (concreteCanonicalIso P f x).inv.hom i =
      (P.forget.naturality (f i).op.toLoc).inv.toNatTrans.app x := by
  have h := congrArg (fun t => t.hom i) (concreteCanonicalIso P f x).inv_hom_id
  change (concreteCanonicalIso P f x).inv.hom i ≫ (concreteCanonicalIso P f x).hom.hom i = 𝟙 _ at h
  rw [concreteCanonicalIso_hom] at h
  apply (cancel_mono ((P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app x)).1
  exact h.trans ((Cat.Hom.toNatIso (P.forget.naturality (f i).op.toLoc)).inv_hom_id_app x).symm

lemma effectiveLocalIso_map {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f)
    (J : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W))
    (e : (descent (fun i => (f i).left)).obj J.line ≅ (concreteDatum P f D).data)
    (he : Realizes (concreteDatum P f D) J e)
    (x : P.functor.obj (.mk (.op T))) (k : SquareIso (root P.toRootDiagram T x) J)
    (i : ι) :
    (P.forget.app (.mk (.op (V i)))).toFunctor.map (effectiveLocalIso P f D J e he x k i).hom =
      (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app x ≫
        (Scheme.Modules.pullback (f i).left).map k.val.hom ≫ e.hom.hom i := by
  simp [effectiveLocalIso, liftIso_hom, OpenSquareRootEffectivityR0197.componentIso]

/-- The effective isomorphism retains the entire original categorical datum. -/
def effectiveIso {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (D : P.functor.DescentData f)
    (J : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W))
    (e : (descent (fun i => (f i).left)).obj J.line ≅ (concreteDatum P f D).data)
    (he : Realizes (concreteDatum P f D) J e)
    (x : P.functor.obj (.mk (.op T))) (k : SquareIso (root P.toRootDiagram T x) J) :
    (P.functor.toDescentData f).obj x ≅ D := by
  let ψ := concreteCanonicalIso P f x ≪≫
    (descent (fun i => (f i).left)).mapIso k.val ≪≫ e
  let φ := liftConcreteHom P (fun i => (effectiveLocalIso P f D J e he x k i).hom) ψ.hom
    (fun i => by
      dsimp only [ψ, Iso.trans_hom, Pseudofunctor.DescentData.comp_hom, Functor.mapIso_hom]
      rw [effectiveLocalIso_map, concreteCanonicalIso_hom]
      rfl)
  exact Pseudofunctor.DescentData.isoMk (effectiveLocalIso P f D J e he x k)
    (fun {_} p {_ _} a b ha hb => φ.comm p a b ha hb)

lemma categorical_essSurj {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T)
    (heff : ∀ D : P.functor.DescentData f, Effective (concreteDatum P f D)) :
    (P.functor.toDescentData f).EssSurj := by
  constructor
  intro D
  obtain ⟨J, e, he⟩ := heff D
  obtain ⟨x, ⟨k⟩⟩ := P.essentially_surjective T J
  exact ⟨x, ⟨effectiveIso P f D J e he x k⟩⟩

def underlyingArrowIso {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) {x y : P.functor.obj (.mk (.op T))}
    (t : (P.functor.toDescentData f).obj x ⟶ (P.functor.toDescentData f).obj y) :
    (descent (fun i => (f i).left)).obj (root P.toRootDiagram T x).line ≅
      (descent (fun i => (f i).left)).obj (root P.toRootDiagram T y).line :=
  (concreteCanonicalIso P f x).symm ≪≫
    (concreteFunctor P f).mapIso (descentArrowIso P t) ≪≫ concreteCanonicalIso P f y

lemma underlyingArrowIso_hom {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) {x y : P.functor.obj (.mk (.op T))}
    (t : (P.functor.toDescentData f).obj x ⟶ (P.functor.toDescentData f).obj y) (i : ι) :
    (underlyingArrowIso P f t).hom.hom i =
    (P.forget.naturality (f i).op.toLoc).inv.toNatTrans.app x ≫
      (P.forget.app (.mk (.op (V i)))).toFunctor.map (t.hom i) ≫
      (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app y := by
  simp only [underlyingArrowIso, Iso.trans_hom, Iso.symm_hom,
    Pseudofunctor.DescentData.comp_hom, Functor.mapIso_hom,
    concreteCanonicalIso_hom, concreteCanonicalIso_inv, descentArrowIso_hom]
  rfl

lemma underlyingArrowIso_compatible {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) {x y : P.functor.obj (.mk (.op T))}
    (t : (P.functor.toDescentData f).obj x ⟶ (P.functor.toDescentData f).obj y) :
    IsoCompatible (fun i => (f i).left) (root P.toRootDiagram T x)
      (root P.toRootDiagram T y) (underlyingArrowIso P f t) := by
  intro i
  rw [underlyingArrowIso_hom]
  exact local_arrow_square P (f i) x y (t.hom i)

lemma categorical_full {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (hW : Scheme.Modules.IsInvertible W)
    (hff : ∀ (M N : T.left.Modules), Scheme.Modules.IsInvertible M →
      Scheme.Modules.IsInvertible N →
      Function.Bijective ((descent (fun i => (f i).left)).map : (M ⟶ N) → _)) :
    (P.functor.toDescentData f).Full := by
  constructor
  intro x y t
  obtain ⟨z, hz, _⟩ := root_iso_descent_family (fun i => (f i).left) hff _ (hW.pullback T.hom)
    (root P.toRootDiagram T x) (root P.toRootDiagram T y)
    (underlyingArrowIso P f t) (underlyingArrowIso_compatible P f t)
  let a := (P.homEquiv T x y).symm z
  have ha : (P.forget.app (.mk (.op T))).toFunctor.map a = z.val.hom := by
    rw [← P.hom_eq]
    exact congrArg (fun z => z.val.hom) ((P.homEquiv T x y).apply_symm_apply z)
  refine ⟨a, ?_⟩
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  letI := forget_faithful P (V i)
  apply (P.forget.app (.mk (.op (V i)))).toFunctor.map_injective
  have hn := (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.naturality a
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  have hi := congrArg (fun e => e.hom.hom i) hz
  change (Scheme.Modules.pullback (f i).left).map z.val.hom =
    (underlyingArrowIso P f t).hom.hom i at hi
  rw [underlyingArrowIso_hom] at hi
  apply (cancel_mono ((P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app y)).1
  change (P.forget.app (.mk (.op (V i)))).toFunctor.map
    ((P.functor.map (f i).op.toLoc).toFunctor.map a) ≫ _ = _
  rw [hn, ha]
  change (P.forget.naturality (f i).op.toLoc).hom.toNatTrans.app x ≫
    (Scheme.Modules.pullback (f i).left).map z.val.hom = _
  rw [hi]
  exact (Cat.Hom.toNatIso (P.forget.naturality (f i).op.toLoc)).hom_inv_id_app_assoc x _

lemma categorical_equivalence {T : Over B} {ι : Type v} {V : ι → Over B}
    (f : ∀ i, V i ⟶ T) (hW : Scheme.Modules.IsInvertible W)
    (hff : ∀ (M N : T.left.Modules), Scheme.Modules.IsInvertible M →
      Scheme.Modules.IsInvertible N →
      Function.Bijective ((descent (fun i => (f i).left)).map : (M ⟶ N) → _))
    (heff : ∀ D : P.functor.DescentData f, Effective (concreteDatum P f D)) :
    (P.functor.toDescentData f).IsEquivalence where
  faithful := categorical_faithful P f hff
  full := categorical_full P f hW hff
  essSurj := categorical_essSurj P f heff


end CategoricalRootDescentR0198
open CategoryTheory AlgebraicGeometry
open CategoricalRootDescentR0198 ArithmeticThetaRootDescentR0197

/-- Categorical fpqc descent for the specified roots in every faithful presentation. -/
theorem categorical_fpqc_root_descent
    (B : Scheme.{0}) (W : B.Modules) (hW : Scheme.Modules.IsInvertible W)
    (P : Presentation B W) : SingletonDescent P.functor := by
  intro T V q hq hf hs
  exact categorical_equivalence P (fun _ : Unit => q) hW
    (fpqc_root_morphisms T.left V.left q.left hq hf hs
      ((Scheme.Modules.pullback T.hom).obj W) (hW.pullback T.hom)).1
    (concrete_effective_fpqc P hW T V q hq hf hs)

/-- Categorical descent for every jointly surjective family of open immersions. -/
theorem categorical_open_root_descent
    (B : Scheme.{0}) (W : B.Modules) (hW : Scheme.Modules.IsInvertible W)
    (P : Presentation B W) (T : Over B) (ι : Type v) (V : ι → Over B)
    (f : ∀ i, V i ⟶ T) (hf : ∀ i, IsOpenImmersion (f i).left)
    (hcover : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) :
    (P.functor.toDescentData f).IsEquivalence := by
  letI : ∀ i, IsOpenImmersion (f i).left := hf
  exact categorical_equivalence P f hW
    (fun M N _ _ => Scheme.Modules.toDescentData_map_bijective_of_openCover
      (fun i => (f i).left) hcover M N)
    (concrete_effective_open P hW T ι V f hf hcover)

#print axioms categorical_fpqc_root_descent
#print axioms categorical_open_root_descent
end ArithmeticThetaRootStackR0198
