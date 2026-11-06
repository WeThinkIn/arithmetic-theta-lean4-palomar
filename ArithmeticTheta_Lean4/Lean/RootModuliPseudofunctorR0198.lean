import RootStackDefinitionsR0198

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace ArithmeticThetaRootStackR0198
namespace RootModuliPseudofunctorR0198
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196

variable {B : Scheme.{0}} (W : B.Modules)

/-- All actual roots over a fixed object of the slice. -/
def Fiber (T : Over B) := SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W)

variable {W}

def refl {Z : Scheme.{0}} {N : Z.Modules} (J : SquareLine Z N) : SquareIso J J :=
  ⟨Iso.refl _, by simp [tensorPowerMap_id]⟩

def trans {Z : Scheme.{0}} {N : Z.Modules} {J K L : SquareLine Z N}
    (e : SquareIso J K) (d : SquareIso K L) : SquareIso J L :=
  ⟨e.val ≪≫ d.val, by
    simp only [Iso.trans_hom, tensorPowerMap_comp, Category.assoc]
    rw [d.property, e.property]⟩

def symm {Z : Scheme.{0}} {N : Z.Modules} {J K : SquareLine Z N}
    (e : SquareIso J K) : SquareIso K J :=
  ⟨e.val.symm, by
    calc
      tensorPowerMap e.val.inv 2 ≫ J.square.hom =
          tensorPowerMap e.val.inv 2 ≫ (tensorPowerMap e.val.hom 2 ≫ K.square.hom) :=
        congrArg (fun h => tensorPowerMap e.val.inv 2 ≫ h) e.property.symm
      _ = K.square.hom := by
        rw [← Category.assoc, ← tensorPowerMap_comp, e.val.inv_hom_id,
          tensorPowerMap_id, Category.id_comp]⟩

instance fiberCategory (T : Over B) : Category (Fiber W T) where
  Hom J K := SquareIso J K
  id := refl
  comp := trans
  id_comp _ := by apply Subtype.ext; apply Iso.ext; exact Category.id_comp _
  comp_id _ := by apply Subtype.ext; apply Iso.ext; exact Category.comp_id _
  assoc _ _ _ := by apply Subtype.ext; apply Iso.ext; exact Category.assoc _ _ _

instance fiberGroupoid (T : Over B) : Groupoid (Fiber W T) where
  inv := symm
  inv_comp e := by apply Subtype.ext; apply Iso.ext; exact e.val.inv_hom_id
  comp_inv e := by apply Subtype.ext; apply Iso.ext; exact e.val.hom_inv_id

@[ext] lemma hom_ext {T : Over B} {J K : Fiber W T} (e d : J ⟶ K)
    (h : e.val.hom = d.val.hom) : e = d := Subtype.ext (Iso.ext h)

def forget (T : Over B) : Fiber W T ⥤ T.left.Modules where
  obj J := J.line
  map e := e.val.hom

instance (T : Over B) : (forget (W := W) T).Faithful where
  map_injective := fun h => hom_ext _ _ h

/-- Pullback along the specified slice map, including its triangle to B. -/
def pullObj {S T : Over B} (f : S ⟶ T) (J : Fiber W T) : Fiber W S :=
  ⟨(Scheme.Modules.pullback f.left).obj J.line, J.invertible.pullback f.left,
    squarePull f.left J ≪≫ (Scheme.Modules.pullbackComp f.left T.hom).app W ≪≫
      (Scheme.Modules.pullbackCongr (Over.w f)).app W⟩

lemma pull_compatible {S T : Over B} (f : S ⟶ T) {J K : Fiber W T} (e : J ⟶ K) :
    tensorPowerMap ((Scheme.Modules.pullback f.left).map e.val.hom) 2 ≫
      (pullObj f K).square.hom = (pullObj f J).square.hom := by
  simp only [pullObj, Iso.trans_hom, squarePull, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (tensorPowerMap _ 2),
    power_natural_inv f.left J.invertible e.val.hom 2]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, e.property]

def pull {S T : Over B} (f : S ⟶ T) : Fiber W T ⥤ Fiber W S where
  obj := pullObj f
  map e := ⟨(Scheme.Modules.pullback f.left).mapIso e.val, pull_compatible f e⟩
  map_id J := by apply hom_ext; exact CategoryTheory.Functor.map_id _ _
  map_comp e d := by apply hom_ext; exact Functor.map_comp _ _ _

open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

lemma pullback_id_section {Z : Scheme.{0}} (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackId Z).hom.app M).app U
      (Scheme.Modules.pullbackLocalSection (𝟙 Z) s) = s := by
  have h := CategoryTheory.unit_conjugateEquiv .id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z))
    (Scheme.Modules.pullbackId Z).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun q => Scheme.Modules.Hom.app q U s) h).symm

lemma power_id {Z : Scheme.{0}} (M : Z.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    (pullback_tensorPower_iso Z Z (𝟙 Z) M n).hom ≫
      tensorPowerMap ((Scheme.Modules.pullbackId Z).hom.app M) n =
    (Scheme.Modules.pullbackId Z).hom.app (tensorPower Z M n) := by
  apply hom_ext_frames
  intro x
  obtain ⟨U, s, hx, hs⟩ := local_frame_exists hM x
  refine ⟨U, Scheme.Modules.pullbackLocalSection (𝟙 Z)
    (tensorPowerSection Z M n U s), hx,
    pullback_frame _ _ _ (tensorPower_frame M s hs n), ?_⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [pullback_tensorPower_local_section, tensorPowerMap_section,
    pullback_id_section, pullback_id_section]
  rfl

lemma square_id {Z : Scheme.{0}} {N : Z.Modules} (J : SquareLine Z N) :
    tensorPowerMap ((Scheme.Modules.pullbackId Z).hom.app J.line) 2 ≫ J.square.hom =
      (squarePull (𝟙 Z) J).hom ≫ (Scheme.Modules.pullbackId Z).hom.app N := by
  apply (cancel_epi (pullback_tensorPower_iso Z Z (𝟙 Z) J.line 2).hom).1
  rw [← Category.assoc, power_id J.line J.invertible]
  simp only [squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact ((Scheme.Modules.pullbackId Z).hom.naturality J.square.hom).symm

def baseComparison {S T : Over B} (f : S ⟶ T) :
    (Scheme.Modules.pullback f.left).obj ((Scheme.Modules.pullback T.hom).obj W) ≅
      (Scheme.Modules.pullback S.hom).obj W :=
  (Scheme.Modules.pullbackComp f.left T.hom).app W ≪≫
    (Scheme.Modules.pullbackCongr (Over.w f)).app W

lemma base_id (T : Over B) :
    (baseComparison (W := W) (𝟙 T)).hom =
      (Scheme.Modules.pullbackId T.left).hom.app ((Scheme.Modules.pullback T.hom).obj W) :=
  comp_id T.hom W

lemma base_comp {R S T : Over B} (f : R ⟶ S) (g : S ⟶ T) :
    (Scheme.Modules.pullbackComp f.left g.left).hom.app
        ((Scheme.Modules.pullback T.hom).obj W) ≫ (baseComparison (W := W) (f ≫ g)).hom =
      (Scheme.Modules.pullback f.left).map (baseComparison (W := W) g).hom ≫
        (baseComparison (W := W) f).hom := by
  dsimp [baseComparison]
  rw [← Category.assoc, comp_assoc_reverse]
  have h := congrArg (fun k =>
    (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullbackComp g.left T.hom).hom.app W) ≫
      k ≫ (Scheme.Modules.pullbackCongr (Over.w f)).hom.app W)
    (comp_congr f.left (Over.w g) W)
  simpa [Category.assoc, Scheme.Modules.pullbackCongr] using h

lemma pull_id_compatible (T : Over B) (J : Fiber W T) :
    tensorPowerMap ((Scheme.Modules.pullbackId T.left).hom.app J.line) 2 ≫ J.square.hom =
      (pullObj (𝟙 T) J).square.hom := by
  change _ = (squarePull (𝟙 T.left) J).hom ≫ (baseComparison (𝟙 T)).hom
  rw [base_id]
  exact square_id J

def pullId (T : Over B) : pull (W := W) (𝟙 T) ≅ 𝟭 (Fiber W T) :=
  NatIso.ofComponents (fun J =>
    { hom := ⟨(Scheme.Modules.pullbackId T.left).app J.line, pull_id_compatible T J⟩
      inv := symm ⟨(Scheme.Modules.pullbackId T.left).app J.line, pull_id_compatible T J⟩
      hom_inv_id := by apply hom_ext; exact Iso.hom_inv_id _
      inv_hom_id := by apply hom_ext; exact Iso.inv_hom_id _ })
    (fun e => by apply hom_ext; exact (Scheme.Modules.pullbackId T.left).hom.naturality e.val.hom)

lemma pull_comp_compatible {R S T : Over B} (f : R ⟶ S) (g : S ⟶ T)
    (J : Fiber W T) :
    tensorPowerMap ((Scheme.Modules.pullbackComp f.left g.left).hom.app J.line) 2 ≫
      (pullObj (f ≫ g) J).square.hom = (pullObj f (pullObj g J)).square.hom := by
  change tensorPowerMap _ 2 ≫ (squarePull (f.left ≫ g.left) J).hom ≫
    (baseComparison (f ≫ g)).hom = _
  rw [← Category.assoc, square_comp]
  change _ = (pullback_tensorPower_iso _ _ f.left _ 2).inv ≫
    (Scheme.Modules.pullback f.left).map ((squarePull g.left J).hom ≫
      (baseComparison g).hom) ≫ (baseComparison f).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [base_comp]

def pullComp {R S T : Over B} (f : R ⟶ S) (g : S ⟶ T) :
    pull (W := W) g ⋙ pull f ≅ pull (f ≫ g) :=
  NatIso.ofComponents (fun J =>
    { hom := ⟨(Scheme.Modules.pullbackComp f.left g.left).app J.line,
        pull_comp_compatible f g J⟩
      inv := symm ⟨(Scheme.Modules.pullbackComp f.left g.left).app J.line,
        pull_comp_compatible f g J⟩
      hom_inv_id := by apply hom_ext; exact Iso.hom_inv_id _
      inv_hom_id := by apply hom_ext; exact Iso.inv_hom_id _ })
    (fun e => by apply hom_ext; exact (Scheme.Modules.pullbackComp f.left g.left).hom.naturality e.val.hom)

@[simp] lemma forget_eqToHom {T : Over B} {J K : Fiber W T} (h : J = K) :
    (eqToHom h : J ⟶ K).val.hom = eqToHom (congrArg SquareLine.line h) := by
  subst K
  rfl

@[simp] lemma comp_val {T : Over B} {J K L : Fiber W T} (e : J ⟶ K) (d : K ⟶ L) :
    (e ≫ d).val.hom = e.val.hom ≫ d.val.hom := rfl

@[simp] lemma id_val {T : Over B} (J : Fiber W T) :
    (𝟙 J : J ⟶ J).val.hom = 𝟙 J.line := rfl

/-- The root pseudofunctor retains the canonical module comparisons. -/
def rootFunctor : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun T => Cat.of (Fiber W T.unop))
    (fun f => (pull (W := W) f.unop).toCatHom)
    (fun T => Cat.Hom.isoMk (pullId T.unop))
    (fun f g => Cat.Hom.isoMk (pullComp g.unop f.unop).symm)
    (fun f g h => by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext J
      apply (forget (W := W) _).map_injective
      simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
        Cat.associator_hom_app, Cat.eqToHom_app, CategoryTheory.Functor.map_comp, eqToHom_map]
      change (Scheme.Modules.pullbackComp h.unop.left (g.unop.left ≫ f.unop.left)).inv.app J.line ≫
        (Scheme.Modules.pullback h.unop.left).map
          ((Scheme.Modules.pullbackComp g.unop.left f.unop.left).inv.app J.line) ≫
        𝟙 _ ≫
        (Scheme.Modules.pullbackComp h.unop.left g.unop.left).hom.app
          ((Scheme.Modules.pullback f.unop.left).obj J.line) ≫
        (Scheme.Modules.pullbackComp (h.unop.left ≫ g.unop.left) f.unop.left).hom.app J.line = eqToHom (congrArg (fun a => (Scheme.Modules.pullback a).obj J.line)
          (Category.assoc h.unop.left g.unop.left f.unop.left).symm)
      have hc := congrArg (fun k => k.app J.line)
        (Scheme.Modules.pseudofunctor_associativity h.unop.left g.unop.left f.unop.left)
      simpa only [NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
        CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.associator_hom_app,
        Category.id_comp, Category.comp_id, eqToHom_app] using hc)
    (fun f => by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext J
      apply (forget (W := W) _).map_injective
      simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
        Cat.eqToHom_app, CategoryTheory.Functor.map_comp, eqToHom_map]
      have hc := congrArg (fun k => k.app J.line)
        (Scheme.Modules.pseudofunctor_left_unitality f.unop.left)
      change (Scheme.Modules.pullbackComp f.unop.left (𝟙 _)).inv.app J.line ≫
        (Scheme.Modules.pullback f.unop.left).map ((Scheme.Modules.pullbackId _).hom.app J.line) ≫
        𝟙 _ = eqToHom (congrArg (fun a => (Scheme.Modules.pullback a).obj J.line)
          (Category.comp_id f.unop.left))
      simpa only [NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
        CategoryTheory.Functor.leftUnitor_hom_app, eqToHom_app, CategoryTheory.Functor.id_obj] using hc)
    (fun f => by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext J
      apply (forget (W := W) _).map_injective
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
        Cat.eqToHom_app, CategoryTheory.Functor.map_comp, eqToHom_map]
      have hc := congrArg (fun k => k.app J.line)
        (Scheme.Modules.pseudofunctor_right_unitality f.unop.left)
      change (Scheme.Modules.pullbackComp (𝟙 _) f.unop.left).inv.app J.line ≫
        (Scheme.Modules.pullbackId _).hom.app ((Scheme.Modules.pullback f.unop.left).obj J.line) ≫
        𝟙 _ = eqToHom (congrArg (fun a => (Scheme.Modules.pullback a).obj J.line)
          (Category.id_comp f.unop.left))
      simpa only [NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
        CategoryTheory.Functor.rightUnitor_hom_app, eqToHom_app, CategoryTheory.Functor.id_obj] using hc)

/-- The forgetful functor commutes with pullback on the underlying modules. -/
def forgetPull {S T : Over B} (f : S ⟶ T) :
    pull (W := W) f ⋙ forget S ≅ forget T ⋙ Scheme.Modules.pullback f.left :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)

/-- The tautological line with the same pullback comparison as the square. -/
def forgetStrong : Pseudofunctor.StrongTrans (rootFunctor (W := W)) (modulesOver B) where
  app T := (forget (W := W) T.as.unop).toCatHom
  naturality f := Cat.Hom.isoMk (forgetPull f.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id T := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext J
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext J
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (Scheme.Modules.pullback g.as.unop.left).map (𝟙 _) ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl

def diagram : RootDiagram B W where
  functor := rootFunctor
  forget := forgetStrong
  invertible _ J := J.invertible
  square _ J := J.square

lemma root_diagram (T : Over B) (J : Fiber W T) : root (diagram (W := W)) T J = J := rfl

lemma square_natural : SquareNatural (diagram (W := W)) := by
  intro S T f J
  change tensorPowerMap (𝟙 _) 2 ≫ (squarePull f.left J).hom ≫
    ((Scheme.Modules.pullbackComp f.left T.hom).app W).hom ≫
    ((Scheme.Modules.pullbackCongr (Over.w f)).app W).hom = _
  rw [tensorPowerMap_id, Category.id_comp]
  rfl

def presentation : Presentation B W where
  toRootDiagram := diagram
  groupoid T := by
    change IsGroupoid (Fiber W T)
    infer_instance
  square_natural := square_natural
  homEquiv _ _ _ := Equiv.refl _
  hom_eq _ _ _ _ := rfl
  essentially_surjective T J := ⟨J, ⟨refl J⟩⟩

end RootModuliPseudofunctorR0198

/-- The actual moduli groupoids of specified square roots, with coherent
pullback and their tautological line and square map. -/
theorem root_moduli_pseudofunctor
    (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (_hW : AlgebraicGeometry.Scheme.Modules.IsInvertible W) :
    Nonempty (ArithmeticThetaRootStackR0198.Presentation B W) :=
  ⟨RootModuliPseudofunctorR0198.presentation⟩

end ArithmeticThetaRootStackR0198

#print axioms ArithmeticThetaRootStackR0198.root_moduli_pseudofunctor
