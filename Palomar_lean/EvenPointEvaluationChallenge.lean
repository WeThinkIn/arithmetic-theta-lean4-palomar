module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section elab "mX" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u v' u'
open CategoryTheory MonoidalCategory Limits Opposite
namespace PresheafOfModules
section general
variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
namespace InternalHom
lemma map_id_apply (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  change (M.presheaf.map (𝟙 X)) x = x
  rw [M.presheaf.map_id]; rfl
abbrev PiFamily (X : Cᵒᵖ) : Type (max u u' v') :=
  ∀ ⦃Y : Cᵒᵖ⦄ (_ : X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y)
variable {F N} in
def IsNatural {X : Cᵒᵖ} (φ : PiFamily F N X) : Prop :=
  ∀ ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y), N.map g (φ f x) = φ (f ≫ g) (F.map g x)
def naturalFamilies (X : Cᵒᵖ) : AddSubgroup (PiFamily F N X) where
  carrier := {φ | IsNatural φ}
  zero_mem' := by
    intro Y Z f g x
    simp only [Pi.zero_apply, LinearMap.zero_apply]
    exact (N.map g).hom.map_zero
  add_mem' := by
    intro φ ψ hφ hψ Y Z f g x
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hφ f g x, hψ f g x]
  neg_mem' := by
    intro φ hφ Y Z f g x
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hφ f g x]
variable {F N}
@[ext] lemma naturalFamilies_ext {X : Cᵒᵖ} {φ ψ : naturalFamilies F N X}
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj Y), φ.1 f x = ψ.1 f x) : φ = ψ :=
  Subtype.ext (funext fun _ => funext fun f => LinearMap.ext (h f))
lemma naturality {X : Cᵒᵖ} (φ : naturalFamilies F N X) ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y) : N.map g (φ.1 f x) = φ.1 (f ≫ g) (F.map g x) := φ.2 f g x
lemma congr_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (x : F.obj Y) : φ.1 f x = φ.1 g x := by subst h; rfl
instance (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩
@[simp] lemma smul_app {X : Cᵒᵖ} (r : R.obj X) (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (r • φ).1 f x = R.map f r • φ.1 f x := rfl
@[simp] lemma add_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ + ψ).1 f x = φ.1 f x + ψ.1 f x := rfl
@[simp] lemma zero_app {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (0 : naturalFamilies F N X).1 f x = 0 := rfl
@[simp] lemma neg_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (-φ).1 f x = - φ.1 f x := rfl
@[simp] lemma sub_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ - ψ).1 f x = φ.1 f x - ψ.1 f x := rfl
instance (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp
variable (F N)
def restrict {X X' : Cᵒᵖ} (h : X ⟶ X') : naturalFamilies F N X →+ naturalFamilies F N X' where
  toFun φ := ⟨fun Y f => φ.1 (h ≫ f), fun Y Z f g x => by
    rw [φ.2 (h ≫ f) g x, Category.assoc]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
@[simp] lemma restrict_app {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : (restrict F N h φ).1 f x = φ.1 (h ≫ f) x := rfl
@[simps obj] def presheaf : Cᵒᵖ ⥤ Ab.{max u u' v'} where
  obj X := AddCommGrpCat.of (naturalFamilies F N X)
  map h := AddCommGrpCat.ofHom (restrict F N h)
  map_id X := by
    ext φ Y f x
    change φ.1 (𝟙 X ≫ f) x = φ.1 f x
    rw [Category.id_comp]
  map_comp h h' := by
    ext φ Y f x
    change φ.1 ((h ≫ h') ≫ f) x = φ.1 (h ≫ (h' ≫ f)) x
    rw [Category.assoc]
@[simp] lemma presheaf_map_apply {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : ((presheaf F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl
instance (X : Cᵒᵖ) : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheaf F N).obj X) :=
  inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))
variable {N} in
def postcomp {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') (X : Cᵒᵖ) : naturalFamilies F N X →+ naturalFamilies F N' X where
  toFun φ := ⟨fun Y f =>
    { toFun := fun x => ψ.app Y (φ.1 f x)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by
        rw [(φ.1 f).map_smul]
        exact (ψ.app Y).hom.map_smul r _ }, by
    intro Y Z f g x
    change N'.map g (ψ.app Y (φ.1 f x)) = ψ.app Z (φ.1 (f ≫ g) (F.map g x))
    rw [← naturality_apply, φ.2 f g x]⟩
  map_zero' := by ext Y f x; exact (ψ.app Y).hom.map_zero
  map_add' φ φ' := by ext Y f x; exact (ψ.app Y).hom.map_add _ _
@[simp] lemma postcomp_app {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') {X : Cᵒᵖ}
    (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    (postcomp F ψ X φ).1 f x = ψ.app Y (φ.1 f x) := rfl
end InternalHom
open InternalHom
@[simps! obj] noncomputable def ihomObj : PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) :=
  ofPresheaf (InternalHom.presheaf F N) (by
    intro X X' h r φ
    apply naturalFamilies_ext
    intro Y f x
    change (R.map (h ≫ f) r) • φ.1 (h ≫ f) x = R.map f (R.map h r) • φ.1 (h ≫ f) x
    rw [Functor.map_comp]
    rfl)
@[simp] lemma ihomObj_map_val {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) :
    ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl
variable {N} in
noncomputable def ihomMap {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') : ihomObj F N ⟶ ihomObj F N' :=
  homMk { app := fun X => AddCommGrpCat.ofHom (postcomp F ψ X)
          naturality := fun {X X'} h => by ext φ; rfl } (by
    intro X r φ
    apply naturalFamilies_ext
    intro Y f x
    exact (ψ.app Y).hom.map_smul _ _)
@[simp] lemma ihomMap_app_val {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N')
    {X : Cᵒᵖ} (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    ((ihomMap F ψ).app X φ).1 f x = ψ.app Y (φ.1 f x) := rfl
noncomputable def ihomFunctor : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) where
  obj N := ihomObj F N
  map ψ := ihomMap F ψ
  map_id N := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
  map_comp ψ ψ' := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
@[simp] lemma ihomFunctor_obj (N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihomFunctor F).obj N' = ihomObj F N' := rfl
@[simp] lemma ihomFunctor_map {N' N'' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N' ⟶ N'') :
    (ihomFunctor F).map ψ = ihomMap F ψ := rfl
end general
section closed
variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
namespace InternalHom
noncomputable def curryFamily (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      map_add' := fun x x' => by rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← (θ.app Y).hom.map_smul]
        rfl }, by
    intro Y Z f g x
    change N.map g (θ.app Y _) = θ.app Z _
    rw [← naturality_apply]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    change θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map g (G.map f y)) =
      θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map (f ≫ g) y)
    rw [← PresheafOfModules.map_comp_apply]⟩
@[simp] lemma curryFamily_app (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl
end InternalHom
open InternalHom
noncomputable def curry' (θ : F ⊗ G ⟶ N) : G ⟶ ihomObj F N :=
  homMk
    { app := fun X => AddCommGrpCat.ofHom
        { toFun := fun y => curryFamily F θ y
          map_zero' := by
            apply naturalFamilies_ext; intro Y f x
            have h0 : G.map f (0 : G.obj X) = 0 := (G.map f).hom.map_zero
            rw [curryFamily_app, h0, TensorProduct.tmul_zero]
            exact (θ.app Y).hom.map_zero
          map_add' := fun y y' => by
            apply naturalFamilies_ext; intro Y f x
            have h1 : G.map f (y + y') = G.map f y + G.map f y' := (G.map f).hom.map_add _ _
            rw [InternalHom.add_app, curryFamily_app, curryFamily_app, curryFamily_app, h1,
              TensorProduct.tmul_add]
            exact (θ.app Y).hom.map_add _ _ }
      naturality := fun {X X'} h => by
        ext y
        apply naturalFamilies_ext; intro Y f x
        change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (G.map h y)) = θ.app Y (x ⊗ₜ[R.obj Y] G.map (h ≫ f) y)
        rw [PresheafOfModules.map_comp_apply] }
    (by
      intro X r y
      apply naturalFamilies_ext; intro Y f x
      change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (r • y)) = R.map f r • θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      rw [G.map_smul]
      change θ.app Y (x ⊗ₜ[R.obj Y] ((R.map f r : R.obj Y) • G.map f y)) = _
      rw [TensorProduct.tmul_smul]
      exact (θ.app Y).hom.map_smul _ _)
@[simp] lemma curry'_app_val (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : ((curry' F θ).app X y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl
noncomputable def uncurryApp (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) : (F ⊗ G).obj X ⟶ N.obj X :=
  ModuleCat.MonoidalCategory.tensorLift (fun (x : F.obj X) (y : G.obj X) => (κ.app X y).1 (𝟙 X) x)
    (fun x x' y => by simp)
    (fun r x y => by simp)
    (fun x y y' => by
      have h1 : κ.app X (y + y') = κ.app X y + κ.app X y' := (κ.app X).hom.map_add _ _
      simp only [h1]; rfl)
    (fun r x y => by
      have h1 : κ.app X (r • y) = r • κ.app X y := (κ.app X).hom.map_smul _ _
      simp only [h1]
      change R.map (𝟙 X) r • (κ.app X y).1 (𝟙 X) x = _
      rw [R.map_id]
      rfl)
lemma tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := rfl
lemma uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by
  erw [ModuleCat.MonoidalCategory.tensorLift_tmul (R := ↑(R.obj X))]
noncomputable def uncurry' (κ : G ⟶ ihomObj F N) : F ⊗ G ⟶ N where
  app X := uncurryApp F κ X
  naturality {X Y} g := ModuleCat.MonoidalCategory.tensor_ext (fun x y => by
    dsimp
    erw [tensorObj_map_tmul' F (G := G) g x y]
    erw [uncurryApp_tmul, uncurryApp_tmul]
    rw [naturality_apply κ g y]
    erw [ihomObj_map_val]
    erw [(κ.app X y).2 (𝟙 X) g x]
    exact congr_app _ (by simp) _)
lemma uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x :=
  uncurryApp_tmul F κ X x y
lemma uncurry'_curry' (θ : F ⊗ G ⟶ N) : uncurry' F (curry' F θ) = θ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  erw [uncurry'_app_tmul]
  change θ.app X (x ⊗ₜ[R.obj X] G.map (𝟙 X) y) = θ.app X (x ⊗ₜ[R.obj X] y)
  rw [InternalHom.map_id_apply]
lemma curry'_uncurry' (κ : G ⟶ ihomObj F N) : curry' F (uncurry' F κ) = κ := by
  ext X y
  apply naturalFamilies_ext; intro Y f x
  rw [curry'_app_val]
  erw [uncurry'_app_tmul]
  rw [naturality_apply κ f y, ihomObj_map_val]
  exact congr_app _ (by simp) _
noncomputable def tensorIhomAdj : tensorLeft F ⊣ ihomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G N =>
        { toFun := curry' F
          invFun := uncurry' F
          left_inv := uncurry'_curry' F
          right_inv := curry'_uncurry' F }
      homEquiv_naturality_left_symm := fun {G G' N} γ κ => by
        ext X : 1
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        change (uncurry' F (γ ≫ κ)).app X (x ⊗ₜ[R.obj X] y) =
          (uncurry' F κ).app X ((F ◁ γ).app X (x ⊗ₜ[R.obj X] y))
        erw [uncurry'_app_tmul, uncurry'_app_tmul]
      homEquiv_naturality_right := fun {G N N'} θ ν => by
        ext X y
        apply naturalFamilies_ext; intro Y f x
        rfl }
noncomputable instance instMonoidalClosed : MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }
end closed
end PresheafOfModules
@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option autoImplicit false
open CategoryTheory MonoidalCategory Limits
noncomputable section
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
set_option backward.isDefEq.respectTransparency true
namespace SheafOfModules
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
abbrev ringSheaf : Sheaf J RingCat.{u} := ⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩
abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)
abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev toPMod : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪 :=
  SheafOfModules.forget (ringSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
instance : (toPMod 𝒪 h𝒪).Faithful := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.faithful
instance : (toPMod 𝒪 h𝒪).Full := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.full
instance : (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪) := inferInstance
include h𝒪 in
theorem presheafW_isMonoidal : (presheafW J 𝒪).IsMonoidal :=
  by sorry
def sheafifyCounitIso (M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) : (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M :=
  (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
set_option backward.isDefEq.respectTransparency false in
def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅ (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))
instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))
instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal
@[simp] theorem tensorUnit_eq : 𝟙_ (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) = unit _ := rfl
instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪)
def tensorIsoSheafify (L M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) : (sheafifyFunctor 𝒪 h𝒪).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (sheafifyFunctor 𝒪 h𝒪) L.val M.val).symm ≪≫
    (sheafifyCounitIso 𝒪 h𝒪 L ⊗ᵢ sheafifyCounitIso 𝒪 h𝒪 M)
end SheafOfModules
namespace AlgebraicGeometry
variable (X : Scheme.{u})
instance Scheme.PresheafOfModulesOfCommRing.monoidalCategory : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.symmetricCategory : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.monoidalClosed : MonoidalClosed X.PresheafOfModules :=
  inferInstanceAs (MonoidalClosed (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.Modules.monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.monoidalClosed : MonoidalClosed X.Modules :=
  inferInstanceAs (MonoidalClosed
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
variable {X}
abbrev Scheme.Modules.tensor (L M : X.Modules) : X.Modules := L ⊗ M
abbrev Scheme.Modules.dual (L : X.Modules) : X.Modules := (ihom L).obj (𝟙_ X.Modules)
@[simp] theorem Scheme.Modules.tensorUnit_eq :
    𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl
variable (X) in
abbrev Scheme.Modules.sheafify : X.PresheafOfModules ⥤ X.Modules :=
  SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property
instance : (Scheme.Modules.sheafify X).Monoidal :=
  inferInstanceAs (SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).Monoidal
def Scheme.Modules.tensorIsoSheafify (L M : X.Modules) : (Scheme.Modules.sheafify X).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  SheafOfModules.tensorIsoSheafify X.sheaf.obj X.ringCatSheaf.property L M
end AlgebraicGeometry
end
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
section Hom
variable (L M : X.Modules)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
def tensorSectionsHom : L.val ⊗ M.val ⟶ (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj (L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (tensorIsoSheafify L M).hom
end Hom
section Sections
variable {L M : X.Modules} {U : X.Opens}
def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
end Sections
end AlgebraicGeometry.Scheme.Modules
section OriginalIdealContext1651
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) : SheafOfModules.unit Y.ringCatSheaf ⟶ (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
namespace Scheme.IdealSheafData
def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)
def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit
def invModule (I : X.IdealSheafData) : X.Modules := Scheme.Modules.dual I.module
def invModuleSection (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι
end Scheme.IdealSheafData
end AlgebraicGeometry
end OriginalIdealContext1651
namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
def Compatible (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Prop :=
  ∀ (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens) (m : Γ(M, U)),
    (e t).app U m = ((ihom.ev M).app N).app U
      (Scheme.Modules.tensorSections m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t))
theorem canonicalGlobalSectionsEquiv : ∃! e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N), Compatible M N e := by
  sorry
def globalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (canonicalGlobalSectionsEquiv M N).exists.choose
end ArithmeticThetaPalomarDual465
open AlgebraicGeometry
namespace NeronModelInfra
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) := {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
open NeronModelInfra
namespace GoodReductionJacobian
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
end GoodReductionJacobian
namespace ArithmeticThetaLocalWeierstrassR0203
structure SchemeLaw {S X : Scheme.{u}} (p : X ⟶ S) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    SchemeHomOver t p → SchemeHomOver t p → SchemeHomOver t p
  one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p → SchemeHomOver t p
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y z : SchemeHomOver t p),
    mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p),
    mul t (inv t x) x = one t
  mul_comm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t p), mul t x y = mul t y x
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t p),
    GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ y)
structure Family (S : Scheme.{u}) where
  curve : Scheme.{u}
  p : curve ⟶ S
  law : SchemeLaw p
  proper : IsProper p
  dimension : SmoothOfRelativeDimension 1 p
  connected : GeometricallyConnected p
def Family.zero {S : Scheme.{u}} (E : Family S) : S ⟶ E.curve := (E.law.one (𝟙 S)).val
end ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaLocalWeierstrassR0203
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
end ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra
def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}} (t : T ⟶ S) : ℕ → SchemeHomOver t E.p → SchemeHomOver t E.p | 0, _ => E.law.one t | n + 1, x => E.law.mul t (multiple E t n x) x
end ArithmeticThetaSchemeLevelR0204
namespace ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 NeronModelInfra
variable {S : Scheme.{u}} (E : Family S)
structure EvenPoint where
  point : SchemeHomOver (𝟙 S) E.p
  killed : multiple E (𝟙 S) 2 point = E.law.one (𝟙 S)
  avoids : Disjoint (Set.range point.val) (Set.range E.zero)
end ArithmeticThetaEvenMarkingTorsorR0216
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
instance Scheme.Hom.opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ h
end AlgebraicGeometry
namespace ArithmeticThetaRelativeDiscriminantR0171
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) : Prop := ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun a : X.presheaf.obj (Opposite.op V) => a • res F h s)
end ArithmeticThetaRelativeDiscriminantR0171
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}}
def IsInvertible (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U)), x ∈ X.basicOpen f ∧
    ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span {g}
end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {M : X.Modules}
def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) := r
def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := m
@[simp] lemma ofUnitSection_toUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ofUnitSection U (toUnitSection U r) = r := rfl
@[simp] lemma toUnitSection_ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    toUnitSection U (ofUnitSection U m) = m := rfl
lemma ofUnitSection_injective (U : X.Opens) : Function.Injective (ofUnitSection (X := X) U) :=
  fun _ _ h => h
lemma ofUnitSection_map {U V : X.Opens} (i : V ⟶ U) (m : Γ(𝟙_ X.Modules, U)) : ofUnitSection V ((𝟙_ X.Modules).presheaf.map i.op m) = X.presheaf.map i.op (ofUnitSection U m) := rfl
lemma ofUnitSection_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(𝟙_ X.Modules, U)) : ofUnitSection U (r • m) = r * ofUnitSection U m := rfl
def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)
def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))
def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))
lemma coeff_mem_coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : coeff s U φ ∈ coeffIdeal s U :=
  Ideal.subset_span ⟨φ, rfl⟩
def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}
end AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaPalomarTheta473
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def thetaIdeal : E.curve.IdealSheafData := P.point.val.ker
def thetaLine : E.curve.Modules := (thetaIdeal E P).invModule
def thetaMap : (𝟙_ E.curve.Modules) ⟶ thetaLine E P :=
  (thetaIdeal E P).invModuleSection
def pushforwardLine : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E P)
def generator : (𝟙_ S.Modules) ⟶ pushforwardLine E P :=
  E.p.unitToPushforwardUnit ≫ (Scheme.Modules.pushforward E.p).map (thetaMap E P)
def originGenerator : (𝟙_ S.Modules) ⟶ (Scheme.Modules.pullback E.zero).obj (thetaLine E P) :=
  (Scheme.Modules.pullbackUnitIso E.zero).inv ≫
    (Scheme.Modules.pullback E.zero).map (thetaMap E P)
def IsRigidification (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Prop := originGenerator E P ≫ e.hom = 𝟙 _
def evaluation (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : pushforwardLine E P ⟶ (𝟙_ S.Modules) :=
  (Scheme.Modules.pushforward E.p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction E.zero).unit.app (thetaLine E P) ≫
      (Scheme.Modules.pushforward E.zero).map e.hom) ≫
    (Scheme.Modules.pushforwardComp E.zero E.p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (E.law.one (𝟙 S)).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId S).hom.app _
def evaluationSection (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Γ(Scheme.Modules.dual (pushforwardLine E P), ⊤) :=
  (ArithmeticThetaPalomarDual465.globalSectionsEquiv (pushforwardLine E P)
    (𝟙_ S.Modules)).symm (evaluation E P e)
theorem evenPointThetaEvaluation :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), (ArithmeticThetaPalomarTheta473.thetaIdeal E P).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaPalomarTheta473.thetaLine E P) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaPalomarTheta473.thetaMap E P) = ArithmeticThetaPalomarTheta473.thetaIdeal E P ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarTheta473.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaPalomarTheta473.IsRigidification E P e) ∧ CategoryTheory.IsIso (ArithmeticThetaPalomarTheta473.generator E P) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarTheta473.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaPalomarTheta473.IsRigidification E P e → CategoryTheory.IsIso (ArithmeticThetaPalomarTheta473.evaluation E P e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaPalomarTheta473.generator E P) (ArithmeticThetaPalomarTheta473.evaluation E P e) = CategoryTheory.CategoryStruct.id (SheafOfModules.unit S.ringCatSheaf) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaPalomarTheta473.pushforwardLine E P)) ⊤ (ArithmeticThetaPalomarTheta473.evaluationSection E P e)) := by
  sorry
end ArithmeticThetaPalomarTheta473
