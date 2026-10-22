module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
section OriginalIdealContext1634
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
end OriginalIdealContext1634
open AlgebraicGeometry
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace NeronModelInfra
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) := {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
namespace HomogeneousIdealQuotientGrading
open DirectSum
section Engine
variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)
def pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) : 𝒜 i →+ ℬ i := AddMonoidHom.codRestrict
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i) (fun a => hmem i a a.2)
@[simp] lemma pieceHom_coe (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) (a : 𝒜 i) : (pieceHom 𝒜 I ℬ hmem i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := by sorry
omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in
theorem gradedMonoidOfImages [AddMonoid ι] [SetLike.GradedMonoid 𝒜] (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) : SetLike.GradedMonoid ℬ := by sorry
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (y : ⨁ i, 𝒜 i) : DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y) = Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 y) := by sorry
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) : A →+ ⨁ i, ℬ i :=
  (DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : preDecompose 𝒜 I ℬ hmem a = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (decompose 𝒜 a) := rfl
lemma preDecompose_apply_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) (i : ι) : preDecompose 𝒜 I ℬ hmem a i = pieceHom 𝒜 I ℬ hmem i (decompose 𝒜 a i) := by
  rw [preDecompose_apply, DirectSum.map_apply]
lemma preDecompose_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) {i : ι} {a : A} (ha : a ∈ 𝒜 i) : preDecompose 𝒜 I ℬ hmem a = DirectSum.of (fun j => ℬ j) i ⟨Ideal.Quotient.mk I a, hmem i a ha⟩ := by sorry
lemma coeAddMonoidHom_preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = Ideal.Quotient.mk I a := by sorry
lemma preDecompose_eq_zero_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) : preDecompose 𝒜 I ℬ hmem a = 0 := by sorry
def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem) (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
@[simp] lemma quotDecompose_mk (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) (a : A) : quotDecompose 𝒜 I ℬ hmem hI (Ideal.Quotient.mk I a) = preDecompose 𝒜 I ℬ hmem a := by sorry
@[reducible] def decompositionOfImages (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition ℬ :=
  DirectSum.Decomposition.ofAddHom ℬ (quotDecompose 𝒜 I ℬ hmem hI)
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotDecompose_mk,
        coeAddMonoidHom_preDecompose])
    (by
      refine DirectSum.addHom_ext fun i b => ?_
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
      obtain ⟨a, ha, hab⟩ := hsurj i (b : A ⧸ I) b.2
      rw [← hab, quotDecompose_mk, preDecompose_of_mem 𝒜 I ℬ hmem ha]
      exact congrArg _ (Subtype.ext hab))
@[reducible] def gradedRingOfImages (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (hI : I.IsHomogeneous 𝒜) : GradedRing ℬ where
  toGradedMonoid := gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition := decompositionOfImages 𝒜 I ℬ hmem hsurj hI
end Engine
section SubmoduleVersion
variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)
def quotGradingSubmodule (i : ι) : Submodule R (A ⧸ I) := (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff {i : ι} {x : A ⧸ I} : x ∈ quotGradingSubmodule 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by sorry
lemma mk_mem_quotGradingSubmodule {i : ι} {a : A} (ha : a ∈ 𝒜 i) : Ideal.Quotient.mk I a ∈ quotGradingSubmodule 𝒜 I i :=
  (mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a, ha, rfl⟩
instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotGradingSubmodule 𝒜 I) := by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I) (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J : HomogeneousIdeal 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal) :=
  quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
end SubmoduleVersion
end HomogeneousIdealQuotientGrading
namespace ProjWeierstrassCubicPrime
open MvPolynomial
variable {F : Type*} [CommRing F]
theorem isHomogeneous_polynomial (V : WeierstrassCurve.Projective F) : V.polynomial.IsHomogeneous 3 := by sorry
end ProjWeierstrassCubicPrime
namespace WeierstrassProjModel
open MvPolynomial HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R : Type*} [CommRing R]
theorem span_polynomial_isHomogeneousCR (V : WeierstrassCurve.Projective R) : (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) := by sorry
def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) : (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl
abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ := MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) : ℕ → Submodule R (ProjModelRingCR V) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme := Proj (projModelGradingCR V)
def projModelStrCR (V : WeierstrassCurve.Projective R) : Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projModelGradingCR V) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
end Carrier
set_option hygiene false
set_option quotPrecheck false
local notation "gh1567_0" => (@HomogeneousIdeal.toIdeal.{0, u_1, u_1} Nat (@Submodule.{u_1, u_1} R (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))) (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Semiring.toModule.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))))) (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat Nat.instAddMonoid)) (@Submodule.setLike.{u_1, u_1} R (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))) (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Semiring.toModule.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))))) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1.{u_1} R inst) (@MvPolynomial.homogeneousSubmodule.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W)))
local notation "gh1567_1" => (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
local notation "gh1567_2" => (@MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst))
local notation "gh1567_3" => (@Submodule.Quotient.module'.{u_1, u_1, u_1} gh1567_2 gh1567_2 (@AddMonoidAlgebra.ring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toRing.{u_1} R inst) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)) (@AddMonoidAlgebra.addCommGroup.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toRing.{u_1} R inst)) (@Semiring.toModule.{u_1} gh1567_2 (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))) R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Algebra.toSMul.{u_1, u_1} R gh1567_2 (@CommRing.toCommSemiring.{u_1} R inst) (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)) (@AddMonoidAlgebra.algebra.{u_1, u_1, 0} R R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toCommSemiring.{u_1} R inst) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Algebra.id.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))) (@MvPolynomial.instModuleSelf.{0, u_1} gh1567_1 R inst) (@WeierstrassProjModel.kw_lrComul_tensorProj._proof_1.{u_1} R inst) gh1567_0)
local notation "gh1567_4" => (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
local notation "gh1567_5" => (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))
local notation "gh1567_6" => (@Submodule.Quotient.addCommGroup.{u_1, u_1} gh1567_2 gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid))) (@Ring.toAddCommGroup.{u_1} gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid)))) (@Semiring.toModule.{u_1} gh1567_2 (@Ring.toSemiring.{u_1} gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid))))) gh1567_0)
local notation "gh1567_7" => (@AddMonoidAlgebra.ring.{u_1, 0} R gh1567_4 (@CommRing.toRing.{u_1} R inst) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))
local notation "gh1567_8" => (@WeierstrassProjModel.ProjModelRingCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W))
local notation "gh1567_9" => (@AddMonoidAlgebra.semiring.{u_1, 0} R gh1567_4 gh1567_5 (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))
local notation "gh1567_10" => (@Submodule.Quotient.addCommGroup.{u_1, u_1} gh1567_2 gh1567_2 gh1567_7 (@AddMonoidAlgebra.addCommGroup.{u_1, 0} R gh1567_4 (@CommRing.toRing.{u_1} R inst)) (@Semiring.toModule.{u_1} gh1567_2 gh1567_9) gh1567_0)
local notation "gh1567_11" => (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R gh1567_4 gh1567_5 gh1567_5 (@Semiring.toModule.{u_1} R gh1567_5))
local notation "gh1567_12" => (@Algebra.toSMul.{u_1, u_1} R gh1567_2 (@CommRing.toCommSemiring.{u_1} R inst) gh1567_9 (@AddMonoidAlgebra.algebra.{u_1, u_1, 0} R R gh1567_4 (@CommRing.toCommSemiring.{u_1} R inst) gh1567_5 (@Algebra.id.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)))
local notation "gh1567_13" => (@OfNat.ofNat.{u_1} R (nat_lit 0) (@Zero.toOfNat0.{u_1} R (@MulZeroClass.toZero.{u_1} R (@instMulZeroClassOfSemiring.{u_1} R gh1567_5))))
local notation "gh1567_14" => (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R gh1567_4 gh1567_5)
local notation "gh1567_15" => (@Ring.toSemiring.{u_1} gh1567_2 gh1567_7)
local notation "gh1567_16" => (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst))
set_option quotPrecheck true
set_option hygiene true
theorem _root_.WeierstrassProjModel.kw_lrSixU_toE._proof_1 : @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (@One.toOfNat1.{0} Nat Nat.instOne)) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAddNegDiag_negSubstGen._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrComul_tensorProj._proof_1.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R], @IsScalarTower.{u_1, u_1, u_1} R gh1567_2 gh1567_2 gh1567_12 (@instSMulOfMul.{u_1} gh1567_2 (@Distrib.toMul.{u_1} gh1567_2 (@instDistribOfSemiring.{u_1} gh1567_2 gh1567_9))) gh1567_12 := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R], @AddSubmonoidClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) gh1567_2 (@AddMonoid.toAddZeroClass.{u_1} gh1567_2 (@AddCommMonoid.toAddMonoid.{u_1} gh1567_2 gh1567_14)) (@Submodule.setLike.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) := by sorry
theorem _root_.WeierstrassProjModel.kwYEvalRingHom._proof_2.{u_1} : ∀ (R : Type u_1) [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R) (a : @MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) (ha : @Membership.mem.{u_1, u_1} gh1567_2 (@Ideal.{u_1} gh1567_2 gh1567_15) (@SetLike.instMembership.{u_1, u_1} (@Ideal.{u_1} gh1567_2 gh1567_15) gh1567_2 (@Submodule.setLike.{u_1, u_1} gh1567_2 gh1567_2 gh1567_15 (@Semiring.toAddCommMonoid.{u_1} gh1567_2 gh1567_15) (@Semiring.toModule.{u_1} gh1567_2 gh1567_15))) gh1567_0 a), @Eq.{u_1 + 1} R (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (@RingHom.{u_1, u_1} gh1567_2 R (@Semiring.toNonAssocSemiring.{u_1} gh1567_2 gh1567_15) (@Semiring.toNonAssocSemiring.{u_1} R gh1567_5)) gh1567_2 (fun (x : @MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) => R) (@RingHom.instFunLike.{u_1, u_1} gh1567_2 R (@Semiring.toNonAssocSemiring.{u_1} gh1567_2 gh1567_15) (@Semiring.toNonAssocSemiring.{u_1} R gh1567_5)) (@MvPolynomial.eval.{u_1, 0} R gh1567_1 (@CommRing.toCommSemiring.{u_1} R inst) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) gh1567_13 (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R (@AddGroupWithOne.toAddMonoidWithOne.{u_1} R (@Ring.toAddGroupWithOne.{u_1} R (@CommRing.toRing.{u_1} R inst)))))) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) gh1567_13 (@Matrix.vecEmpty.{u_1} R))))) a) gh1567_13 := by sorry
theorem _root_.WeierstrassProjModel.kw_lrChart_aux._proof_1.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @AddSubgroupClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_10) gh1567_3) gh1567_8 (@AddGroup.toSubNegMonoid.{u_1} gh1567_8 (@AddCommGroup.toAddGroup.{u_1} gh1567_8 gh1567_10)) (@Submodule.setLike.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_10) gh1567_3) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAdd_comulHom._proof_3.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @Ideal.IsTwoSided.{u_1} gh1567_2 (@CommSemiring.toSemiring.{u_1} gh1567_2 (@CommRing.toCommSemiring.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid)))) (@HomogeneousIdeal.toIdeal.{0, u_1, u_1} Nat (@Submodule.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) gh1567_2 gh1567_9 (@Submodule.setLike.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) (@WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} R inst) (@MvPolynomial.homogeneousSubmodule.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W))) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrChart_aux._proof_2.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @AddSubgroupClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_6) gh1567_3) gh1567_8 (@AddGroup.toSubNegMonoid.{u_1} gh1567_8 (@AddCommGroup.toAddGroup.{u_1} gh1567_8 gh1567_6)) (@Submodule.setLike.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_6) gh1567_3) := by sorry
run_cmd do
  for n in [`WeierstrassProjModel.kw_lrSixU_toE._proof_1,`WeierstrassProjModel.kw_lrAddNegDiag_negSubstGen._proof_1,`WeierstrassProjModel.kw_lrComul_tensorProj._proof_1,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_2,`WeierstrassProjModel.kwYEvalRingHom._proof_2,`WeierstrassProjModel.kw_lrChart_aux._proof_1,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_3,`WeierstrassProjModel.kw_lrChart_aux._proof_2] do
    let env ← Lean.getEnv
    let some ci := env.find? n | throwError "Missing support obligation {n}"
    let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
      { s with lemmas := s.lemmas.insert key (ci.name, ci.levelParams) }
variable (R : Type u) [CommRing R]
section ZeroSection
variable (W : WeierstrassCurve R)
open MvPolynomial in
theorem kw_mk_X1_mem_one_CR : Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 1 : MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
open MvPolynomial in
def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact WeierstrassCurve.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1 : kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by sorry
def kwYChartEval : HomogeneousLocalization.Away (projModelGradingCR W.toProjective) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))) (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap : (kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R := by sorry
theorem kwYChartEval_section : (kwYChartEval R W).comp ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by sorry
def kwZeroSect : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      kwYChartEval_section, CommRingCat.ofHom_id, Spec.map_id]⟩
end ZeroSection
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
end WeierstrassProjModel
namespace ArithmeticThetaRelativeKatoR0169
open NeronModelInfra
variable (R : Type u) [CommRing R]
abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} := WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) := WeierstrassProjModel.projModelStrCR W.toProjective
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W := (WeierstrassProjModel.kwZeroSect R W).val
abbrev Law (W : WeierstrassCurve R) := WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop := (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)),
    (G.one t).val = t ≫ origin R W) ∧ (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (structureMap R W)), G.mul t x y = G.mul t y x)
end ArithmeticThetaRelativeKatoR0169
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
end WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
namespace ArithmeticThetaRelativeDiscriminantR0171
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
structure FullLevel (L : ℕ) {T : Scheme.{u}} (t : T ⟶ Base R) where
  x : SchemeHomOver t (structureMap R W)
  y : SchemeHomOver t (structureMap R W)
  killed_x : G.nsmul t L x = G.one t
  killed_y : G.nsmul t L y = G.one t
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val)
      (Set.range (origin R W))
end ArithmeticThetaFullLevelCoverR0175
namespace ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))
def twoLabel (i : Fin 3) : Base R ⟶ Curve R W :=
  ![(G.nsmul (𝟙 _) (L/2) M.x).val,
    (G.nsmul (𝟙 _) (L/2) M.y).val,
    (G.mul (𝟙 _) (G.nsmul (𝟙 _) (L/2) M.x)
      (G.nsmul (𝟙 _) (L/2) M.y)).val] i
end ArithmeticThetaGlobalFourTorsionR0190
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
instance Scheme.Hom.opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
namespace ArithmeticThetaPalomarRigidification484
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (M : FullLevel R W G 4 (𝟙 (Base R)))
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def evenPoint : Base R ⟶ Curve R W := twoLabel R W G 4 M 2
def thetaIdeal : (Curve R W).IdealSheafData := (evenPoint R W G M).ker
def thetaLine : (Curve R W).Modules := (thetaIdeal R W G M).invModule
def thetaMap : (𝟙_ (Curve R W).Modules) ⟶ thetaLine R W G M := (thetaIdeal R W G M).invModuleSection
def originGenerator : (𝟙_ (Base R).Modules) ⟶ (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) :=
  (Scheme.Modules.pullbackUnitIso (origin R W)).inv ≫ (Scheme.Modules.pullback (origin R W)).map (thetaMap R W G M)
def IsRigidification (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅ (𝟙_ (Base R).Modules)) : Prop := originGenerator R W G M ≫ e.hom = 𝟙 _
theorem arbitraryEvenThetaRigidification :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (ArithmeticThetaPalomarRigidification484.thetaIdeal R W G M).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaPalomarRigidification484.thetaLine R W G M) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaPalomarRigidification484.thetaMap R W G M) = ArithmeticThetaPalomarRigidification484.thetaIdeal R W G M ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaPalomarRigidification484.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaPalomarRigidification484.IsRigidification R W G M e) := by sorry
end ArithmeticThetaPalomarRigidification484
