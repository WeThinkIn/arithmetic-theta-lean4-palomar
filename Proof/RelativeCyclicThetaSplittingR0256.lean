module

public import RelativeThetaRelationsDefinitionsR0256
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
public import Definitions.Def_AlgebraicGeometry_ThetaGroup
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_mul

@[expose] public section

/-! The relative cyclic theta splitting: normalized lifts, zero, addition, and period.
The period law uses the tensor-square presentation of the actual even-degree theta line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

namespace ArithmeticThetaRelativeThetaRelationsR0256
namespace RelativeCyclicThetaSplittingR0256
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255

namespace EvenInversion
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open MonoidalCategory
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

/-- An involution of a line acts trivially on its tensor square, over any base. -/
lemma tensor_involution {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (δ : M ≅ M) (hδ : δ ≪≫ δ = Iso.refl M) : δ ⊗ᵢ δ = Iso.refl (M ⊗ M) := by
  obtain ⟨c, hc⟩ := RelativeMidpointSymmetricThetaLift.aut_scalar hM δ
  have hc2 : (c : Γ(X, ⊤)) * (c : Γ(X, ⊤)) = 1 := by
    apply RelativeMidpointSymmetricThetaLift.smulHom_injective hM
    change smulHom ((c : Γ(X, ⊤)) * (c : Γ(X, ⊤))) M = smulHom 1 M
    rw [smulHom_mul, smulHom_one]
    have H := congrArg Iso.hom hδ
    rw [← hc] at H
    exact H
  apply Iso.ext
  apply Scheme.Modules.tensor_hom_ext_monoidalV2
  intro U x y
  rw [← hc]
  change ((smulHom (c : Γ(X, ⊤)) M) ⊗ₘ (smulHom (c : Γ(X, ⊤)) M)).app U
    (Scheme.Modules.tensorSections x y) = Scheme.Modules.tensorSections x y
  rw [Scheme.Modules.tensorHom_app_tensorSections_monoidalV2, smulHom_app_apply,
    smulHom_app_apply, Scheme.Modules.tensorSections_smul_left,
    Scheme.Modules.tensorSections_smul_right, smul_smul]
  have hU : resTop (c : Γ(X, ⊤)) U * resTop (c : Γ(X, ⊤)) U = 1 := by
    simp only [resTop, ← map_mul, hc2, map_one]
  rw [hU, one_smul]

/-- Restriction of an involutive lift to a fixed section remains involutive. -/
lemma fixed_involution {S X : Scheme.{u}} (e : S ⟶ X) (f : X ⟶ X)
    (he : e ≫ f = e) (hf : f ≫ f = 𝟙 X) (M : X.Modules)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (hα : (Scheme.Modules.pullback f).mapIso α ≪≫ α =
      FixedPointPullback.squareComparison f hf M) :
    let δ := ((FixedPointPullback.compare e f e he).app M).symm ≪≫
      (Scheme.Modules.pullback e).mapIso α
    δ ≪≫ δ = Iso.refl _ := by
  dsimp only
  apply Iso.ext
  let C := FixedPointPullback.compare e f e he
  change C.inv.app M ≫ (Scheme.Modules.pullback e).map α.hom ≫
    C.inv.app M ≫ (Scheme.Modules.pullback e).map α.hom = 𝟙 _
  rw [← Category.assoc ((Scheme.Modules.pullback e).map α.hom), C.inv.naturality α.hom]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc]
  apply (cancel_epi (C.hom.app ((Scheme.Modules.pullback f).obj M) ≫ C.hom.app M)).mp
  have hcomp := FixedPointPullback.compare_comp e f f e (𝟙 X) e he hf he M
  rw [FixedPointPullback.compare_id] at hcomp
  have hs := congrArg (fun i => (Scheme.Modules.pullback e).map i.hom) hα
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    FixedPointPullback.squareComparison, Iso.app_hom] at hs
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id,
    Functor.comp_map] using hs.trans hcomp.symm

/-- The tensor comparison respects a specified equality of composite maps. -/
lemma compare_tensor {S X Y : Scheme.{u}} (e : S ⟶ X) (f : X ⟶ Y)
    (ef : S ⟶ Y) (h : e ≫ f = ef) (M N : Y.Modules) :
    (FixedPointPullback.compare e f ef h).app (M ⊗ N) =
      (Scheme.Modules.pullback e).mapIso (Scheme.Modules.pullbackTensorObjIso f M N) ≪≫
        Scheme.Modules.pullbackTensorObjIso e ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) ≪≫
        ((FixedPointPullback.compare e f ef h).app M ⊗ᵢ
          (FixedPointPullback.compare e f ef h).app N) ≪≫
        (Scheme.Modules.pullbackTensorObjIso ef M N).symm := by
  subst ef
  simpa [FixedPointPullback.compare, Scheme.Modules.pullbackCongr] using
    Scheme.Modules.pullbackComp_app_tensorObj e f M N

lemma tensor_naturality {S X : Scheme.{u}} (e : S ⟶ X)
    {M N : X.Modules} (α : M ≅ N) :
    (Scheme.Modules.pullback e).mapIso (α ⊗ᵢ α) ≪≫
      Scheme.Modules.pullbackTensorObjIso e N N =
    Scheme.Modules.pullbackTensorObjIso e M M ≪≫
      ((Scheme.Modules.pullback e).mapIso α ⊗ᵢ (Scheme.Modules.pullback e).mapIso α) := by
  apply Iso.ext
  exact (Functor.OplaxMonoidal.δ_natural (Scheme.Modules.pullback e) α.hom α.hom).symm

set_option maxHeartbeats 800000 in
/-- The square of an involutive line lift is the identity at every fixed section. -/
lemma tensor_lift_fixed {S X : Scheme.{u}} (e : S ⟶ X) (f : X ⟶ X)
    (he : e ≫ f = e) (hf : f ≫ f = 𝟙 X) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (hα : (Scheme.Modules.pullback f).mapIso α ≪≫ α =
      FixedPointPullback.squareComparison f hf M) :
    (Scheme.Modules.pullback e).mapIso
      (Scheme.Modules.pullbackTensorObjIso f M M ≪≫ (α ⊗ᵢ α)) =
      (FixedPointPullback.compare e f e he).app (M ⊗ M) := by
  let C := (FixedPointPullback.compare e f e he).app M
  let B := (Scheme.Modules.pullback e).mapIso α
  let δ := C.symm ≪≫ B
  have hδ := fixed_involution e f he hf M α hα
  have ht := tensor_involution (hM.pullback e) δ hδ
  have hBC : (B ⊗ᵢ B) = (C ⊗ᵢ C) := by
    apply Iso.ext
    apply (cancel_epi (C.inv ⊗ₘ C.inv)).mp
    simpa only [δ, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
      tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id, Iso.refl_hom] using
      congrArg Iso.hom ht
  have hn := tensor_naturality e α
  have hc := compare_tensor e f e he M M
  have H : (Scheme.Modules.pullback e).mapIso
      (Scheme.Modules.pullbackTensorObjIso f M M ≪≫ (α ⊗ᵢ α)) ≪≫
      Scheme.Modules.pullbackTensorObjIso e M M =
      (FixedPointPullback.compare e f e he).app (M ⊗ M) ≪≫
        Scheme.Modules.pullbackTensorObjIso e M M := by
    rw [Functor.mapIso_trans, Iso.trans_assoc, hn, hc]
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    exact congrArg (fun i =>
      (Scheme.Modules.pullback e).mapIso (Scheme.Modules.pullbackTensorObjIso f M M) ≪≫
        Scheme.Modules.pullbackTensorObjIso e ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj M) ≪≫ i) hBC
  apply Iso.ext
  exact (cancel_mono (Scheme.Modules.pullbackTensorObjIso e M M).hom).mp
    (congrArg Iso.hom H)

/-- Fixed-section normalization is invariant under an actual sheaf isomorphism. -/
lemma transport_fixed {S X : Scheme.{u}} (e : S ⟶ X) (f : X ⟶ X)
    (he : e ≫ f = e) {L M : X.Modules} (η : L ≅ M)
    (β : (Scheme.Modules.pullback f).obj M ≅ M)
    (hβ : (Scheme.Modules.pullback e).mapIso β =
      (FixedPointPullback.compare e f e he).app M) :
    (Scheme.Modules.pullback e).mapIso
      ((Scheme.Modules.pullback f).mapIso η ≪≫ β ≪≫ η.symm) =
      (FixedPointPullback.compare e f e he).app L := by
  apply Iso.ext
  have hb := congrArg Iso.hom hβ
  simp only [Functor.mapIso_hom, Iso.app_hom] at hb
  simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp, Iso.symm_hom]
  rw [hb]
  change (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback e).map η.hom ≫
    (FixedPointPullback.compare e f e he).hom.app M ≫
      (Scheme.Modules.pullback e).map η.inv = _
  rw [← Category.assoc, (FixedPointPullback.compare e f e he).hom.naturality η.hom]
  simp only [Category.assoc, ← Functor.map_comp, η.hom_inv_id, Iso.app_hom]
  rw [(Scheme.Modules.pullback e).map_id, Category.comp_id]

end EvenInversion

namespace TotalLift
open CategoryTheory.Bicategory

/-- The actual sheaf pullback pseudofunctor, in the original universe. -/
def fibration : Pseudofunctor (LocallyDiscrete (Scheme.{u}ᵒᵖ)) Cat.{u, u+1} :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

abbrev Total := Pseudofunctor.CoGrothendieck fibration.{u}
abbrev pair {X : Scheme.{u}} (M : X.Modules) : Total.{u} := ⟨X, M⟩

lemma compComparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (fibration.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp f g).hom.app M := by
  simp [fibration, Pseudofunctor.comp_mapComp]
  exact Category.id_comp _

lemma idComparison (X : Scheme.{u}) (M : X.Modules) :
    (fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackId X).inv.app M := by
  simp [fibration, Pseudofunctor.comp_mapId]

/-- A lift represented by its inverse in the actual category of module sheaves. -/
def lift {X : Scheme.{u}} (M : X.Modules) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) : pair M ⟶ pair M := ⟨f, α.inv⟩

def aut {X : Scheme.{u}} (M : X.Modules) (f : X ≅ X)
    (α : (Scheme.Modules.pullback f.hom).obj M ≅ M) : Aut (pair M) :=
  Pseudofunctor.CoGrothendieck.isoMk f α.symm

lemma aut_hom {X : Scheme.{u}} (M : X.Modules) (f : X ≅ X)
    (α : (Scheme.Modules.pullback f.hom).obj M ≅ M) : (aut M f α).hom = lift M f.hom α := rfl

lemma lift_injective {X : Scheme.{u}} (M : X.Modules) (f : X ⟶ X) :
    Function.Injective (lift M f) := by
  intro α β h
  have hi : α.inv = β.inv := by
    simpa only [lift, eqToHom_refl, Category.comp_id] using
      Pseudofunctor.CoGrothendieck.Hom.congr h
  exact Iso.ext_inv hi

lemma lift_comp {X : Scheme.{u}} (M : X.Modules) (f g : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (β : (Scheme.Modules.pullback g).obj M ≅ M) :
    lift M (f ≫ g) (((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ α) = lift M f α ≫ lift M g β := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
  simp only [lift, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    eqToHom_refl, Category.comp_id, Category.assoc]

lemma lift_change {X : Scheme.{u}} (M : X.Modules) {f g : X ⟶ X} (h : f = g)
    (α : (Scheme.Modules.pullback g).obj M ≅ M) :
    lift M f ((Scheme.Modules.pullbackCongr h).app M ≪≫ α) = lift M g α := by
  subst g
  congr 1

/-- The tautological morphism from the pullback along a section. -/
def sectionHom {S X : Scheme.{u}} (M : X.Modules) (e : S ⟶ X) :
    pair ((Scheme.Modules.pullback e).obj M) ⟶ pair M := ⟨e, 𝟙 _⟩

lemma lift_id {X : Scheme.{u}} (M : X.Modules) :
    lift M (𝟙 X) ((Scheme.Modules.pullbackId X).app M) = 𝟙 (pair M) := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
  simp [lift]

lemma congr_inv {S X : Scheme.{u}} {f g : S ⟶ X} (h : f = g) (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst g
  rfl

lemma fixed_of_normalized {S X : Scheme.{u}} (M : X.Modules) (e : S ⟶ X)
    (f : X ⟶ X) (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (h : e ≫ f = e)
    (hα : (Scheme.Modules.pullback e).mapIso α =
      (Scheme.Modules.pullbackComp e f).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M) :
    sectionHom M e ≫ lift M f α = sectionHom M e := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h
  have hi := congrArg Iso.inv hα
  change (Scheme.Modules.pullback e).map α.inv =
    (Scheme.Modules.pullbackCongr h).inv.app M ≫ (Scheme.Modules.pullbackComp e f).inv.app M at hi
  change (𝟙 _ ≫ (Scheme.Modules.pullback e).map α.inv ≫
    (Scheme.Modules.pullbackComp e f).hom.app M) = 𝟙 _ ≫ _
  rw [hi, Category.id_comp, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, congr_inv]

lemma normalized_of_fixed {S X : Scheme.{u}} (M : X.Modules) (e : S ⟶ X)
    (f : X ⟶ X) (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (H : sectionHom M e ≫ lift M f α = sectionHom M e) :
    ∃ h : e ≫ f = e, (Scheme.Modules.pullback e).mapIso α =
      (Scheme.Modules.pullbackComp e f).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M := by
  have h : e ≫ f = e := congrArg Pseudofunctor.CoGrothendieck.Hom.base H
  refine ⟨h, ?_⟩
  apply Iso.ext_inv
  have hi := Pseudofunctor.CoGrothendieck.Hom.congr H
  change 𝟙 _ ≫ (Scheme.Modules.pullback e).map α.inv ≫
    (Scheme.Modules.pullbackComp e f).hom.app M = 𝟙 _ ≫ eqToHom _ at hi
  simp only [Category.id_comp] at hi
  change (Scheme.Modules.pullback e).map α.inv =
    (Scheme.Modules.pullbackCongr h).inv.app M ≫ (Scheme.Modules.pullbackComp e f).inv.app M
  apply (cancel_mono ((Scheme.Modules.pullbackComp e f).hom.app M)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, congr_inv]
  exact hi

/-- A normalized reflection fixes every morphism above its fixed section. -/
lemma fixes_all_over {X : Scheme.{u}} (M : X.Modules) (F : pair M ⟶ pair M)
    {T : Total.{u}} (j : T ⟶ pair M)
    (h : sectionHom M j.base ≫ F = sectionHom M j.base) : j ≫ F = j := by
  have hb : j.base ≫ F.base = j.base := congrArg Pseudofunctor.CoGrothendieck.Hom.base h
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb
  have hf := Pseudofunctor.CoGrothendieck.Hom.congr h
  change (𝟙 _ ≫ (Scheme.Modules.pullback j.base).map F.fiber ≫
    (Scheme.Modules.pullbackComp j.base F.base).hom.app M) = 𝟙 _ ≫ eqToHom _ at hf
  simp only [Category.id_comp] at hf
  change j.fiber ≫ (Scheme.Modules.pullback j.base).map F.fiber ≫
    (Scheme.Modules.pullbackComp j.base F.base).hom.app M = j.fiber ≫ eqToHom _
  rw [hf]

/-- Conjugation preserves normalization at the transported actual section. -/
lemma conjugate_fixed {S X : Scheme.{u}} (M : X.Modules) (e : S ⟶ X)
    (T : pair M ≅ pair M) (F : pair M ⟶ pair M)
    (h : sectionHom M ((sectionHom M e ≫ T.hom).base) ≫ F =
      sectionHom M ((sectionHom M e ≫ T.hom).base)) :
    sectionHom M e ≫ (T.hom ≫ F ≫ T.inv) = sectionHom M e := by
  have H := fixes_all_over M F (sectionHom M e ≫ T.hom) h
  calc
    _ = ((sectionHom M e ≫ T.hom) ≫ F) ≫ T.inv := by simp only [Category.assoc]
    _ = (sectionHom M e ≫ T.hom) ≫ T.inv := by rw [H]
    _ = sectionHom M e := by simp

lemma lift_square {X : Scheme.{u}} (M : X.Modules) (f : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (h : f ≫ f = 𝟙 X)
    (hα : (Scheme.Modules.pullback f).mapIso α ≪≫ α =
      (Scheme.Modules.pullbackComp f f).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M ≪≫ (Scheme.Modules.pullbackId X).app M) :
    lift M f α ≫ lift M f α = 𝟙 (pair M) := by
  rw [← lift_comp]
  have he : ((Scheme.Modules.pullbackComp f f).app M).symm ≪≫
      (Scheme.Modules.pullback f).mapIso α ≪≫ α =
      (Scheme.Modules.pullbackCongr h).app M ≪≫ (Scheme.Modules.pullbackId X).app M := by
    rw [hα]
    simp
  rw [he, lift_change, lift_id]

def inverseLift {X : Scheme.{u}} (M : X.Modules) (e : X ≅ X)
    (α : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (Scheme.Modules.pullback e.inv).obj M ≅ M :=
  ((Scheme.Modules.pullback e.inv).mapIso α).symm ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId X).app M

lemma lift_inverse {X : Scheme.{u}} (M : X.Modules) (e : X ≅ X)
    (α : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    lift M e.inv (inverseLift M e α) = (aut M e α).inv := by
  apply (cancel_mono (aut M e α).hom).mp
  rw [Iso.inv_hom_id, aut_hom, ← lift_comp]
  have he : ((Scheme.Modules.pullbackComp e.inv e.hom).app M).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso α ≪≫ inverseLift M e α =
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId X).app M := by
    simp [inverseLift]
  rw [he, lift_change, lift_id]

lemma conjugate_lift {X : Scheme.{u}} (M : X.Modules) (e : X ≅ X)
    (α : (Scheme.Modules.pullback e.hom).obj M ≅ M)
    (f : X ⟶ X) (β : (Scheme.Modules.pullback f).obj M ≅ M)
    (g : X ⟶ X) (hg : g = e.hom ≫ f ≫ e.inv) :
    ∃ γ : (Scheme.Modules.pullback g).obj M ≅ M,
      lift M g γ = (aut M e α).hom ≫ lift M f β ≫ (aut M e α).inv := by
  let δ := ((Scheme.Modules.pullbackComp f e.inv).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (inverseLift M e α) ≪≫ β
  let γ := (Scheme.Modules.pullbackCongr hg).app M ≪≫
    ((Scheme.Modules.pullbackComp e.hom (f ≫ e.inv)).app M).symm ≪≫
      (Scheme.Modules.pullback e.hom).mapIso δ ≪≫ α
  refine ⟨γ, ?_⟩
  dsimp only [γ]
  rw [lift_change, lift_comp]
  dsimp only [δ]
  rw [lift_comp, lift_inverse, aut_hom]

/-- The normalized-reflection recurrence determines all nonnegative powers. -/
lemma powers_of_reflections {C : Type*} [Category C] {X : C} (T I : Aut X)
    (A : ℕ → (X ⟶ X)) (h0 : A 0 = 𝟙 X) (h1 : A 1 = T.hom)
    (hI : I.hom ≫ I.hom = 𝟙 X)
    (hR : (A 1 ≫ I.hom) ≫ (A 1 ≫ I.hom) = 𝟙 X)
    (hstep : ∀ n, A (n+2) ≫ I.hom = T.hom ≫ (A n ≫ I.hom) ≫ T.inv) :
    ∀ n, A n = (T ^ n).hom := by
  have hTI : I.hom ≫ T.hom ≫ I.hom = T.inv := by
    apply (cancel_epi T.hom).mp
    rw [Iso.hom_inv_id]
    simpa only [h1, Category.assoc] using hR
  have hIT : I.hom ≫ T.inv = T.hom ≫ I.hom := by
    rw [← hTI]
    simp only [← Category.assoc, hI, Category.id_comp]
  have hrec (n : ℕ) : A (n+2) = T.hom ≫ A n ≫ T.hom := by
    apply (cancel_mono I.hom).mp
    rw [hstep]
    simp only [Category.assoc, hIT]
  have hp : ∀ n, A n = (T ^ n).hom ∧ A (n+1) = (T ^ (n+1)).hom := by
    intro n
    induction n with
    | zero =>
      constructor
      · rw [pow_zero]; exact h0
      · simpa only [Nat.zero_add, pow_one] using h1
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec, ih.1]
      change T.hom ≫ (T ^ n).hom ≫ T.hom = (T ^ ((n+1)+1)).hom
      rw [pow_succ, pow_succ']
      simp only [Aut.Aut_mul_def, Iso.trans_hom]
  exact fun n => (hp n).1

end TotalLift

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

lemma pullback_identity_left {X : Scheme.{u}} (f : X ⟶ X) (M : X.Modules)
    (β : (Scheme.Modules.pullback f).obj M ≅ M) :
    ((Scheme.Modules.pullbackComp (𝟙 X) f).app M).symm ≪≫
      (Scheme.Modules.pullback (𝟙 X)).mapIso β ≪≫ (Scheme.Modules.pullbackId X).app M =
    (Scheme.Modules.pullbackCongr (Category.id_comp f)).app M ≪≫ β := by
  apply Iso.ext
  have H := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_refl, NatTrans.id_app] at H
  erw [Category.comp_id] at H
  change (Scheme.Modules.pullbackComp (𝟙 X) f).inv.app M ≫
    (Scheme.Modules.pullback (𝟙 X)).map β.hom ≫
      (Scheme.Modules.pullbackId X).hom.app M = β.hom
  rw [(Scheme.Modules.pullbackId X).hom.naturality β.hom, ← Category.assoc, H]
  rfl

lemma identity_reflection_normalized {S X : Scheme.{u}} (o : S ⟶ X)
    (f g : X ⟶ X) (hf : f = 𝟙 X) (M : X.Modules)
    (β : (Scheme.Modules.pullback g).obj M ≅ M)
    (hβ : ∃ h : o ≫ g = o, (Scheme.Modules.pullback o).mapIso β =
      (Scheme.Modules.pullbackComp o g).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M) :
    ∃ h : o ≫ (f ≫ g) = o,
      (Scheme.Modules.pullback o).mapIso
        (((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
          (Scheme.Modules.pullback f).mapIso β ≪≫
            (Scheme.Modules.pullbackCongr hf).app M ≪≫ (Scheme.Modules.pullbackId X).app M) =
      (Scheme.Modules.pullbackComp o (f ≫ g)).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M := by
  subst f
  have hr : (Scheme.Modules.pullbackCongr (rfl : 𝟙 X = 𝟙 X)).app M =
      Iso.refl ((Scheme.Modules.pullback (𝟙 X)).obj M) := rfl
  rw [hr, Iso.refl_trans, pullback_identity_left]
  have hg : (Scheme.Modules.pullbackCongr (Category.id_comp g)).app M =
      Iso.refl ((Scheme.Modules.pullback g).obj M) := rfl
  rw [hg]
  erw [Iso.refl_trans]
  exact hβ

lemma multiple_killed (m : ℕ) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E) (n : ℕ) :
    (multiple E P n).val ≫ E.law.schemeNsmul (2*m) = zero E := by
  apply (killed_iff E _ _).mpr
  have hp := (killed_iff E P (2*m)).mp hP
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  simp only [nsmul_pow] at hp
  change P ^ (2*m) = 1 at hp
  change E.law.nsmul (𝟙 _) (2*m) (E.law.nsmul (𝟙 _) n P) = _
  simp only [nsmul_pow]
  change (P ^ n) ^ (2*m) = 1
  rw [← pow_mul, Nat.mul_comm n, pow_mul, hp, one_pow]

lemma translation_multiple_zero (P : point E) :
    ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P 0) = 𝟙 E.curve := by
  unfold ArithmeticThetaRelativeThetaLiftsR0255.translation multiple
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  simp only [nsmul_pow, pow_zero, one_pow]
  exact E.law.translate_one

lemma translation_multiple_add (P : point E) (a b : ℕ) :
    ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P a) ≫
      ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P b) =
    ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P (a+b)) := by
  unfold ArithmeticThetaRelativeThetaLiftsR0255.translation multiple
  rw [← E.law.translate_mul]
  congr 1
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  simp only [nsmul_pow]
  change (P ^ a) ^ 2 * (P ^ b) ^ 2 = (P ^ (a+b)) ^ 2
  rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.add_mul, pow_add]

lemma translation_multiple_period (m : ℕ) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E) (a : ℕ) :
    ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P (a+m)) =
      ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P a) := by
  unfold ArithmeticThetaRelativeThetaLiftsR0255.translation multiple
  congr 1
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  have hp := (killed_iff E P (2*m)).mp hP
  simp only [nsmul_pow] at hp ⊢
  change P ^ (2*m) = 1 at hp
  rw [← pow_mul, Nat.add_mul, pow_add, Nat.mul_comm m 2, hp, mul_one, pow_mul]

lemma multiple_one (P : point E) : multiple E P 1 = P := by
  unfold multiple
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  simp only [nsmul_pow, pow_one]

def translationIso (P : point E) : E.curve ≅ E.curve where
  hom := ArithmeticThetaRelativeThetaLiftsR0255.translation E P
  inv := E.law.translate (E.law.inv (𝟙 _) (E.law.nsmul (𝟙 _) 2 P))
  hom_inv_id := by
    rw [ArithmeticThetaRelativeThetaLiftsR0255.translation, ← E.law.translate_mul,
      E.law.mul_inv_cancel, E.law.translate_one]
  inv_hom_id := by
    rw [ArithmeticThetaRelativeThetaLiftsR0255.translation, ← E.law.translate_mul,
      E.law.inv_mul_cancel, E.law.translate_one]

lemma midpoint_step (P : point E) (n : ℕ) :
    negative E (multiple E P (n+2)) ≫ ArithmeticThetaRelativeThetaLiftsR0255.translation E P =
      negative E (multiple E P n) := by
  unfold negative ArithmeticThetaRelativeThetaLiftsR0255.translation
  rw [RelativeMidpointSymmetricThetaLift.point_translate]
  have hid : (⟨𝟙 _ ≫ (E.law.nsmul (𝟙 _) 2 P).val, by
      rw [Category.assoc, (E.law.nsmul (𝟙 _) 2 P).property, Category.comp_id]⟩ : point E) =
      E.law.nsmul (𝟙 _) 2 P := Subtype.ext (Category.id_comp _)
  rw [hid]
  congr 1
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  simp only [multiple, nsmul_pow]
  change (P ^ (n+2))⁻¹ * P ^ 2 = (P ^ n)⁻¹
  group

lemma reflection_step (P : point E) (n : ℕ) :
    ArithmeticThetaRelativeThetaLiftsR0255.translation E P ≫ reflection E (multiple E P n) =
      reflection E (multiple E P (n+2)) ≫ ArithmeticThetaRelativeThetaLiftsR0255.translation E P := by
  have hi : ArithmeticThetaRelativeThetaLiftsR0255.translation E P ≫ inverse E ≫
      ArithmeticThetaRelativeThetaLiftsR0255.translation E P = inverse E := by
    letI : IsIso (inverse E) := (RelativeNormalizedThetaInversion.inversionIso E).isIso_hom
    apply (cancel_mono (inverse E)).mp
    simpa only [Category.assoc, reflection, RelativeNormalizedThetaInversion.inverse_square] using
      RelativeMidpointSymmetricThetaLift.reflection_square E P
  have hadd (a b : ℕ) := translation_multiple_add E P a b
  have hleft : ArithmeticThetaRelativeThetaLiftsR0255.translation E P ≫
      ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P n) =
      ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P (n+1)) := by
    simpa only [multiple_one, Nat.add_comm 1 n] using hadd 1 n
  have hright : ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P (n+1)) ≫
      ArithmeticThetaRelativeThetaLiftsR0255.translation E P =
      ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P (n+2)) := by
    simpa only [multiple_one, Nat.add_assoc] using hadd (n+1) 1
  unfold reflection
  rw [← Category.assoc, hleft, ← hright]
  simp only [Category.assoc]
  rw [hi]

lemma negative_multiple_zero (P : point E) : negative E (multiple E P 0) = zero E := by
  unfold negative multiple
  congr 1
  letI := E.law.pointGroup (𝟙 (base (R := R)))
  change (1 : point E)⁻¹ = 1
  exact inv_one

lemma identityLift_midpoint_zero (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    MidpointNormalized E m (multiple E P 0) ι
      (changeMap E m (translation_multiple_zero E P) (identityLift E m)) := by
  unfold MidpointNormalized reflectionLift reflection changeMap identityLift
  exact identity_reflection_normalized _ _ _ (translation_multiple_zero E P) _ ι
    (by rw [negative_multiple_zero E P]; exact hι.1)

/-- The exact even-degree theta line is a square of the half-degree theta line. -/
def thetaLineDoubleIso (k : ℕ) (hk : 0 < k) :
    thetaLine E (k+k) ≅ MonoidalCategory.tensorObj (thetaLine E k) (thetaLine E k) := by
  let L := primitiveThetaLine E
  have hL := primitiveThetaLine_invertible E
  have hpow : Nonempty (L.tensorPow (k+k) ≅
      MonoidalCategory.tensorObj (L.tensorPow k) (L.tensorPow k)) := by
    apply (lineClass_eq_iff _ _ (hL.tensorPow (k+k))
      ((hL.tensorPow k).tensor_monoidalV2 (hL.tensorPow k))).mp
    rw [lineClass_tensor _ _ (hL.tensorPow k) (hL.tensorPow k),
      lineClass_tensorPow L hL, lineClass_tensorPow L hL, pow_add]
  exact thetaLinePowerIso E (k+k) (by omega) ≪≫ hpow.some ≪≫
    MonoidalCategory.tensorIso (thetaLinePowerIso E k hk).symm (thetaLinePowerIso E k hk).symm

variable [Algebra ℚ R] [IsNoetherianRing R]

omit [Algebra ℚ R] [IsNoetherianRing R] in
/-- Conjugation by an actual translation lift shifts the normalized reflection by two. -/
lemma normalized_reflection_step (m : ℕ) (P : point E) (n : ℕ)
    (α : Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P 1)))
    (β : Lift E m (reflection E (multiple E P n)))
    (γ : Lift E m (reflection E (multiple E P (n+2))))
    (hβ : ∃ h : negative E (multiple E P n) ≫ reflection E (multiple E P n) =
        negative E (multiple E P n),
      (Scheme.Modules.pullback (negative E (multiple E P n))).mapIso β =
        fixedComparison E m _ _ h)
    (hγ : ∃ h : negative E (multiple E P (n+2)) ≫ reflection E (multiple E P (n+2)) =
        negative E (multiple E P (n+2)),
      (Scheme.Modules.pullback (negative E (multiple E P (n+2)))).mapIso γ =
        fixedComparison E m _ _ h) :
    TotalLift.lift (thetaLine E m) _ γ =
      (TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) α).hom ≫
        TotalLift.lift (thetaLine E m) _ β ≫
          (TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) α).inv := by
  let e := translationIso E (multiple E P 1)
  let T := TotalLift.aut (thetaLine E m) e α
  have hg : reflection E (multiple E P (n+2)) =
      e.hom ≫ reflection E (multiple E P n) ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    simpa only [e, translationIso, multiple_one] using (reflection_step E P n).symm
  obtain ⟨δ, hδ⟩ := TotalLift.conjugate_lift (thetaLine E m) e α _ β _ hg
  have hδfixed : TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2))) ≫
      TotalLift.lift (thetaLine E m) _ δ =
      TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2))) := by
    rw [hδ]
    apply TotalLift.conjugate_fixed
    change TotalLift.sectionHom (thetaLine E m)
      (negative E (multiple E P (n+2)) ≫ e.hom) ≫ TotalLift.lift (thetaLine E m) _ β =
        TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2)) ≫ e.hom)
    have he : negative E (multiple E P (n+2)) ≫ e.hom = negative E (multiple E P n) := by
      simpa only [e, translationIso, multiple_one] using midpoint_step E P n
    rw [he]
    obtain ⟨h, hβ⟩ := hβ
    exact TotalLift.fixed_of_normalized _ _ _ _ h hβ
  obtain ⟨hδbase, hδnorm⟩ := TotalLift.normalized_of_fixed _ _ _ _ hδfixed
  obtain ⟨hγbase, hγnorm⟩ := hγ
  have hδγ : δ = γ :=
    (RelativeMidpointSymmetricThetaLift.normalized_reflection E m (multiple E P (n+2)) ⟨δ⟩).unique
      hδnorm hγnorm
  rw [hδγ] at hδ
  exact hδ

lemma pointwise_exists_unique (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    ∃! α : Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P n)),
      MidpointNormalized E m (multiple E P n) ι α ∧
        Symmetric E m (multiple E P n) ι α :=
  relative_midpoint_symmetric_theta_lift R E m hm he (multiple E P n)
    (multiple_killed E m P hP n) ι hι

def normalizedFamily (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    ∀ n : ℕ, Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P n)) :=
  fun n => Classical.choose (pointwise_exists_unique E m hm he P hP ι hι n)

lemma normalizedFamily_spec (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    MidpointNormalized E m (multiple E P n) ι (normalizedFamily E m hm he P hP ι hι n) ∧
      Symmetric E m (multiple E P n) ι (normalizedFamily E m hm he P hP ι hι n) :=
  (Classical.choose_spec (pointwise_exists_unique E m hm he P hP ι hι n)).1

omit [Algebra ℚ R] [IsNoetherianRing R] in
lemma symmetric_of_midpoint (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E P))
    (hα : MidpointNormalized E m P ι α) : Symmetric E m P ι α := by
  obtain ⟨h, hα⟩ := hα
  exact ⟨RelativeMidpointSymmetricThetaLift.reflection_square E P,
    RelativeMidpointSymmetricThetaLift.normalized_square E m P _ hα⟩

lemma normalizedFamily_zero (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    normalizedFamily E m hm he P hP ι hι 0 =
      changeMap E m (translation_multiple_zero E P) (identityLift E m) := by
  apply (pointwise_exists_unique E m hm he P hP ι hι 0).unique
  · exact normalizedFamily_spec E m hm he P hP ι hι 0
  · have h := identityLift_midpoint_zero E m P ι hι
    exact ⟨h, symmetric_of_midpoint E m (multiple E P 0) ι _ h⟩

/-- Every normalized family member is the corresponding power of its generator,
expressed in the category of the actual module sheaves. -/
lemma normalizedFamily_powers (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    TotalLift.lift (thetaLine E m) _ (normalizedFamily E m hm he P hP ι hι n) =
      ((TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1))
        (normalizedFamily E m hm he P hP ι hι 1)) ^ n).hom := by
  let a := normalizedFamily E m hm he P hP ι hι
  let A := fun n => TotalLift.lift (thetaLine E m) _ (a n)
  let I := TotalLift.aut (thetaLine E m) (RelativeNormalizedThetaInversion.inversionIso E) ι
  let T := TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) (a 1)
  have href (k : ℕ) : TotalLift.lift (thetaLine E m) _
      (reflectionLift E m (multiple E P k) ι (a k)) = A k ≫ I.hom :=
    TotalLift.lift_comp _ _ _ _ _
  apply TotalLift.powers_of_reflections T I A ?_ rfl ?_ ?_ ?_ n
  · dsimp only [A, a]
    rw [normalizedFamily_zero, changeMap, TotalLift.lift_change, identityLift, TotalLift.lift_id]
  · obtain ⟨hi, hιsquare⟩ := hι.2
    exact TotalLift.lift_square _ _ _ hi hιsquare
  · obtain ⟨hr, hα⟩ := (normalizedFamily_spec E m hm he P hP ι hι 1).2
    rw [← href]
    exact TotalLift.lift_square _ _ _ hr hα
  · intro k
    have h := normalized_reflection_step E m P k (a 1) _ _
      (normalizedFamily_spec E m hm he P hP ι hι k).1
      (normalizedFamily_spec E m hm he P hP ι hι (k+2)).1
    rw [href, href] at h
    exact h

/-- The all-a+b composition law is an equality of actual sheaf isomorphisms. -/
lemma normalizedFamily_add (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (a b : ℕ) :
    compose E m _ _ (normalizedFamily E m hm he P hP ι hι a)
      (normalizedFamily E m hm he P hP ι hι b) =
      changeMap E m (translation_multiple_add E P a b)
        (normalizedFamily E m hm he P hP ι hι (a+b)) := by
  apply TotalLift.lift_injective (thetaLine E m) _
  unfold compose changeMap
  rw [TotalLift.lift_comp, TotalLift.lift_change,
    normalizedFamily_powers, normalizedFamily_powers, normalizedFamily_powers]
  rw [Nat.add_comm a b, pow_add]
  rfl

/-- Reduction of the period law to the actual inversion action at the two-torsion
midpoint. This lemma does not assert that the remaining inversion equation holds. -/
lemma normalizedFamily_period_of_fixedInversion (m : ℕ) (hm : 0 < m) (he : Even m)
    (P : point E) (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι)
    (hfix : ∃ h : negative E (multiple E P m) ≫ inverse E = negative E (multiple E P m),
      (Scheme.Modules.pullback (negative E (multiple E P m))).mapIso ι =
        fixedComparison E m _ _ h) (a : ℕ) :
    normalizedFamily E m hm he P hP ι hι (a+m) =
      changeMap E m (translation_multiple_period E m P hP a)
        (normalizedFamily E m hm he P hP ι hι a) := by
  have ht : ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P m) = 𝟙 E.curve := by
    simpa only [Nat.zero_add] using
      (translation_multiple_period E m P hP 0).trans (translation_multiple_zero E P)
  have hmid : MidpointNormalized E m (multiple E P m) ι
      (changeMap E m ht (identityLift E m)) := by
    unfold MidpointNormalized reflectionLift reflection changeMap identityLift
    exact identity_reflection_normalized _ _ _ ht _ ι hfix
  have ham : normalizedFamily E m hm he P hP ι hι m =
      changeMap E m ht (identityLift E m) := by
    exact (pointwise_exists_unique E m hm he P hP ι hι m).unique
      (normalizedFamily_spec E m hm he P hP ι hι m)
      ⟨hmid, symmetric_of_midpoint E m (multiple E P m) ι _ hmid⟩
  let T := TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1))
    (normalizedFamily E m hm he P hP ι hι 1)
  have hpow : T ^ m = 1 := by
    apply Aut.ext
    change (T ^ m).hom = 𝟙 _
    rw [← normalizedFamily_powers E m hm he P hP ι hι m, ham]
    unfold changeMap identityLift
    rw [TotalLift.lift_change, TotalLift.lift_id]
  apply TotalLift.lift_injective (thetaLine E m) _
  unfold changeMap
  rw [TotalLift.lift_change, normalizedFamily_powers, normalizedFamily_powers]
  change (T ^ (a+m)).hom = (T ^ a).hom
  rw [pow_add, hpow, mul_one]

open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily in
/-- Even-degree normalized inversion is the identity on every fixed section. -/
lemma even_inversion_fixed (m : ℕ) (hm : 0 < m) (he : Even m)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι)
    (e : base (R := R) ⟶ E.curve) (hefix : e ≫ inverse E = e) :
    (Scheme.Modules.pullback e).mapIso ι = fixedComparison E m e (inverse E) hefix := by
  obtain ⟨k, rfl⟩ := he
  have hk : 0 < k := by omega
  obtain ⟨α, hα, _⟩ := RelativeNormalizedThetaInversion.normalized_exists_unique E k
  obtain ⟨hf, hαsquare⟩ := hα.2
  have hs : (Scheme.Modules.pullback (inverse E)).mapIso α ≪≫ α =
      FixedPointPullback.squareComparison (inverse E) hf (thetaLine E k) := by
    simpa only [FixedPointPullback.squareComparison, FixedPointPullback.compare,
      NatIso.trans_app, squareComparison, Iso.trans_assoc] using hαsquare
  let η := thetaLineDoubleIso E k hk
  let β := Scheme.Modules.pullbackTensorObjIso (inverse E) (thetaLine E k) (thetaLine E k) ≪≫
    MonoidalCategory.tensorIso α α
  let γ : Lift E (k+k) (inverse E) := (Scheme.Modules.pullback (inverse E)).mapIso η ≪≫
    β ≪≫ η.symm
  have hn (o : base (R := R) ⟶ E.curve) (ho : o ≫ inverse E = o) :
      (Scheme.Modules.pullback o).mapIso γ = fixedComparison E (k+k) o (inverse E) ho := by
    exact EvenInversion.transport_fixed o (inverse E) ho η β
      (EvenInversion.tensor_lift_fixed o (inverse E) ho hf (thetaLine E k)
        (RelativeNormalizedThetaInversion.line_invertible E k) α hs)
  have hγι : γ = ι := (RelativeNormalizedThetaInversion.unique_fixed_lift E (k+k)).unique
    (hn (zero E) (RelativeNormalizedThetaInversion.inverse_zero E)) hι.1.choose_spec
  rw [← hγι]
  exact hn e hefix

/-- The full period law, with no additional hypothesis on inversion. -/
lemma normalizedFamily_period (m : ℕ) (hm : 0 < m) (he : Even m)
    (P : point E) (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (a : ℕ) :
    normalizedFamily E m hm he P hP ι hι (a+m) =
      changeMap E m (translation_multiple_period E m P hP a)
        (normalizedFamily E m hm he P hP ι hι a) := by
  apply normalizedFamily_period_of_fixedInversion E m hm he P hP ι hι
  have ht : ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P m) = 𝟙 E.curve := by
    simpa only [Nat.zero_add] using
      (translation_multiple_period E m P hP 0).trans (translation_multiple_zero E P)
  have hf : negative E (multiple E P m) ≫ inverse E = negative E (multiple E P m) := by
    simpa only [reflection, ht, Category.id_comp] using
      RelativeMidpointSymmetricThetaLift.reflection_fixed E (multiple E P m)
  exact ⟨hf, even_inversion_fixed E m hm he ι hι _ hf⟩

omit [Algebra ℚ R] [IsNoetherianRing R] in
lemma cyclicSystem_unique (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (A B : ∀ n : ℕ, Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E (multiple E P n)))
    (hA : CyclicSystem E m P ι A) (hB : CyclicSystem E m P ι B) : A = B := by
  funext n
  exact (RelativeMidpointSymmetricThetaLift.midpoint_exists_unique E m (multiple E P n)
    ι ⟨A n⟩).unique (hA.1 n) (hB.1 n)

#print axioms multiple_killed
#print axioms translation_multiple_zero
#print axioms translation_multiple_add
#print axioms translation_multiple_period
#print axioms normalizedFamily_spec
#print axioms normalizedFamily_zero
#print axioms cyclicSystem_unique
#print axioms normalized_reflection_step
#print axioms normalizedFamily_powers
#print axioms normalizedFamily_add
#print axioms thetaLineDoubleIso
#print axioms EvenInversion.tensor_involution
#print axioms normalizedFamily_period_of_fixedInversion

#print axioms EvenInversion.fixed_involution
#print axioms EvenInversion.tensor_lift_fixed
#print axioms EvenInversion.transport_fixed
#print axioms even_inversion_fixed
#print axioms normalizedFamily_period

end RelativeCyclicThetaSplittingR0256

open RelativeCyclicThetaSplittingR0256 in
/-- The unique midpoint-normalized cyclic theta splitting on the entire base. -/
theorem relative_cyclic_theta_splitting :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R), ∀ m : ℕ, 0 < m → Even m →
      ∀ (P : ArithmeticThetaRelativeThetaLiftsR0255.point E),
      CategoryTheory.CategoryStruct.comp P.val (E.law.schemeNsmul (2*m)) =
        ArithmeticThetaRelativeThetaLiftsR0255.zero E →
      ∀ ι : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m
        (ArithmeticThetaRelativeThetaLiftsR0255.inverse E),
      ArithmeticThetaRelativeThetaLiftsR0255.NormalizedInversion E m ι →
      ∃! A : (∀ n : ℕ, ArithmeticThetaRelativeThetaLiftsR0255.Lift E m
        (ArithmeticThetaRelativeThetaLiftsR0255.translation E
          (ArithmeticThetaRelativeThetaRelationsR0256.multiple E P n))),
        ArithmeticThetaRelativeThetaRelationsR0256.CyclicSystem E m P ι A := by
  intro R _ _ _ E m hm he P hP ι hι
  let A := normalizedFamily E m hm he P hP ι hι
  have hA : CyclicSystem E m P ι A := by
    refine ⟨normalizedFamily_spec E m hm he P hP ι hι,
      ⟨translation_multiple_zero E P, normalizedFamily_zero E m hm he P hP ι hι⟩, ?_, ?_⟩
    · intro a b
      exact ⟨translation_multiple_add E P a b, normalizedFamily_add E m hm he P hP ι hι a b⟩
    · intro a
      exact ⟨translation_multiple_period E m P hP a, normalizedFamily_period E m hm he P hP ι hι a⟩
  exact ⟨A, hA, fun B hB => cyclicSystem_unique E m P ι B A hB hA⟩

#print axioms relative_cyclic_theta_splitting
end ArithmeticThetaRelativeThetaRelationsR0256
