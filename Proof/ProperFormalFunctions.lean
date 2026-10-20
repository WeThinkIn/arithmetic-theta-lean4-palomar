module

public import GeometricPrerequisiteDefinitions
public import Mathlib
public import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
public import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util
public import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
public import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d

@[expose] public section

/-! Degree-zero proper formal functions.
Candidate arguments below are adapted from the frozen round-0005 reference
sources. Accepted support modules remain unchanged; all new declarations are
compiled here before they may be used as mathematical evidence. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


/- Adapted reference: Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap. -/
section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover

theorem preimage_iInf_fin {Y Z : Scheme.{u}} (f : Y ⟶ Z) {n : ℕ} (W : Fin (n + 1) → Z.Opens) :
    f ⁻¹ᵁ (⨅ j, W j) = ⨅ j, f ⁻¹ᵁ (W j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, W j) = W 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, f ⁻¹ᵁ (W j)) = f ⁻¹ᵁ (W 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit W, Scheme.Hom.preimage_inf, ih (fun j => W j.succ), hsplit (fun j => f ⁻¹ᵁ (W j))]

section Comap

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (f : Y ⟶ X) [IsAffineHom f]

def comap : Y.OrderedAffineCover where
  ι := 𝒰.ι
  instFintype := 𝒰.instFintype
  instLinearOrder := 𝒰.instLinearOrder
  U i := f ⁻¹ᵁ 𝒰.U i
  isAffineOpen i := (𝒰.isAffineOpen i).preimage f
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_eq_top]; rfl

theorem comap_ι : (𝒰.comap f).ι = 𝒰.ι := rfl

theorem comap_U (i : 𝒰.ι) : (𝒰.comap f).U i = f ⁻¹ᵁ 𝒰.U i := rfl

theorem comap_Idx (i : ℕ) : (𝒰.comap f).Idx i = 𝒰.Idx i := rfl

theorem comap_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) : (𝒰.comap f).face s j = 𝒰.face s j := rfl

theorem comap_inter {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s = f ⁻¹ᵁ 𝒰.inter s :=
  (preimage_iInf_fin f (fun j => 𝒰.U (s.1 j))).symm

theorem comap_inter_le {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s ≤ f ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.comap_inter f s).le

theorem le_comap_inter {i : ℕ} (s : 𝒰.Idx i) : f ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.comap f).inter s :=
  (𝒰.comap_inter f s).ge

end Comap

section BaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

abbrev baseChange : (Limits.pullback π (specMap R A)).OrderedAffineCover :=
  haveI := isAffineHom_fst π A
  𝒰.comap (Limits.pullback.fst π (specMap R A))

theorem baseChange_ι : (𝒰.baseChange π A).ι = 𝒰.ι := rfl

theorem baseChange_U (i : 𝒰.ι) :
    (𝒰.baseChange π A).U i = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.U i := rfl

theorem baseChange_Idx (i : ℕ) : (𝒰.baseChange π A).Idx i = 𝒰.Idx i := rfl

theorem baseChange_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) :
    (𝒰.baseChange π A).face s j = 𝒰.face s j := rfl

theorem baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  haveI := isAffineHom_fst π A
  𝒰.comap_inter _ s

theorem baseChange_inter_le {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.baseChange_inter π A s).le

theorem le_baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.baseChange π A).inter s :=
  (𝒰.baseChange_inter π A s).ge

end BaseChange

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem toOrderedAffineCover_pullback :
    (𝒱.pullback π A).toOrderedAffineCover = 𝒱.toOrderedAffineCover.baseChange π A := by
  unfold Scheme.TwoAffineOpenCover.toOrderedAffineCover Scheme.OrderedAffineCover.baseChange
    Scheme.OrderedAffineCover.comap
  congr 1
  funext i; rcases i with ⟨i⟩; fin_cases i <;> rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData. -/
section
namespace P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FormalGAGAFiniteRelSpecAux

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

scoped instance instIsLocallyDirected :
    ((relativeGluingData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

set_option backward.isDefEq.respectTransparency false in
theorem ι_toBase (U : X.AffineZariskiSite) :
    (relativeGluingData H).cover.f U ≫ (relativeGluingData H).toBase =
      Spec.map (α.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

theorem toBase_preimage (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
  have h__af := (relativeGluingData H).toBase_preimage_eq_opensRange_ι U
  simp at h__af
  exact h__af

end FormalGAGAFiniteRelSpecAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.FormalGAGAFiniteRelSpecAux"

open FormalGAGAFiniteRelSpecAux AlgebraicGeometry.Scheme in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
    (hfin : ∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) :
    IsFinite (Scheme.AffineZariskiSite.relativeGluingData H).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_affineOpens_eq_top _)]
  intro U
  let U' : X.AffineZariskiSite := ⟨U.1, U.2⟩
  let e := IsOpenImmersion.isoOfRangeEq ((AffineZariskiSite.relativeGluingData H).toBase ⁻¹ᵁ U).ι
    ((AffineZariskiSite.relativeGluingData H).cover.f U')
      (by simpa using congr($(toBase_preimage H U').1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U')
  rw [← cancel_mono U.2.fromSpec]
  have h := ι_toBase H U'
  simp only [Cover.RelativeGluingData.cover_f] at h
  simp [IsAffineOpen.isoSpec_hom, e, h, U']
end P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData. -/
section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData
    {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
    (hfin : ∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) :
    IsFinite (Scheme.AffineZariskiSite.relativeGluingData H).toBase := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.solution
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper. -/
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
attribute [-instance] ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

universe u

noncomputable section

namespace SolKS

lemma preimage_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Fintype ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ (⨅ j, U j) = ⨅ j, f ⁻¹ᵁ (U j) := by
  classical
  rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

section Setup

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

def Rr : Type u := ↥(reesAlgebra I)

scoped instance : CommRing (Rr I) := inferInstanceAs (CommRing ↥(reesAlgebra I))
scoped instance : Algebra A (Rr I) := inferInstanceAs (Algebra A ↥(reesAlgebra I))
scoped instance [IsNoetherianRing A] : IsNoetherianRing (Rr I) :=
  inferInstanceAs (IsNoetherianRing ↥(reesAlgebra I))

abbrev Rr.val (r : Rr I) : A[X] := (show ↥(reesAlgebra I) from r).1

lemma Rr.coeff_mem (r : Rr I) (i : ℕ) : (Rr.val I r).coeff i ∈ I ^ i :=
  (mem_reesAlgebra_iff _ _).mp (show ↥(reesAlgebra I) from r).2 i

abbrev Rr.mk (p : A[X]) (hp : p ∈ reesAlgebra I) : Rr I := (show ↥(reesAlgebra I) from ⟨p, hp⟩)

abbrev Rr.incl : Rr I →+* A[X] := (reesAlgebra I).val.toRingHom

abbrev sA : Spec (CommRingCat.of (Rr I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Rr I)))

abbrev sX : Spec (CommRingCat.of A[X]) ⟶ Spec (CommRingCat.of (Rr I)) :=
  Spec.map (CommRingCat.ofHom (Rr.incl I))

abbrev P' : Scheme.{u} := pullback q (sA I)

abbrev fst' : P' I q ⟶ P := pullback.fst q (sA I)

abbrev π' : P' I q ⟶ Spec (CommRingCat.of (Rr I)) := pullback.snd q (sA I)

abbrev P₁ : Scheme.{u} := pullback (π' I q) (sX I)

abbrev g : P₁ I q ⟶ P' I q := pullback.fst (π' I q) (sX I)

abbrev snd₁ : P₁ I q ⟶ Spec (CommRingCat.of A[X]) := pullback.snd (π' I q) (sX I)

abbrev p₁ : P₁ I q ⟶ P := g I q ≫ fst' I q

lemma sX_sA : sX I ≫ sA I = Spec.map (CommRingCat.ofHom (algebraMap A A[X])) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma isPullback_P' : IsPullback (fst' I q) (π' I q) q (sA I) := IsPullback.of_hasPullback _ _

lemma isPullback_P₁ :
    IsPullback (p₁ I q) (snd₁ I q) q (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) := by
  rw [← sX_sA]
  exact IsPullback.paste_horiz (IsPullback.of_hasPullback (π' I q) (sX I)) (isPullback_P' I q)

scoped instance : IsAffineHom (g I q) := MorphismProperty.pullback_fst _ _ inferInstance
scoped instance : IsAffineHom (fst' I q) := MorphismProperty.pullback_fst _ _ inferInstance

def alg (U : P.Opens) : A →+* Γ(P, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U le_top).hom

lemma alg_res {U V : P.Opens} (h : V ≤ U) (a : A) :
    P.presheaf.map (homOfLE h).op (alg q U a) = alg q V a := by
  simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

def T (W : (P₁ I q).Opens) : Γ(P₁ I q, W) :=
  ((snd₁ I q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom X)

def θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) : Γ(P, U)[X] →+* Γ(P₁ I q, W) :=
  eval₂RingHom ((p₁ I q).appLE U W e).hom (T I q W)

lemma θ_C (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (c : Γ(P, U)) :
    θ I q U W e (C c) = ((p₁ I q).appLE U W e).hom c := by
  simp [θ]

lemma θ_X (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) :
    θ I q U W e X = T I q W := by
  simp [θ]

lemma appLE_top_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  f.appLE_eq_app

lemma ΓSpecIso_inv_C (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A A[X]))
  have := congrArg (fun ψ : CommRingCat.of A ⟶ _ => ψ.hom a) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

lemma θ_map (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : A[X]) :
    θ I q U W e (Polynomial.map (alg q U) r) =
      ((snd₁ I q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom r) := by
  have key : ((θ I q U W e).comp (mapRingHom (alg q U))) =
      ((snd₁ I q).appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      have lhs : ((p₁ I q).appLE U W e).hom (alg q U a) =
          ((p₁ I q ≫ q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      have rhs : ((snd₁ I q).appLE ⊤ W le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a)) =
          ((snd₁ I q ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ W le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        rw [ΓSpecIso_inv_C, ← appLE_top_top, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      rw [lhs, rhs]
      exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
        (appLE_congr_hom (isPullback_P₁ I q).w ⊤ W _ _)
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
  exact congrArg (fun φ : A[X] →+* Γ(P₁ I q, W) => φ r) key

lemma θ_res {U U' : P.Opens} {W W' : (P₁ I q).Opens} (e : W ≤ p₁ I q ⁻¹ᵁ U)
    (e' : W' ≤ p₁ I q ⁻¹ᵁ U') (hU : U' ≤ U) (hW : W' ≤ W) (p : Γ(P, U)[X]) :
    (P₁ I q).presheaf.map (homOfLE hW).op (θ I q U W e p) =
      θ I q U' W' e' (Polynomial.map (P.presheaf.map (homOfLE hU).op).hom p) := by
  have key : ((P₁ I q).presheaf.map (homOfLE hW).op).hom.comp (θ I q U W e) =
      (θ I q U' W' e').comp (mapRingHom (P.presheaf.map (homOfLE hU).op).hom) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact congrArg (fun φ : Γ(P, U)[X] →+* Γ(P₁ I q, W') => φ p) key

lemma θ_bijective {U : P.Opens} (hU : IsAffineOpen U) {W : (P₁ I q).Opens}
    (hW : W = p₁ I q ⁻¹ᵁ U ⊓ snd₁ I q ⁻¹ᵁ ⊤) :
    Function.Bijective (θ I q U W (hW.le.trans inf_le_left)) := by
  have H := isPullback_P₁ I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    hW (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hW).mp h1

  let ΦC : Γ(P, U) ⟶ CommRingCat.of Γ(P, U)[X] := CommRingCat.ofHom C
  let ΦX : Γ(Spec (CommRingCat.of A[X]), ⊤) ⟶ CommRingCat.of Γ(P, U)[X] :=
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom ≫ CommRingCat.ofHom (mapRingHom (alg q U))
  have w : q.appLE ⊤ U le_top ≫ ΦC =
      (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ ⊤ le_top ≫ ΦX := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ΦC, ΦX,
      CommRingCat.hom_ofHom, coe_mapRingHom]
    rw [appLE_top_top]
    change C ((q.appLE ⊤ U le_top).hom x) = Polynomial.map (alg q U)
      (((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom x)
    rw [Scheme.ΓSpecIso_naturality]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C]
    congr 1
    simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]
  let Φ : Γ(P₁ I q, W) ⟶ CommRingCat.of Γ(P, U)[X] := hP.desc ΦC ΦX w
  have hΦl : (p₁ I q).appLE U W _ ≫ Φ = ΦC := hP.inl_desc _ _ _
  have hΦr : (snd₁ I q).appLE ⊤ W _ ≫ Φ = ΦX := hP.inr_desc _ _ _
  set θ' := θ I q U W (hW.le.trans inf_le_left)

  have h1 : Φ.hom.comp θ' = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_C, RingHom.id_apply]
      change (((p₁ I q).appLE U W _) ≫ Φ).hom c = C c
      rw [hΦl]; rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_X, T, RingHom.id_apply]
      change ((snd₁ I q).appLE ⊤ W _ ≫ Φ).hom _ = X
      rw [hΦr]
      change Polynomial.map (alg q U) (((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom X) = X
      rw [Iso.inv_hom_id]
      simp

  have h2 : Φ ≫ CommRingCat.ofHom θ' = 𝟙 _ := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hΦl, Category.comp_id]
      ext c
      exact θ_C I q U W _ c
    · rw [← Category.assoc, hΦr, Category.comp_id]
      ext r
      change θ' (Polynomial.map (alg q U) ((Scheme.ΓSpecIso (CommRingCat.of A[X])).hom.hom r)) = _
      rw [θ_map]
      congr 1
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  constructor
  · intro x y hxy
    have := congrArg Φ.hom hxy
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, h1] at this
  · intro z
    refine ⟨Φ.hom z, ?_⟩
    change (Φ ≫ CommRingCat.ofHom θ').hom z = z
    rw [h2]; rfl

lemma closure_eq_top {U : P.Opens} (hU : IsAffineOpen U) {W' : (P' I q).Opens}
    (hW' : W' = fst' I q ⁻¹ᵁ U ⊓ π' I q ⁻¹ᵁ ⊤) :
    Subring.closure (Set.range ((fst' I q).appLE U W' (hW'.le.trans inf_le_left)).hom ∪
      Set.range ((π' I q).appLE ⊤ W' le_top).hom) = ⊤ := by
  have H := isPullback_P' I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    hW' (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hW').mp h1
  exact CommRingCat.closure_range_union_range_eq_top_of_isPushout hP

def algR (W' : (P' I q).Opens) : Rr I →+* Γ(P' I q, W') :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (π' I q).appLE ⊤ W' le_top).hom

def algR₁ (W : (P₁ I q).Opens) : Rr I →+* Γ(P₁ I q, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (g I q ≫ π' I q).appLE ⊤ W le_top).hom

lemma algR₁_eq_θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : Rr I) :
    algR₁ I q W r = θ I q U W e (Polynomial.map (alg q U) (Rr.val I r)) := by
  rw [θ_map]
  simp only [algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_congr_hom (pullback.condition (f := π' I q) (g := sX I)) ⊤ W _ le_top,
    ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top, CommRingCat.comp_apply, appLE_top_top]
  congr 1
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Rr.incl I))
  have := congrArg (fun ψ : CommRingCat.of (Rr I) ⟶ _ => ψ.hom r) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

lemma g_appLE_algR (W' : (P' I q).Opens) (r : Rr I) :
    ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (algR I q W' r) = algR₁ I q (g I q ⁻¹ᵁ W') r := by
  simp only [algR, algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma algR_res {W W' : (P' I q).Opens} (h : W ≤ W') (r : Rr I) :
    (P' I q).presheaf.map (homOfLE h).op (algR I q W' r) = algR I q W r := by
  simp only [algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma g_appLE_res {W W' : (P' I q).Opens} (h : W ≤ W') (x : Γ(P' I q, W')) :
    (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op
        (((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x) =
      ((g I q).appLE W (g I q ⁻¹ᵁ W) le_rfl).hom ((P' I q).presheaf.map (homOfLE h).op x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

def φg : OModulePresheaf.Hom (OModulePresheaf.unit (π' I q))
    (OModulePresheaf.pushforwardUnit (π' I q) (g I q)) where
  app W' :=
    { toFun := fun x => ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        show ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (algR I q W' r * (show Γ(P' I q, W') from x)) =
          algR₁ I q (g I q ⁻¹ᵁ W') r * ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
        rw [map_mul, g_appLE_algR] }
  app_smul W' a x := by
    show ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (a * (show Γ(P' I q, W') from x)) =
      ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a * ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
    exact map_mul _ a x
  naturality {W W'} h := by
    refine LinearMap.ext fun x => ?_
    exact (g_appLE_res I q h x).symm

lemma φg_app (W' : (P' I q).Opens) (x : Γ(P' I q, W')) :
    (φg I q).app W' x = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x := rfl

abbrev F' : OModulePresheaf (π' I q) := OModulePresheaf.im (φg I q)

abbrev F'val {W' : (P' I q).Opens} (y : (F' I q).obj W') : Γ(P₁ I q, g I q ⁻¹ᵁ W') := y.1

lemma F'_exists {W' : (P' I q).Opens} (y : (F' I q).obj W') :
    ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = F'val I q y :=
  LinearMap.mem_range.mp y.2

lemma mem_F'_iff (W' : (P' I q).Opens)
    (y : (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj W') :
    y ∈ LinearMap.range ((φg I q).app W') ↔
      ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = (show Γ(P₁ I q, g I q ⁻¹ᵁ W') from y) :=
  LinearMap.mem_range

lemma F'_res_val {W W' : (P' I q).Opens} (h : W ≤ W') (y : (F' I q).obj W') :
    F'val I q ((F' I q).res h y) =
      (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op (F'val I q y) := rfl

lemma F'_smul_val (W' : (P' I q).Opens) (a : Γ(P' I q, W')) (y : (F' I q).obj W') :
    F'val I q (a • y) = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a * F'val I q y := rfl

lemma F'_rsmul_val (W' : (P' I q).Opens) (r : Rr I) (y : (F' I q).obj W') :
    F'val I q (r • y) = algR₁ I q (g I q ⁻¹ᵁ W') r * F'val I q y := rfl

lemma F'_add_val (W' : (P' I q).Opens) (y y' : (F' I q).obj W') :
    F'val I q (y + y') = F'val I q y + F'val I q y' := rfl

lemma F'_zero_val (W' : (P' I q).Opens) : F'val I q (0 : (F' I q).obj W') = 0 := rfl

lemma F'_ext {W' : (P' I q).Opens} {y y' : (F' I q).obj W'} (h : F'val I q y = F'val I q y') :
    y = y' := Subtype.ext h

lemma isCoherent_F' : (F' I q).IsCoherent := fun U => by
  haveI : Module.Finite Γ(P' I q, U.1) ((OModulePresheaf.unit (π' I q)).obj U.1) :=
    inferInstanceAs (Module.Finite Γ(P' I q, U.1) Γ(P' I q, U.1))
  exact Module.Finite.of_surjective ((OModulePresheaf.kerImSES (φg I q)).proj.appSections U.1)
    ((OModulePresheaf.kerImSES (φg I q)).surjective U.1)

lemma res_eq_zero_iff_of_eq {X : Scheme.{u}} {W V₁ V₂ : X.Opens} (h : V₁ = V₂) (e₁ : V₁ ≤ W)
    (e₂ : V₂ ≤ W) (s : Γ(X, W)) :
    X.presheaf.map (homOfLE e₁).op s = 0 ↔ X.presheaf.map (homOfLE e₂).op s = 0 := by
  subst h; rfl

lemma isQuasicoherent_F' : (F' I q).IsQuasicoherent := by
  intro U f
  have hle : (P' I q).basicOpen f ≤ U.1 := (P' I q).basicOpen_le f
  constructor
  · intro x
    obtain ⟨a', ha'⟩ := F'_exists I q x
    haveI := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a₀, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) a'
    refine ⟨n, ⟨(φg I q).app U.1 a₀, ⟨a₀, rfl⟩⟩, F'_ext I q ?_⟩
    rw [F'_res_val, F'_smul_val, ← ha']
    change (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op
        (((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom a₀) = _
    dsimp only at h
    rw [mul_comm] at h
    change ((P' I q).presheaf.map (homOfLE hle).op).hom (f ^ n) * a' =
      ((P' I q).presheaf.map (homOfLE hle).op).hom a₀ at h
    rw [← map_mul, h, g_appLE_res]
  · intro y hy
    obtain ⟨x, hx⟩ := F'_exists I q y
    have h0 : (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op (F'val I q y) = 0 :=
      congrArg Subtype.val hy
    set f₁ : Γ(P₁ I q, g I q ⁻¹ᵁ U.1) := ((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom f with hf₁
    have hopen : g I q ⁻¹ᵁ (P' I q).basicOpen f = (P₁ I q).basicOpen f₁ := by
      rw [Scheme.preimage_basicOpen, hf₁, Scheme.Hom.appLE_eq_app]
    rw [res_eq_zero_iff_of_eq hopen _ ((P₁ I q).basicOpen_le f₁)] at h0
    haveI := (U.2.preimage (g I q)).isLocalization_basicOpen f₁
    have h0' : algebraMap Γ(P₁ I q, g I q ⁻¹ᵁ U.1) Γ(P₁ I q, (P₁ I q).basicOpen f₁)
        (F'val I q y) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f₁) _ _).mp h0'
    refine ⟨n, F'_ext I q ?_⟩
    rw [F'_smul_val, map_pow]
    exact hn

variable (K : P.OrderedAffineCover)

def K' : (P' I q).OrderedAffineCover where
  ι := K.ι
  U i := fst' I q ⁻¹ᵁ K.U i
  isAffineOpen i := (K.isAffineOpen i).preimage _
  iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top _ K.iSup_eq_top

lemma K'_inter {i : ℕ} (s : K.Idx i) : (K' I q K).inter s = fst' I q ⁻¹ᵁ K.inter s :=
  (preimage_iInf (fst' I q) fun j => K.U (s.1 j)).symm

lemma hW' {i : ℕ} (s : K.Idx i) : (K' I q K).inter s = fst' I q ⁻¹ᵁ K.inter s ⊓ π' I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq]

lemma hW {i : ℕ} (s : K.Idx i) :
    g I q ⁻¹ᵁ (K' I q K).inter s = p₁ I q ⁻¹ᵁ K.inter s ⊓ snd₁ I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq, Scheme.Hom.comp_preimage]

lemma e_s {i : ℕ} (s : K.Idx i) : g I q ⁻¹ᵁ (K' I q K).inter s ≤ p₁ I q ⁻¹ᵁ K.inter s :=
  (hW I q K s).le.trans inf_le_left

lemma e'_s {i : ℕ} (s : K.Idx i) : (K' I q K).inter s ≤ fst' I q ⁻¹ᵁ K.inter s :=
  (hW' I q K s).le.trans inf_le_left

end Setup

section Cochains

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
  [IsSeparated q] (K : P.OrderedAffineCover)

include q in
lemma haff {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := K.isAffineOpen_inter q s

def ΦC {i : ℕ} (s : K.Idx i) : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter s) ≃+* Γ(P, K.inter s)[X] :=
  (RingEquiv.ofBijective (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s))
    (θ_bijective I q (haff q K s) (hW I q K s))).symm

lemma ΦC_θ {i : ℕ} (s : K.Idx i) (p : Γ(P, K.inter s)[X]) :
    ΦC I q K s (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) p) = p :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).symm_apply_apply p

lemma θ_ΦC {i : ℕ} (s : K.Idx i) (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter s)) :
    θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) (ΦC I q K s v) = v :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).apply_symm_apply v

lemma ΦC_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter ((K' I q K).face s j))) :
    ΦC I q K s ((P₁ I q).presheaf.map
        (homOfLE ((g I q).preimage_mono ((K' I q K).inter_le_inter_face s j))).op v) =
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
        (ΦC I q K (K.face s j) v) := by
  have h := θ_res I q (e_s I q K (K.face s j)) (e_s I q K s) (K.inter_le_inter_face s j)
    ((g I q).preimage_mono ((K' I q K).inter_le_inter_face s j)) (ΦC I q K (K.face s j) v)
  rw [θ_ΦC] at h
  exact (congrArg (ΦC I q K s) h).trans (ΦC_θ I q K s _)

lemma ΦC_algR₁ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    ΦC I q K s (algR₁ I q _ r) = Polynomial.map (alg q (K.inter s)) (Rr.val I r) := by
  rw [algR₁_eq_θ I q (K.inter s) _ (e_s I q K s), ΦC_θ]

def coeffC (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) : (OModulePresheaf.unit q).cochain K i :=
  fun s => (ΦC I q K s (F'val I q (z s))).coeff j

lemma coeffC_apply (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    coeffC I q K i j z s = (ΦC I q K s (F'val I q (z s))).coeff j := rfl

lemma coeffC_add (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z + z') = coeffC I q K i j z + coeffC I q K i j z' := by
  funext s
  simp only [coeffC_apply, Pi.add_apply, F'_add_val, map_add, coeff_add]
  rfl

lemma coeffC_zero (i j : ℕ) : coeffC I q K i j 0 = 0 := by
  funext s
  change (ΦC I q K s (F'val I q (0 : (F' I q).obj _))).coeff j = 0
  rw [F'_zero_val, map_zero, coeff_zero]

lemma coeffC_sub (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z - z') = coeffC I q K i j z - coeffC I q K i j z' := by
  rw [eq_sub_iff_add_eq, ← coeffC_add, sub_add_cancel]

def F'valHom (W' : (P' I q).Opens) : (F' I q).obj W' →+ Γ(P₁ I q, g I q ⁻¹ᵁ W') :=
  { toFun := F'val I q, map_zero' := rfl, map_add' := fun _ _ => rfl }

lemma F'valHom_apply (W' : (P' I q).Opens) (y : (F' I q).obj W') : F'valHom I q W' y = F'val I q y := rfl

lemma coeffC_d (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K (i + 1) j ((F' I q).d (K' I q K) i z) =
      (OModulePresheaf.unit q).d K i (coeffC I q K i j z) := by
  funext s
  rw [coeffC_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  change _ = ∑ j' : Fin (i + 2), ((-1 : ℤ) ^ (j' : ℕ)) •
    (P.presheaf.map (homOfLE (K.inter_le_inter_face s j')).op).hom (coeffC I q K i j z (K.face s j'))
  rw [← F'valHom_apply, map_sum, map_sum, ← lcoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, lcoeff_apply, F'valHom_apply, F'_res_val, ΦC_res, coeff_map]
  rfl

lemma coeffC_smul (i j : ℕ) (r : Rr I) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (r • z) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, ((Rr.val I r).coeff x.1) • coeffC I q K i x.2 z := by
  funext s
  rw [Finset.sum_apply, coeffC_apply, Pi.smul_apply, F'_rsmul_val, map_mul, ΦC_algR₁, coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map]
  rfl

lemma coeffC_mem (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    (show Γ(P, K.inter s) from coeffC I q K i j z s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
        (I ^ j) := by
  obtain ⟨x, hx⟩ := F'_exists I q (z s)
  rw [coeffC_apply, ← hx]
  set J : Ideal Γ(P, K.inter s) := I.map (alg q (K.inter s)) with hJ

  let S : Subring Γ(P' I q, (K' I q K).inter s) :=
    (reesAlgebra J).toSubring.comap
      ((ΦC I q K s).toRingHom.comp ((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom)
  have hS : Subring.closure (Set.range ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
      (e'_s I q K s)).hom ∪ Set.range ((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom) ≤ S := by
    rw [Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨r₀, rfl⟩)
    · show ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom
        (((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c)) ∈ reesAlgebra J
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← θ_C I q _ _ (e_s I q K s), ΦC_θ]
      exact Subalgebra.algebraMap_mem (reesAlgebra J) c
    · show ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom
        (((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom r₀)) ∈ reesAlgebra J
      have hr₀ : r₀ = (Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).hom.hom r₀) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [hr₀]
      change ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom (algR I q _ _)) ∈ _
      rw [g_appLE_algR, ΦC_algR₁]
      intro n
      rw [coeff_map, hJ, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Rr.coeff_mem I _ n)
  rw [closure_eq_top I q (haff q K s) (hW' I q K s)] at hS
  have hxS : x ∈ S := hS (Subring.mem_top x)
  have : ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom x) ∈ reesAlgebra J := hxS
  have := (mem_reesAlgebra_iff _ _).mp this j
  rwa [hJ, ← Ideal.map_pow] at this

def Sθ {i : ℕ} (s : K.Idx i) : Subring Γ(P, K.inter s)[X] :=
  (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom.range).comap
    (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s))

lemma mem_range_of_mem_Sθ {i : ℕ} (s : K.Idx i) {p : Γ(P, K.inter s)[X]} (hp : p ∈ Sθ I q K s) :
    (show (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj ((K' I q K).inter s) from
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) p) ∈
      LinearMap.range ((φg I q).app ((K' I q K).inter s)) :=
  (mem_F'_iff I q _ _).mpr (RingHom.mem_range.mp (Subring.mem_comap.mp hp))

lemma C_mem_Sθ {i : ℕ} (s : K.Idx i) (c : Γ(P, K.inter s)) : C c ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr
    ⟨((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c, ?_⟩)
  rw [θ_C, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma map_mem_Sθ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    Polynomial.map (alg q (K.inter s)) (Rr.val I r) ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr ⟨algR I q _ r, ?_⟩)
  rw [g_appLE_algR, algR₁_eq_θ I q (K.inter s) _ (e_s I q K s)]

lemma monomial_mem_Sθ {i : ℕ} (s : K.Idx i) {k : ℕ} {x : Γ(P, K.inter s)}
    (hx : x ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) :
    monomial k x ∈ Sθ I q K s := by
  change x ∈ Ideal.map (alg q (K.inter s)) (I ^ k) at hx
  unfold Ideal.map at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, rfl⟩ := h
    have : monomial k (alg q (K.inter s) a) = Polynomial.map (alg q (K.inter s))
        (Rr.val I (Rr.mk I (monomial k a) (reesAlgebra.monomial_mem.mpr ha))) :=
      (Polynomial.map_monomial _).symm
    rw [this]
    exact map_mem_Sθ I q K s _
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, ← C_mul_monomial]
    exact Subring.mul_mem _ (C_mem_Sθ I q K s c) hx

def zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) :
    (F' I q).cochain (K' I q K) i :=
  fun s => ⟨_, mem_range_of_mem_Sθ I q K s (monomial_mem_Sθ I q K s (hb s))⟩

lemma F'val_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) (s : K.Idx i) :
    F'val I q (zC I q K i k b hb s) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) (monomial k (b s)) := rfl

lemma coeffC_zC (i k j : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) :
    coeffC I q K i j (zC I q K i k b hb) = if j = k then b else 0 := by
  funext s
  rw [coeffC_apply, F'val_zC, ΦC_θ, coeff_monomial]
  split_ifs with h h' h'
  · rfl
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · rfl

lemma F'val_d_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) (s : K.Idx (i + 1)) :
    F'val I q ((F' I q).d (K' I q K) i (zC I q K i k b hb) s) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
        (monomial k ((OModulePresheaf.unit q).d K i b s)) := by
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  change _ = θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
    (monomial k (∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (b (K.face s j))))
  rw [← F'valHom_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, F'valHom_apply, F'_res_val, F'val_zC,
    θ_res I q (e_s I q K ((K' I q K).face s j)) (e_s I q K s) (K.inter_le_inter_face s j),
    map_monomial]
  rfl

lemma d_zC_eq_zero (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb)
    (hdb : (OModulePresheaf.unit q).d K i b = 0) :
    (F' I q).d (K' I q K) i (zC I q K i k b hb) = 0 := by
  funext s
  apply F'_ext I q
  rw [F'val_d_zC, hdb, Pi.zero_apply, F'_zero_val]
  change θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
    (monomial k (0 : Γ(P, K.inter s))) = 0
  rw [map_zero, map_zero]

end Cochains

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {P : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] (K : P.OrderedAffineCover)

def IC (m : ℕ) : Submodule A ((OModulePresheaf.unit q).cochain K 0) where
  carrier := {w | ∀ s, (show Γ(P, K.inter s) from w s) ∈
    Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom (I ^ m)}
  add_mem' hw hw' s := Ideal.add_mem _ (hw s) (hw' s)
  zero_mem' _ := Ideal.zero_mem _
  smul_mem' a _ hw s := Ideal.mul_mem_left _ (alg q (K.inter s) a) (hw s)

lemma mem_IC {m : ℕ} (w : (OModulePresheaf.unit q).cochain K 0) :
    w ∈ IC I q K m ↔ ∀ s, (show Γ(P, K.inter s) from w s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) le_top).hom (I ^ m) := Iff.rfl

lemma IC_anti {m m' : ℕ} (h : m ≤ m') : IC I q K m' ≤ IC I q K m := fun _ hw s =>
  Ideal.map_mono (Ideal.pow_le_pow_right h) (hw s)

lemma smul_mem_IC {a : A} {l m : ℕ} (ha : a ∈ I ^ l) {w : (OModulePresheaf.unit q).cochain K 0}
    (hw : w ∈ IC I q K m) : a • w ∈ IC I q K (l + m) := by
  intro s
  show alg q (K.inter s) a * (show Γ(P, K.inter s) from w s) ∈
    Ideal.map (alg q (K.inter s)) (I ^ (l + m))
  rw [pow_add, Ideal.map_mul]
  exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) (hw s)

abbrev Dg (m : ℕ) : Submodule A ((OModulePresheaf.unit q).cochain K 1) :=
  (IC I q K m).map ((OModulePresheaf.unit q).d K 0)

def Z1 : Submodule (Rr I) ((F' I q).cochain (K' I q K) (0 + 1)) :=
  LinearMap.ker ((F' I q).d (K' I q K) (0 + 1))

def B1 : Submodule (Rr I) (Z1 I q K) :=
  (LinearMap.range ((F' I q).d (K' I q K) 0)).comap (Z1 I q K).subtype

lemma mem_Z1 (z : (F' I q).cochain (K' I q K) (0 + 1)) :
    z ∈ Z1 I q K ↔ (F' I q).d (K' I q K) (0 + 1) z = 0 := LinearMap.mem_ker

lemma mem_B1 (z : Z1 I q K) :
    z ∈ B1 I q K ↔ ∃ w', (F' I q).d (K' I q K) 0 w' = z.1 := by
  unfold B1; rw [Submodule.mem_comap]; exact LinearMap.mem_range

def M : Type u := Z1 I q K ⧸ B1 I q K

scoped instance : AddCommGroup (M I q K) := Submodule.Quotient.addCommGroup _
scoped instance : Module (Rr I) (M I q K) := Submodule.Quotient.module _

scoped instance : Module.Finite (Rr I) (M I q K) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper (F' I q) (isCoherent_F' I q)
    (isQuasicoherent_F' I q) (K' I q K)).2 0

scoped instance : _root_.IsNoetherian (Rr I) (M I q K) := isNoetherian_of_isNoetherianRing_of_finite _ _

def mkM (z : Z1 I q K) : M I q K := Submodule.Quotient.mk (p := B1 I q K) z

lemma mkM_add (z z' : Z1 I q K) : mkM I q K (z + z') = mkM I q K z + mkM I q K z' := rfl
lemma mkM_smul (r : Rr I) (z : Z1 I q K) : mkM I q K (r • z) = r • mkM I q K z := rfl
lemma mkM_zero : mkM I q K 0 = 0 := rfl
lemma mkM_eq_mkM {z z' : Z1 I q K} : mkM I q K z = mkM I q K z' ↔ z - z' ∈ B1 I q K :=
  Submodule.Quotient.eq _

def zZ (k : ℕ) (b : (OModulePresheaf.unit q).cochain K 1)
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0))
    (hb₂ : ∀ s : K.Idx 1, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) : Z1 I q K :=
  ⟨zC I q K 1 k b hb₂, (mem_Z1 I q K _).mpr (d_zC_eq_zero I q K 1 k b hb₂ (by
    obtain ⟨w, rfl⟩ := hb₁
    exact LinearMap.congr_fun (AlgebraicGeometry.OModulePresheaf.d_comp_d
      (OModulePresheaf.unit q) K 0) w))⟩

def cls (k : ℕ) (b : (OModulePresheaf.unit q).cochain K 1)
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0))
    (hb₂ : ∀ s : K.Idx 1, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) : M I q K :=
  mkM I q K (zZ I q K k b hb₁ hb₂)

def gens (m : ℕ) : Set (M I q K) :=
  {x | ∃ k, k ≤ m ∧ ∃ b hb₁ hb₂, x = cls I q K k b hb₁ hb₂}

def N (m : ℕ) : Submodule (Rr I) (M I q K) := Submodule.span (Rr I) (gens I q K m)

lemma N_mono : Monotone (N I q K) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨k, hk, b, hb₁, hb₂, hx⟩ => ⟨k, hk.trans h, b, hb₁, hb₂, hx⟩

def Good (c₀ : ℕ) (x : M I q K) : Prop :=
  ∃ z : Z1 I q K, mkM I q K z = x ∧ ∀ j, coeffC I q K 1 j z.1 ∈ Dg I q K (j - c₀)

lemma good_of_mem (c₀ : ℕ) {x : M I q K} (hx : x ∈ N I q K c₀) : Good I q K c₀ x := by
  unfold N at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, b, hb₁, hb₂, rfl⟩ := h
    refine ⟨zZ I q K k b hb₁ hb₂, rfl, fun j => ?_⟩
    show coeffC I q K 1 j (zC I q K 1 k b hb₂) ∈ _
    rw [coeffC_zC]
    split_ifs with hj
    · subst hj
      obtain ⟨w, rfl⟩ := hb₁
      refine Submodule.mem_map.mpr ⟨w, fun s => ?_, rfl⟩
      rw [Nat.sub_eq_zero_of_le hk, pow_zero, Ideal.one_eq_top, Ideal.map_top]
      trivial
    · exact Submodule.zero_mem _
  | zero =>
    exact ⟨0, mkM_zero I q K, fun j => by
      rw [Submodule.coe_zero, coeffC_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hy
    refine ⟨z + z', mkM_add I q K z z', fun j => ?_⟩
    rw [Submodule.coe_add, coeffC_add]
    exact Submodule.add_mem _ (hz j) (hz' j)
  | smul r x _ hx =>
    obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨r • z, mkM_smul I q K r z, fun j => ?_⟩
    rw [Submodule.coe_smul, coeffC_smul]
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨w, hw, hdw⟩ := Submodule.mem_map.mp (hz x.2)
    rw [← hdw, ← LinearMap.map_smul]
    refine Submodule.mem_map.mpr ⟨_, IC_anti I q K ?_ (smul_mem_IC I q K (Rr.coeff_mem I r x.1) hw),
      rfl⟩
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

theorem main (n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K 0,
      (∀ s : K.Idx 1, (OModulePresheaf.unit q).d K 0 w s ∈
        Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
          (I ^ (n + c))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K 0,
        (∀ s : K.Idx 0, w' s ∈
          Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
            (I ^ n)) ∧
        (OModulePresheaf.unit q).d K 0 w' = (OModulePresheaf.unit q).d K 0 w := by
  obtain ⟨c₀, hc₀⟩ := (monotone_stabilizes_iff_noetherian (R := Rr I) (M := M I q K)).mpr
    inferInstance ⟨N I q K, N_mono I q K⟩
  refine ⟨c₀, fun w hw => ?_⟩
  set b := (OModulePresheaf.unit q).d K 0 w with hb
  have hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0) := ⟨w, rfl⟩
  have hmem : cls I q K (n + c₀) b hb₁ hw ∈ N I q K (n + c₀) :=
    Submodule.subset_span ⟨n + c₀, le_rfl, b, hb₁, hw, rfl⟩
  have hstab : N I q K c₀ = N I q K (n + c₀) := hc₀ (n + c₀) (Nat.le_add_left c₀ n)
  rw [← hstab] at hmem
  obtain ⟨z, hz, hgood⟩ := good_of_mem I q K c₀ hmem
  have hdiff : zZ I q K (n + c₀) b hb₁ hw - z ∈ B1 I q K := (mkM_eq_mkM I q K).mp hz.symm
  obtain ⟨w', hw'⟩ := (mem_B1 I q K _).mp hdiff
  change (F' I q).d (K' I q K) 0 w' = zC I q K 1 (n + c₀) b hw - z.1 at hw'

  have key := congrArg (coeffC I q K 1 (n + c₀)) hw'
  rw [coeffC_d, coeffC_sub, coeffC_zC, if_pos rfl] at key
  obtain ⟨w₁, hw₁, hdw₁⟩ := Submodule.mem_map.mp (hgood (n + c₀))
  rw [Nat.add_sub_cancel] at hw₁
  refine ⟨w₁ + coeffC I q K 0 (n + c₀) w', fun s => ?_, ?_⟩
  · have h2 := Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_add_right n c₀))
      (coeffC_mem I q K 0 (n + c₀) w' s)
    show (show Γ(P, K.inter s) from w₁ s) +
        (show Γ(P, K.inter s) from coeffC I q K 0 (n + c₀) w' s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom (I ^ n)
    exact Ideal.add_mem _ (hw₁ s) h2
  · rw [map_add, hdw₁, key, add_sub_cancel]

end Main

end SolKS
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.SolKS"

open SolKS in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K 0,
      (∀ s : K.Idx 1, (OModulePresheaf.unit q).d K 0 w s ∈
        Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
          (I ^ (n + c))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K 0,
        (∀ s : K.Idx 0, w' s ∈
          Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
            (I ^ n)) ∧
        (OModulePresheaf.unit q).d K 0 w' = (OModulePresheaf.unit q).d K 0 w :=
  SolKS.main I q K n
end 
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper. -/
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K 0,
      (∀ s : K.Idx 1, (OModulePresheaf.unit q).d K 0 w s ∈
        Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
          (I ^ (n + c))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K 0,
        (∀ s : K.Idx 0, w' s ∈
          Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
            (I ^ n)) ∧
        (OModulePresheaf.unit q).d K 0 w' = (OModulePresheaf.unit q).d K 0 w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.solution
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper. -/
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry"

noncomputable section

namespace FormalGAGAFiniteSqZeroAux

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite TrivSqZeroExt"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)} (F : OModulePresheaf q)

scoped instance instModuleMop (U : P.Opens) : Module (Γ(P, U))ᵐᵒᵖ (F.obj U) :=
  Module.compHom (F.obj U) ((RingHom.id Γ(P, U)).fromOpposite fun a b => mul_comm a b)

scoped instance instIsCentralScalar (U : P.Opens) : IsCentralScalar Γ(P, U) (F.obj U) := ⟨fun _ _ => rfl⟩

abbrev T (U : P.Opens) : Type u := TrivSqZeroExt Γ(P, U) (F.obj U)

example (U : P.Opens) : CommRing (T F U) := inferInstance

abbrev rmap {U V : P.Opens} (h : V ≤ U) : Γ(P, U) →+* Γ(P, V) := (P.presheaf.map (homOfLE h).op).hom

def ρ {U V : P.Opens} (h : V ≤ U) : T F U →+* T F V where
  toFun x := (rmap h x.fst, F.res h x.snd)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · change F.res h (x.fst • y.snd + MulOpposite.op y.fst • x.snd) =
        rmap h x.fst • F.res h y.snd + MulOpposite.op (rmap h y.fst) • F.res h x.snd
      rw [map_add, op_smul_eq_smul, op_smul_eq_smul, F.res_smul, F.res_smul]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp

@[scoped simp] lemma fst_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).fst = rmap h x.fst := rfl
@[scoped simp] lemma snd_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).snd = F.res h x.snd := rfl

lemma ρ_inl {U V : P.Opens} (h : V ≤ U) (a : Γ(P, U)) : ρ F h (inl a) = inl (rmap h a) :=
  TrivSqZeroExt.ext rfl (by simp)

lemma ρ_inr {U V : P.Opens} (h : V ≤ U) (m : F.obj U) : ρ F h (inr m) = inr (F.res h m) :=
  TrivSqZeroExt.ext (by simp) rfl

lemma ρ_refl (U : P.Opens) : ρ F (le_refl U) = RingHom.id _ := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE (le_refl U)).op).hom x.fst = x.fst
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), P.presheaf.map_id]; rfl
  · exact F.res_refl_apply U x.snd

lemma ρ_comp {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) : (ρ F h).comp (ρ F h') = ρ F (h.trans h') := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE h).op).hom ((P.presheaf.map (homOfLE h').op).hom x.fst) =
      (P.presheaf.map (homOfLE (h.trans h')).op).hom x.fst
    rw [← CommRingCat.comp_apply, ← P.presheaf.map_comp]; rfl
  · exact F.res_res h h' x.snd

lemma ρ_ρ {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) (x : T F U) : ρ F h (ρ F h' x) = ρ F (h.trans h') x :=
  RingHom.congr_fun (ρ_comp F h h') x

def Tfun : P.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (T F U.unop.1)
  map {U V} i := CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le))
  map_id U := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    exact ρ_refl F U.unop.1
  map_comp {U V W} i j := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    exact (ρ_comp F _ _).symm

@[scoped simp] lemma Tfun_obj (U : P.AffineZariskiSiteᵒᵖ) : (Tfun F).obj U = CommRingCat.of (T F U.unop.1) := rfl
@[scoped simp] lemma Tfun_map {U V : P.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (Tfun F).map i = CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le)) := rfl

def α : (toOpensFunctor P).op ⋙ P.presheaf ⟶ Tfun F where
  app U := (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
    P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1))
  naturality {U V} i := by
    ext a
    change algebraMap Γ(P, V.unop.1) (T F V.unop.1) (rmap (toOpens_mono i.unop.le) a) =
      ρ F (toOpens_mono i.unop.le) (algebraMap Γ(P, U.unop.1) (T F U.unop.1) a)
    rw [algebraMap_eq_inl, algebraMap_eq_inl, ρ_inl]

@[scoped simp] lemma α_app (U : P.AffineZariskiSiteᵒᵖ) :
    (α F).app U = (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
      P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1)) := rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in

lemma coequifibered (hq : F.IsQuasicoherent) : (α F).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  simp only [α_app, CommRingCat.hom_ofHom]
  letI inst : Algebra (T F U.1) (T F (P.basicOpen f)) := (ρ F (P.basicOpen_le f)).toAlgebra
  change IsLocalization.Away (algebraMap Γ(P, U.1) (T F U.1) f) (T F (P.basicOpen f))
  have hΓ : IsLocalization.Away f Γ(P, P.basicOpen f) := U.2.isLocalization_basicOpen f
  have halg : ∀ x : T F U.1, algebraMap (T F U.1) (T F (P.basicOpen f)) x = ρ F (P.basicOpen_le f) x :=
    fun _ => rfl
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, k, rfl⟩
    rw [halg, map_pow, algebraMap_eq_inl, ρ_inl]
    refine IsUnit.pow k (isUnit_inl_iff.mpr ?_)
    exact IsLocalization.map_units (M := .powers f) Γ(P, P.basicOpen f) ⟨f, 1, pow_one f⟩
  · intro z
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (.powers f) z.fst
    obtain ⟨k', m, hm⟩ := (hq U f).1 z.snd
    change z.fst * rmap (P.basicOpen_le f) (f ^ k) = rmap (P.basicOpen_le f) a at ha
    refine ⟨⟨algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m,
      ⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩⟩, ?_⟩
    change z * ρ F _ (algebraMap _ _ (f ^ (k + k'))) =
      ρ F _ (algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m)
    simp only [map_add, map_mul, algebraMap_eq_inl, ρ_inl, ρ_inr, inl_mul_inl, inl_mul_inr]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_add, fst_inl, fst_inl, fst_inr, add_zero, map_pow, pow_add, ← mul_assoc,
        ← map_pow, ha, mul_comm, map_pow]
    · rw [snd_mul, snd_add, snd_inl, snd_inl, snd_inr, fst_inl, smul_zero, zero_add, zero_add,
        op_smul_eq_smul, F.res_smul, hm, ← mul_smul, ← map_mul, ← pow_add]
  · intro x y hxy
    rw [halg, halg] at hxy
    have h1 : rmap (P.basicOpen_le f) x.fst = rmap (P.basicOpen_le f) y.fst := congrArg fst hxy
    have h2 : F.res (P.basicOpen_le f) (x.snd - y.snd) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg snd hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := .powers f) h1
    obtain ⟨k', hk'⟩ := (hq U f).2 _ h2
    change f ^ k * x.fst = f ^ k * y.fst at hk
    refine ⟨⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩, ?_⟩
    change algebraMap _ _ (f ^ (k + k')) * x = algebraMap _ _ (f ^ (k + k')) * y
    rw [← sub_eq_zero, ← mul_sub, algebraMap_eq_inl]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_inl, fst_sub, fst_zero, mul_sub, pow_add, mul_comm (f ^ k), mul_assoc, mul_assoc, hk,
        sub_self]
    · rw [snd_mul, fst_inl, snd_inl, snd_sub, snd_zero, smul_zero, add_zero, pow_add, mul_smul, hk', smul_zero]

section Scheme

variable (hq : F.IsQuasicoherent)

def D : (directedCover P).RelativeGluingData := relativeGluingData (coequifibered hq)

scoped instance : ((D hq).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

abbrev Y : Scheme.{u} := (D hq).glued

abbrev p : Y hq ⟶ P := (D hq).toBase

def ιU (U : P.AffineZariskiSite) : Spec (CommRingCat.of (T F U.1)) ⟶ Y hq := colimit.ι (D hq).functor U

lemma D_cover_f (U : P.AffineZariskiSite) : (D hq).cover.f U = ιU hq U := by
  simp [D, ιU]

scoped instance ιU_isOpenImmersion (U : P.AffineZariskiSite) : IsOpenImmersion (ιU hq U) := by
  rw [← D_cover_f]; exact (D hq).cover.map_prop U

lemma D_functor_map {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    (D hq).functor.map i = Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) := rfl

include hq in

lemma isOpenImmersion_SpecMap_ρ {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) :
      Spec (CommRingCat.of (T F U.1)) ⟶ Spec (CommRingCat.of (T F V.1))) :=
  (D hq).instIsOpenImmersionMapI₀Functor i

@[reassoc]
lemma SpecMap_ι {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) ≫ ιU hq V = ιU hq U :=
  colimit.w (D hq).functor i

lemma ι_toBase (U : P.AffineZariskiSite) :
    ιU hq U ≫ p hq = Spec.map ((α F).app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma toBase_preimage (U : P.AffineZariskiSite) : p hq ⁻¹ᵁ U.1 = (ιU hq U).opensRange := by
  have h := (D hq).toBase_preimage_eq_opensRange_ι U
  simp only [ιU]
  first | exact h | (simp at h ⊢; exact h)

lemma opensRange_functor_map_basicOpen (V : P.AffineZariskiSite) (r : Γ(P, V.1)) :
    ((D hq).functor.map (homOfLE (V.basicOpen_le r))).opensRange = PrimeSpectrum.basicOpen (inl r : T F V.1) :=
  opensRange_relativeGluingData_map (Tfun F) (α F) (coequifibered hq) (U := V) r

lemma SpecMap_ρ_ι {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U = ιU hq V := by

  let J : Type u := {r : (P.presheaf.obj (op U.1)) // P.basicOpen r ≤ V.1}
  let r' : J → (P.presheaf.obj (op V.1)) := fun r => rmap h r.1
  have hbo : ∀ r : J, P.basicOpen (r' r) = P.basicOpen r.1 := fun r =>
    (P.basicOpen_res r.1 (homOfLE h).op).trans (inf_eq_right.mpr r.2)
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨r, hr, hxr⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (h hx)
    refine Opens.mem_iSup.mpr ⟨⟨r' ⟨r, hr⟩, ⟨r, hr⟩, rfl⟩, ?_⟩
    change x ∈ P.basicOpen (r' ⟨r, hr⟩)
    rw [hbo]; exact hxr
  have hspanT : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) = ⊤ := by
    have : Ideal.map (algebraMap Γ(P, V.1) (T F V.1)) (Ideal.span (Set.range r')) = ⊤ := by
      rw [hspan, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at this
    exact this
  have iV : ∀ r : J, V.basicOpen (r' r) ≤ V := fun r => V.basicOpen_le (r' r)
  have iU : ∀ r : J, V.basicOpen (r' r) ≤ U := fun r => ⟨r.1, (hbo r).symm⟩
  let 𝒲 : (Spec (CommRingCat.of (T F V.1))).OpenCover :=
    { I₀ := J
      X := fun r => Spec (CommRingCat.of (T F (P.basicOpen (r' r))))
      f := fun r => Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r))))
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun r => isOpenImmersion_SpecMap_ρ hq (homOfLE (iV r))⟩
        have hx : ∃ r : J, x ∈ PrimeSpectrum.basicOpen (inl (r' r) : T F V.1) := by
          by_contra hcon
          push Not at hcon
          have hle : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) ≤ x.asIdeal :=
            Ideal.span_le.mpr (by
              rintro _ ⟨r, rfl⟩
              by_contra h'
              exact hcon r ((PrimeSpectrum.mem_basicOpen _ _).mpr h'))
          rw [hspanT, top_le_iff] at hle
          exact x.2.ne_top hle
        obtain ⟨r, hr⟩ := hx
        rw [← opensRange_functor_map_basicOpen hq V (r' r)] at hr
        obtain ⟨y, hy⟩ := hr
        exact ⟨r, y, hy⟩ }
  refine Cover.hom_ext 𝒲 _ _ fun r ↦ ?_
  change Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ Spec.map (CommRingCat.ofHom (ρ F h)) ≫
    ιU hq U = Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ ιU hq V
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ρ_comp]
  exact (SpecMap_ι hq (homOfLE (iU r))).trans (SpecMap_ι hq (homOfLE (iV r))).symm

end Scheme

section Sections

variable (hq : F.IsQuasicoherent)

lemma appLE_congr_hom {X₁ X₂ : Scheme.{u}} {f g : X₁ ⟶ X₂} (hfg : f = g) (U : X₂.Opens) (V : X₁.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

lemma appLE_top_top {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂) (e : (⊤ : X₁.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have : (homOfLE e).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this]
  simp

lemma preimage_ι_eq_top (U : P.AffineZariskiSite) : ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) = ⊤ := by
  rw [toBase_preimage, Scheme.Hom.preimage_opensRange]

lemma le_preimage_ι (U : P.AffineZariskiSite) :
    (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤ ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) :=
  (preimage_ι_eq_top hq U).ge

def eHom (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ⟶ CommRingCat.of (T F U.1) :=
  (ιU hq U).appLE (p hq ⁻¹ᵁ U.1) ⊤ (le_preimage_ι hq U) ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom

scoped instance isIso_eHom (U : P.AffineZariskiSite) : IsIso (eHom hq U) := by
  have h1 : IsIso ((ιU hq U).app (p hq ⁻¹ᵁ U.1)) := Scheme.Hom.isIso_app _ _ (by rw [toBase_preimage])
  have h2 : IsIso ((Spec (CommRingCat.of (T F U.1))).presheaf.map (homOfLE (le_preimage_ι hq U)).op) := by
    have : homOfLE (le_preimage_ι hq U) = eqToHom (preimage_ι_eq_top hq U).symm := Subsingleton.elim _ _
    rw [this, eqToHom_op]; infer_instance
  unfold eHom Scheme.Hom.appLE
  infer_instance

def e (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ≃+* T F U.1 :=
  (asIso (eHom hq U)).commRingCatIsoToRingEquiv

lemma e_apply (U : P.AffineZariskiSite) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) : e hq U x = eHom hq U x := rfl

lemma map_eHom {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    (Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op ≫ eHom hq V = eHom hq U ≫ CommRingCat.ofHom (ρ F h) := by
  unfold eHom
  have hle : (⊤ : (Spec (CommRingCat.of (T F V.1))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U) ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) := by
    rw [Scheme.Hom.comp_preimage, preimage_ι_eq_top]; exact (Opens.map_top _).ge
  rw [Scheme.Hom.map_appLE_assoc,
    appLE_congr_hom (SpecMap_ρ_ι hq h).symm (p hq ⁻¹ᵁ U.1) ⊤ _ hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ (p hq ⁻¹ᵁ U.1) ⊤ ⊤ (le_preimage_ι hq U) (Opens.map_top _).ge,
    Category.assoc, appLE_top_top, Scheme.ΓSpecIso_naturality, Category.assoc]

lemma e_map {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) :
    e hq V ((Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op x) = ρ F h (e hq U x) := by
  rw [e_apply, e_apply, ← CommRingCat.comp_apply, map_eHom hq h, CommRingCat.comp_apply]
  rfl

lemma appLE_eHom (U : P.AffineZariskiSite) :
    (p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl ≫ eHom hq U = (α F).app (op U) := by
  have h1 : (⊤ : (Spec _).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by rw [IsAffineOpen.fromSpec_preimage_self]
  have h2 : (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤
      (Spec.map ((α F).app (op U)) ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.comp_preimage]; exact (Opens.map_top _).ge.trans ((Spec.map _).preimage_mono h1)
  have h4 : U.2.fromSpec.appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(P, U.1)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← CategoryTheory.Functor.map_comp]
    have : ((eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE h1).op) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have h5 : (Spec.map ((α F).app (op U))).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom =
      (Scheme.ΓSpecIso (P.presheaf.obj (op U.1))).hom ≫ (α F).app (op U) :=
    Scheme.ΓSpecIso_naturality _
  unfold eHom
  rw [Scheme.Hom.appLE_comp_appLE_assoc, appLE_congr_hom (ι_toBase hq U) U.1 ⊤ _ h2]
  trans (U.2.fromSpec.appLE U.1 ⊤ h1 ≫ (Spec.map ((α F).app (op U))).appLE ⊤ ⊤ (Opens.map_top _).ge) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom
  · congr 1
  rw [h4, Category.assoc, appLE_top_top]
  exact (congrArg ((Scheme.ΓSpecIso Γ(P, U.1)).inv ≫ ·) h5).trans (Iso.inv_hom_id_assoc _ _)

lemma e_appLE (U : P.AffineZariskiSite) (a : Γ(P, U.1)) :
    e hq U ((p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl a) = inl a := by
  rw [e_apply, ← CommRingCat.comp_apply, appLE_eHom, α_app]
  rfl

theorem isFinite_p (hc : F.IsCoherent) : IsFinite (p hq) := by
  refine AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData (coequifibered hq) fun U => ?_
  change (algebraMap Γ(P, U.1) (T F U.1)).Finite
  rw [RingHom.finite_algebraMap]
  haveI : Module.Finite Γ(P, U.1) (F.obj U.1) := hc ⟨U.1, U.2⟩
  exact inferInstanceAs (Module.Finite Γ(P, U.1) (Γ(P, U.1) × F.obj U.1))

end Sections

section AffineHom

variable (hq : F.IsQuasicoherent)

scoped instance isAffineHom_p : IsAffineHom (p hq) :=
  isAffineHom_of_forall_exists_isAffineOpen _ fun x => by
    obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top P).ge (Set.mem_univ x))
    exact ⟨U.1, hxU, U.2, by rw [toBase_preimage hq ⟨U.1, U.2⟩]; exact isAffineOpen_opensRange _⟩

end AffineHom

section Ideals

variable (F) (U : P.Opens) (I' : Ideal A)

def σT : A →+* T F U :=
  (algebraMap Γ(P, U) (T F U)).comp (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap

lemma σT_apply (a : A) : σT F U a = inl ((Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a) := rfl

lemma algebraMap_smul_eq (a : A) (m : F.obj U) :
    (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a • m = a • m := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  exact algebraMap_smul Γ(P, U) a m

lemma sections_smul_mem {m : F.obj U} (hm : m ∈ I' • (⊤ : Submodule A (F.obj U))) (r : Γ(P, U)) :
    r • m ∈ I' • (⊤ : Submodule A (F.obj U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

lemma smul_mem_of_fst_mem {r : Γ(P, U)}
    (hr : r ∈ I'.map (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap) (m : F.obj U) :
    r • m ∈ I' • (⊤ : Submodule A (F.obj U)) := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [algebraMap_smul_eq]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_smul]; exact sections_smul_mem F U I' hx t

def J : Ideal (T F U) where
  carrier := {z | z.fst ∈ I'.map (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap ∧
    z.snd ∈ I' • (⊤ : Submodule A (F.obj U))}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {x y} hx hy := ⟨by rw [fst_add]; exact Ideal.add_mem _ hx.1 hy.1,
    by rw [snd_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' t z hz := by
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, fst_mul]; exact Ideal.mul_mem_left _ _ hz.1
    · rw [smul_eq_mul, snd_mul, op_smul_eq_smul]
      exact Submodule.add_mem _ (sections_smul_mem F U I' hz.2 _) (smul_mem_of_fst_mem F U I' hz.1 _)

lemma map_σT_le : I'.map (σT F U) ≤ J F U I' := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  refine ⟨?_, ?_⟩
  · rw [σT_apply, fst_inl]; exact Ideal.mem_map_of_mem _ ha
  · rw [σT_apply, snd_inl]; exact Submodule.zero_mem _

lemma snd_mem_of_mem_map_σT {z : T F U} (hz : z ∈ I'.map (σT F U)) :
    z.snd ∈ I' • (⊤ : Submodule A (F.obj U)) :=
  (map_σT_le F U I' hz).2

lemma inr_mem_map_σT {m : F.obj U} (hm : m ∈ I' • (⊤ : Submodule A (F.obj U))) :
    (inr m : T F U) ∈ I'.map (σT F U) := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [← algebraMap_smul_eq, ← inl_mul_inr, ← σT_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [inr_add]; exact Ideal.add_mem _ hx hy

end Ideals

section Cech

variable [IsSeparated q]

abbrev Ks (_hq : F.IsQuasicoherent) (K : P.OrderedAffineCover) {i : ℕ} (s : K.Idx i) : P.AffineZariskiSite :=
  ⟨K.inter s, K.isAffineOpen_inter q s⟩

variable (hq : F.IsQuasicoherent) (K : P.OrderedAffineCover)

abbrev KY : (Y hq).OrderedAffineCover := K.comap (p hq)

abbrev toP {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) →+* Γ(Y hq, p hq ⁻¹ᵁ K.inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op).hom

abbrev ofP {i : ℕ} (s : K.Idx i) : Γ(Y hq, p hq ⁻¹ᵁ K.inter s) →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.comap_inter_le (p hq) s)).op).hom

lemma Ymap_Ymap {U V W : (Y hq).Opens} (f : op U ⟶ op V) (g : op V ⟶ op W) (h : op U ⟶ op W) (x : Γ(Y hq, U)) :
    (Y hq).presheaf.map g ((Y hq).presheaf.map f x) = (Y hq).presheaf.map h x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

lemma Ymap_id {U : (Y hq).Opens} (f : op U ⟶ op U) (x : Γ(Y hq, U)) : (Y hq).presheaf.map f x = x := by
  rw [Subsingleton.elim f (𝟙 _), CategoryTheory.Functor.map_id]; rfl

lemma toP_ofP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, p hq ⁻¹ᵁ K.inter s)) : toP hq K s (ofP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

lemma ofP_toP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) : ofP hq K s (toP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

def eY {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) ≃+* T F (K.inter s) where
  toFun x := e hq (Ks hq K s) (toP hq K s x)
  invFun t := ofP hq K s ((e hq (Ks hq K s)).symm t)
  left_inv x := by
    change ofP hq K s ((e hq (Ks hq K s)).symm (e hq (Ks hq K s) (toP hq K s x))) = x
    rw [RingEquiv.symm_apply_apply, ofP_toP]
  right_inv t := by
    change e hq (Ks hq K s) (toP hq K s (ofP hq K s ((e hq (Ks hq K s)).symm t))) = t
    rw [toP_ofP, RingEquiv.apply_symm_apply]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add' x y := by rw [map_add, map_add]

lemma eY_apply {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) :
    eY hq K s x = e hq (Ks hq K s) (toP hq K s x) := rfl

abbrev σY {i : ℕ} (s : K.Idx i) : A →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top).hom

lemma eY_σY {i : ℕ} (s : K.Idx i) (a : A) : eY hq K s (σY hq K s a) = σT F (K.inter s) a := by
  rw [eY_apply, σT_apply, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  change e hq (Ks hq K s) (((p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top ≫
    (Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = _
  rw [Scheme.Hom.appLE_map, ← Scheme.Hom.appLE_comp_appLE (p hq) q ⊤ (K.inter s) (p hq ⁻¹ᵁ K.inter s) le_top le_rfl,
    CommRingCat.comp_apply]
  exact e_appLE hq (Ks hq K s) _

lemma eY_comp_σY {i : ℕ} (s : K.Idx i) : (eY hq K s).toRingHom.comp (σY hq K s) = σT F (K.inter s) :=
  RingHom.ext (eY_σY hq K s)

def Φ (i : ℕ) (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) (s : K.Idx i) : T F (K.inter s) :=
  eY hq K s (c s)

def Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i :=
  fun s => (eY hq K s).symm (c s)

lemma Φ_Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : Φ hq K i (Ψ hq K i c) = c := by
  funext s; exact (eY hq K s).apply_symm_apply (c s)

def dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) : T F (K.inter s) :=
  ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • ρ F (K.inter_le_inter_face s j) (c (K.face s j))

lemma snd_dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) :
    (dT K c s).snd = F.d K 0 (fun t => (c t).snd) s := by
  rw [OModulePresheaf.d_apply, dT, snd_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (snd_smul _ _).trans (by rw [snd_ρ])

lemma fst_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).fst = 0 := by
  rw [dT, fst_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact (fst_smul _ _).trans (by rw [fst_ρ, fst_inr, map_zero, smul_zero])

lemma snd_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).snd = F.d K 0 w s := by
  rw [snd_dT]; rfl

lemma dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    dT K (fun t => inr (w t)) s = inr (F.d K 0 w s) :=
  TrivSqZeroExt.ext (by rw [fst_dT_inr, fst_inr]) (by rw [snd_dT_inr, snd_inr])

lemma Φ_d (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0) :
    Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 c) = dT K (Φ hq K 0 c) := by
  funext s
  rw [Φ, OModulePresheaf.d_apply, dT]
  change eY hq K s (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
    (Y hq).presheaf.map (homOfLE ((KY hq K).inter_le_inter_face s j)).op (c ((KY hq K).face s j))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [Φ, eY_apply, eY_apply, ← e_map hq (U := Ks hq K (K.face s j)) (V := Ks hq K s) (K.inter_le_inter_face s j)]
  congr 1
  have hcommon : op ((KY hq K).inter ((KY hq K).face s j)) ⟶ op (p hq ⁻¹ᵁ K.inter s) :=
    (homOfLE (((p hq).preimage_mono (K.inter_le_inter_face s j)).trans (K.le_comap_inter (p hq) (K.face s j)))).op
  change (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _)) = (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _))
  exact (Ymap_Ymap hq _ _ hcommon _).trans (Ymap_Ymap hq _ _ hcommon _).symm

lemma mem_map_σY_iff {i : ℕ} (s : K.Idx i) (I' : Ideal A) (x : Γ(Y hq, (KY hq K).inter s)) :
    x ∈ I'.map (σY hq K s) ↔ eY hq K s x ∈ I'.map (σT F (K.inter s)) := by
  constructor
  · intro hx
    have := Ideal.mem_map_of_mem (eY hq K s).toRingHom hx
    rwa [Ideal.map_map, eY_comp_σY] at this
  · intro hy
    rw [← eY_comp_σY hq K s, ← Ideal.map_map] at hy
    have := Ideal.mem_map_of_mem (eY hq K s).symm.toRingHom hy
    rwa [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this

end Cech

theorem main [IsNoetherianRing A] (I : Ideal A) [IsProper q] (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w := by
  haveI : IsFinite (p hq) := isFinite_p hq hc
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper I (p hq ≫ q) (KY hq K) n
  refine ⟨c, fun w hw => ?_⟩
  let wY : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0 := Ψ hq K 0 fun s => inr (w s)
  have hΦwY : Φ hq K 0 wY = fun s => inr (w s) := Φ_Ψ hq K 0 _
  have hdwY : ∀ s : K.Idx 1,
      eY hq K s ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 wY s) = inr (F.d K 0 w s) := by
    intro s
    have := congr_fun (Φ_d hq K wY) s
    rw [hΦwY, dT_inr] at this
    exact this
  obtain ⟨w'Y, hw'1, hw'2⟩ := hc' wY fun s =>
    (mem_map_σY_iff hq K s _ _).mpr (by rw [hdwY s]; exact inr_mem_map_σT F _ _ (hw s))
  refine ⟨fun s => (Φ hq K 0 w'Y s).snd, fun s => ?_, ?_⟩
  · exact snd_mem_of_mem_map_σT F _ _ ((mem_map_σY_iff hq K s _ _).mp (hw'1 s))
  · funext s
    calc F.d K 0 (fun t => (Φ hq K 0 w'Y t).snd) s
        = (dT K (Φ hq K 0 w'Y) s).snd := (snd_dT K _ s).symm
      _ = (Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 w'Y) s).snd := by rw [Φ_d]
      _ = (Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 wY) s).snd := by rw [hw'2]
      _ = (dT K (Φ hq K 0 wY) s).snd := by rw [Φ_d]
      _ = F.d K 0 w s := by rw [hΦwY, dT_inr, snd_inr]

end FormalGAGAFiniteSqZeroAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux"

namespace FormalGAGAFiniteSqZeroDock

variable {A : Type u} [CommRing A] {ι : Type u} {M : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

lemma apply_mem_smul_top (J : Ideal A) {x : ∀ i, M i} (hx : x ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    x i ∈ J • (⊤ : Submodule A (M i)) := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun y z hy hz => ?_)
  · rw [Pi.smul_apply]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [Pi.add_apply]
    exact Submodule.add_mem _ hy hz

lemma single_mem_smul_top [DecidableEq ι] (J : Ideal A) (i : ι) {m : M i}
    (hm : m ∈ J • (⊤ : Submodule A (M i))) : (Pi.single i m : ∀ i, M i) ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  refine Submodule.smul_induction_on hm (fun a ha m' _ => ?_) (fun y z hy hz => ?_)
  · rw [Pi.single_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [Pi.single_add]
    exact Submodule.add_mem _ hy hz

lemma mem_smul_top_of_forall [Fintype ι] [DecidableEq ι] (J : Ideal A) {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ J • (⊤ : Submodule A (M i))) : x ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ fun i _ => single_mem_smul_top J i (hx i)

end FormalGAGAFiniteSqZeroDock
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K 0,
      F.d K 0 t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 1)) →
      ∃ a : F.cochain K 0, F.d K 0 a = 0 ∧ t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K 0)) := by
  classical
  obtain ⟨c, hc'⟩ := FormalGAGAFiniteSqZeroAux.main I hc hqc K n
  refine ⟨c, fun t ht => ?_⟩
  obtain ⟨w', hw'1, hw'2⟩ := hc' t fun s => FormalGAGAFiniteSqZeroDock.apply_mem_smul_top _ ht s
  refine ⟨t - w', ?_, ?_⟩
  · rw [map_sub, hw'2, sub_self]
  · rw [sub_sub_cancel]
    exact FormalGAGAFiniteSqZeroDock.mem_smul_top_of_forall _ hw'1
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper. -/
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K 0,
      F.d K 0 t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 1)) →
      ∃ a : F.cochain K 0, F.d K 0 a = 0 ∧ t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K 0)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.solution
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper. -/
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
attribute [-instance] ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

universe u

noncomputable section

namespace SolFF0SepUnit

lemma preimage_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Fintype ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ (⨅ j, U j) = ⨅ j, f ⁻¹ᵁ (U j) := by
  classical
  rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

section Setup

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

def Rr : Type u := ↥(reesAlgebra I)

scoped instance : CommRing (Rr I) := inferInstanceAs (CommRing ↥(reesAlgebra I))
scoped instance : Algebra A (Rr I) := inferInstanceAs (Algebra A ↥(reesAlgebra I))
scoped instance [IsNoetherianRing A] : IsNoetherianRing (Rr I) :=
  inferInstanceAs (IsNoetherianRing ↥(reesAlgebra I))

abbrev Rr.val (r : Rr I) : A[X] := (show ↥(reesAlgebra I) from r).1

lemma Rr.coeff_mem (r : Rr I) (i : ℕ) : (Rr.val I r).coeff i ∈ I ^ i :=
  (mem_reesAlgebra_iff _ _).mp (show ↥(reesAlgebra I) from r).2 i

abbrev Rr.mk (p : A[X]) (hp : p ∈ reesAlgebra I) : Rr I := (show ↥(reesAlgebra I) from ⟨p, hp⟩)

abbrev Rr.incl : Rr I →+* A[X] := (reesAlgebra I).val.toRingHom

abbrev sA : Spec (CommRingCat.of (Rr I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Rr I)))

abbrev sX : Spec (CommRingCat.of A[X]) ⟶ Spec (CommRingCat.of (Rr I)) :=
  Spec.map (CommRingCat.ofHom (Rr.incl I))

abbrev P' : Scheme.{u} := pullback q (sA I)

abbrev fst' : P' I q ⟶ P := pullback.fst q (sA I)

abbrev π' : P' I q ⟶ Spec (CommRingCat.of (Rr I)) := pullback.snd q (sA I)

abbrev P₁ : Scheme.{u} := pullback (π' I q) (sX I)

abbrev g : P₁ I q ⟶ P' I q := pullback.fst (π' I q) (sX I)

abbrev snd₁ : P₁ I q ⟶ Spec (CommRingCat.of A[X]) := pullback.snd (π' I q) (sX I)

abbrev p₁ : P₁ I q ⟶ P := g I q ≫ fst' I q

lemma sX_sA : sX I ≫ sA I = Spec.map (CommRingCat.ofHom (algebraMap A A[X])) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma isPullback_P' : IsPullback (fst' I q) (π' I q) q (sA I) := IsPullback.of_hasPullback _ _

lemma isPullback_P₁ :
    IsPullback (p₁ I q) (snd₁ I q) q (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) := by
  rw [← sX_sA]
  exact IsPullback.paste_horiz (IsPullback.of_hasPullback (π' I q) (sX I)) (isPullback_P' I q)

scoped instance : IsAffineHom (g I q) := MorphismProperty.pullback_fst _ _ inferInstance
scoped instance : IsAffineHom (fst' I q) := MorphismProperty.pullback_fst _ _ inferInstance

def alg (U : P.Opens) : A →+* Γ(P, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U le_top).hom

lemma alg_res {U V : P.Opens} (h : V ≤ U) (a : A) :
    P.presheaf.map (homOfLE h).op (alg q U a) = alg q V a := by
  simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

def T (W : (P₁ I q).Opens) : Γ(P₁ I q, W) :=
  ((snd₁ I q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom X)

def θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) : Γ(P, U)[X] →+* Γ(P₁ I q, W) :=
  eval₂RingHom ((p₁ I q).appLE U W e).hom (T I q W)

lemma θ_C (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (c : Γ(P, U)) :
    θ I q U W e (C c) = ((p₁ I q).appLE U W e).hom c := by
  simp [θ]

lemma θ_X (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) :
    θ I q U W e X = T I q W := by
  simp [θ]

lemma appLE_top_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  f.appLE_eq_app

lemma ΓSpecIso_inv_C (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A A[X]))
  have := congrArg (fun ψ : CommRingCat.of A ⟶ _ => ψ.hom a) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

lemma θ_map (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : A[X]) :
    θ I q U W e (Polynomial.map (alg q U) r) =
      ((snd₁ I q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom r) := by
  have key : ((θ I q U W e).comp (mapRingHom (alg q U))) =
      ((snd₁ I q).appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      have lhs : ((p₁ I q).appLE U W e).hom (alg q U a) =
          ((p₁ I q ≫ q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      have rhs : ((snd₁ I q).appLE ⊤ W le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a)) =
          ((snd₁ I q ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ W le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        rw [ΓSpecIso_inv_C, ← appLE_top_top, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      rw [lhs, rhs]
      exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
        (appLE_congr_hom (isPullback_P₁ I q).w ⊤ W _ _)
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
  exact congrArg (fun φ : A[X] →+* Γ(P₁ I q, W) => φ r) key

lemma θ_res {U U' : P.Opens} {W W' : (P₁ I q).Opens} (e : W ≤ p₁ I q ⁻¹ᵁ U)
    (e' : W' ≤ p₁ I q ⁻¹ᵁ U') (hU : U' ≤ U) (hW : W' ≤ W) (p : Γ(P, U)[X]) :
    (P₁ I q).presheaf.map (homOfLE hW).op (θ I q U W e p) =
      θ I q U' W' e' (Polynomial.map (P.presheaf.map (homOfLE hU).op).hom p) := by
  have key : ((P₁ I q).presheaf.map (homOfLE hW).op).hom.comp (θ I q U W e) =
      (θ I q U' W' e').comp (mapRingHom (P.presheaf.map (homOfLE hU).op).hom) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact congrArg (fun φ : Γ(P, U)[X] →+* Γ(P₁ I q, W') => φ p) key

lemma θ_bijective {U : P.Opens} (hU : IsAffineOpen U) {W : (P₁ I q).Opens}
    (hW : W = p₁ I q ⁻¹ᵁ U ⊓ snd₁ I q ⁻¹ᵁ ⊤) :
    Function.Bijective (θ I q U W (hW.le.trans inf_le_left)) := by
  have H := isPullback_P₁ I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    hW (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hW).mp h1

  let ΦC : Γ(P, U) ⟶ CommRingCat.of Γ(P, U)[X] := CommRingCat.ofHom C
  let ΦX : Γ(Spec (CommRingCat.of A[X]), ⊤) ⟶ CommRingCat.of Γ(P, U)[X] :=
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom ≫ CommRingCat.ofHom (mapRingHom (alg q U))
  have w : q.appLE ⊤ U le_top ≫ ΦC =
      (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ ⊤ le_top ≫ ΦX := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ΦC, ΦX,
      CommRingCat.hom_ofHom, coe_mapRingHom]
    rw [appLE_top_top]
    change C ((q.appLE ⊤ U le_top).hom x) = Polynomial.map (alg q U)
      (((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom x)
    rw [Scheme.ΓSpecIso_naturality]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C]
    congr 1
    simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]
  let Φ : Γ(P₁ I q, W) ⟶ CommRingCat.of Γ(P, U)[X] := hP.desc ΦC ΦX w
  have hΦl : (p₁ I q).appLE U W _ ≫ Φ = ΦC := hP.inl_desc _ _ _
  have hΦr : (snd₁ I q).appLE ⊤ W _ ≫ Φ = ΦX := hP.inr_desc _ _ _
  set θ' := θ I q U W (hW.le.trans inf_le_left)

  have h1 : Φ.hom.comp θ' = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_C, RingHom.id_apply]
      change (((p₁ I q).appLE U W _) ≫ Φ).hom c = C c
      rw [hΦl]; rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_X, T, RingHom.id_apply]
      change ((snd₁ I q).appLE ⊤ W _ ≫ Φ).hom _ = X
      rw [hΦr]
      change Polynomial.map (alg q U) (((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom X) = X
      rw [Iso.inv_hom_id]
      simp

  have h2 : Φ ≫ CommRingCat.ofHom θ' = 𝟙 _ := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hΦl, Category.comp_id]
      ext c
      exact θ_C I q U W _ c
    · rw [← Category.assoc, hΦr, Category.comp_id]
      ext r
      change θ' (Polynomial.map (alg q U) ((Scheme.ΓSpecIso (CommRingCat.of A[X])).hom.hom r)) = _
      rw [θ_map]
      congr 1
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  constructor
  · intro x y hxy
    have := congrArg Φ.hom hxy
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, h1] at this
  · intro z
    refine ⟨Φ.hom z, ?_⟩
    change (Φ ≫ CommRingCat.ofHom θ').hom z = z
    rw [h2]; rfl

lemma closure_eq_top {U : P.Opens} (hU : IsAffineOpen U) {W' : (P' I q).Opens}
    (hW' : W' = fst' I q ⁻¹ᵁ U ⊓ π' I q ⁻¹ᵁ ⊤) :
    Subring.closure (Set.range ((fst' I q).appLE U W' (hW'.le.trans inf_le_left)).hom ∪
      Set.range ((π' I q).appLE ⊤ W' le_top).hom) = ⊤ := by
  have H := isPullback_P' I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    hW' (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hW').mp h1
  exact CommRingCat.closure_range_union_range_eq_top_of_isPushout hP

def algR (W' : (P' I q).Opens) : Rr I →+* Γ(P' I q, W') :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (π' I q).appLE ⊤ W' le_top).hom

def algR₁ (W : (P₁ I q).Opens) : Rr I →+* Γ(P₁ I q, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (g I q ≫ π' I q).appLE ⊤ W le_top).hom

lemma algR₁_eq_θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : Rr I) :
    algR₁ I q W r = θ I q U W e (Polynomial.map (alg q U) (Rr.val I r)) := by
  rw [θ_map]
  simp only [algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_congr_hom (pullback.condition (f := π' I q) (g := sX I)) ⊤ W _ le_top,
    ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top, CommRingCat.comp_apply, appLE_top_top]
  congr 1
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Rr.incl I))
  have := congrArg (fun ψ : CommRingCat.of (Rr I) ⟶ _ => ψ.hom r) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

lemma g_appLE_algR (W' : (P' I q).Opens) (r : Rr I) :
    ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (algR I q W' r) = algR₁ I q (g I q ⁻¹ᵁ W') r := by
  simp only [algR, algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma algR_res {W W' : (P' I q).Opens} (h : W ≤ W') (r : Rr I) :
    (P' I q).presheaf.map (homOfLE h).op (algR I q W' r) = algR I q W r := by
  simp only [algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma g_appLE_res {W W' : (P' I q).Opens} (h : W ≤ W') (x : Γ(P' I q, W')) :
    (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op
        (((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x) =
      ((g I q).appLE W (g I q ⁻¹ᵁ W) le_rfl).hom ((P' I q).presheaf.map (homOfLE h).op x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

def φg : OModulePresheaf.Hom (OModulePresheaf.unit (π' I q))
    (OModulePresheaf.pushforwardUnit (π' I q) (g I q)) where
  app W' :=
    { toFun := fun x => ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        show ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (algR I q W' r * (show Γ(P' I q, W') from x)) =
          algR₁ I q (g I q ⁻¹ᵁ W') r * ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
        rw [map_mul, g_appLE_algR] }
  app_smul W' a x := by
    show ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (a * (show Γ(P' I q, W') from x)) =
      ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a * ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
    exact map_mul _ a x
  naturality {W W'} h := by
    refine LinearMap.ext fun x => ?_
    exact (g_appLE_res I q h x).symm

lemma φg_app (W' : (P' I q).Opens) (x : Γ(P' I q, W')) :
    (φg I q).app W' x = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x := rfl

abbrev F' : OModulePresheaf (π' I q) := OModulePresheaf.im (φg I q)

abbrev F'val {W' : (P' I q).Opens} (y : (F' I q).obj W') : Γ(P₁ I q, g I q ⁻¹ᵁ W') := y.1

lemma F'_exists {W' : (P' I q).Opens} (y : (F' I q).obj W') :
    ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = F'val I q y :=
  LinearMap.mem_range.mp y.2

lemma mem_F'_iff (W' : (P' I q).Opens)
    (y : (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj W') :
    y ∈ LinearMap.range ((φg I q).app W') ↔
      ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = (show Γ(P₁ I q, g I q ⁻¹ᵁ W') from y) :=
  LinearMap.mem_range

lemma F'_res_val {W W' : (P' I q).Opens} (h : W ≤ W') (y : (F' I q).obj W') :
    F'val I q ((F' I q).res h y) =
      (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op (F'val I q y) := rfl

lemma F'_smul_val (W' : (P' I q).Opens) (a : Γ(P' I q, W')) (y : (F' I q).obj W') :
    F'val I q (a • y) = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a * F'val I q y := rfl

lemma F'_rsmul_val (W' : (P' I q).Opens) (r : Rr I) (y : (F' I q).obj W') :
    F'val I q (r • y) = algR₁ I q (g I q ⁻¹ᵁ W') r * F'val I q y := rfl

lemma F'_add_val (W' : (P' I q).Opens) (y y' : (F' I q).obj W') :
    F'val I q (y + y') = F'val I q y + F'val I q y' := rfl

lemma F'_zero_val (W' : (P' I q).Opens) : F'val I q (0 : (F' I q).obj W') = 0 := rfl

lemma F'_ext {W' : (P' I q).Opens} {y y' : (F' I q).obj W'} (h : F'val I q y = F'val I q y') :
    y = y' := Subtype.ext h

lemma isCoherent_F' : (F' I q).IsCoherent := fun U => by
  haveI : Module.Finite Γ(P' I q, U.1) ((OModulePresheaf.unit (π' I q)).obj U.1) :=
    inferInstanceAs (Module.Finite Γ(P' I q, U.1) Γ(P' I q, U.1))
  exact Module.Finite.of_surjective ((OModulePresheaf.kerImSES (φg I q)).proj.appSections U.1)
    ((OModulePresheaf.kerImSES (φg I q)).surjective U.1)

lemma res_eq_zero_iff_of_eq {X : Scheme.{u}} {W V₁ V₂ : X.Opens} (h : V₁ = V₂) (e₁ : V₁ ≤ W)
    (e₂ : V₂ ≤ W) (s : Γ(X, W)) :
    X.presheaf.map (homOfLE e₁).op s = 0 ↔ X.presheaf.map (homOfLE e₂).op s = 0 := by
  subst h; rfl

lemma isQuasicoherent_F' : (F' I q).IsQuasicoherent := by
  intro U f
  have hle : (P' I q).basicOpen f ≤ U.1 := (P' I q).basicOpen_le f
  constructor
  · intro x
    obtain ⟨a', ha'⟩ := F'_exists I q x
    haveI := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a₀, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) a'
    refine ⟨n, ⟨(φg I q).app U.1 a₀, ⟨a₀, rfl⟩⟩, F'_ext I q ?_⟩
    rw [F'_res_val, F'_smul_val, ← ha']
    change (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op
        (((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom a₀) = _
    dsimp only at h
    rw [mul_comm] at h
    change ((P' I q).presheaf.map (homOfLE hle).op).hom (f ^ n) * a' =
      ((P' I q).presheaf.map (homOfLE hle).op).hom a₀ at h
    rw [← map_mul, h, g_appLE_res]
  · intro y hy
    obtain ⟨x, hx⟩ := F'_exists I q y
    have h0 : (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op (F'val I q y) = 0 :=
      congrArg Subtype.val hy
    set f₁ : Γ(P₁ I q, g I q ⁻¹ᵁ U.1) := ((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom f with hf₁
    have hopen : g I q ⁻¹ᵁ (P' I q).basicOpen f = (P₁ I q).basicOpen f₁ := by
      rw [Scheme.preimage_basicOpen, hf₁, Scheme.Hom.appLE_eq_app]
    rw [res_eq_zero_iff_of_eq hopen _ ((P₁ I q).basicOpen_le f₁)] at h0
    haveI := (U.2.preimage (g I q)).isLocalization_basicOpen f₁
    have h0' : algebraMap Γ(P₁ I q, g I q ⁻¹ᵁ U.1) Γ(P₁ I q, (P₁ I q).basicOpen f₁)
        (F'val I q y) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f₁) _ _).mp h0'
    refine ⟨n, F'_ext I q ?_⟩
    rw [F'_smul_val, map_pow]
    exact hn

variable (K : P.OrderedAffineCover)

def K' : (P' I q).OrderedAffineCover where
  ι := K.ι
  U i := fst' I q ⁻¹ᵁ K.U i
  isAffineOpen i := (K.isAffineOpen i).preimage _
  iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top _ K.iSup_eq_top

lemma K'_inter {i : ℕ} (s : K.Idx i) : (K' I q K).inter s = fst' I q ⁻¹ᵁ K.inter s :=
  (preimage_iInf (fst' I q) fun j => K.U (s.1 j)).symm

lemma hW' {i : ℕ} (s : K.Idx i) : (K' I q K).inter s = fst' I q ⁻¹ᵁ K.inter s ⊓ π' I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq]

lemma hW {i : ℕ} (s : K.Idx i) :
    g I q ⁻¹ᵁ (K' I q K).inter s = p₁ I q ⁻¹ᵁ K.inter s ⊓ snd₁ I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq, Scheme.Hom.comp_preimage]

lemma e_s {i : ℕ} (s : K.Idx i) : g I q ⁻¹ᵁ (K' I q K).inter s ≤ p₁ I q ⁻¹ᵁ K.inter s :=
  (hW I q K s).le.trans inf_le_left

lemma e'_s {i : ℕ} (s : K.Idx i) : (K' I q K).inter s ≤ fst' I q ⁻¹ᵁ K.inter s :=
  (hW' I q K s).le.trans inf_le_left

end Setup

section Cochains

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
  [IsSeparated q] (K : P.OrderedAffineCover)

include q in
lemma haff {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := K.isAffineOpen_inter q s

def ΦC {i : ℕ} (s : K.Idx i) : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter s) ≃+* Γ(P, K.inter s)[X] :=
  (RingEquiv.ofBijective (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s))
    (θ_bijective I q (haff q K s) (hW I q K s))).symm

lemma ΦC_θ {i : ℕ} (s : K.Idx i) (p : Γ(P, K.inter s)[X]) :
    ΦC I q K s (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) p) = p :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).symm_apply_apply p

lemma θ_ΦC {i : ℕ} (s : K.Idx i) (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter s)) :
    θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) (ΦC I q K s v) = v :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).apply_symm_apply v

lemma ΦC_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter ((K' I q K).face s j))) :
    ΦC I q K s ((P₁ I q).presheaf.map
        (homOfLE ((g I q).preimage_mono ((K' I q K).inter_le_inter_face s j))).op v) =
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
        (ΦC I q K (K.face s j) v) := by
  have h := θ_res I q (e_s I q K (K.face s j)) (e_s I q K s) (K.inter_le_inter_face s j)
    ((g I q).preimage_mono ((K' I q K).inter_le_inter_face s j)) (ΦC I q K (K.face s j) v)
  rw [θ_ΦC] at h
  exact (congrArg (ΦC I q K s) h).trans (ΦC_θ I q K s _)

lemma ΦC_algR₁ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    ΦC I q K s (algR₁ I q _ r) = Polynomial.map (alg q (K.inter s)) (Rr.val I r) := by
  rw [algR₁_eq_θ I q (K.inter s) _ (e_s I q K s), ΦC_θ]

def coeffC (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) : (OModulePresheaf.unit q).cochain K i :=
  fun s => (ΦC I q K s (F'val I q (z s))).coeff j

lemma coeffC_apply (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    coeffC I q K i j z s = (ΦC I q K s (F'val I q (z s))).coeff j := rfl

lemma coeffC_add (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z + z') = coeffC I q K i j z + coeffC I q K i j z' := by
  funext s
  simp only [coeffC_apply, Pi.add_apply, F'_add_val, map_add, coeff_add]
  rfl

lemma coeffC_zero (i j : ℕ) : coeffC I q K i j 0 = 0 := by
  funext s
  change (ΦC I q K s (F'val I q (0 : (F' I q).obj _))).coeff j = 0
  rw [F'_zero_val, map_zero, coeff_zero]

lemma coeffC_sub (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z - z') = coeffC I q K i j z - coeffC I q K i j z' := by
  rw [eq_sub_iff_add_eq, ← coeffC_add, sub_add_cancel]

def F'valHom (W' : (P' I q).Opens) : (F' I q).obj W' →+ Γ(P₁ I q, g I q ⁻¹ᵁ W') :=
  { toFun := F'val I q, map_zero' := rfl, map_add' := fun _ _ => rfl }

lemma F'valHom_apply (W' : (P' I q).Opens) (y : (F' I q).obj W') : F'valHom I q W' y = F'val I q y := rfl

lemma coeffC_d (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K (i + 1) j ((F' I q).d (K' I q K) i z) =
      (OModulePresheaf.unit q).d K i (coeffC I q K i j z) := by
  funext s
  rw [coeffC_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  change _ = ∑ j' : Fin (i + 2), ((-1 : ℤ) ^ (j' : ℕ)) •
    (P.presheaf.map (homOfLE (K.inter_le_inter_face s j')).op).hom (coeffC I q K i j z (K.face s j'))
  rw [← F'valHom_apply, map_sum, map_sum, ← lcoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, lcoeff_apply, F'valHom_apply, F'_res_val, ΦC_res, coeff_map]
  rfl

lemma coeffC_smul (i j : ℕ) (r : Rr I) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (r • z) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, ((Rr.val I r).coeff x.1) • coeffC I q K i x.2 z := by
  funext s
  rw [Finset.sum_apply, coeffC_apply, Pi.smul_apply, F'_rsmul_val, map_mul, ΦC_algR₁, coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map]
  rfl

lemma coeffC_mem (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    (show Γ(P, K.inter s) from coeffC I q K i j z s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom
        (I ^ j) := by
  obtain ⟨x, hx⟩ := F'_exists I q (z s)
  rw [coeffC_apply, ← hx]
  set J : Ideal Γ(P, K.inter s) := I.map (alg q (K.inter s)) with hJ

  let S : Subring Γ(P' I q, (K' I q K).inter s) :=
    (reesAlgebra J).toSubring.comap
      ((ΦC I q K s).toRingHom.comp ((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom)
  have hS : Subring.closure (Set.range ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
      (e'_s I q K s)).hom ∪ Set.range ((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom) ≤ S := by
    rw [Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨r₀, rfl⟩)
    · show ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom
        (((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c)) ∈ reesAlgebra J
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← θ_C I q _ _ (e_s I q K s), ΦC_θ]
      exact Subalgebra.algebraMap_mem (reesAlgebra J) c
    · show ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom
        (((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom r₀)) ∈ reesAlgebra J
      have hr₀ : r₀ = (Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).hom.hom r₀) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [hr₀]
      change ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom (algR I q _ _)) ∈ _
      rw [g_appLE_algR, ΦC_algR₁]
      intro n
      rw [coeff_map, hJ, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Rr.coeff_mem I _ n)
  rw [closure_eq_top I q (haff q K s) (hW' I q K s)] at hS
  have hxS : x ∈ S := hS (Subring.mem_top x)
  have : ΦC I q K s (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom x) ∈ reesAlgebra J := hxS
  have := (mem_reesAlgebra_iff _ _).mp this j
  rwa [hJ, ← Ideal.map_pow] at this

def Sθ {i : ℕ} (s : K.Idx i) : Subring Γ(P, K.inter s)[X] :=
  (((g I q).appLE ((K' I q K).inter s) _ le_rfl).hom.range).comap
    (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s))

lemma mem_range_of_mem_Sθ {i : ℕ} (s : K.Idx i) {p : Γ(P, K.inter s)[X]} (hp : p ∈ Sθ I q K s) :
    (show (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj ((K' I q K).inter s) from
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) p) ∈
      LinearMap.range ((φg I q).app ((K' I q K).inter s)) :=
  (mem_F'_iff I q _ _).mpr (RingHom.mem_range.mp (Subring.mem_comap.mp hp))

lemma C_mem_Sθ {i : ℕ} (s : K.Idx i) (c : Γ(P, K.inter s)) : C c ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr
    ⟨((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c, ?_⟩)
  rw [θ_C, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma map_mem_Sθ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    Polynomial.map (alg q (K.inter s)) (Rr.val I r) ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr ⟨algR I q _ r, ?_⟩)
  rw [g_appLE_algR, algR₁_eq_θ I q (K.inter s) _ (e_s I q K s)]

lemma monomial_mem_Sθ {i : ℕ} (s : K.Idx i) {k : ℕ} {x : Γ(P, K.inter s)}
    (hx : x ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) :
    monomial k x ∈ Sθ I q K s := by
  change x ∈ Ideal.map (alg q (K.inter s)) (I ^ k) at hx
  unfold Ideal.map at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, rfl⟩ := h
    have : monomial k (alg q (K.inter s) a) = Polynomial.map (alg q (K.inter s))
        (Rr.val I (Rr.mk I (monomial k a) (reesAlgebra.monomial_mem.mpr ha))) :=
      (Polynomial.map_monomial _).symm
    rw [this]
    exact map_mem_Sθ I q K s _
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, ← C_mul_monomial]
    exact Subring.mul_mem _ (C_mem_Sθ I q K s c) hx

def zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) :
    (F' I q).cochain (K' I q K) i :=
  fun s => ⟨_, mem_range_of_mem_Sθ I q K s (monomial_mem_Sθ I q K s (hb s))⟩

lemma F'val_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) (s : K.Idx i) :
    F'val I q (zC I q K i k b hb s) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s) (monomial k (b s)) := rfl

lemma coeffC_zC (i k j : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) :
    coeffC I q K i j (zC I q K i k b hb) = if j = k then b else 0 := by
  funext s
  rw [coeffC_apply, F'val_zC, ΦC_θ, coeff_monomial]
  split_ifs with h h' h'
  · rfl
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · rfl

lemma F'val_d_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb) (s : K.Idx (i + 1)) :
    F'val I q ((F' I q).d (K' I q K) i (zC I q K i k b hb) s) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
        (monomial k ((OModulePresheaf.unit q).d K i b s)) := by
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  change _ = θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
    (monomial k (∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (b (K.face s j))))
  rw [← F'valHom_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, F'valHom_apply, F'_res_val, F'val_zC,
    θ_res I q (e_s I q K ((K' I q K).face s j)) (e_s I q K s) (K.inter_le_inter_face s j),
    map_monomial]
  rfl

lemma d_zC_eq_zero (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i) (hb)
    (hdb : (OModulePresheaf.unit q).d K i b = 0) :
    (F' I q).d (K' I q K) i (zC I q K i k b hb) = 0 := by
  funext s
  apply F'_ext I q
  rw [F'val_d_zC, hdb, Pi.zero_apply, F'_zero_val]
  change θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
    (monomial k (0 : Γ(P, K.inter s))) = 0
  rw [map_zero, map_zero]

end Cochains

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {P : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] (K : P.OrderedAffineCover)

lemma mem_map_of_mem_smul_top (I' : Ideal A) {z : (OModulePresheaf.unit q).cochain K 0}
    (hz : z ∈ I' • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K 0))) (s : K.Idx 0) :
    (show Γ(P, K.inter s) from z s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (K.inter s) le_top).hom I' := by
  refine Submodule.smul_induction_on hz (fun a ha x _ => ?_) (fun x y hx hy => Ideal.add_mem _ hx hy)
  show alg q (K.inter s) a * (show Γ(P, K.inter s) from x s) ∈ Ideal.map (alg q (K.inter s)) I'
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

def Z0 : Submodule (Rr I) ((F' I q).cochain (K' I q K) 0) :=
  LinearMap.ker ((F' I q).d (K' I q K) 0)

lemma mem_Z0 (z : (F' I q).cochain (K' I q K) 0) :
    z ∈ Z0 I q K ↔ (F' I q).d (K' I q K) 0 z = 0 := LinearMap.mem_ker

scoped instance : Module.Finite (Rr I) (Z0 I q K) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper (F' I q) (isCoherent_F' I q)
    (isQuasicoherent_F' I q) (K' I q K)).1

scoped instance : _root_.IsNoetherian (Rr I) (Z0 I q K) := isNoetherian_of_isNoetherianRing_of_finite _ _

def zZ (k : ℕ) (z : (OModulePresheaf.unit q).cochain K 0)
    (hz₁ : (OModulePresheaf.unit q).d K 0 z = 0)
    (hz₂ : ∀ s : K.Idx 0, z s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ k)) : Z0 I q K :=
  ⟨zC I q K 0 k z hz₂, (mem_Z0 I q K _).mpr (d_zC_eq_zero I q K 0 k z hz₂ hz₁)⟩

def gens (m : ℕ) : Set (Z0 I q K) :=
  {x | ∃ k, k ≤ m ∧ ∃ z hz₁ hz₂, x = zZ I q K k z hz₁ hz₂}

def N (m : ℕ) : Submodule (Rr I) (Z0 I q K) := Submodule.span (Rr I) (gens I q K m)

lemma N_mono : Monotone (N I q K) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨k, hk, z, hz₁, hz₂, hx⟩ => ⟨k, hk.trans h, z, hz₁, hz₂, hx⟩

def Good (c₀ : ℕ) (x : Z0 I q K) : Prop :=
  ∀ j, coeffC I q K 0 j x.1 ∈ I ^ (j - c₀) • (OModulePresheaf.unit q).H0 K

lemma good_of_mem (c₀ : ℕ) {x : Z0 I q K} (hx : x ∈ N I q K c₀) : Good I q K c₀ x := by
  unfold N at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, z, hz₁, hz₂, rfl⟩ := h
    intro j
    show coeffC I q K 0 j (zC I q K 0 k z hz₂) ∈ _
    rw [coeffC_zC]
    split_ifs with hj
    · subst hj
      rw [Nat.sub_eq_zero_of_le hk, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact LinearMap.mem_ker.mpr hz₁
    · exact Submodule.zero_mem _
  | zero =>
    intro j
    rw [Submodule.coe_zero, coeffC_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro j
    rw [Submodule.coe_add, coeffC_add]
    exact Submodule.add_mem _ (hx j) (hy j)
  | smul r x _ hx =>
    intro j
    rw [Submodule.coe_smul, coeffC_smul]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
    have h1 : (Rr.val I r).coeff y.1 • coeffC I q K 0 y.2 x.1 ∈
        (I ^ y.1 * I ^ (y.2 - c₀)) • (OModulePresheaf.unit q).H0 K := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul (Rr.coeff_mem I r y.1) (hx y.2)
    refine Submodule.smul_mono_left ?_ h1
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by omega)

theorem main (n : ℕ) :
    ∃ c : ℕ, (OModulePresheaf.unit q).H0 K ⊓
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K 0)) ≤
      I ^ n • (OModulePresheaf.unit q).H0 K := by
  obtain ⟨c₀, hc₀⟩ := (monotone_stabilizes_iff_noetherian (R := Rr I) (M := Z0 I q K)).mpr
    inferInstance ⟨N I q K, N_mono I q K⟩
  refine ⟨c₀, fun z hz => ?_⟩
  have hz₁ : (OModulePresheaf.unit q).d K 0 z = 0 := LinearMap.mem_ker.mp hz.1
  have hz₂ : ∀ s : K.Idx 0, z s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) le_top).hom (I ^ (n + c₀)) :=
    mem_map_of_mem_smul_top q K (I ^ (n + c₀)) hz.2
  have hmem : zZ I q K (n + c₀) z hz₁ hz₂ ∈ N I q K (n + c₀) :=
    Submodule.subset_span ⟨n + c₀, le_rfl, z, hz₁, hz₂, rfl⟩
  have hstab : N I q K c₀ = N I q K (n + c₀) := hc₀ (n + c₀) (Nat.le_add_left c₀ n)
  rw [← hstab] at hmem

  have key := good_of_mem I q K c₀ hmem (n + c₀)
  change coeffC I q K 0 (n + c₀) (zC I q K 0 (n + c₀) z hz₂) ∈ _ at key
  rwa [coeffC_zC, if_pos rfl, Nat.add_sub_cancel] at key

end Main

end SolFF0SepUnit
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper.SolFF0SepUnit"

open SolFF0SepUnit in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, (OModulePresheaf.unit q).H0 K ⊓
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K 0)) ≤
      I ^ n • (OModulePresheaf.unit q).H0 K :=
  SolFF0SepUnit.main I q K n
end 
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper. -/
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, (OModulePresheaf.unit q).H0 K ⊓
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K 0)) ≤
      I ^ n • (OModulePresheaf.unit q).H0 K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper.solution
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper. -/
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry"

noncomputable section

namespace FF0SepSqZeroAux

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite TrivSqZeroExt"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)} (F : OModulePresheaf q)

scoped instance instModuleMop (U : P.Opens) : Module (Γ(P, U))ᵐᵒᵖ (F.obj U) :=
  Module.compHom (F.obj U) ((RingHom.id Γ(P, U)).fromOpposite fun a b => mul_comm a b)

scoped instance instIsCentralScalar (U : P.Opens) : IsCentralScalar Γ(P, U) (F.obj U) := ⟨fun _ _ => rfl⟩

abbrev T (U : P.Opens) : Type u := TrivSqZeroExt Γ(P, U) (F.obj U)

example (U : P.Opens) : CommRing (T F U) := inferInstance

abbrev rmap {U V : P.Opens} (h : V ≤ U) : Γ(P, U) →+* Γ(P, V) := (P.presheaf.map (homOfLE h).op).hom

def ρ {U V : P.Opens} (h : V ≤ U) : T F U →+* T F V where
  toFun x := (rmap h x.fst, F.res h x.snd)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · change F.res h (x.fst • y.snd + MulOpposite.op y.fst • x.snd) =
        rmap h x.fst • F.res h y.snd + MulOpposite.op (rmap h y.fst) • F.res h x.snd
      rw [map_add, op_smul_eq_smul, op_smul_eq_smul, F.res_smul, F.res_smul]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp

@[scoped simp] lemma fst_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).fst = rmap h x.fst := rfl
@[scoped simp] lemma snd_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).snd = F.res h x.snd := rfl

lemma ρ_inl {U V : P.Opens} (h : V ≤ U) (a : Γ(P, U)) : ρ F h (inl a) = inl (rmap h a) :=
  TrivSqZeroExt.ext rfl (by simp)

lemma ρ_inr {U V : P.Opens} (h : V ≤ U) (m : F.obj U) : ρ F h (inr m) = inr (F.res h m) :=
  TrivSqZeroExt.ext (by simp) rfl

lemma ρ_refl (U : P.Opens) : ρ F (le_refl U) = RingHom.id _ := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE (le_refl U)).op).hom x.fst = x.fst
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), P.presheaf.map_id]; rfl
  · exact F.res_refl_apply U x.snd

lemma ρ_comp {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) : (ρ F h).comp (ρ F h') = ρ F (h.trans h') := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE h).op).hom ((P.presheaf.map (homOfLE h').op).hom x.fst) =
      (P.presheaf.map (homOfLE (h.trans h')).op).hom x.fst
    rw [← CommRingCat.comp_apply, ← P.presheaf.map_comp]; rfl
  · exact F.res_res h h' x.snd

lemma ρ_ρ {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) (x : T F U) : ρ F h (ρ F h' x) = ρ F (h.trans h') x :=
  RingHom.congr_fun (ρ_comp F h h') x

def Tfun : P.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (T F U.unop.1)
  map {U V} i := CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le))
  map_id U := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    exact ρ_refl F U.unop.1
  map_comp {U V W} i j := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    exact (ρ_comp F _ _).symm

@[scoped simp] lemma Tfun_obj (U : P.AffineZariskiSiteᵒᵖ) : (Tfun F).obj U = CommRingCat.of (T F U.unop.1) := rfl
@[scoped simp] lemma Tfun_map {U V : P.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (Tfun F).map i = CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le)) := rfl

def α : (toOpensFunctor P).op ⋙ P.presheaf ⟶ Tfun F where
  app U := (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
    P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1))
  naturality {U V} i := by
    ext a
    change algebraMap Γ(P, V.unop.1) (T F V.unop.1) (rmap (toOpens_mono i.unop.le) a) =
      ρ F (toOpens_mono i.unop.le) (algebraMap Γ(P, U.unop.1) (T F U.unop.1) a)
    rw [algebraMap_eq_inl, algebraMap_eq_inl, ρ_inl]

@[scoped simp] lemma α_app (U : P.AffineZariskiSiteᵒᵖ) :
    (α F).app U = (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
      P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1)) := rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in

lemma coequifibered (hq : F.IsQuasicoherent) : (α F).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  simp only [α_app, CommRingCat.hom_ofHom]
  letI inst : Algebra (T F U.1) (T F (P.basicOpen f)) := (ρ F (P.basicOpen_le f)).toAlgebra
  change IsLocalization.Away (algebraMap Γ(P, U.1) (T F U.1) f) (T F (P.basicOpen f))
  have hΓ : IsLocalization.Away f Γ(P, P.basicOpen f) := U.2.isLocalization_basicOpen f
  have halg : ∀ x : T F U.1, algebraMap (T F U.1) (T F (P.basicOpen f)) x = ρ F (P.basicOpen_le f) x :=
    fun _ => rfl
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, k, rfl⟩
    rw [halg, map_pow, algebraMap_eq_inl, ρ_inl]
    refine IsUnit.pow k (isUnit_inl_iff.mpr ?_)
    exact IsLocalization.map_units (M := .powers f) Γ(P, P.basicOpen f) ⟨f, 1, pow_one f⟩
  · intro z
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (.powers f) z.fst
    obtain ⟨k', m, hm⟩ := (hq U f).1 z.snd
    change z.fst * rmap (P.basicOpen_le f) (f ^ k) = rmap (P.basicOpen_le f) a at ha
    refine ⟨⟨algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m,
      ⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩⟩, ?_⟩
    change z * ρ F _ (algebraMap _ _ (f ^ (k + k'))) =
      ρ F _ (algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m)
    simp only [map_add, map_mul, algebraMap_eq_inl, ρ_inl, ρ_inr, inl_mul_inl, inl_mul_inr]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_add, fst_inl, fst_inl, fst_inr, add_zero, map_pow, pow_add, ← mul_assoc,
        ← map_pow, ha, mul_comm, map_pow]
    · rw [snd_mul, snd_add, snd_inl, snd_inl, snd_inr, fst_inl, smul_zero, zero_add, zero_add,
        op_smul_eq_smul, F.res_smul, hm, ← mul_smul, ← map_mul, ← pow_add]
  · intro x y hxy
    rw [halg, halg] at hxy
    have h1 : rmap (P.basicOpen_le f) x.fst = rmap (P.basicOpen_le f) y.fst := congrArg fst hxy
    have h2 : F.res (P.basicOpen_le f) (x.snd - y.snd) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg snd hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := .powers f) h1
    obtain ⟨k', hk'⟩ := (hq U f).2 _ h2
    change f ^ k * x.fst = f ^ k * y.fst at hk
    refine ⟨⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩, ?_⟩
    change algebraMap _ _ (f ^ (k + k')) * x = algebraMap _ _ (f ^ (k + k')) * y
    rw [← sub_eq_zero, ← mul_sub, algebraMap_eq_inl]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_inl, fst_sub, fst_zero, mul_sub, pow_add, mul_comm (f ^ k), mul_assoc, mul_assoc, hk,
        sub_self]
    · rw [snd_mul, fst_inl, snd_inl, snd_sub, snd_zero, smul_zero, add_zero, pow_add, mul_smul, hk', smul_zero]

section Scheme

variable (hq : F.IsQuasicoherent)

def D : (directedCover P).RelativeGluingData := relativeGluingData (coequifibered hq)

scoped instance : ((D hq).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

abbrev Y : Scheme.{u} := (D hq).glued

abbrev p : Y hq ⟶ P := (D hq).toBase

def ιU (U : P.AffineZariskiSite) : Spec (CommRingCat.of (T F U.1)) ⟶ Y hq := colimit.ι (D hq).functor U

lemma D_cover_f (U : P.AffineZariskiSite) : (D hq).cover.f U = ιU hq U := by
  simp [D, ιU]

scoped instance ιU_isOpenImmersion (U : P.AffineZariskiSite) : IsOpenImmersion (ιU hq U) := by
  rw [← D_cover_f]; exact (D hq).cover.map_prop U

lemma D_functor_map {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    (D hq).functor.map i = Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) := rfl

include hq in

lemma isOpenImmersion_SpecMap_ρ {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) :
      Spec (CommRingCat.of (T F U.1)) ⟶ Spec (CommRingCat.of (T F V.1))) :=
  (D hq).instIsOpenImmersionMapI₀Functor i

@[reassoc]
lemma SpecMap_ι {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) ≫ ιU hq V = ιU hq U :=
  colimit.w (D hq).functor i

lemma ι_toBase (U : P.AffineZariskiSite) :
    ιU hq U ≫ p hq = Spec.map ((α F).app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma toBase_preimage (U : P.AffineZariskiSite) : p hq ⁻¹ᵁ U.1 = (ιU hq U).opensRange := by
  first
    | simpa using (D hq).toBase_preimage_eq_opensRange_ι U
    | (have h' := (D hq).toBase_preimage_eq_opensRange_ι U; simp at h' ⊢; exact h')
    | (have h' := (D hq).toBase_preimage_eq_opensRange_ι U; simp at h'; exact h')
    | exact (D hq).toBase_preimage_eq_opensRange_ι U

lemma opensRange_functor_map_basicOpen (V : P.AffineZariskiSite) (r : Γ(P, V.1)) :
    ((D hq).functor.map (homOfLE (V.basicOpen_le r))).opensRange = PrimeSpectrum.basicOpen (inl r : T F V.1) :=
  opensRange_relativeGluingData_map (Tfun F) (α F) (coequifibered hq) (U := V) r

lemma SpecMap_ρ_ι {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U = ιU hq V := by

  let J : Type u := {r : (P.presheaf.obj (op U.1)) // P.basicOpen r ≤ V.1}
  let r' : J → (P.presheaf.obj (op V.1)) := fun r => rmap h r.1
  have hbo : ∀ r : J, P.basicOpen (r' r) = P.basicOpen r.1 := fun r =>
    (P.basicOpen_res r.1 (homOfLE h).op).trans (inf_eq_right.mpr r.2)
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨r, hr, hxr⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (h hx)
    refine Opens.mem_iSup.mpr ⟨⟨r' ⟨r, hr⟩, ⟨r, hr⟩, rfl⟩, ?_⟩
    change x ∈ P.basicOpen (r' ⟨r, hr⟩)
    rw [hbo]; exact hxr
  have hspanT : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) = ⊤ := by
    have : Ideal.map (algebraMap Γ(P, V.1) (T F V.1)) (Ideal.span (Set.range r')) = ⊤ := by
      rw [hspan, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at this
    exact this
  have iV : ∀ r : J, V.basicOpen (r' r) ≤ V := fun r => V.basicOpen_le (r' r)
  have iU : ∀ r : J, V.basicOpen (r' r) ≤ U := fun r => ⟨r.1, (hbo r).symm⟩
  let 𝒲 : (Spec (CommRingCat.of (T F V.1))).OpenCover :=
    { I₀ := J
      X := fun r => Spec (CommRingCat.of (T F (P.basicOpen (r' r))))
      f := fun r => Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r))))
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun r => isOpenImmersion_SpecMap_ρ hq (homOfLE (iV r))⟩
        have hx : ∃ r : J, x ∈ PrimeSpectrum.basicOpen (inl (r' r) : T F V.1) := by
          by_contra hcon
          push Not at hcon
          have hle : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) ≤ x.asIdeal :=
            Ideal.span_le.mpr (by
              rintro _ ⟨r, rfl⟩
              by_contra h'
              exact hcon r ((PrimeSpectrum.mem_basicOpen _ _).mpr h'))
          rw [hspanT, top_le_iff] at hle
          exact x.2.ne_top hle
        obtain ⟨r, hr⟩ := hx
        rw [← opensRange_functor_map_basicOpen hq V (r' r)] at hr
        obtain ⟨y, hy⟩ := hr
        exact ⟨r, y, hy⟩ }
  refine Cover.hom_ext 𝒲 _ _ fun r ↦ ?_
  change Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ Spec.map (CommRingCat.ofHom (ρ F h)) ≫
    ιU hq U = Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ ιU hq V
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ρ_comp]
  exact (SpecMap_ι hq (homOfLE (iU r))).trans (SpecMap_ι hq (homOfLE (iV r))).symm

end Scheme

section Sections

variable (hq : F.IsQuasicoherent)

lemma appLE_congr_hom {X₁ X₂ : Scheme.{u}} {f g : X₁ ⟶ X₂} (hfg : f = g) (U : X₂.Opens) (V : X₁.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

lemma appLE_top_top {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂) (e : (⊤ : X₁.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have : (homOfLE e).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this]
  simp

lemma preimage_ι_eq_top (U : P.AffineZariskiSite) : ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) = ⊤ := by
  rw [toBase_preimage, Scheme.Hom.preimage_opensRange]

lemma le_preimage_ι (U : P.AffineZariskiSite) :
    (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤ ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) :=
  (preimage_ι_eq_top hq U).ge

def eHom (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ⟶ CommRingCat.of (T F U.1) :=
  (ιU hq U).appLE (p hq ⁻¹ᵁ U.1) ⊤ (le_preimage_ι hq U) ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom

scoped instance isIso_eHom (U : P.AffineZariskiSite) : IsIso (eHom hq U) := by
  have h1 : IsIso ((ιU hq U).app (p hq ⁻¹ᵁ U.1)) := Scheme.Hom.isIso_app _ _ (by rw [toBase_preimage])
  have h2 : IsIso ((Spec (CommRingCat.of (T F U.1))).presheaf.map (homOfLE (le_preimage_ι hq U)).op) := by
    have : homOfLE (le_preimage_ι hq U) = eqToHom (preimage_ι_eq_top hq U).symm := Subsingleton.elim _ _
    rw [this, eqToHom_op]; infer_instance
  unfold eHom Scheme.Hom.appLE
  infer_instance

def e (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ≃+* T F U.1 :=
  (asIso (eHom hq U)).commRingCatIsoToRingEquiv

lemma e_apply (U : P.AffineZariskiSite) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) : e hq U x = eHom hq U x := rfl

lemma map_eHom {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    (Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op ≫ eHom hq V = eHom hq U ≫ CommRingCat.ofHom (ρ F h) := by
  unfold eHom
  have hle : (⊤ : (Spec (CommRingCat.of (T F V.1))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U) ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) := by
    rw [Scheme.Hom.comp_preimage, preimage_ι_eq_top]; exact (Opens.map_top _).ge
  rw [Scheme.Hom.map_appLE_assoc,
    appLE_congr_hom (SpecMap_ρ_ι hq h).symm (p hq ⁻¹ᵁ U.1) ⊤ _ hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ (p hq ⁻¹ᵁ U.1) ⊤ ⊤ (le_preimage_ι hq U) (Opens.map_top _).ge,
    Category.assoc, appLE_top_top, Scheme.ΓSpecIso_naturality, Category.assoc]

lemma e_map {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) :
    e hq V ((Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op x) = ρ F h (e hq U x) := by
  rw [e_apply, e_apply, ← CommRingCat.comp_apply, map_eHom hq h, CommRingCat.comp_apply]
  rfl

lemma appLE_eHom (U : P.AffineZariskiSite) :
    (p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl ≫ eHom hq U = (α F).app (op U) := by
  have h1 : (⊤ : (Spec _).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by rw [IsAffineOpen.fromSpec_preimage_self]
  have h2 : (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤
      (Spec.map ((α F).app (op U)) ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.comp_preimage]; exact (Opens.map_top _).ge.trans ((Spec.map _).preimage_mono h1)
  have h4 : U.2.fromSpec.appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(P, U.1)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← CategoryTheory.Functor.map_comp]
    have : ((eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE h1).op) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have h5 : (Spec.map ((α F).app (op U))).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom =
      (Scheme.ΓSpecIso (P.presheaf.obj (op U.1))).hom ≫ (α F).app (op U) :=
    Scheme.ΓSpecIso_naturality _
  unfold eHom
  rw [Scheme.Hom.appLE_comp_appLE_assoc, appLE_congr_hom (ι_toBase hq U) U.1 ⊤ _ h2]
  trans (U.2.fromSpec.appLE U.1 ⊤ h1 ≫ (Spec.map ((α F).app (op U))).appLE ⊤ ⊤ (Opens.map_top _).ge) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom
  · congr 1
  rw [h4, Category.assoc, appLE_top_top]
  exact (congrArg ((Scheme.ΓSpecIso Γ(P, U.1)).inv ≫ ·) h5).trans (Iso.inv_hom_id_assoc _ _)

lemma e_appLE (U : P.AffineZariskiSite) (a : Γ(P, U.1)) :
    e hq U ((p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl a) = inl a := by
  rw [e_apply, ← CommRingCat.comp_apply, appLE_eHom, α_app]
  rfl

theorem isFinite_p (hc : F.IsCoherent) : IsFinite (p hq) := by
  refine AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData (coequifibered hq) fun U => ?_
  change (algebraMap Γ(P, U.1) (T F U.1)).Finite
  rw [RingHom.finite_algebraMap]
  haveI : Module.Finite Γ(P, U.1) (F.obj U.1) := hc ⟨U.1, U.2⟩
  exact inferInstanceAs (Module.Finite Γ(P, U.1) (Γ(P, U.1) × F.obj U.1))

end Sections

section AffineHom

variable (hq : F.IsQuasicoherent)

scoped instance isAffineHom_p : IsAffineHom (p hq) :=
  isAffineHom_of_forall_exists_isAffineOpen _ fun x => by
    obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top P).ge (Set.mem_univ x))
    exact ⟨U.1, hxU, U.2, by rw [toBase_preimage hq ⟨U.1, U.2⟩]; exact isAffineOpen_opensRange _⟩

end AffineHom

section Ideals

variable (F) (U : P.Opens)

def σT : A →+* T F U :=
  (algebraMap Γ(P, U) (T F U)).comp (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap

lemma σT_apply (a : A) : σT F U a = inl ((Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a) := rfl

lemma algebraMap_smul_eq (a : A) (m : F.obj U) :
    (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a • m = a • m := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  exact algebraMap_smul Γ(P, U) a m

end Ideals

section Cech

variable [IsSeparated q]

abbrev Ks (_hq : F.IsQuasicoherent) (K : P.OrderedAffineCover) {i : ℕ} (s : K.Idx i) : P.AffineZariskiSite :=
  ⟨K.inter s, K.isAffineOpen_inter q s⟩

variable (hq : F.IsQuasicoherent) (K : P.OrderedAffineCover)

abbrev KY : (Y hq).OrderedAffineCover := K.comap (p hq)

abbrev toP {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) →+* Γ(Y hq, p hq ⁻¹ᵁ K.inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op).hom

abbrev ofP {i : ℕ} (s : K.Idx i) : Γ(Y hq, p hq ⁻¹ᵁ K.inter s) →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.comap_inter_le (p hq) s)).op).hom

lemma Ymap_Ymap {U V W : (Y hq).Opens} (f : op U ⟶ op V) (g : op V ⟶ op W) (h : op U ⟶ op W) (x : Γ(Y hq, U)) :
    (Y hq).presheaf.map g ((Y hq).presheaf.map f x) = (Y hq).presheaf.map h x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

lemma Ymap_id {U : (Y hq).Opens} (f : op U ⟶ op U) (x : Γ(Y hq, U)) : (Y hq).presheaf.map f x = x := by
  rw [Subsingleton.elim f (𝟙 _), CategoryTheory.Functor.map_id]; rfl

lemma toP_ofP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, p hq ⁻¹ᵁ K.inter s)) : toP hq K s (ofP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

lemma ofP_toP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) : ofP hq K s (toP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

def eY {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) ≃+* T F (K.inter s) where
  toFun x := e hq (Ks hq K s) (toP hq K s x)
  invFun t := ofP hq K s ((e hq (Ks hq K s)).symm t)
  left_inv x := by
    change ofP hq K s ((e hq (Ks hq K s)).symm (e hq (Ks hq K s) (toP hq K s x))) = x
    rw [RingEquiv.symm_apply_apply, ofP_toP]
  right_inv t := by
    change e hq (Ks hq K s) (toP hq K s (ofP hq K s ((e hq (Ks hq K s)).symm t))) = t
    rw [toP_ofP, RingEquiv.apply_symm_apply]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add' x y := by rw [map_add, map_add]

lemma eY_apply {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) :
    eY hq K s x = e hq (Ks hq K s) (toP hq K s x) := rfl

abbrev σY {i : ℕ} (s : K.Idx i) : A →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top).hom

lemma eY_σY {i : ℕ} (s : K.Idx i) (a : A) : eY hq K s (σY hq K s a) = σT F (K.inter s) a := by
  rw [eY_apply, σT_apply, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  change e hq (Ks hq K s) (((p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top ≫
    (Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = _
  rw [Scheme.Hom.appLE_map, ← Scheme.Hom.appLE_comp_appLE (p hq) q ⊤ (K.inter s) (p hq ⁻¹ᵁ K.inter s) le_top le_rfl,
    CommRingCat.comp_apply]
  exact e_appLE hq (Ks hq K s) _

def Φ (i : ℕ) (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) (s : K.Idx i) : T F (K.inter s) :=
  eY hq K s (c s)

def Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i :=
  fun s => (eY hq K s).symm (c s)

lemma Φ_Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : Φ hq K i (Ψ hq K i c) = c := by
  funext s; exact (eY hq K s).apply_symm_apply (c s)

def dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) : T F (K.inter s) :=
  ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • ρ F (K.inter_le_inter_face s j) (c (K.face s j))

lemma snd_dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) :
    (dT K c s).snd = F.d K 0 (fun t => (c t).snd) s := by
  rw [OModulePresheaf.d_apply, dT, snd_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (snd_smul _ _).trans (by rw [snd_ρ])

lemma fst_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).fst = 0 := by
  rw [dT, fst_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact (fst_smul _ _).trans (by rw [fst_ρ, fst_inr, map_zero, smul_zero])

lemma snd_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).snd = F.d K 0 w s := by
  rw [snd_dT]; rfl

lemma dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    dT K (fun t => inr (w t)) s = inr (F.d K 0 w s) :=
  TrivSqZeroExt.ext (by rw [fst_dT_inr, fst_inr]) (by rw [snd_dT_inr, snd_inr])

lemma Φ_d (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0) :
    Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 c) = dT K (Φ hq K 0 c) := by
  funext s
  rw [Φ, OModulePresheaf.d_apply, dT]
  change eY hq K s (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
    (Y hq).presheaf.map (homOfLE ((KY hq K).inter_le_inter_face s j)).op (c ((KY hq K).face s j))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [Φ, eY_apply, eY_apply, ← e_map hq (U := Ks hq K (K.face s j)) (V := Ks hq K s) (K.inter_le_inter_face s j)]
  congr 1
  have hcommon : op ((KY hq K).inter ((KY hq K).face s j)) ⟶ op (p hq ⁻¹ᵁ K.inter s) :=
    (homOfLE (((p hq).preimage_mono (K.inter_le_inter_face s j)).trans (K.le_comap_inter (p hq) (K.face s j)))).op
  change (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _)) = (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _))
  exact (Ymap_Ymap hq _ _ hcommon _).trans (Ymap_Ymap hq _ _ hcommon _).symm

end Cech

section Transport

variable [IsSeparated q] (hq : F.IsQuasicoherent) (K : P.OrderedAffineCover)

lemma σT_mul_inr (U : P.Opens) (a : A) (m : F.obj U) : σT F U a * inr m = inr (a • m) := by
  rw [σT_apply, inl_mul_inr, algebraMap_smul_eq]

lemma snd_σT_mul (U : P.Opens) (a : A) (t : T F U) : (σT F U a * t).snd = a • t.snd := by
  rw [σT_apply, inl_mul_eq_smul, snd_smul, algebraMap_smul_eq]

lemma unitY_smul {i : ℕ} (s : K.Idx i) (a : A) (y : Γ(Y hq, (KY hq K).inter s)) :
    (a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from y)) =
      (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from σY hq K s a * y) := rfl

lemma eY_smul {i : ℕ} (s : K.Idx i) (a : A) (y : Γ(Y hq, (KY hq K).inter s)) :
    eY hq K s (show Γ(Y hq, (KY hq K).inter s) from
        a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from y)) =
      σT F (K.inter s) a * eY hq K s y := by
  rw [unitY_smul, map_mul, eY_σY]

lemma eY_symm_σT_mul {i : ℕ} (s : K.Idx i) (a : A) (t : T F (K.inter s)) :
    (eY hq K s).symm (σT F (K.inter s) a * t) = (show Γ(Y hq, (KY hq K).inter s) from
      a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from (eY hq K s).symm t)) := by
  apply (eY hq K s).injective
  rw [eY_smul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

def L : F.cochain K 0 →ₗ[A] (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0 where
  toFun z := Ψ hq K 0 fun s => inr (z s)
  map_add' z z' := by
    funext s
    change (eY hq K s).symm (inr (z s + z' s)) = (eY hq K s).symm (inr (z s)) + (eY hq K s).symm (inr (z' s))
    rw [inr_add, map_add]
  map_smul' a z := by
    funext s
    change (eY hq K s).symm (inr (a • z s)) = (show Γ(Y hq, (KY hq K).inter s) from
      a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from (eY hq K s).symm (inr (z s))))
    rw [← σT_mul_inr, eY_symm_σT_mul]

lemma L_apply (z : F.cochain K 0) : L hq K z = Ψ hq K 0 fun s => inr (z s) := rfl

def Q : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0 →ₗ[A] F.cochain K 0 where
  toFun v s := (eY hq K s (v s)).snd
  map_add' v v' := by
    funext s
    exact (congrArg TrivSqZeroExt.snd (map_add (eY hq K s) (v s) (v' s))).trans (snd_add _ _)
  map_smul' a v := by
    funext s
    change (eY hq K s (show Γ(Y hq, (KY hq K).inter s) from
      a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from v s))).snd =
      a • (eY hq K s (v s)).snd
    rw [eY_smul, snd_σT_mul]

lemma Q_apply (v : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0) (s : K.Idx 0) :
    Q hq K v s = (Φ hq K 0 v s).snd := rfl

lemma Q_L (z : F.cochain K 0) : Q hq K (L hq K z) = z := by
  funext s
  change (eY hq K s ((eY hq K s).symm (inr (z s)))).snd = z s
  rw [RingEquiv.apply_symm_apply, snd_inr]

lemma L_mem_H0 {z : F.cochain K 0} (hz : F.d K 0 z = 0) :
    L hq K z ∈ (OModulePresheaf.unit (p hq ≫ q)).H0 (KY hq K) := by
  rw [LinearMap.mem_ker]
  have h1 : Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 (L hq K z)) = 0 := by
    rw [Φ_d, L_apply, Φ_Ψ]
    funext s
    rw [dT_inr, hz, Pi.zero_apply, inr_zero, Pi.zero_apply]
  funext s
  have := congr_fun h1 s
  exact (eY hq K s).map_eq_zero_iff.mp this

lemma Q_mem_H0 {v : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0}
    (hv : (OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 v = 0) : Q hq K v ∈ F.H0 K := by
  rw [LinearMap.mem_ker]
  funext s
  change F.d K 0 (fun t => (Φ hq K 0 v t).snd) s = 0
  rw [← snd_dT, ← Φ_d, hv]
  change (eY hq K s 0).snd = 0
  rw [map_zero, snd_zero]

end Transport

theorem main [IsNoetherianRing A] (I : Ideal A) [IsProper q] (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, F.H0 K ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 0)) ≤ I ^ n • F.H0 K := by
  haveI : IsFinite (p hq) := isFinite_p hq hc
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper I (p hq ≫ q)
      (KY hq K) n
  refine ⟨c, fun z hz => ?_⟩

  have h1 : L hq K z ∈ (OModulePresheaf.unit (p hq ≫ q)).H0 (KY hq K) ⊓
      I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0)) := by
    refine ⟨L_mem_H0 hq K (LinearMap.mem_ker.mp hz.1), ?_⟩
    have h := Submodule.mem_map_of_mem (f := L hq K) hz.2
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h

  have h2 := Submodule.mem_map_of_mem (f := Q hq K) (hc' h1)
  rw [Submodule.map_smul'', Q_L] at h2
  refine Submodule.smul_mono le_rfl ?_ h2
  rintro _ ⟨v, hv, rfl⟩
  exact Q_mem_H0 hq K (LinearMap.mem_ker.mp hv)

end FF0SepSqZeroAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, F.H0 K ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 0)) ≤ I ^ n • F.H0 K :=
  FF0SepSqZeroAux.main I hc hqc K n
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper. -/
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, F.H0 K ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 0)) ≤ I ^ n • F.H0 K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.solution
end


/- Adapted reference: P2M.Sol.S_IsAdicComplete_of_finite_of_isNoetherianRing. -/
section
namespace P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing

open scoped TensorProduct

namespace SolFinComplete
open AdicCompletion

universe u

theorem isAdicComplete_of_finite_aux {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : M ≃ₗ[R] R ⊗[R] M := (TensorProduct.lid R M).symm
  let e2 : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
     LinearEquiv.rTensor M (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have : (of I M : M → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp only [e1, e2, e3, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      ofTensorProductEquivOfFiniteNoetherian_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul, ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      simpa using this
    rw [h1, one_smul]
  rw [this]; exact e3.bijective.comp (e2.bijective.comp e1.bijective)

theorem isAdicComplete_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr_apply, map_of]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  haveI : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker p) := isAdicComplete_of_finite_aux I _
  exact isAdicComplete_of_linearEquiv I (p.quotKerEquivOfSurjective hp)

end SolFinComplete

theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M :=
  SolFinComplete.isAdicComplete_of_finite I M
end P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing
end


/- Adapted reference: Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing. -/
section

theorem IsAdicComplete.of_finite_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.solution
end


/- Adapted reference: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper. -/
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry"

namespace FF0LimAux

section Algebra

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem coe_mem_smul_iff (J : Ideal A) (p : Submodule A M) (x : p) :
    (x : M) ∈ J • p ↔ x ∈ J • (⊤ : Submodule A p) := by
  have hmap : (J • (⊤ : Submodule A p)).map p.subtype = J • p := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  constructor
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext (by simpa using hyx)
    exact this ▸ hy
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩

theorem pow_smul_le_pow_smul (I : Ideal A) (N : Submodule A M) {m n : ℕ} (h : m ≤ n) :
    I ^ n • N ≤ I ^ m • N :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

def env (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => c 0
  | n + 1 => max (env c n) (n + 1 + c (n + 1))

theorem add_le_env (c : ℕ → ℕ) : ∀ n, n + c n ≤ env c n
  | 0 => by simp [env]
  | n + 1 => by
    show n + 1 + c (n + 1) ≤ max (env c n) (n + 1 + c (n + 1))
    exact le_max_right _ _

theorem env_mono (c : ℕ → ℕ) : Monotone (env c) :=
  monotone_nat_of_le_succ fun n => by
    show env c n ≤ max (env c n) (n + 1 + c (n + 1))
    exact le_max_left _ _

theorem le_env (c : ℕ → ℕ) (n : ℕ) : n ≤ env c n :=
  (Nat.le_add_right n (c n)).trans (add_le_env c n)

end Algebra

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
  (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
  (K : P.OrderedAffineCover)

theorem sub_mem_of_le (t : ℕ → F.cochain K 0)
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)))
    {n m : ℕ} (h : n ≤ m) :
    t m - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  induction h with
  | refl => simp
  | @step m hnm ih =>
    have h1 : t (m + 1) - t m ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) :=
      pow_smul_le_pow_smul I ⊤ (Nat.succ_le_succ hnm) (ht m)
    have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
    rw [this]
    exact Submodule.add_mem _ h1 ih

theorem sub_mem_of_le_of_le (t : ℕ → F.cochain K 0)
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)))
    {n k l : ℕ} (hk : n ≤ k) (hl : n ≤ l) :
    t k - t l ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  have : t k - t l = (t k - t n) - (t l - t n) := by abel
  rw [this]
  exact Submodule.sub_mem _ (sub_mem_of_le I q F K t ht hk) (sub_mem_of_le I q F K t ht hl)

include hc hqc in

theorem main (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  classical

  let J : ℕ → Submodule A (F.cochain K 0) := fun n => I ^ n • ⊤
  have hJ : ∀ {m n : ℕ}, m ≤ n → J n ≤ J m := fun h => pow_smul_le_pow_smul I ⊤ h

  haveI hfin : Module.Finite A (F.H0 K) :=
    (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).1
  haveI hcomplete : IsAdicComplete I (F.H0 K) :=
    IsAdicComplete.of_finite_of_isNoetherianRing I (F.H0 K)

  have step1 : ∀ n : ℕ, ∃ a : F.cochain K 0, F.d K 0 a = 0 ∧ ∃ k : ℕ, n ≤ k ∧ t k - a ∈ J n := by
    intro n
    obtain ⟨c, hcn⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
        I q F hc hqc K n
    have hdt : F.d K 0 (t (n + c)) ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 1)) :=
      pow_smul_le_pow_smul I ⊤ (Nat.le_succ (n + c)) (hd (n + c))
    obtain ⟨a, hda, hta⟩ := hcn (t (n + c)) hdt
    exact ⟨a, hda, n + c, Nat.le_add_right n c, hta⟩
  choose a hda k hnk hka using step1

  have step2 : ∀ n : ℕ, ∃ c : ℕ, ∀ x : F.cochain K 0, x ∈ F.H0 K → x ∈ J (n + c) → x ∈ I ^ n • F.H0 K := by
    intro n
    obtain ⟨c, hcle⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I q F hc hqc K n
    exact ⟨c, fun x hxH hxJ => hcle (Submodule.mem_inf.mpr ⟨hxH, hxJ⟩)⟩
  choose c₂ hc₂ using step2

  have hamem : ∀ n, a n ∈ F.H0 K := fun n => LinearMap.mem_ker.mpr (hda n)
  have hasub : ∀ {n m : ℕ}, n ≤ m → a m - a n ∈ J n := by
    intro n m hnm
    have h1 : a m - t (k m) ∈ J n := by
      have : a m - t (k m) = -(t (k m) - a m) := by abel
      rw [this]; exact Submodule.neg_mem _ (hJ hnm (hka m))
    have h2 : t (k m) - t (k n) ∈ J n :=
      hJ (Nat.le_succ n) (sub_mem_of_le_of_le I q F K t ht (hnm.trans (hnk m)) (hnk n))
    have h3 : t (k n) - a n ∈ J n := hka n
    have : a m - a n = (a m - t (k m)) + (t (k m) - t (k n)) + (t (k n) - a n) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

  let e : ℕ → ℕ := env c₂
  let b : ℕ → F.H0 K := fun n => ⟨a (e n), hamem (e n)⟩
  have hb : ∀ {n m : ℕ}, n ≤ m → b m - b n ∈ I ^ n • (⊤ : Submodule A (F.H0 K)) := by
    intro n m hnm
    rw [← coe_mem_smul_iff]
    have hdiff : ((b m - b n : F.H0 K) : F.cochain K 0) = a (e m) - a (e n) := rfl
    rw [hdiff]
    refine hc₂ n _ (Submodule.sub_mem _ (hamem _) (hamem _)) ?_
    exact hJ (add_le_env c₂ n) (hasub (env_mono c₂ hnm))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomplete.toIsPrecomplete (f := b) fun {m n} hmn => by
    rw [SModEq.sub_mem]
    have : b m - b n = -(b n - b m) := by abel
    rw [this]
    exact Submodule.neg_mem _ (hb hmn)

  have hLb : ∀ n, (L : F.cochain K 0) - a (e n) ∈ J n := by
    intro n
    have h := (SModEq.sub_mem.mp (hL n))

    have h' : ((b n - L : F.H0 K) : F.cochain K 0) ∈ I ^ n • F.H0 K := (coe_mem_smul_iff _ _ _).mpr h
    have h'' : a (e n) - (L : F.cochain K 0) ∈ J n := Submodule.smul_mono le_rfl le_top h'
    have : (L : F.cochain K 0) - a (e n) = -(a (e n) - (L : F.cochain K 0)) := by abel
    rw [this]; exact Submodule.neg_mem _ h''

  refine ⟨(L : F.cochain K 0), ⟨LinearMap.mem_ker.mp L.2, fun n => ?_⟩, ?_⟩
  · have h1 : (L : F.cochain K 0) - a (e (n + 1)) ∈ J (n + 1) := hLb (n + 1)
    have h2 : a (e (n + 1)) - t (k (e (n + 1))) ∈ J (n + 1) := by
      have : a (e (n + 1)) - t (k (e (n + 1))) = -(t (k (e (n + 1))) - a (e (n + 1))) := by abel
      rw [this]
      exact Submodule.neg_mem _ (hJ (le_env c₂ (n + 1)) (hka (e (n + 1))))
    have h3 : t (k (e (n + 1))) - t n ∈ J (n + 1) :=
      sub_mem_of_le I q F K t ht ((Nat.le_succ n).trans ((le_env c₂ (n + 1)).trans (hnk _)))
    have : (L : F.cochain K 0) - t n
        = ((L : F.cochain K 0) - a (e (n + 1))) + (a (e (n + 1)) - t (k (e (n + 1))))
          + (t (k (e (n + 1))) - t n) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

  · rintro a' ⟨hda', hta'⟩
    have hδH : a' - (L : F.cochain K 0) ∈ F.H0 K :=
      Submodule.sub_mem _ (LinearMap.mem_ker.mpr hda') L.2
    have hδJ : ∀ m, a' - (L : F.cochain K 0) ∈ J m := by
      intro m
      have h1 : a' - t m ∈ J m := hJ (Nat.le_succ m) (hta' m)
      have h2 : (L : F.cochain K 0) - t m ∈ J m := by
        have h1' : (L : F.cochain K 0) - a (e (m + 1)) ∈ J m := hJ (Nat.le_succ m) (hLb (m + 1))
        have h2' : a (e (m + 1)) - t (k (e (m + 1))) ∈ J m := by
          have : a (e (m + 1)) - t (k (e (m + 1))) = -(t (k (e (m + 1))) - a (e (m + 1))) := by abel
          rw [this]
          exact Submodule.neg_mem _
            (hJ ((Nat.le_succ m).trans (le_env c₂ (m + 1))) (hka (e (m + 1))))
        have h3' : t (k (e (m + 1))) - t m ∈ J m :=
          hJ (Nat.le_succ m)
            (sub_mem_of_le I q F K t ht ((Nat.le_succ m).trans ((le_env c₂ (m + 1)).trans (hnk _))))
        have : (L : F.cochain K 0) - t m
            = ((L : F.cochain K 0) - a (e (m + 1))) + (a (e (m + 1)) - t (k (e (m + 1))))
              + (t (k (e (m + 1))) - t m) := by abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.add_mem _ h1' h2') h3'
      have : a' - (L : F.cochain K 0) = (a' - t m) - ((L : F.cochain K 0) - t m) := by abel
      rw [this]
      exact Submodule.sub_mem _ h1 h2

    let δ : F.H0 K := ⟨a' - (L : F.cochain K 0), hδH⟩
    have hδ0 : δ = 0 := by
      refine IsHausdorff.haus hcomplete.toIsHausdorff δ fun n => ?_
      rw [SModEq.sub_mem, sub_zero, ← coe_mem_smul_iff]
      exact hc₂ n _ hδH (hδJ (n + c₂ n))
    have : a' - (L : F.cochain K 0) = 0 := congrArg Subtype.val hδ0
    exact sub_eq_zero.mp this

end Main

end FF0LimAux

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) :=
  FF0LimAux.main I q F hc hqc K t hd ht
end P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
end


/- Adapted reference: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper. -/
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.solution
end

/- The bridge from actual subscheme sections to these cochains follows. -/

section


open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Pointwise

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGeometricPrerequisites
namespace FormalBridge

def resTop (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma res_resTop (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U) (s : Γ(X,⊤)) :
    X.presheaf.map (homOfLE h).op (resTop X U s) = resTop X V s := by
  change (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE le_top).op).hom s) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma app_resTop {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) (a : Γ(X,⊤)) :
    g.app U (resTop X U a) = resTop Y (g ⁻¹ᵁ U) (g.appTop a) := by
  change ((X.presheaf.map (homOfLE le_top).op) ≫ g.app U) a = _
  rw [g.naturality]
  rfl

lemma app_res {X Y : Scheme.{u}} (g : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(X,U)) :
    g.app V (X.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app U a) := by
  change ((X.presheaf.map (homOfLE h).op) ≫ g.app V) a = _
  rw [g.naturality]
  rfl

lemma lift_restrict {X : Scheme.{u}} (I : X.IdealSheafData) {U V : X.Opens}
    (h : V ≤ U) (a : Γ(X,U)) (s : Γ(I.subscheme,⊤))
    (ha : I.subschemeι.app U a = resTop _ _ s) :
    I.subschemeι.app V (X.presheaf.map (homOfLE h).op a) = resTop _ _ s := by
  rw [app_res, ha, res_resTop]

lemma lift_transition {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (U : X.Opens) (a : Γ(X,U)) (s : Γ(I.subscheme,⊤))
    (ha : I.subschemeι.app U a = resTop _ _ s) :
    J.subschemeι.app U a =
      resTop _ _ ((Scheme.IdealSheafData.inclusion h).appTop s) := by
  let g := Scheme.IdealSheafData.inclusion h
  have hg : g ≫ I.subschemeι = J.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι h
  have e : J.subschemeι ⁻¹ᵁ U ≤ g ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hg]
  have hcomp : I.subschemeι.app U ≫ g.appLE _ (J.subschemeι ⁻¹ᵁ U) e =
      J.subschemeι.app U := by
    rw [← Scheme.Hom.comp_appLE]
    simpa only [hg] using J.subschemeι.appLE_eq_app (U := U)
  rw [← hcomp, CommRingCat.comp_apply, ha]
  change ((I.subscheme.presheaf.map (homOfLE le_top).op) ≫
    g.appLE _ (J.subschemeι ⁻¹ᵁ U) e) s = _
  rw [Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R)

lemma parameter_ideal_affine (U : X.affineOpens) (n : ℕ) :
    (parameterIdeal R X f t ^ n).ideal U =
      Ideal.span {((Scheme.TwoAffineOpenCover.algebraOfHom f U.1).algebraMap t) ^ n} := by
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, parameterIdeal,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow]
  congr 3
lemma cochain_mem_pow_iff (K : X.OrderedAffineCover) (i n : ℕ)
    (a : (OModulePresheaf.unit f).cochain K i) :
    a ∈ (Ideal.span {t}) ^ n • (⊤ : Submodule R ((OModulePresheaf.unit f).cochain K i)) ↔
    ∀ s : K.Idx i, ∃ b : Γ(X,K.inter s),
      ((Scheme.TwoAffineOpenCover.algebraOfHom f (K.inter s)).algebraMap t)^n * b = a s := by
  classical
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, _, hb⟩ s
    refine ⟨b s, ?_⟩
    have h := congrFun hb s
    simpa only [Pi.smul_apply, OModulePresheaf.unit_algebraMap_smul, map_pow] using h
  · intro h
    choose b hb using h
    refine ⟨b, Submodule.mem_top, funext fun s => ?_⟩
    change ((Scheme.TwoAffineOpenCover.algebraOfHom f (K.inter s)).algebraMap (t^n)) * b s = a s
    simpa only [map_pow] using hb s

lemma cochain_mem_pow_iff_kernel [IsSeparated f] (K : X.OrderedAffineCover) (i n : ℕ)
    (a : (OModulePresheaf.unit f).cochain K i) :
    a ∈ (Ideal.span {t}) ^ n • (⊤ : Submodule R ((OModulePresheaf.unit f).cochain K i)) ↔
    ∀ s : K.Idx i, (parameterIdeal R X f t ^ n).subschemeι.app (K.inter s) (a s) = 0 := by
  rw [cochain_mem_pow_iff]
  apply forall_congr'
  intro s
  rw [← RingHom.mem_ker, Scheme.IdealSheafData.ker_subschemeι_app _
    ⟨K.inter s, K.isAffineOpen_inter f s⟩, parameter_ideal_affine, Ideal.mem_span_singleton]
  exact exists_congr fun b => eq_comm

def properCover [IsProper f] : X.OrderedAffineCover := by
  classical
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let C := X.affineCover.finiteSubcover
  exact
    { ι := C.I₀
      instFintype := inferInstance
      instLinearOrder := LinearOrder.lift' (Fintype.equivFin C.I₀)
        (Fintype.equivFin C.I₀).injective
      U := fun i => (C.f i).opensRange
      isAffineOpen := fun i => isAffineOpen_opensRange (C.f i)
      iSup_eq_top := C.iSup_opensRange }


lemma powers_antitone (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n) : I^n ≤ I^m := by
  intro U
  change (I.ideal U)^n ≤ (I.ideal U)^m
  exact Ideal.pow_le_pow_right h

lemma d_lift_zero (K : X.OrderedAffineCover) (I : X.IdealSheafData)
    (s : Γ(I.subscheme,⊤)) (a : (OModulePresheaf.unit f).cochain K 0)
    (ha : ∀ j : K.Idx 0, I.subschemeι.app (K.inter j) (a j) = resTop _ _ s) :
    ∀ j : K.Idx 1, I.subschemeι.app (K.inter j) ((OModulePresheaf.unit f).d K 0 a j) = 0 := by
  intro j
  rw [OModulePresheaf.d_apply]
  change (I.subschemeι.app (K.inter j)).hom
    (∑ k : Fin 2, ((-1 : ℤ)^(k : ℕ)) •
      X.presheaf.map (homOfLE (K.inter_le_inter_face j k)).op (a (K.face j k))) = 0
  rw [map_sum]
  simp_rw [map_zsmul, app_res, ha, res_resTop]
  simp [Fin.sum_univ_two]

include f in
lemma sections_ext (K : X.OrderedAffineCover) (a b : Γ(X,⊤))
    (h : ∀ j : K.Idx 0, resTop X (K.inter j) a = resTop X (K.inter j) b) : a = b := by
  apply K.toCoverOf.aug_injective f
  exact funext h

include f in
lemma subscheme_sections_ext (K : X.OrderedAffineCover) (I : X.IdealSheafData)
    (a b : Γ(I.subscheme,⊤))
    (h : ∀ j : K.Idx 0, resTop _ (I.subschemeι ⁻¹ᵁ K.inter j) a =
      resTop _ (I.subschemeι ⁻¹ᵁ K.inter j) b) : a = b := by
  apply sections_ext R _ (I.subschemeι ≫ f) (K.comap I.subschemeι)
  intro j
  rw [K.comap_inter I.subschemeι j]
  exact h j

lemma global_cocycle (K : X.OrderedAffineCover) (a : Γ(X,⊤)) :
    (OModulePresheaf.unit f).d K 0 (K.toCoverOf.aug f a) = 0 := by
  letI : ∀ U : X.Opens, Module R Γ(X,U) := Scheme.OrderedAffineCoverOf.moduleSections f
  apply LinearMap.mem_ker.mp
  change K.toCoverOf.aug f a ∈ LinearMap.ker (K.toCoverOf.d f 0)
  rw [K.toCoverOf.ker_d_zero_eq_range_aug f]
  exact ⟨a, rfl⟩

variable [IsNoetherianRing R] [IsProper f] [IsAdicComplete (Ideal.span {t}) R]

theorem algebraize (K : X.OrderedAffineCover)
    (s : ∀ n : ℕ, Γ((parameterIdeal R X f t ^ n).subscheme,⊤))
    (hs : CompatibleFormalFunctions X (parameterIdeal R X f t) s) :
    ∃! a : Γ(X,⊤), ∀ n : ℕ, (parameterIdeal R X f t ^ n).subschemeι.appTop a = s n := by
  classical
  letI : ∀ U : X.Opens, Module R Γ(X,U) := Scheme.OrderedAffineCoverOf.moduleSections f
  let I := parameterIdeal R X f t
  have hLift (n : ℕ) (j : K.Idx 0) : ∃ a : Γ(X,K.inter j),
      (I^(n+1)).subschemeι.app (K.inter j) a = resTop _ _ (s (n+1)) :=
    (I^(n+1)).subschemeι_app_surjective ⟨K.inter j,K.isAffineOpen_inter f j⟩ _
  choose a ha using hLift
  have hd (n : ℕ) : (OModulePresheaf.unit f).d K 0 (a n) ∈
      (Ideal.span {t})^(n+1) • (⊤ : Submodule R ((OModulePresheaf.unit f).cochain K 1)) := by
    rw [cochain_mem_pow_iff_kernel]
    exact d_lift_zero R X f K _ (s (n+1)) (a n) (ha n)
  have ht (n : ℕ) : a (n+1) - a n ∈
      (Ideal.span {t})^(n+1) • (⊤ : Submodule R ((OModulePresheaf.unit f).cochain K 0)) := by
    rw [cochain_mem_pow_iff_kernel]
    intro j
    change (I^(n+1)).subschemeι.app (K.inter j) (a (n+1) j - a n j) = 0
    rw [map_sub, sub_eq_zero, ha]
    have hle : I^(n+1+1) ≤ I^(n+1) := powers_antitone X I (Nat.le_succ _)
    have h := lift_transition hle (K.inter j) (a (n+1) j) (s (n+1+1)) (ha (n+1) j)
    rw [hs (n+1) (n+1+1) hle] at h
    exact h
  have hc : (OModulePresheaf.unit f).IsCoherent := by
    intro U
    exact inferInstanceAs (Module.Finite Γ(X,U.1) Γ(X,U.1))
  obtain ⟨b, ⟨hdb,hb⟩, huniq⟩ :=
    OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
      (Ideal.span {t}) f (OModulePresheaf.unit f) hc
      (OModulePresheaf.isQuasicoherent_unit f) K a hd ht
  have hbR : b ∈ LinearMap.range (K.toCoverOf.aug f) := by
    rw [← K.toCoverOf.ker_d_zero_eq_range_aug f]
    exact hdb
  obtain ⟨z,hz⟩ := hbR
  have hzpos (n : ℕ) : (I^(n+1)).subschemeι.appTop z = s (n+1) := by
    apply subscheme_sections_ext R X f K (I^(n+1))
    intro j
    rw [← app_resTop]
    have h := (cochain_mem_pow_iff_kernel R X f t K 0 (n+1) (b - (show (OModulePresheaf.unit f).cochain K 0 from a n))).mp (hb n) j
    change (I^(n+1)).subschemeι.app (K.inter j) ((show Γ(X,K.inter j) from b j) - a n j) = 0 at h
    rw [map_sub, sub_eq_zero, ha] at h
    have hj : resTop X (K.inter j) z = b j := congrFun hz j
    rw [hj]
    exact h
  have hzall (n : ℕ) : (I^n).subschemeι.appTop z = s n := by
    cases n with
    | succ n => exact hzpos n
    | zero =>
      have hle : I^1 ≤ I^0 := powers_antitone X I (Nat.zero_le _)
      have h := congrArg (fun x => (Scheme.IdealSheafData.inclusion hle).appTop x) (hzpos 0)
      rw [hs 0 1 hle] at h
      change (((I^1).subschemeι.appTop) ≫ (Scheme.IdealSheafData.inclusion hle).appTop) z = _ at h
      rw [← Scheme.Hom.comp_appTop, Scheme.IdealSheafData.inclusion_subschemeι] at h
      exact h
  refine ⟨z, hzall, ?_⟩
  intro z' hz'
  apply sections_ext R X f K
  have hzb : K.toCoverOf.aug f z' = b := by
    apply huniq
    refine ⟨global_cocycle R X f K z', fun n => ?_⟩
    rw [cochain_mem_pow_iff_kernel]
    intro j
    change (I^(n+1)).subschemeι.app (K.inter j) (resTop X (K.inter j) z' - a n j) = 0
    rw [map_sub, sub_eq_zero, ha, app_resTop, hz']
  intro j
  exact (congrFun hzb j).trans (congrFun hz j).symm

end FormalBridge
end ArithmeticThetaGeometricPrerequisites

end

/-- Algebraization on all actual infinitesimal thickenings, with the frozen type. -/
theorem ArithmeticThetaGeometricPrerequisites.proper_formal_functions_h0 :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R] (X : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of R))) [AlgebraicGeometry.IsProper f] (s : ∀ n : ℕ, ((ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t ^ n).subscheme).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaGeometricPrerequisites.CompatibleFormalFunctions X (ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t) s → ∃! a : X.presheaf.obj (Opposite.op ⊤), ∀ n : ℕ, (ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t ^ n).subschemeι.appTop a = s n := by
  intro R _ _ t _ X f _ s hs
  exact ArithmeticThetaGeometricPrerequisites.FormalBridge.algebraize R X f t (ArithmeticThetaGeometricPrerequisites.FormalBridge.properCover R X f) s hs

#print axioms ArithmeticThetaGeometricPrerequisites.proper_formal_functions_h0
