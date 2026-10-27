import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import MarkedSectionAlgebraizationR0136
import AlgebraizedEffectiveCartierR0136
import AlgebraizedMarkedIdealSpecializationR0136
import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
import Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
import P2M.Util

/-! Coherent morphism completion, adapted from the local library proof.
The proper Cech and adic-completeness providers are reused from the frozen
ProperFormalFunctions module to avoid duplicate imported declarations. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace HomCompleteAux

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero"

section Generic

variable {A : Type*} [CommRing A]

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    g x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_smul_top_iff_of_linearEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (e : M ≃ₗ[A] M') (x : M) :
    x ∈ J • (⊤ : Submodule A M) ↔ e x ∈ J • (⊤ : Submodule A M') := by
  constructor
  · intro hx
    exact map_mem_smul_top J e.toLinearMap hx
  · intro hx
    have h := map_mem_smul_top J e.symm.toLinearMap hx
    rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at h

theorem pi_mem_smul_top {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (J : Ideal A) (w : ∀ i, M i) (hw : ∀ i, w i ∈ J • (⊤ : Submodule A (M i))) :
    w ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact map_mem_smul_top J (LinearMap.single A M i) (hw i)

theorem apply_mem_smul_top {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (J : Ideal A) {w : ∀ i, M i} (hw : w ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    w i ∈ J • (⊤ : Submodule A (M i)) :=
  map_mem_smul_top J (LinearMap.proj i) hw

theorem mem_smul_top_of_coe_mem {M : Type*} [AddCommGroup M] [Module A M] (J : Ideal A) (p : Submodule A M)
    (y : p) (hy : (y : M) ∈ J • p) : y ∈ J • (⊤ : Submodule A p) := by
  have h : (J • (⊤ : Submodule A p)).map p.subtype = J • p := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [← h] at hy
  obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.mp hy
  have : y' = y := Subtype.ext hyy
  exact this ▸ hy'

theorem coe_mem_of_mem_smul_top {M : Type*} [AddCommGroup M] [Module A M] (J : Ideal A) (p : Submodule A M)
    (y : p) (hy : y ∈ J • (⊤ : Submodule A p)) : (y : M) ∈ J • (⊤ : Submodule A M) :=
  map_mem_smul_top J p.subtype hy

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (a b : AffHom F G) (h : ∀ (W : V.affineOpens) (x : F.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

theorem d_zero_apply {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (H : OModulePresheaf π)
    (K : V.OrderedAffineCover) (c : H.cochain K 0) (t : K.Idx 1) :
    H.d K 0 c t = H.res (K.inter_le_inter_face t 0) (c (K.face t 0)) -
      H.res (K.inter_le_inter_face t 1) (c (K.face t 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul]
  rw [sub_eq_add_neg]

theorem d_zero_res_eq_zero {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (H : OModulePresheaf π) (K : V.OrderedAffineCover) (x : H.obj ⊤) :
    H.d K 0 (fun s => H.res (le_top : K.inter s ≤ ⊤) x) = 0 := by
  funext t
  rw [d_zero_apply]
  change H.res _ (H.res _ x) - H.res _ (H.res _ x) = 0
  rw [H.res_res, H.res_res, sub_self]

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Generic

structure Sys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  F : OModulePresheaf f
  G : OModulePresheaf f
  hFc : F.IsCoherent
  hFq : F.IsQuasicoherent
  hGc : G.IsCoherent
  hGq : G.IsQuasicoherent
  Gn : ℕ → OModulePresheaf f
  τ : ∀ n : ℕ, AffHom (Gn (n + 1)) (Gn n)
  ρ : ∀ n : ℕ, AffHom G (Gn n)
  hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U)
  hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))
  hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n
  ψ : ∀ n : ℕ, AffHom F (Gn n)
  hψ : ∀ n : ℕ, (τ n).comp (ψ (n + 1)) = ψ n

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

namespace Sys

theorem isLN (S : Sys I f) : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

theorem noeth (S : Sys I f) (U : X.affineOpens) : IsNoetherianRing (A U) := by
  haveI := S.isLN
  exact IsLocallyNoetherian.component_noetherian U

theorem compactSpace (S : Sys I f) : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f

def K (S : Sys I f) : X.OrderedAffineCover :=
  haveI := S.compactSpace
  coverOfCompact X

def IU (S : Sys I f) (U : X.affineOpens) : Ideal (A U) :=
  I.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom

end Sys

variable (S : Sys I f)

namespace Sys

abbrev H : OModulePresheaf f := internalHom S.F S.G

theorem H_coh_qc : S.H.IsCoherent ∧ S.H.IsQuasicoherent := by
  haveI := S.isLN
  have h := AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq f S.F S.G S.hFc S.hFq
    S.hGc S.hGq
  exact ⟨h.1, h.2.1⟩

theorem hρc_app (n : ℕ) (U : X.affineOpens) (y : S.G.obj U.1) :
    (S.τ n).app U ((S.ρ (n + 1)).app U y) = (S.ρ n).app U y := by
  rw [← AffHom.comp_app, S.hρc n]

theorem hψ_app (n : ℕ) (U : X.affineOpens) (x : S.F.obj U.1) :
    (S.τ n).app U ((S.ψ (n + 1)).app U x) = (S.ψ n).app U x := by
  rw [← AffHom.comp_app, S.hψ n]

theorem smul_Gn_eq_zero (n : ℕ) (U : X.affineOpens) (i : R) (hi : i ∈ I ^ (n + 1)) (y : (S.Gn n).obj U.1) :
    i • y = 0 := by
  obtain ⟨g, rfl⟩ := S.hρs n U y
  rw [← map_smul, ← LinearMap.mem_ker, S.hρk n U]
  exact Submodule.smul_mem_smul hi Submodule.mem_top

theorem sections_smul_mem (M : OModulePresheaf f) (U : X.Opens) (J : Ideal R) (a : Γ(X, U)) {y : M.obj U}
    (hy : y ∈ J • (⊤ : Submodule R (M.obj U))) : a • y ∈ J • (⊤ : Submodule R (M.obj U)) := by
  induction hy using Submodule.smul_induction_on' with
  | smul i hi m hm =>
    rw [← smul_comm_sections M U i a m]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  | add x hx y hy h₁ h₂ =>
    rw [smul_add]
    exact Submodule.add_mem _ h₁ h₂

theorem isQuasicoherent_Gn (n : ℕ) : (S.Gn n).IsQuasicoherent := by
  intro U r

  let D : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
  have hD : D.1 ≤ U.1 := X.basicOpen_le r
  let rr : ℕ → A D := fun N => (X.presheaf.map (homOfLE hD).op).hom (r ^ N)
  have hrr : ∀ N, rr N = (rr 1) ^ N := fun N => by simp only [rr, pow_one, map_pow]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨g, rfl⟩ := S.hρs n D x
    obtain ⟨N, y, hy⟩ := (S.hGq U r).1 g
    refine ⟨N, (S.ρ n).app U y, ?_⟩
    have nat := (S.ρ n).naturality_apply (U := D) (U' := U) hD y
    change (S.Gn n).res hD ((S.ρ n).app U y) = rr N • (S.ρ n).app D g
    rw [← nat, hy, (S.ρ n).app_smul]
  · obtain ⟨g, rfl⟩ := S.hρs n U y

    have hker : S.G.res hD g ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj D.1)) := by
      rw [← S.hρk n D, LinearMap.mem_ker, (S.ρ n).naturality_apply (U := D) (U' := U) hD g]
      exact hy

    have key : ∀ x ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj D.1)), ∃ (N : ℕ) (y₀ : S.G.obj U.1),
        y₀ ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj U.1)) ∧ S.G.res hD y₀ = rr N • x := by
      intro x hx
      induction hx using Submodule.smul_induction_on' with
      | smul i hi m hm =>
        obtain ⟨N, y₁, hy₁⟩ := (S.hGq U r).1 m
        refine ⟨N, i • y₁, Submodule.smul_mem_smul hi Submodule.mem_top, ?_⟩
        rw [map_smul, hy₁, smul_comm_sections S.G D.1 i (rr N) m]
      | add x hx y hy h₁ h₂ =>
        obtain ⟨N₁, y₁, hy₁, e₁⟩ := h₁
        obtain ⟨N₂, y₂, hy₂, e₂⟩ := h₂
        refine ⟨N₁ + N₂, (r ^ N₂) • y₁ + (r ^ N₁) • y₂,
          Submodule.add_mem _ (sections_smul_mem S.G U.1 _ _ hy₁) (sections_smul_mem S.G U.1 _ _ hy₂), ?_⟩
        rw [map_add, S.G.res_smul, S.G.res_smul, e₁, e₂, smul_add]
        change rr N₂ • rr N₁ • x + rr N₁ • rr N₂ • y = rr (N₁ + N₂) • x + rr (N₁ + N₂) • y
        rw [hrr N₁, hrr N₂, hrr (N₁ + N₂), smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm N₂ N₁]
    obtain ⟨N, y₀, hy₀, e₀⟩ := key _ hker

    have hz : S.G.res hD ((r ^ N) • g - y₀) = 0 := by
      rw [map_sub, S.G.res_smul, e₀, sub_self]
    obtain ⟨N', hN'⟩ := (S.hGq U r).2 _ hz
    refine ⟨N' + N, ?_⟩
    rw [← (S.ρ n).app_smul, ← LinearMap.mem_ker, S.hρk n U]
    have e : (r ^ (N' + N)) • g = (r ^ N') • y₀ := by
      rw [smul_sub, smul_smul, ← pow_add, sub_eq_zero] at hN'
      exact hN'
    rw [e]
    exact sections_smul_mem S.G U.1 _ _ hy₀

section Local

variable (U : X.affineOpens)

theorem mem_IU_pow_smul_top_iff (M : OModulePresheaf f) (k : ℕ) (x : M.obj U.1) :
    x ∈ S.IU U ^ k • (⊤ : Submodule (A U) (M.obj U.1)) ↔ x ∈ I ^ k • (⊤ : Submodule R (M.obj U.1)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
  haveI := M.isScalarTower U.1
  have e : S.IU U = I.map (algebraMap R (A U)) := rfl
  rw [← Submodule.restrictScalars_mem R, e, ← Ideal.map_pow, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

abbrev HomU : Type u := S.F.obj U.1 →ₗ[A U] S.G.obj U.1

theorem res_refl_fun (a : A U) : (X.presheaf.map (homOfLE (le_refl U.1)).op).hom a = a := by
  rw [Subsingleton.elim (homOfLE (le_refl U.1)).op (𝟙 (op U.1)), X.presheaf.map_id]
  rfl

def evalA : S.H.obj U.1 →ₗ[A U] S.HomU U where
  toFun φ :=
    { toFun := fun x => φ.1 ⟨U, le_rfl⟩ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => φ.2.1 ⟨U, le_rfl⟩ a x }
  map_add' φ ψ := rfl
  map_smul' a φ := by
    refine LinearMap.ext fun x => ?_
    change (a • φ).1 ⟨U, le_rfl⟩ x = a • φ.1 ⟨U, le_rfl⟩ x
    rw [internalHom_smul_apply]
    exact congrArg (· • φ.1 ⟨U, le_rfl⟩ x) (res_refl_fun U a)

theorem evalA_apply (φ : S.H.obj U.1) (x : S.F.obj U.1) : S.evalA U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem evalA_bijective : Function.Bijective (S.evalA U) := by
  haveI := S.isLN
  constructor
  · intro φ ψ h
    exact AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq S.hGq U φ ψ
      fun x => by rw [← evalA_apply, ← evalA_apply, h]
  · intro g
    obtain ⟨φ, hφ, -⟩ :=
      (AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq f S.F S.G S.hFc S.hFq
        S.hGc S.hGq).2.2 U g
    exact ⟨φ, LinearMap.ext hφ⟩

def evalE : S.H.obj U.1 ≃ₗ[A U] S.HomU U := LinearEquiv.ofBijective (S.evalA U) (S.evalA_bijective U)

theorem evalE_apply (φ : S.H.obj U.1) (x : S.F.obj U.1) : S.evalE U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem sub_mem_iff_evalE (k : ℕ) (φ φ' : S.H.obj U.1) :
    φ - φ' ∈ I ^ k • (⊤ : Submodule R (S.H.obj U.1)) ↔
      S.evalE U φ - S.evalE U φ' ∈ S.IU U ^ k • (⊤ : Submodule (A U) (S.HomU U)) := by
  rw [← S.mem_IU_pow_smul_top_iff U S.H k, mem_smul_top_iff_of_linearEquiv _ (S.evalE U), map_sub]

abbrev PU (n : ℕ) : Submodule (A U) (S.G.obj U.1) := S.IU U ^ (n + 1) • ⊤

theorem PU_eq_ker (n : ℕ) : S.PU U n = LinearMap.ker ((S.ρ n).appSections U) := by
  ext x
  rw [S.mem_IU_pow_smul_top_iff U S.G, LinearMap.mem_ker, AffHom.appSections_apply, ← LinearMap.mem_ker,
    S.hρk n U]

def eQ (n : ℕ) : (S.G.obj U.1 ⧸ S.PU U n) ≃ₗ[A U] (S.Gn n).obj U.1 :=
  (Submodule.quotEquivOfEq _ _ (S.PU_eq_ker U n)).trans
    (LinearMap.quotKerEquivOfSurjective ((S.ρ n).appSections U) (S.hρs n U))

theorem eQ_mk (n : ℕ) (y : S.G.obj U.1) : S.eQ U n (Submodule.Quotient.mk y) = (S.ρ n).app U y := by
  rw [eQ, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

theorem eQ_symm_apply (n : ℕ) (y : S.G.obj U.1) : (S.eQ U n).symm ((S.ρ n).app U y) = Submodule.Quotient.mk y := by
  rw [← eQ_mk, LinearEquiv.symm_apply_apply]

def psiT (n : ℕ) : S.F.obj U.1 →ₗ[A U] S.G.obj U.1 ⧸ S.PU U n :=
  (S.eQ U n).symm.toLinearMap ∘ₗ (S.ψ n).appSections U

theorem psiT_apply (n : ℕ) (x : S.F.obj U.1) : S.psiT U n x = (S.eQ U n).symm ((S.ψ n).app U x) := rfl

theorem PU_le (n : ℕ) : S.PU U (n + 1) ≤ S.PU U n :=
  show S.IU U ^ (n + 1 + 1) • (⊤ : Submodule (A U) (S.G.obj U.1)) ≤ S.IU U ^ (n + 1) • ⊤ from
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem factor_psiT (n : ℕ) : Submodule.factor (S.PU_le U n) ∘ₗ S.psiT U (n + 1) = S.psiT U n := by
  refine LinearMap.ext fun x => (S.eQ U n).injective ?_
  rw [LinearMap.comp_apply, psiT_apply, psiT_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨y, hy⟩ := S.hρs (n + 1) U ((S.ψ (n + 1)).app U x)
  rw [← hy, eQ_symm_apply, ← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply, eQ_mk,
    ← S.hρc_app, hy, S.hψ_app]

theorem mkQ_comp_eq_psiT_iff (n : ℕ) (g : S.HomU U) :
    Submodule.mkQ (S.PU U n) ∘ₗ g = S.psiT U n ↔ ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x := by
  constructor
  · intro h x
    have hx := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, psiT_apply] at hx
    have := congrArg (S.eQ U n) hx
    rwa [eQ_mk, LinearEquiv.apply_symm_apply] at this
  · intro h
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, psiT_apply, ← h x, eQ_symm_apply]

theorem hal :
    ∃! Φ : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
        (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : S.HomU U), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.G.obj U.1)))) ∘ₗ g = S.psiT U n) := by
  haveI := S.noeth U
  haveI : Module.Finite (A U) (S.F.obj U.1) := S.hFc U
  haveI : Module.Finite (A U) (S.G.obj U.1) := S.hGc U
  exact Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq (S.IU U) (S.psiT U)
    (S.factor_psiT U)

def Phi : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))) := (S.hal U).exists.choose

theorem Phi_compat (n : ℕ) :
    Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (S.Phi U (n + 1)) =
      S.Phi U n :=
  (S.hal U).exists.choose_spec.1 n

theorem Phi_alpha (n : ℕ) (g : S.HomU U) (hg : Submodule.Quotient.mk g = S.Phi U n) :
    ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x :=
  (S.mkQ_comp_eq_psiT_iff U n g).mp ((S.hal U).exists.choose_spec.2 n g hg)

theorem Phi_unique (Φ' : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))))
    (h1 : ∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
        (Φ' (n + 1)) = Φ' n)
    (h2 : ∀ (n : ℕ) (g : S.HomU U), Submodule.Quotient.mk g = Φ' n →
        ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x) :
    Φ' = S.Phi U :=
  (S.hal U).unique ⟨h1, fun n g hg => (S.mkQ_comp_eq_psiT_iff U n g).mpr (h2 n g hg)⟩
    (S.hal U).exists.choose_spec

theorem classes_eq_Phi (h : ℕ → S.H.obj U.1)
    (hcomp : ∀ n : ℕ, h (n + 1) - h n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)))
    (halpha : ∀ (n : ℕ) (x : S.F.obj U.1), (S.ρ n).app U ((h n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x) :
    (fun n => Submodule.Quotient.mk (S.evalE U (h n))) = S.Phi U := by
  refine S.Phi_unique U _ (fun n => ?_) (fun n g hg x => ?_)
  · change Submodule.factor _ (Submodule.mkQ _ (S.evalE U (h (n + 1)))) = Submodule.mkQ _ (S.evalE U (h n))
    rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (S.sub_mem_iff_evalE U (n + 1) _ _).mp (hcomp n)
  ·
    have hg' : g - S.evalE U (h n) ∈ S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U)) :=
      (Submodule.Quotient.eq _).mp hg
    have hgx : g x - (h n).1 ⟨U, le_rfl⟩ x ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj U.1)) := by
      rw [← S.mem_IU_pow_smul_top_iff U S.G, ← evalE_apply, ← LinearMap.sub_apply]
      exact map_mem_smul_top _ (LinearMap.applyₗ x) hg'
    have hzero : (S.ρ n).app U (g x - (h n).1 ⟨U, le_rfl⟩ x) = 0 := by
      rw [← LinearMap.mem_ker, S.hρk n U]
      exact hgx
    rw [map_sub, sub_eq_zero] at hzero
    rw [hzero, halpha]

theorem alpha_of_class (n : ℕ) (h : S.H.obj U.1) (hh : Submodule.Quotient.mk (S.evalE U h) = S.Phi U n)
    (x : S.F.obj U.1) : (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x :=
  S.Phi_alpha U n (S.evalE U h) hh x

def rep (n : ℕ) : S.H.obj U.1 :=
  (S.evalE U).symm (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose

theorem evalE_rep (n : ℕ) : S.evalE U (S.rep U n) = (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose :=
  LinearEquiv.apply_symm_apply _ _

theorem mk_evalE_rep (n : ℕ) : Submodule.Quotient.mk (S.evalE U (S.rep U n)) = S.Phi U n := by
  rw [evalE_rep]
  exact (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose_spec

theorem rep_alpha (n : ℕ) (x : S.F.obj U.1) : (S.ρ n).app U ((S.rep U n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x :=
  S.alpha_of_class U n (S.rep U n) (S.mk_evalE_rep U n) x

theorem rep_succ_sub_rep (n : ℕ) : S.rep U (n + 1) - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  rw [S.sub_mem_iff_evalE U, ← Submodule.Quotient.eq]
  have h := S.Phi_compat U n
  rw [← mk_evalE_rep, ← mk_evalE_rep] at h
  change Submodule.factor _ (Submodule.mkQ _ (S.evalE U (S.rep U (n + 1)))) =
    Submodule.mkQ _ (S.evalE U (S.rep U n)) at h
  rw [Submodule.factor_mk] at h
  exact h

theorem rep_sub_rep_of_le {n m : ℕ} (hnm : n ≤ m) :
    S.rep U m - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  induction m, hnm using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ m hnm ih =>
    have e : S.rep U (m + 1) - S.rep U n = (S.rep U (m + 1) - S.rep U m) + (S.rep U m - S.rep U n) := by abel
    rw [e]
    have hle : n + 1 ≤ m + 1 := by omega
    exact Submodule.add_mem _
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right hle) (S.rep_succ_sub_rep U m)) ih

theorem sub_rep_mem_of_classes (h : ℕ → S.H.obj U.1)
    (hcomp : ∀ n : ℕ, h (n + 1) - h n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)))
    (halpha : ∀ (n : ℕ) (x : S.F.obj U.1), (S.ρ n).app U ((h n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x) (n : ℕ) :
    h n - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  rw [S.sub_mem_iff_evalE U, ← Submodule.Quotient.eq, mk_evalE_rep]
  exact congrFun (S.classes_eq_Phi U h hcomp halpha) n

theorem alpha_of_sub_rep_mem (n : ℕ) (h : S.H.obj U.1)
    (hh : h - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1))) (x : S.F.obj U.1) :
    (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x := by
  refine S.alpha_of_class U n h ?_ x
  rw [← mk_evalE_rep, Submodule.Quotient.eq]
  exact (S.sub_mem_iff_evalE U (n + 1) _ _).mp hh

end Local

def pushFam (n : ℕ) {U : X.Opens} (h : S.H.obj U) : (internalHom S.F (S.Gn n)).obj U :=
  ⟨fun W => (S.ρ n).app W.1 ∘ₗ h.1 W,
    ⟨fun W a x => by
      change (S.ρ n).app W.1 (h.1 W (a • x)) = a • (S.ρ n).app W.1 (h.1 W x)
      rw [h.2.1 W a x, (S.ρ n).app_smul],
    fun W W' hW x => by
      change (S.ρ n).app W.1 (h.1 W (S.F.res hW x)) = (S.Gn n).res hW ((S.ρ n).app W'.1 (h.1 W' x))
      rw [h.2.2 W W' hW x, (S.ρ n).naturality_apply (U := W.1) (U' := W'.1) hW]⟩⟩

theorem pushFam_apply (n : ℕ) {U : X.Opens} (h : S.H.obj U) (W : AffBelow U) (x : S.F.obj W.1.1) :
    (S.pushFam n h).1 W x = (S.ρ n).app W.1 (h.1 W x) := rfl

def psiFam (n : ℕ) (U : X.Opens) : (internalHom S.F (S.Gn n)).obj U :=
  (internalHom S.F (S.Gn n)).res (le_top : U ≤ ⊤) (internalHom.ofAffHom S.F (S.Gn n) (S.ψ n))

theorem psiFam_apply (n : ℕ) (U : X.Opens) (W : AffBelow U) (x : S.F.obj W.1.1) :
    (S.psiFam n U).1 W x = (S.ψ n).app W.1 x := rfl

theorem alpha_below (n : ℕ) (U : X.affineOpens) (h : S.H.obj U.1)
    (halpha : ∀ x : S.F.obj U.1, (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x)
    (W : AffBelow U.1) (x : S.F.obj W.1.1) : (S.ρ n).app W.1 (h.1 W x) = (S.ψ n).app W.1 x := by
  have key : S.pushFam n h = S.psiFam n U.1 :=
    AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq (S.isQuasicoherent_Gn n) U _ _
      fun x => halpha x
  have := congrArg (fun θ : (internalHom S.F (S.Gn n)).obj U.1 => θ.1 W x) key
  exact this

theorem res_rep_sub_rep_mem (U : X.affineOpens) (W : X.affineOpens) (hW : W.1 ≤ U.1) (n : ℕ) :
    S.H.res hW (S.rep U n) - S.rep W n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj W.1)) := by
  refine S.sub_rep_mem_of_classes W (fun n => S.H.res hW (S.rep U n)) (fun n => ?_) (fun n x => ?_) n
  · rw [← map_sub]
    exact map_mem_smul_top _ (S.H.res hW) (S.rep_succ_sub_rep U n)
  · exact S.alpha_below n U (S.rep U n) (S.rep_alpha U n) ⟨W, hW⟩ x

theorem res_rep_sub_res_rep_mem (U U' W : X.affineOpens) (hW : W.1 ≤ U.1) (hW' : W.1 ≤ U'.1) (n : ℕ) :
    S.H.res hW (S.rep U n) - S.H.res hW' (S.rep U' n) ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj W.1)) := by
  have e : S.H.res hW (S.rep U n) - S.H.res hW' (S.rep U' n) =
      (S.H.res hW (S.rep U n) - S.rep W n) - (S.H.res hW' (S.rep U' n) - S.rep W n) := by abel
  rw [e]
  exact Submodule.sub_mem _ (S.res_rep_sub_rep_mem U W hW n) (S.res_rep_sub_rep_mem U' W hW' n)

abbrev Us {i : ℕ} (s : S.K.Idx i) : X.affineOpens := S.K.affineInter f s

def hcoch (n : ℕ) : S.H.cochain S.K 0 := fun s => S.rep (S.Us s) n

theorem d_hcoch_mem (n : ℕ) (t : S.K.Idx 1) :
    S.H.d S.K 0 (S.hcoch n) t ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter t))) := by
  rw [d_zero_apply]
  exact S.res_rep_sub_res_rep_mem (S.Us (S.K.face t 0)) (S.Us (S.K.face t 1)) (S.Us t)
    (S.K.inter_le_inter_face t 0) (S.K.inter_le_inter_face t 1) n

/-- Apply the already accepted coherent cochain completion theorem directly. -/
theorem exists_limit :
    ∃! a : S.H.cochain S.K 0, S.H.d S.K 0 a = 0 ∧
      ∀ n : ℕ, a - S.hcoch n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.cochain S.K 0)) := by
  apply AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
    I f S.H S.H_coh_qc.1 S.H_coh_qc.2 S.K (S.hcoch)
  · intro n
    exact pi_mem_smul_top _ _ (S.d_hcoch_mem n)
  · intro n
    exact pi_mem_smul_top _ _ (fun s => S.rep_succ_sub_rep (S.Us s) n)

def L : S.H.H0 S.K := ⟨S.exists_limit.exists.choose,
  LinearMap.mem_ker.mpr S.exists_limit.exists.choose_spec.1⟩

theorem L_sub_rep_mem (n : ℕ) (s : S.K.Idx 0) :
    (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
  apply_mem_smul_top (I ^ (n + 1)) (S.exists_limit.exists.choose_spec.2 n) s

theorem d_L : S.H.d S.K 0 (S.L : S.H.cochain S.K 0) = 0 := LinearMap.mem_ker.mp S.L.2

theorem exists_glued : ∃! Lt : S.H.obj ⊤, ∀ s : S.K.Idx 0, (S.L : S.H.cochain S.K 0) s = S.H.res le_top Lt :=
  (AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique S.hGq S.K _).mp S.d_L

def Lt : S.H.obj ⊤ := S.exists_glued.exists.choose

theorem res_Lt (s : S.K.Idx 0) : S.H.res (le_top : S.K.inter s ≤ ⊤) S.Lt = (S.L : S.H.cochain S.K 0) s :=
  (S.exists_glued.exists.choose_spec s).symm

theorem Lt_unique (M : S.H.obj ⊤) (hM : ∀ s : S.K.Idx 0, S.H.res (le_top : S.K.inter s ≤ ⊤) M =
    (S.L : S.H.cochain S.K 0) s) : M = S.Lt :=
  S.exists_glued.unique (fun s => (hM s).symm) S.exists_glued.exists.choose_spec

def phi : AffHom S.F S.G := internalHom.toAffHom S.F S.G S.Lt

theorem Lt_alpha (n : ℕ) (W : X.affineOpens) (x : S.F.obj W.1) :
    (S.ρ n).app W (S.Lt.1 ⟨W, le_top⟩ x) = (S.ψ n).app W x := by

  have hglue := (AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
    (F := S.F) (S.isQuasicoherent_Gn n) S.K
    (fun s => (internalHom S.F (S.Gn n)).res (le_top : S.K.inter s ≤ ⊤) (S.psiFam n ⊤))).mp
    (d_zero_res_eq_zero (internalHom S.F (S.Gn n)) S.K (S.psiFam n ⊤))
  have key : S.pushFam n S.Lt = S.psiFam n ⊤ := by
    refine hglue.unique (fun s => ?_) (fun s => rfl)

    refine (AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq (S.isQuasicoherent_Gn n)
      (S.Us s) _ _ fun y => ?_).symm
    change (S.ρ n).app (S.Us s) (S.Lt.1 ⟨S.Us s, le_top⟩ y) = (S.ψ n).app (S.Us s) y
    have e : S.Lt.1 ⟨S.Us s, le_top⟩ y = ((S.L : S.H.cochain S.K 0) s).1 ⟨S.Us s, le_rfl⟩ y := by
      rw [← S.res_Lt s]; rfl
    rw [e]
    exact S.alpha_of_sub_rep_mem (S.Us s) n _ (S.L_sub_rep_mem n s) y
  exact congrArg (fun θ : (internalHom S.F (S.Gn n)).obj ⊤ => θ.1 ⟨W, le_top⟩ x) key

theorem phi_spec (n : ℕ) : (S.ρ n).comp S.phi = S.ψ n :=
  affHom_ext _ _ fun W x => S.Lt_alpha n W x

theorem phi_unique (φ' : AffHom S.F S.G) (hφ' : ∀ n : ℕ, (S.ρ n).comp φ' = S.ψ n) : φ' = S.phi := by
  let M : S.H.obj ⊤ := internalHom.ofAffHom S.F S.G φ'

  let δ : S.H.cochain S.K 0 := fun s => S.H.res (le_top : S.K.inter s ≤ ⊤) M - (S.L : S.H.cochain S.K 0) s
  have hδmem : ∀ (n : ℕ) (s : S.K.Idx 0),
      δ s ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
    intro n s
    have hM : S.H.res (le_top : S.K.inter s ≤ ⊤) M - S.rep (S.Us s) n ∈
        I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
      refine S.sub_rep_mem_of_classes (S.Us s) (fun _ => S.H.res (le_top : S.K.inter s ≤ ⊤) M)
        (fun k => by rw [sub_self]; exact Submodule.zero_mem _) (fun k x => ?_) n
      change (S.ρ k).app (S.Us s) (φ'.app (S.Us s) x) = (S.ψ k).app (S.Us s) x
      rw [← AffHom.comp_app, hφ' k]
    have e : δ s = (S.H.res (le_top : S.K.inter s ≤ ⊤) M - S.rep (S.Us s) n) -
        ((S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n) := by
      change S.H.res le_top M - (S.L : S.H.cochain S.K 0) s = _
      abel
    rw [e]
    exact Submodule.sub_mem _ hM (S.L_sub_rep_mem n s)
  have hδ0 : S.H.d S.K 0 δ = 0 := by
    have e : δ = (fun s => S.H.res (le_top : S.K.inter s ≤ ⊤) M) - (S.L : S.H.cochain S.K 0) := rfl
    rw [e, map_sub, d_zero_res_eq_zero, S.d_L, sub_self]
  have hδ : δ = 0 := by
    obtain ⟨z, hz, hu⟩ :=
      AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
        I f S.H S.H_coh_qc.1 S.H_coh_qc.2 S.K (fun _ => 0)
        (fun n => by simp) (fun n => by simp)
    have hd : δ = z := hu δ ⟨hδ0, fun n => by
      simpa only [sub_zero] using pi_mem_smul_top (I ^ (n + 1)) δ (hδmem n)⟩
    have hzero : (0 : S.H.cochain S.K 0) = z := hu 0 (by simp)
    exact hd.trans hzero.symm
  have hM : M = S.Lt := S.Lt_unique M fun s => by
    have := congrFun hδ s
    rwa [Pi.zero_apply, sub_eq_zero] at this
  calc φ' = internalHom.toAffHom S.F S.G M := (internalHom.toAffHom_ofAffHom S.F S.G φ').symm
    _ = S.phi := by rw [hM]; rfl

theorem main :
    ∃ φ : AffHom S.F S.G, (∀ n : ℕ, (S.ρ n).comp φ = S.ψ n) ∧
      ∀ φ' : AffHom S.F S.G, (∀ n : ℕ, (S.ρ n).comp φ' = S.ψ n) → φ' = φ :=
  ⟨S.phi, S.phi_spec, S.phi_unique⟩

end Sys
p2m_reactivate "ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux.Sys"

end HomCompleteAux
p2m_reactivate "ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux.Sys ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux"

end
p2m_reactivate "ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux.Sys ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.HomCompleteAux"

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F G : OModulePresheaf f)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (Gn : ℕ → OModulePresheaf f) (τ : ∀ n : ℕ, OModulePresheaf.AffHom (Gn (n + 1)) (Gn n))
    (ρ : ∀ n : ℕ, OModulePresheaf.AffHom G (Gn n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (Gn n)) (hψ : ∀ n : ℕ, (τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ :=
  HomCompleteAux.Sys.main
    { F := F, G := G, hFc := hFc, hFq := hFq, hGc := hGc, hGq := hGq, Gn := Gn, τ := τ, ρ := ρ,
      hρs := hρs, hρk := hρk, hρc := hρc, ψ := ψ, hψ := hψ }

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion

#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion.solution

noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCartierR0133

lemma comap_power {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (d : ℕ) : (I ^ d).comap f = (I.comap f) ^ d := by
  induction d with
  | zero => simp only [pow_zero, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | succ d ih => rw [pow_succ, Scheme.IdealSheafData.comap_mul, ih, pow_succ]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma power_invertible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) :
    ((ArithmeticThetaAlgebraizedMarkedLineR0136.markedIdeal k M s)^d).IsInvertible := by
  apply Scheme.IdealSheafData.IsInvertible.pow
  rw [AlgebraizedEffectiveCartierR0136.markedIdeal_eq_product k M hM a s hs]
  apply AlgebraizedEffectiveCartierR0136.invertible_product
  intro i _
  exact AlgebraizedEffectiveCartierR0136.section_invertible k h3 M hM i (a i) (s i) (hs i)

lemma power_module_invertible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) :
    Scheme.Modules.IsInvertible (ArithmeticThetaAlgebraizedMarkedLineR0136.powerIdealModule k M s d) :=
  (power_invertible k h3 M hM a s hs d).isInvertible_module

lemma stage_power (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d n : ℕ) :
    ((ArithmeticThetaAlgebraizedMarkedLineR0136.markedIdeal k M s)^d).comap (M.inclusion n) =
      (ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d := by
  rw [comap_power, algebraized_marked_ideal_specialization k r hr h3 T M hM a s hs n]


lemma effective_invertible {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsEffectiveCartierIdeal I) : I.IsInvertible := by
  intro x
  obtain ⟨U, hx, f, hf, hIf⟩ := hI x
  refine ⟨U, 1, by simpa using hx, ?_⟩
  have he : X.affineBasicOpen (1 : Γ(X, U)) = U :=
    Subtype.ext (X.basicOpen_one)
  rw [he]
  exact ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, hIf⟩

lemma stage_invertible (h3 : 3 ≤ r) (a : Fin r → kˣ) (d n : ℕ) :
    ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d).IsInvertible :=
  (effective_invertible _ (GlobalCartierIdealLineR0133.effective_cartier
    k r n hr h3 (T.overlap n) (T.overlap_spec n) (T.atlas n) a)).pow d

lemma ideal_comparison_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    I.pullbackModuleComparison f ≫ (I.comap f).moduleι =
      (Scheme.Modules.pullback f).map I.moduleι ≫ unitPullback f := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Scheme.IdealSheafData.pullbackModuleComparison]
  erw [Equiv.apply_symm_apply]
  change I.moduleToPushforwardComapModule f ≫
    (Scheme.Modules.pushforward f).map (I.comap f).moduleι = _
  have hc : I.moduleToPushforwardComapModule f ≫
      (Scheme.Modules.pushforward f).map (I.comap f).moduleι =
      I.moduleι ≫ f.unitToPushforwardUnit := by
    unfold Scheme.IdealSheafData.moduleToPushforwardComapModule Scheme.IdealSheafData.moduleι
    rw [Category.assoc]
    erw [PreservesKernel.iso_inv_ι (SheafOfModules.pushforward f.toRingCatSheafHom)
      ((I.comap f).subschemeι.unitToPushforwardUnit)]
    exact kernel.lift_ι _ _ _
  rw [hc]
  rw [Adjunction.homEquiv_naturality_left]
  change I.moduleι ≫ _ = I.moduleι ≫
    ((SheafOfModules.pullbackPushforwardAdjunction _).homEquiv _ _)
      (((SheafOfModules.pullbackPushforwardAdjunction _).homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]

def idealPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I.comap f = J) :
    (Scheme.Modules.pullback f).obj I.module ≅ J.module := by
  have hJ' : (I.comap f).IsInvertible := h ▸ hJ
  letI := hI.isIso_pullbackModuleComparison f hJ'
  exact asIso (I.pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module h)

lemma idealPullbackIso_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I.comap f = J) :
    (idealPullbackIso f I J hI hJ h).hom ≫ J.moduleι =
      (Scheme.Modules.pullback f).map I.moduleι ≫ unitPullback f := by
  subst J
  simpa [idealPullbackIso] using ideal_comparison_inclusion f I

/-- Canonical comparison to the actual ideal power on every given stage. -/
def stageIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).obj
      (ArithmeticThetaAlgebraizedMarkedLineR0136.powerIdealModule k M s d) ≅
        ArithmeticThetaPositiveLineR0134.powerIdealModule k (T.atlas n) a d :=
  idealPullbackIso (M.inclusion n) _ _ (power_invertible k h3 M hM a s hs d)
    (stage_invertible k h3 a d n) (stage_power k h3 M hM a s hs d n)

lemma stageIso_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d n : ℕ) :
    (stageIso k h3 M hM a s hs d n).hom ≫
      GlobalCartierIdealLineR0133.idealInclusion
        ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d) =
      (Scheme.Modules.pullback (M.inclusion n)).map
        (GlobalCartierIdealLineR0133.idealInclusion
          ((ArithmeticThetaAlgebraizedMarkedLineR0136.markedIdeal k M s)^d)) ≫ unitPullback (M.inclusion n) :=
  idealPullbackIso_inclusion (M.inclusion n) _ _ _ _ _


section MorphismCompletion
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

lemma affHom_ext {F G : OModulePresheaf f} {Φ Ψ : OModulePresheaf.AffHom F G}
    (h : ∀ (U : X.affineOpens) (x : F.obj U.1), Φ.app U x = Ψ.app U x) : Φ = Ψ := by
  obtain ⟨a, b, c⟩ := Φ
  obtain ⟨a', b', c'⟩ := Ψ
  have : a = a' := funext fun U => LinearMap.ext (h U)
  subst this
  rfl

def ofMap {M N : X.Modules} (α : M ⟶ N) :
    OModulePresheaf.AffHom (OModulePresheaf.ofModules f M) (OModulePresheaf.ofModules f N) where
  app U :=
    { toFun := fun s => α.app U.1 s
      map_add' := fun x y => map_add (α.app U.1).hom x y
      map_smul' := fun r x => by
        show α.app U.1 ((Scheme.TwoAffineOpenCover.algebraOfHom f U.1).algebraMap r • x)
          = (Scheme.TwoAffineOpenCover.algebraOfHom f U.1).algebraMap r • α.app U.1 x
        exact Scheme.Modules.Hom.app_smul α _ x }
  app_smul U a x := Scheme.Modules.Hom.app_smul α a x
  naturality h := by
    refine LinearMap.ext fun s => ?_
    exact ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE h).op) s

lemma ofMap_comp {M N K : X.Modules} (α : M ⟶ N) (β : N ⟶ K) :
    ofMap f (α ≫ β) = (ofMap f β).comp (ofMap f α) := by
  apply affHom_ext
  intro U s
  change (α ≫ β).app U.1 s = β.app U.1 (α.app U.1 s)
  rw [Scheme.Modules.Hom.comp_app]
  rfl

lemma ofMap_injective {M N : X.Modules} : Function.Injective (ofMap f (M := M) (N := N)) := by
  intro α β h
  obtain ⟨γ, _, hu⟩ := OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules f M N (ofMap f α)
  exact (hu α (fun _ _ => rfl)).trans (hu β (by intro U s; exact congrArg (fun q => q.app U s) h.symm)).symm

/-- Formal completeness for actual sheaf morphisms between invertible modules.
The tower is specified by actual module maps, with verified affine quotient kernels. -/
theorem hom_completion [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [IsProper f]
    (F G : X.Modules) (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (N : ℕ → X.Modules) (τ : ∀ n, N (n + 1) ⟶ N n)
    (ρ : ∀ n, G ⟶ N n)
    (hρs : ∀ n (U : X.affineOpens), Function.Surjective ((ρ n).app U.1))
    (hρk : ∀ n (U : X.affineOpens), LinearMap.ker ((ofMap f (ρ n)).app U) =
      I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.ofModules f G).obj U.1)))
    (hρc : ∀ n, ρ (n + 1) ≫ τ n = ρ n)
    (ψ : ∀ n, F ⟶ N n) (hψ : ∀ n, ψ (n + 1) ≫ τ n = ψ n) :
    ∃! φ : F ⟶ G, ∀ n, φ ≫ ρ n = ψ n := by
  obtain ⟨Φ, hΦ, hu⟩ := CoherentCompletion.solution I f
    (OModulePresheaf.ofModules f F) (OModulePresheaf.ofModules f G)
    (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial f F hF.exists_trivialization)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f F hF.exists_trivialization)
    (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial f G hG.exists_trivialization)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f G hG.exists_trivialization)
    (fun n => OModulePresheaf.ofModules f (N n)) (fun n => ofMap f (τ n))
    (fun n => ofMap f (ρ n)) hρs hρk
    (fun n => by rw [← ofMap_comp, hρc]) (fun n => ofMap f (ψ n))
    (fun n => by rw [← ofMap_comp, hψ])
  obtain ⟨φ, hφ, _⟩ := OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules f F G Φ
  have hof : ofMap f φ = Φ := affHom_ext f hφ
  refine ⟨φ, ?_, ?_⟩
  · intro n
    apply ofMap_injective f
    rw [ofMap_comp, hof]
    exact hΦ n
  · intro φ' hφ'
    apply ofMap_injective f
    rw [hof]
    apply hu
    intro n
    rw [← ofMap_comp, hφ']

end MorphismCompletion


open CanonicalCartierLineReductionR0133

def chartIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (Q : Y.Modules) (e : (Scheme.Modules.pullback g).obj L ≅ Q) :
    (Scheme.Modules.pullback (f ≫ g)).obj L ≅ (Scheme.Modules.pullback f).obj Q :=
  ((Scheme.Modules.pullbackComp f g).app L).symm ≪≫ (Scheme.Modules.pullback f).mapIso e

lemma chartIso_inclusion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (Q : Y.Modules) (e : (Scheme.Modules.pullback g).obj L ≅ Q)
    (jL : L ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules))
    (jQ : Q ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (he : e.hom ≫ jQ = pulledInclusion g jL) :
    (chartIso f g L Q e).hom ≫ pulledInclusion f jQ = pulledInclusion (f ≫ g) jL := by
  unfold chartIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc]
  change (Scheme.Modules.pullbackComp f g).inv.app L ≫
    ((Scheme.Modules.pullback f).map e.hom ≫
      (Scheme.Modules.pullback f).map jQ ≫ unitPullback f) = _
  rw [← Category.assoc ((Scheme.Modules.pullback f).map e.hom), ← Functor.map_comp, he]
  exact pulledInclusion_comp_inv f g jL

lemma witness_iso {X : Scheme.{u}} {P Q : X.Modules} (e : P ≅ Q)
    (jP qP : P ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (jQ qQ : Q ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : e.hom ≫ jQ = jP) (hq : e.hom ≫ qQ = qP) (a b : Γ(X, ⊤)) :
    (∃ t : Γ(P, ⊤), jP.app ⊤ t = a ∧ qP.app ⊤ t = b) ↔
      (∃ t : Γ(Q, ⊤), jQ.app ⊤ t = a ∧ qQ.app ⊤ t = b) := by
  have hj' : e.inv ≫ jP = jQ := by rw [← hj, Iso.inv_hom_id_assoc]
  have hq' : e.inv ≫ qP = qQ := by rw [← hq, Iso.inv_hom_id_assoc]
  constructor
  · rintro ⟨t, ht, hu⟩
    refine ⟨e.hom.app ⊤ t, ?_, ?_⟩
    · change (e.hom ≫ jQ).app ⊤ t = a
      rw [hj]; exact ht
    · change (e.hom ≫ qQ).app ⊤ t = b
      rw [hq]; exact hu
  · rintro ⟨t, ht, hu⟩
    refine ⟨e.inv.app ⊤ t, ?_, ?_⟩
    · change (e.inv ≫ jP).app ⊤ t = a
      rw [hj']; exact ht
    · change (e.inv ≫ qP).app ⊤ t = b
      rw [hq']; exact hu

def reduceDual (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d n : ℕ) (φ : DualSections k M s d) :
    ArithmeticThetaPositiveLineR0134.GlobalDualSections k (T.atlas n) a d :=
  (stageIso k h3 M hM a s hs d n).inv ≫ pulledInclusion (M.inclusion n) φ

/-- The frozen chartwise realization predicate is exactly realization of every
canonical finite-stage reduction, including stage and degree zero. -/
lemma realizes_iff_reductions (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) (v : FormalSection k r hr T a d)
    (φ : DualSections k M s d) :
    Realizes k M a s d v φ ↔ ∀ n,
      ArithmeticThetaPositiveLineR0134.Realizes k (T.atlas n) a d (v.val n)
        (reduceDual k h3 M hM a s hs d n φ) := by
  apply forall_congr'
  intro n
  apply forall_congr'
  intro i
  apply witness_iso (chartIso (T.atlas n |>.chart i) (M.inclusion n) _ _
    (stageIso k h3 M hM a s hs d n))
  · exact chartIso_inclusion _ _ _ _ _ _ _ (stageIso_inclusion k h3 M hM a s hs d n)
  · apply chartIso_inclusion
    simp only [reduceDual, Iso.hom_inv_id_assoc]

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.hom_completion
#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.stageIso_inclusion
#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.realizes_iff_reductions

namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

/-- Exact affine quotient calculation for any specified pullback square. -/
lemma unit_quotient {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (f' : X' ⟶ Spec (.of (R ⧸ I ^ (n + 1)))) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))))
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (U : X.affineOpens) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app N).app U.1) ∧
      ∀ s : (OModulePresheaf.ofModules f N).obj U.1,
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app N).app U.1 s = 0 ↔
          s ∈ I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.ofModules f N).obj U.1)) := by
  letI algU : Algebra R Γ(X, U.1) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom.toAlgebra
  letI modU : Module R Γ(N, U.1) := Module.compHom _ (algebraMap R Γ(X, U.1))

  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
      (R ⧸ I ^ (n + 1)) f f' c hc N hN U.1 U.2

  have h1 : ∀ x : (R ⧸ I ^ (n + 1)) ⊗[R] Γ(N, U.1), ∃ m : Γ(N, U.1), x = 1 ⊗ₜ m := by
    intro x
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.quotTensorEquivQuotSMul Γ(N, U.1) (I ^ (n + 1)) x)
    refine ⟨m, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ (n + 1)) m, hm, LinearEquiv.symm_apply_apply]
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := β.surjective y
    obtain ⟨m, rfl⟩ := h1 x
    exact ⟨m, (hβ m).symm⟩
  · show ∀ s : Γ(N, U.1),
      (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app N).app U.1) s = 0 ↔
        s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(N, U.1))
    intro s
    have key : β (1 ⊗ₜ[R] s) = 0 ↔ s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(N, U.1)) := by
      rw [LinearEquiv.map_eq_zero_iff, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ (n + 1)) s,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    refine Iff.trans ?_ (Iff.trans key Iff.rfl)
    rw [← hβ s]


section Transition
variable {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X) (c : Z ⟶ X) (h : t ≫ c' = c)

def compIso (N : X.Modules) :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback c').obj N) ≅
      (Scheme.Modules.pullback c).obj N :=
  (Scheme.Modules.pullbackComp t c').app N ≪≫ (Scheme.Modules.pullbackCongr h).app N

def transition (N : X.Modules) :
    (Scheme.Modules.pushforward c').obj ((Scheme.Modules.pullback c').obj N) ⟶
      (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pullback c).obj N) :=
  (Scheme.Modules.pushforward c').map
      ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback c').obj N))
    ≫ (Scheme.Modules.pushforwardComp t c').hom.app
        ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback c').obj N))
    ≫ (Scheme.Modules.pushforward (t ≫ c')).map ((Scheme.Modules.pullbackComp t c').hom.app N)
    ≫ (Scheme.Modules.pushforward (t ≫ c')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
    ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback c).obj N)

lemma transition_unit (N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction c').unit.app N ≫ transition t c' c h N =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app N :=
  (Scheme.Modules.pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq t c' c h N).symm

lemma transition_map (N N' : X.Modules)
    (φ' : (Scheme.Modules.pullback c').obj N ⟶ (Scheme.Modules.pullback c').obj N')
    (φ : (Scheme.Modules.pullback c).obj N ⟶ (Scheme.Modules.pullback c).obj N')
    (hφ : φ = (compIso t c' c h N).inv ≫ (Scheme.Modules.pullback t).map φ' ≫ (compIso t c' c h N').hom) :
    transition t c' c h N ≫ (Scheme.Modules.pushforward c).map φ =
      (Scheme.Modules.pushforward c').map φ' ≫ transition t c' c h N' :=
  Scheme.Modules.transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
    t c' c h N N' φ' φ hφ

end Transition

lemma adjoint_map {X Y : Scheme.{u}} (c : Y ⟶ X) {F G : X.Modules} (φ : F ⟶ G) :
    ((Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _)
      ((Scheme.Modules.pullback c).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app G := by
  rw [Adjunction.homEquiv_unit]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.naturality φ).symm

/-- Full faithfulness for compatible morphisms on a specified system of actual
adic pullbacks, with no assumed algebraization or expansion map. -/
lemma pullback_completion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (Y : ℕ → Scheme.{u}) (c : ∀ n, Y n ⟶ X)
    (fn : ∀ n, Y n ⟶ Spec (.of (R ⧸ I ^ (n + 1))))
    (hc : ∀ n, IsPullback (c n) (fn n) f
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))))
    (t : ∀ n, Y n ⟶ Y (n + 1)) (ht : ∀ n, t n ≫ c (n + 1) = c n)
    (F G : X.Modules) (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (φn : ∀ n, (Scheme.Modules.pullback (c n)).obj F ⟶ (Scheme.Modules.pullback (c n)).obj G)
    (hφn : ∀ n, φn n = (compIso (t n) (c (n + 1)) (c n) (ht n) F).inv ≫
      (Scheme.Modules.pullback (t n)).map (φn (n + 1)) ≫
        (compIso (t n) (c (n + 1)) (c n) (ht n) G).hom) :
    ∃! φ : F ⟶ G, ∀ n, (Scheme.Modules.pullback (c n)).map φ = φn n := by
  let ρ (n : ℕ) := (Scheme.Modules.pullbackPushforwardAdjunction (c n)).unit.app G
  let ψ (n : ℕ) := (Scheme.Modules.pullbackPushforwardAdjunction (c n)).unit.app F ≫
    (Scheme.Modules.pushforward (c n)).map (φn n)
  have hψ (n : ℕ) : ψ (n + 1) ≫ transition (t n) (c (n + 1)) (c n) (ht n) G = ψ n := by
    dsimp [ψ]
    rw [Category.assoc, ← transition_map _ _ _ _ F G _ _ (hφn n),
      ← Category.assoc, transition_unit]
  obtain ⟨φ, hφ, hu⟩ := hom_completion f I F G hF hG
    (fun n => (Scheme.Modules.pushforward (c n)).obj ((Scheme.Modules.pullback (c n)).obj G))
    (fun n => transition (t n) (c (n + 1)) (c n) (ht n) G) ρ
    (fun n U => (unit_quotient I n f (fn n) (c n) (hc n) G hG U).1)
    (fun n U => Submodule.ext fun s => (unit_quotient I n f (fn n) (c n) (hc n) G hG U).2 s)
    (fun n => transition_unit _ _ _ _ G) ψ hψ
  have he (α : F ⟶ G) :
      (∀ n, (Scheme.Modules.pullback (c n)).map α = φn n) ↔ ∀ n, α ≫ ρ n = ψ n := by
    apply forall_congr'
    intro n
    rw [← Equiv.apply_eq_iff_eq ((Scheme.Modules.pullbackPushforwardAdjunction (c n)).homEquiv _ _), adjoint_map]
    rfl
  exact ⟨φ, (he φ).mpr hφ, fun α hα => hu α ((he α).mp hα)⟩

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCartierR0133 GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134

lemma pull_witness {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (j q : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (a b : Γ(Y, ⊤))
    (h : ∃ t : Γ(M, ⊤), j.app ⊤ t = a ∧ q.app ⊤ t = b) :
    ∃ t : Γ((Scheme.Modules.pullback f).obj M, ⊤),
      (pulledInclusion f j).app ⊤ t = f.appTop a ∧
      (pulledInclusion f q).app ⊤ t = f.appTop b := by
  obtain ⟨t, ht, hu⟩ := h
  let α := fromSection M t
  have hj : α ≫ j = fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) a := by
    apply unit_hom_ext
    convert ht using 1 <;> simp [α, fromSection_apply]
  have hq : α ≫ q = fromSection (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) b := by
    apply unit_hom_ext
    convert hu using 1 <;> simp [α, fromSection_apply]
  refine ⟨Scheme.Modules.Hom.app (pullFrame f α) ⊤ (1 : Γ(X, ⊤)), ?_, ?_⟩
  · have he := ConcreteCategory.congr_hom
      (congrArg (fun z => Scheme.Modules.Hom.app z ⊤) (pullFrame_evaluation f α j a hj))
      (1 : Γ(X, ⊤))
    change (pulledInclusion f j).app ⊤ _ =
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) (f.appTop a)).app ⊤ (1 : Γ(X, ⊤)) at he
    simpa [fromSection_apply] using! he
  · have he := ConcreteCategory.congr_hom
      (congrArg (fun z => Scheme.Modules.Hom.app z ⊤) (pullFrame_evaluation f α q b hq))
      (1 : Γ(X, ⊤))
    change (pulledInclusion f q).app ⊤ _ =
      (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules) (f.appTop b)).app ⊤ (1 : Γ(X, ⊤)) at he
    simpa [fromSection_apply] using! he

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma chartReduction_value (n N : ℕ) (h : n ≤ N) (x : A k N) :
    (chartReduction k n N h).appTop ((Scheme.ΓSpecIso (.of (A k N))).inv x) =
      (Scheme.ΓSpecIso (.of (A k n))).inv
        (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h x) := by
  apply (Scheme.ΓSpecIso (.of (A k n))).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of (A k n))).hom _ = (Scheme.ΓSpecIso (.of (A k n))).hom _
  erw [Iso.inv_hom_id_apply]
  exact
    affine_pullback_inv (CommRingCat.ofHom (truncReduce (ArithmeticThetaNodeCharts.Node k)
      (ArithmeticThetaNodeCharts.t k) n N h)) x

def finiteIso (h3 : 3 ≤ r) (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N) :
    (Scheme.Modules.pullback (T.transition n N h)).obj
      (ArithmeticThetaPositiveLineR0134.powerIdealModule k (T.atlas N) a d) ≅
        ArithmeticThetaPositiveLineR0134.powerIdealModule k (T.atlas n) a d :=
  idealPullbackIso _ _ _ (stage_invertible k h3 a d N) (stage_invertible k h3 a d n)
    (by rw [comap_power, marked_ideal_tower_base_change k r hr h3 T a n N h])

lemma finiteIso_inclusion (h3 : 3 ≤ r) (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N) :
    (finiteIso k h3 a d n N h (T := T)).hom ≫
      idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d) =
      pulledInclusion (T.transition n N h)
        (idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r N hr (T.atlas N) a)^d)) :=
  idealPullbackIso_inclusion _ _ _ _ _ _

def finiteReduce (h3 : 3 ≤ r) (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N)
    (φ : ArithmeticThetaPositiveLineR0134.GlobalDualSections k (T.atlas N) a d) :
    ArithmeticThetaPositiveLineR0134.GlobalDualSections k (T.atlas n) a d :=
  (finiteIso k h3 a d n N h).inv ≫ pulledInclusion (T.transition n N h) φ

lemma finiteReduce_realizes (h3 : 3 ≤ r) (a : Fin r → kˣ) (d : ℕ)
    (v : FormalSection k r hr T a d) (n N : ℕ) (h : n ≤ N)
    (φ : ArithmeticThetaPositiveLineR0134.GlobalDualSections k (T.atlas N) a d)
    (hφ : ArithmeticThetaPositiveLineR0134.Realizes k (T.atlas N) a d (v.val N) φ) :
    ArithmeticThetaPositiveLineR0134.Realizes k (T.atlas n) a d (v.val n)
      (finiteReduce k h3 a d n N h φ) := by
  intro i
  let f := T.transition n N h
  let cn := (T.atlas n).chart i
  let cN := (T.atlas N).chart i
  let g := chartReduction k n N h
  let L := ArithmeticThetaPositiveLineR0134.powerIdealModule k (T.atlas N) a d
  let Q := ArithmeticThetaPositiveLineR0134.powerIdealModule k (T.atlas n) a d
  let jL := idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r N hr (T.atlas N) a)^d)
  let jQ := idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d)
  let e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback cN).obj L) ≅
      (Scheme.Modules.pullback cn).obj Q :=
    squareIso f cn cN g ((T.transition_spec n N h).2 i) L ≪≫
      (Scheme.Modules.pullback cn).mapIso (finiteIso k h3 a d n N h)
  have hj : e.hom ≫ pulledInclusion cn jQ = pulledInclusion g (pulledInclusion cN jL) :=
    square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q jL jQ
      (finiteIso k h3 a d n N h).hom (finiteIso_inclusion k h3 a d n N h)
  have hq : e.hom ≫ pulledInclusion cn (finiteReduce k h3 a d n N h φ) =
      pulledInclusion g (pulledInclusion cN φ) := by
    apply square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q φ
      (finiteReduce k h3 a d n N h φ) (finiteIso k h3 a d n N h).hom
    simp only [finiteReduce, Iso.hom_inv_id_assoc]
    rfl
  have hw := pull_witness g ((Scheme.Modules.pullback cN).obj L)
    (pulledInclusion cN jL) (pulledInclusion cN φ) _ _ (hφ i)
  have ht := (witness_iso e _ _ _ _ hj hq _ _).mp hw
  dsimp only [g] at ht
  rw [chartReduction_value, chartReduction_value, map_pow,
    ArithmeticThetaPositiveLineR0134.PositiveSectionsReductionR0134.reduce_equation,
    v.property n N h i] at ht
  exact ht

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133 ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

lemma compIso_unit {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X)
    (c : Z ⟶ X) (h : t ≫ c' = c) :
    (compIso t c' c h (SheafOfModules.unit X.ringCatSheaf : X.Modules)).hom ≫ unitPullback c =
      (Scheme.Modules.pullback t).map (unitPullback c') ≫ unitPullback t := by
  have hh := pulledInclusion_congr h (𝟙 (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  simp only [pulledInclusion, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simp only [compIso, Iso.trans_hom, Category.assoc]
  erw [hh]
  exact unitPullback_comp_hom t c'

lemma pullback_dual_completion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (Y : ℕ → Scheme.{u}) (c : ∀ n, Y n ⟶ X)
    (fn : ∀ n, Y n ⟶ Spec (.of (R ⧸ I ^ (n + 1))))
    (hc : ∀ n, IsPullback (c n) (fn n) f
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))))
    (t : ∀ n, Y n ⟶ Y (n + 1)) (ht : ∀ n, t n ≫ c (n + 1) = c n)
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (q : ∀ n, (Scheme.Modules.pullback (c n)).obj F ⟶ (SheafOfModules.unit (Y n).ringCatSheaf : (Y n).Modules))
    (hq : ∀ n, (compIso (t n) (c (n + 1)) (c n) (ht n) F).hom ≫ q n =
      pulledInclusion (t n) (q (n + 1))) :
    ∃! φ : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      ∀ n, pulledInclusion (c n) φ = q n := by
  let G : X.Modules := SheafOfModules.unit X.ringCatSheaf
  letI (n : ℕ) : IsIso (unitPullback (c n)) := unitPullback_isIso (c n)
  let φn (n : ℕ) := q n ≫ inv (unitPullback (c n))
  have hφn (n : ℕ) : φn n = (compIso (t n) (c (n + 1)) (c n) (ht n) F).inv ≫
      (Scheme.Modules.pullback (t n)).map (φn (n + 1)) ≫
        (compIso (t n) (c (n + 1)) (c n) (ht n) G).hom := by
    apply (cancel_mono (unitPullback (c n))).mp
    have he : (Scheme.Modules.pullback (t n)).map (φn (n + 1)) ≫
        (compIso (t n) (c (n + 1)) (c n) (ht n) G).hom ≫ unitPullback (c n) =
        pulledInclusion (t n) (q (n + 1)) := by
      rw [compIso_unit]
      dsimp only [φn]
      rw [Functor.map_comp, Category.assoc,
        ← Category.assoc ((Scheme.Modules.pullback (t n)).map (inv (unitPullback (c (n + 1))))),
        ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    simp only [Category.assoc]
    rw [he, ← hq n, Iso.inv_hom_id_assoc]
    dsimp only [φn]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨φ, hφ, hu⟩ := pullback_completion I f Y c fn hc t ht F G hF
    (Scheme.Modules.isInvertible_unit X) φn hφn
  have he (α : F ⟶ G) : (∀ n, (Scheme.Modules.pullback (c n)).map α = φn n) ↔
      ∀ n, pulledInclusion (c n) α = q n := by
    apply forall_congr'
    intro n
    rw [← cancel_mono (unitPullback (c n))]
    dsimp only [φn]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rfl
  exact ⟨φ, (he φ).mp hφ, fun α hα => hu α ((he α).mpr hα)⟩

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCartierR0133 GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

lemma compIso_inclusion {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X)
    (c : Z ⟶ X) (h : t ≫ c' = c) (F : X.Modules)
    (j : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    (compIso t c' c h F).hom ≫ pulledInclusion c j = pulledInclusion t (pulledInclusion c' j) := by
  change (Scheme.Modules.pullbackComp t c').hom.app F ≫
    ((Scheme.Modules.pullbackCongr h).hom.app F ≫ pulledInclusion c j) = _
  exact (congrArg (fun z => (Scheme.Modules.pullbackComp t c').hom.app F ≫ z)
    (pulledInclusion_congr h j)).trans (pulledInclusion_comp t c' j)

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma stageIso_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d n N : ℕ) (h : n ≤ N) :
    (compIso (T.transition n N h) (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h)
      (powerIdealModule k M s d)).hom ≫ (stageIso k h3 M hM a s hs d n).hom =
      (Scheme.Modules.pullback (T.transition n N h)).map (stageIso k h3 M hM a s hs d N).hom ≫
        (finiteIso k h3 a d n N h).hom := by
  let jn := idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a)^d)
  letI : Mono jn := (ideal_realization _).1
  apply (cancel_mono jn).mp
  rw [Category.assoc, Category.assoc]
  change _ ≫ ((stageIso k h3 M hM a s hs d n).hom ≫ idealInclusion _) =
    _ ≫ ((finiteIso k h3 a d n N h).hom ≫ idealInclusion _)
  rw [stageIso_inclusion, finiteIso_inclusion]
  change _ ≫ pulledInclusion (M.inclusion n) (idealInclusion _) = _
  rw [compIso_inclusion]
  change pulledInclusion (T.transition n N h) (pulledInclusion (M.inclusion N) (idealInclusion _)) = _
  have he : (stageIso k h3 M hM a s hs d N).hom ≫
      idealInclusion ((ArithmeticThetaPolygonCartierR0133.markedIdeal k r N hr (T.atlas N) a)^d) =
      pulledInclusion (M.inclusion N)
        (idealInclusion ((ArithmeticThetaAlgebraizedMarkedLineR0136.markedIdeal k M s)^d)) :=
    stageIso_inclusion k h3 M hM a s hs d N
  rw [← he]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

def finiteDual (h3 : 3 ≤ r) (a : Fin r → kˣ) (d : ℕ)
    (v : FormalSection k r hr T a d) (n : ℕ) :
    ArithmeticThetaPositiveLineR0134.GlobalDualSections k (T.atlas n) a d :=
  (ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.exists_realizes
    k r n hr h3 (T.overlap_spec n) (T.atlas n) a d (v.val n)).choose

lemma finiteDual_realizes (h3 : 3 ≤ r) (a : Fin r → kˣ) (d : ℕ)
    (v : FormalSection k r hr T a d) (n : ℕ) :
    ArithmeticThetaPositiveLineR0134.Realizes k (T.atlas n) a d (v.val n)
      (finiteDual k h3 a d v n) :=
  (ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.exists_realizes
    k r n hr h3 (T.overlap_spec n) (T.atlas n) a d (v.val n)).choose_spec

lemma finiteDual_compatible (h3 : 3 ≤ r) (a : Fin r → kˣ) (d : ℕ)
    (v : FormalSection k r hr T a d) (n N : ℕ) (h : n ≤ N) :
    finiteDual k h3 a d v n = finiteReduce k h3 a d n N h (finiteDual k h3 a d v N) := by
  apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.realizes_unique
    k r n hr h3 (T.overlap_spec n) (T.atlas n) a d (v.val n)
  · exact finiteDual_realizes k h3 a d v n
  · exact finiteReduce_realizes k h3 a d v n N h _ (finiteDual_realizes k h3 a d v N)

def prescribedDual (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) (v : FormalSection k r hr T a d) (n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).obj (powerIdealModule k M s d) ⟶
      (SheafOfModules.unit (T.atlas n).X.ringCatSheaf : (T.atlas n).X.Modules) :=
  (stageIso k h3 M hM a s hs d n).hom ≫ finiteDual k h3 a d v n

lemma prescribedDual_compatible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) (v : FormalSection k r hr T a d) (n N : ℕ) (h : n ≤ N) :
    (compIso (T.transition n N h) (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h)
      (powerIdealModule k M s d)).hom ≫ prescribedDual k h3 M hM a s hs d v n =
      pulledInclusion (T.transition n N h) (prescribedDual k h3 M hM a s hs d v N) := by
  dsimp only [prescribedDual]
  rw [← Category.assoc, stageIso_transition, Category.assoc,
    finiteDual_compatible k h3 a d v n N h]
  simp only [finiteReduce, Iso.hom_inv_id_assoc]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCartierR0133 CanonicalCartierLineReductionR0133
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma realizes_iff_prescribed (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (d : ℕ) (v : FormalSection k r hr T a d)
    (φ : DualSections k M s d) :
    Realizes k M a s d v φ ↔ ∀ n,
      pulledInclusion (M.inclusion n) φ = prescribedDual k h3 M hM a s hs d v n := by
  rw [realizes_iff_reductions k h3 M hM a s hs d v φ]
  apply forall_congr'
  intro n
  constructor
  · intro hφ
    have he := ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.realizes_unique
      k r n hr h3 (T.overlap_spec n) (T.atlas n) a d (v.val n) hφ (finiteDual_realizes k h3 a d v n)
    have hh := congrArg (fun q => (stageIso k h3 M hM a s hs d n).hom ≫ q) he
    simpa only [reduceDual, Iso.hom_inv_id_assoc, prescribedDual] using hh
  · intro hφ
    have he : reduceDual k h3 M hM a s hs d n φ = finiteDual k h3 a d v n := by
      dsimp only [reduceDual]
      rw [hφ]
      simp only [prescribedDual, Iso.inv_hom_id_assoc]
    rw [he]
    exact finiteDual_realizes k h3 a d v n

end ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open AlgebraizedPositiveFormalSectionsR0136

/-- Every full compatible positive-line numerator system has a unique actual
algebraic dual section of the specified marked ideal power. -/
theorem algebraized_positive_formal_sections :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : Tower k r hr) (M : Model k T), IsModel k T M →
    ∀ (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)), LiftFamily k M a s →
    ∀ (d : ℕ) (v : FormalSection k r hr T a d),
      ∃! φ : DualSections k M s d, Realizes k M a s d v φ := by
  intro k _ _ r hr h3 T M hM a s hs d v
  letI : IsProper M.p := hM.1
  obtain ⟨φ, hφ, hu⟩ := pullback_dual_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n)
    (fun n => T.transition n (n + 1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n + 1) (Nat.le_succ n))
    (powerIdealModule k M s d) (power_module_invertible k h3 M hM a s hs d)
    (prescribedDual k h3 M hM a s hs d v)
    (fun n => prescribedDual_compatible k h3 M hM a s hs d v n (n + 1) (Nat.le_succ n))
  exact ⟨φ, (realizes_iff_prescribed k h3 M hM a s hs d v φ).mpr hφ,
    fun ψ hψ => hu ψ ((realizes_iff_prescribed k h3 M hM a s hs d v ψ).mp hψ)⟩

end ArithmeticThetaAlgebraizedMarkedLineR0136

#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.algebraized_positive_formal_sections
