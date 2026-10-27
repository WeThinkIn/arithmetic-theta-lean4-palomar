import ModelSymmetriesDefinitionsR0137
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_LinearMap_ExtPushout
import Mathlib
import P2M.Util
import Theorems.Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
import Theorems.Thm_AdicCompletion_isAdicComplete_map_algebraMap_of_fg
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_eq_zero_of_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_cechPushforward_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
import Theorems.Thm_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
import Theorems.Thm_IsAdicComplete_of_module_finite
import Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
import Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension
import Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
import Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
import Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
import Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
import Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
import Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open _root_.AlgebraicGeometry

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace K72W4

theorem mem_smul_top_pi_iff {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (I : Ideal R) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule R (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  constructor
  · intro hx i
    have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := M) i) hx
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)]
      at this
    exact this
  · intro hx
    have : x = ∑ i, Pi.single i (x i) := by
      ext j; simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := Submodule.mem_map_of_mem (f := LinearMap.single R M i) (hx i)
    rw [Submodule.map_smul'', Submodule.map_top] at this
    exact Submodule.smul_mono le_rfl le_top this

theorem smul_top_mem_map {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem core
    {R : Type*} [CommRing R] (I : Ideal R)
    {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1)
    (L0 L1 : ℕ → Type*) [∀ n, AddCommGroup (L0 n)] [∀ n, AddCommGroup (L1 n)]
    (lam0 : ∀ n, C0 →+ L0 n) (lam1 : ∀ n, C1 →+ L1 n)
    (hsurj : ∀ n, Function.Surjective (lam0 n))
    (hker0 : ∀ n (x : C0), lam0 n x = 0 ↔ x ∈ I ^ (n + 1) • (⊤ : Submodule R C0))
    (hker1 : ∀ n (x : C1), lam1 n x = 0 → x ∈ I ^ (n + 1) • (⊤ : Submodule R C1))
    (dn : ∀ n, L0 n →+ L1 n) (hd : ∀ n (x : C0), dn n (lam0 n x) = lam1 n (d x))
    (τ : ∀ n, L0 (n + 1) →+ L0 n) (hτ : ∀ n (x : C0), τ n (lam0 (n + 1) x) = lam0 n x)
    (H : ∀ t : ℕ → C0, (∀ n, d (t n) ∈ I ^ (n + 1) • (⊤ : Submodule R C1)) →
      (∀ n, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0)) →
      ∃! a : C0, d a = 0 ∧ ∀ n, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0)) :
    (∀ a : C0, d a = 0 → (∀ n, lam0 n a = 0) → a = 0) ∧
    (∀ ℓ : ∀ n, L0 n, (∀ n, dn n (ℓ n) = 0) → (∀ n, τ n (ℓ (n + 1)) = ℓ n) →
      ∃ a : C0, d a = 0 ∧ ∀ n, lam0 n a = ℓ n) := by
  constructor
  · intro a hda hlam
    obtain ⟨a', -, huniq⟩ := H (fun _ => 0) (fun n => by simp) (fun n => by simp)
    have h1 : a = a' := huniq a ⟨hda, fun n => by rw [sub_zero, ← hker0 n]; exact hlam n⟩
    have h2 : (0 : C0) = a' := huniq 0 ⟨map_zero d, fun n => by simp⟩
    rw [h1, ← h2]
  · intro ℓ hdℓ hτℓ
    choose t ht using fun n => hsurj n (ℓ n)
    have hdt : ∀ n, d (t n) ∈ I ^ (n + 1) • (⊤ : Submodule R C1) := fun n => by
      apply hker1 n
      rw [← hd, ht, hdℓ]
    have htt : ∀ n, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0) := fun n => by
      rw [← hker0 n, map_sub, ← hτ, ht, ht, hτℓ, sub_self]
    obtain ⟨a, ⟨hda, han⟩, -⟩ := H t hdt htt
    refine ⟨a, hda, fun n => ?_⟩
    have : lam0 n (a - t n) = 0 := (hker0 n _).mpr (han n)
    rw [map_sub, sub_eq_zero] at this
    rw [this, ht]

section Bridge

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {π : Y ⟶ Spec (CommRingCat.of R)}
  (G : OModulePresheaf π) (K : Y.OrderedAffineCover)

def σ (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by omega)⟩

@[scoped simp] theorem σ_val (i : K.ι) (k : Fin 1) : (σ K i).1 k = i := rfl

theorem eq_σ (s : K.Idx 0) : σ K (s.1 0) = s :=
  Subtype.ext (funext fun k => by rw [σ_val, Fin.fin_one_eq_zero k])

theorem le_inter_σ (i : K.ι) : K.U i ≤ K.inter (σ K i) := le_iInf fun _ => le_rfl

theorem inter_le_fst {n : ℕ} (s : K.Idx n) : K.inter s ≤ K.U (s.1 0) := K.inter_le s 0

abbrev pairU (s : K.Idx 1) : Y.Opens := K.U (s.1 0) ⊓ K.U (s.1 1)

theorem inter_le_pairU (s : K.Idx 1) : K.inter s ≤ pairU K s := le_inf (K.inter_le s 0) (K.inter_le s 1)

theorem pairU_le_inter (s : K.Idx 1) : pairU K s ≤ K.inter s :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem res_congr_idx (x : G.cochain K 0) {s s' : K.Idx 0} (h : s = s')
    {O : Y.Opens} (h1 : O ≤ K.inter s) :
    G.res h1 (x s) = G.res (h ▸ h1) (x s') := by
  subst h; rfl

def E0 : G.cochain K 0 ≃ₗ[R] (∀ i : K.ι, G.obj (K.U i)) where
  toFun x i := G.res (le_inter_σ K i) (x (σ K i))
  invFun y s := G.res (inter_le_fst K s) (y (s.1 0))
  map_add' x y := funext fun i => map_add _ _ _
  map_smul' r x := funext fun i => LinearMap.map_smul _ _ _
  left_inv x := by
    funext s
    show G.res _ (G.res _ (x (σ K (s.1 0)))) = x s
    rw [G.res_res, res_congr_idx G K x (eq_σ K s)]
    exact G.res_refl_apply _ _
  right_inv y := by
    funext i
    show G.res _ (G.res _ (y i)) = y i
    rw [G.res_res]
    exact G.res_refl_apply _ _

theorem E0_apply (x : G.cochain K 0) (i : K.ι) : E0 G K x i = G.res (le_inter_σ K i) (x (σ K i)) := rfl

def E1 : G.cochain K 1 ≃ₗ[R] (∀ s : K.Idx 1, G.obj (pairU K s)) where
  toFun x s := G.res (pairU_le_inter K s) (x s)
  invFun y s := G.res (inter_le_pairU K s) (y s)
  map_add' x y := funext fun s => map_add _ _ _
  map_smul' r x := funext fun s => LinearMap.map_smul _ _ _
  left_inv x := by
    funext s
    show G.res _ (G.res _ (x s)) = x s
    rw [G.res_res]
    exact G.res_refl_apply _ _
  right_inv y := by
    funext s
    show G.res _ (G.res _ (y s)) = y s
    rw [G.res_res]
    exact G.res_refl_apply _ _

theorem E1_apply (x : G.cochain K 1) (s : K.Idx 1) : E1 G K x s = G.res (pairU_le_inter K s) (x s) := rfl

theorem face_zero_eq (s : K.Idx 1) : K.face s 0 = σ K (s.1 1) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem face_one_eq (s : K.Idx 1) : K.face s 1 = σ K (s.1 0) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem E1_d0 (x : G.cochain K 0) (s : K.Idx 1) :
    E1 G K (G.d K 0 x) s =
      G.res inf_le_right (E0 G K x (s.1 1)) - G.res inf_le_left (E0 G K x (s.1 0)) := by
  rw [E1_apply, OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_add, map_neg]
  rw [G.res_res, G.res_res, res_congr_idx G K x (face_zero_eq K s), res_congr_idx G K x (face_one_eq K s),
    E0_apply, E0_apply, G.res_res, G.res_res, sub_eq_add_neg]

def σ₂ {i j : K.ι} (hij : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exact hij⟩

theorem σ₂_fst {i j : K.ι} (hij : i < j) : (σ₂ K hij).1 0 = i := rfl
theorem σ₂_snd {i j : K.ι} (hij : i < j) : (σ₂ K hij).1 1 = j := rfl

theorem d0_eq_zero_iff (x : G.cochain K 0) :
    G.d K 0 x = 0 ↔ ∀ i j : K.ι,
      G.res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (E0 G K x i)
        = G.res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (E0 G K x j) := by
  constructor
  · intro hd
    have key : ∀ s : K.Idx 1,
        G.res (inf_le_left : pairU K s ≤ K.U (s.1 0)) (E0 G K x (s.1 0))
          = G.res (inf_le_right : pairU K s ≤ K.U (s.1 1)) (E0 G K x (s.1 1)) := fun s => by
      have hs : E1 G K (G.d K 0 x) s = 0 := by rw [hd, map_zero]; rfl
      rw [E1_d0, sub_eq_zero] at hs
      exact hs.symm
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key (σ₂ K hij)
    · rfl
    · have hk : G.res (inf_le_left : K.U j ⊓ K.U i ≤ K.U j) (E0 G K x j)
          = G.res (inf_le_right : K.U j ⊓ K.U i ≤ K.U i) (E0 G K x i) := key (σ₂ K hji)
      have h := congrArg (G.res (le_inf inf_le_right inf_le_left : K.U i ⊓ K.U j ≤ K.U j ⊓ K.U i)) hk
      rw [G.res_res, G.res_res] at h
      exact h.symm
  · intro h
    apply (E1 G K).injective
    rw [map_zero]
    funext s
    rw [E1_d0, Pi.zero_apply, sub_eq_zero]
    exact (h (s.1 0) (s.1 1)).symm

theorem mem_H0_iff (x : G.cochain K 0) :
    x ∈ G.H0 K ↔ ∀ i j : K.ι,
      G.res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (E0 G K x i)
        = G.res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (E0 G K x j) := by
  rw [OModulePresheaf.H0, LinearMap.mem_ker, d0_eq_zero_iff]

end Bridge

section Cover

variable {P : Scheme.{u}} {Z : Scheme.{u}} (i : Z ⟶ P) {V' : Scheme.{u}} (g : V' ⟶ Z)
  (K' : V'.OrderedAffineCover) (W : P.affineOpens) {Y : Scheme.{u}} (t : Y ⟶ V')

def KY (hta : ∀ j : K'.ι, IsAffineOpen (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)))
    (hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤) :
    Y.OrderedAffineCover where
  ι := K'.ι
  U j := t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)
  isAffineOpen := hta
  iSup_eq_top := hcov

theorem KY_U (hta : ∀ j : K'.ι, IsAffineOpen (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)))
    (hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤) (j : K'.ι) :
    (KY i g K' W t hta hcov).U j = t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) := rfl

theorem iSup_preimage_chart_eq_top {S : Scheme.{u}} (sY : Y ⟶ S) (f : S ⟶ P)
    (hf : f ⁻¹ᵁ W.1 = ⊤) (hw : t ≫ (g ≫ i) = sY ≫ f) :
    ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤ := by
  have hW : t ⁻¹ᵁ ((g ≫ i) ⁻¹ᵁ W.1) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage, hf, Scheme.Hom.preimage_top]
  have hj : ∀ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = t ⁻¹ᵁ K'.U j :=
    fun j => by
      show t ⁻¹ᵁ K'.U j ⊓ t ⁻¹ᵁ ((g ≫ i) ⁻¹ᵁ W.1) = t ⁻¹ᵁ K'.U j
      rw [hW, inf_top_eq]
  simp_rw [hj]
  exact t.iSup_preimage_eq_top K'.iSup_eq_top

end Cover

end K72W4
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4"

open K72W4 in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) :
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∃ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) ∧
          ∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = (ℓ n).1 j) ∧
    (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        (∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = 0) →
        c = 0) ∧
    (∃ s : Finset (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))),
        (∀ c ∈ s, (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j'))) ∧
        ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) → c ∈ Submodule.span R (s : Set (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))))) := by
  classical
  haveI := hRc
  haveI : IsSeparated ((g ≫ i) ≫ q) := inferInstance

  set J : Ideal R := I.map ((algebraMap Γ(P, W.1) R).comp
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) with hJ

  let aC : K'.ι → V'.affineOpens := fun j => OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j
  have hC : ∀ j, (aC j).1 ≤ (g ≫ i) ⁻¹ᵁ W.1 := fun j =>
    OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j

  have hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤ :=
    iSup_preimage_chart_eq_top i g K' W t sY
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec)
      (by rw [Scheme.Hom.comp_preimage, W.2.fromSpec_preimage_self, Scheme.Hom.preimage_top]) hY.w
  let KYc : Y.OrderedAffineCover := KY i g K' W t (fun j => hta (aC j) (hC j)) hcov
  let aP : KYc.Idx 1 → V'.affineOpens := fun s =>
    ⟨(aC (s.1 0)).1 ⊓ (aC (s.1 1)).1,
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated ((g ≫ i) ≫ q) (aC (s.1 0)).2 (aC (s.1 1)).2⟩
  have hP : ∀ s, (aP s).1 ≤ (g ≫ i) ⁻¹ᵁ W.1 := fun s => inf_le_left.trans (hC _)

  let L0 : ℕ → Type u := fun n => ∀ j : K'.ι, (F' n).obj (aC j).1
  let L1 : ℕ → Type u := fun n => ∀ s : KYc.Idx 1, (F' n).obj (aP s).1
  let lam0 : ∀ n, G.cochain KYc 0 →+ L0 n := fun n =>
    (AddMonoidHom.pi fun j => (θ n (aC j) (hC j)).comp
      (Pi.evalAddMonoidHom (fun j : K'.ι => G.obj (KYc.U j)) j)).comp (E0 G KYc).toLinearMap.toAddMonoidHom
  let lam1 : ∀ n, G.cochain KYc 1 →+ L1 n := fun n =>
    (AddMonoidHom.pi fun s => (θ n (aP s) (hP s)).comp
      (Pi.evalAddMonoidHom (fun s : KYc.Idx 1 => G.obj (pairU KYc s)) s)).comp
        (E1 G KYc).toLinearMap.toAddMonoidHom
  let dn : ∀ n, L0 n →+ L1 n := fun n =>
    AddMonoidHom.pi fun s =>
      ((F' n).res (inf_le_right : (aP s).1 ≤ (aC (s.1 1)).1)).toAddMonoidHom.comp
          (Pi.evalAddMonoidHom (fun j : K'.ι => (F' n).obj (aC j).1) (s.1 1))
        - ((F' n).res (inf_le_left : (aP s).1 ≤ (aC (s.1 0)).1)).toAddMonoidHom.comp
          (Pi.evalAddMonoidHom (fun j : K'.ι => (F' n).obj (aC j).1) (s.1 0))
  let τ : ∀ n, L0 (n + 1) →+ L0 n := fun n =>
    AddMonoidHom.pi fun j => ((φ' n).app (aC j)).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun j : K'.ι => (F' (n + 1)).obj (aC j).1) j)
  have hsurj : ∀ n, Function.Surjective (lam0 n) := fun n y => by
    choose z hz using fun j => hθo n (aC j) (hC j) (y j)
    refine ⟨(E0 G KYc).symm z, funext fun j => ?_⟩
    show θ n (aC j) (hC j) (E0 G KYc ((E0 G KYc).symm z) j) = y j
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker0 : ∀ n (x : G.cochain KYc 0), lam0 n x = 0 ↔ x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := by
    intro n x
    constructor
    · intro h0
      have h1 : ∀ j, E0 G KYc x j ∈ J ^ (n + 1) • (⊤ : Submodule R _) := fun j =>
        (hθk n (aC j) (hC j) _).mp (congrFun h0 j)
      have h2 : E0 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := (mem_smul_top_pi_iff _ _).mpr h1
      have h3 : (E0 G KYc).symm (E0 G KYc x) ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
        smul_top_mem_map _ (E0 G KYc).symm.toLinearMap h2
      rwa [LinearEquiv.symm_apply_apply] at h3
    · intro hx
      funext j
      show θ n (aC j) (hC j) (E0 G KYc x j) = 0
      rw [hθk n (aC j) (hC j)]
      have h3 : E0 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
        smul_top_mem_map _ (E0 G KYc).toLinearMap hx
      exact (mem_smul_top_pi_iff _ _).mp h3 j
  have hker1 : ∀ n (x : G.cochain KYc 1), lam1 n x = 0 → x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := by
    intro n x h0
    have h1 : ∀ s, E1 G KYc x s ∈ J ^ (n + 1) • (⊤ : Submodule R _) := fun s =>
      (hθk n (aP s) (hP s) _).mp (congrFun h0 s)
    have h2 : E1 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := (mem_smul_top_pi_iff _ _).mpr h1
    have h3 : (E1 G KYc).symm (E1 G KYc x) ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
      smul_top_mem_map _ (E1 G KYc).symm.toLinearMap h2
    rwa [LinearEquiv.symm_apply_apply] at h3
  have hd : ∀ n (x : G.cochain KYc 0), dn n (lam0 n x) = lam1 n (G.d KYc 0 x) := by
    intro n x
    funext s
    show (F' n).res inf_le_right (θ n (aC (s.1 1)) (hC (s.1 1)) (E0 G KYc x (s.1 1)))
        - (F' n).res inf_le_left (θ n (aC (s.1 0)) (hC (s.1 0)) (E0 G KYc x (s.1 0)))
      = θ n (aP s) (hP s) (E1 G KYc (G.d KYc 0 x) s)
    rw [hθr n (aP s) (aC (s.1 1)) (hP s) (hC (s.1 1)) inf_le_right,
      hθr n (aP s) (aC (s.1 0)) (hP s) (hC (s.1 0)) inf_le_left, E1_d0]
    exact (map_sub (θ n (aP s) (hP s)) _ _).symm
  have hτ : ∀ n (x : G.cochain KYc 0), τ n (lam0 (n + 1) x) = lam0 n x := by
    intro n x
    funext j
    exact hθφ n (aC j) (hC j) _
  have H : ∀ tt : ℕ → G.cochain KYc 0, (∀ n, G.d KYc 0 (tt n) ∈ J ^ (n + 1) • (⊤ : Submodule R _)) →
      (∀ n, tt (n + 1) - tt n ∈ J ^ (n + 1) • (⊤ : Submodule R _)) →
      ∃! a : G.cochain KYc 0, G.d KYc 0 a = 0 ∧ ∀ n, a - tt n ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
    fun tt hd' ht' =>
      AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
        J sY G hGc hGq KYc tt hd' ht'
  obtain ⟨hinj, hsur⟩ := core J (G.d KYc 0) L0 L1 lam0 lam1 hsurj hker0 hker1 dn hd τ hτ H
  refine ⟨?_, ?_, ?_⟩
  ·
    intro ℓ hℓ
    obtain ⟨a, hda, hla⟩ := hsur (fun n => (ℓ n).1)
      (fun n => funext fun s => by
        show (F' n).res inf_le_right ((ℓ n).1 (s.1 1)) - (F' n).res inf_le_left ((ℓ n).1 (s.1 0)) = 0
        rw [sub_eq_zero]
        exact ((OModulePresheaf.cechPushforward.mem_cocycles_iff (g ≫ i) q K' (F' n) W.1 (ℓ n).1).mp
          (ℓ n).2 (s.1 0) (s.1 1)).symm)
      (fun n => funext fun j => congrArg (fun z => z.1 j) (hℓ n))
    refine ⟨E0 G KYc a, (d0_eq_zero_iff G KYc a).mp hda, fun n j => ?_⟩
    exact congrFun (hla n) j
  ·
    intro c hc h0
    have hda : G.d KYc 0 ((E0 G KYc).symm c) = 0 := by
      rw [d0_eq_zero_iff]
      intro j j'
      rw [LinearEquiv.apply_symm_apply]
      exact hc j j'
    have hz := hinj ((E0 G KYc).symm c) hda (fun n => funext fun j => by
      show θ n (aC j) (hC j) (E0 G KYc ((E0 G KYc).symm c) j) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact h0 n j)
    have : c = E0 G KYc ((E0 G KYc).symm c) := ((E0 G KYc).apply_symm_apply c).symm
    rw [this, hz]
    exact map_zero (E0 G KYc)
  ·
    have hfin : Module.Finite R (G.H0 KYc) :=
      (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper G hGc hGq KYc).1
    let Φ : G.H0 KYc →ₗ[R] (∀ j : KYc.ι, G.obj (KYc.U j)) :=
      (E0 G KYc).toLinearMap.comp (G.H0 KYc).subtype
    have hfg : (LinearMap.range Φ).FG := by
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map Φ
    obtain ⟨s, hs⟩ := hfg
    have hrange : ∀ c : ∀ j : KYc.ι, G.obj (KYc.U j), c ∈ LinearMap.range Φ ↔
        ∀ j j' : KYc.ι, G.res (inf_le_left : KYc.U j ⊓ KYc.U j' ≤ KYc.U j) (c j)
          = G.res (inf_le_right : KYc.U j ⊓ KYc.U j' ≤ KYc.U j') (c j') := by
      intro c
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact (mem_H0_iff G KYc a).mp ha
      · intro hc
        refine ⟨⟨(E0 G KYc).symm c, (mem_H0_iff G KYc _).mpr fun j j' => ?_⟩, ?_⟩
        · rw [LinearEquiv.apply_symm_apply]; exact hc j j'
        · exact (E0 G KYc).apply_symm_apply c
    refine ⟨s, fun c hcs => (hrange c).mp (hs ▸ Submodule.subset_span hcs), fun c hc => ?_⟩
    have hc' := (hrange c).mpr hc
    rw [← hs] at hc'
    exact hc'

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) :
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∃ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) ∧
          ∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = (ℓ n).1 j) ∧
    (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        (∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = 0) →
        c = 0) ∧
    (∃ s : Finset (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))),
        (∀ c ∈ s, (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j'))) ∧
        ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) → c ∈ Submodule.span R (s : Set (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))))) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

namespace W_ASM

theorem algebraMap_smul_eq_app_appLE_smul
    {P V' Y : Scheme.{u}} (p' : V' ⟶ P) (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (sY : Y ⟶ Spec (CommRingCat.of R)) (t : Y ⟶ V')
    (hY : IsPullback t sY p' (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (G : OModulePresheaf sY) (V : V'.Opens) (h : V ≤ p' ⁻¹ᵁ W.1) (a : Γ(P, W.1)) (y : G.obj (t ⁻¹ᵁ V)) :
    algebraMap Γ(P, W.1) R a • y = (t.app V).hom ((p'.appLE W.1 V h).hom a) • y := by
  letI inst := Scheme.TwoAffineOpenCover.algebraOfHom sY (t ⁻¹ᵁ V)
  rw [← IsScalarTower.algebraMap_smul Γ(Y, t ⁻¹ᵁ V) (algebraMap Γ(P, W.1) R a) y]
  congr 1

  have appLE_congr_hom : ∀ {f₁ f₂ : Y ⟶ P} (hf : f₁ = f₂) (e : t ⁻¹ᵁ V ≤ f₁ ⁻¹ᵁ W.1),
      f₁.appLE W.1 (t ⁻¹ᵁ V) e = f₂.appLE W.1 (t ⁻¹ᵁ V) (hf ▸ e) := by
    rintro f₁ f₂ rfl e; rfl
  have e1 : t ⁻¹ᵁ V ≤ (t ≫ p') ⁻¹ᵁ W.1 := (Opens.map t.base).monotone h
  have e4 : (⊤ : (Spec (P.presheaf.obj (Opposite.op W.1))).Opens) ≤ W.2.fromSpec ⁻¹ᵁ W.1 :=
    (W.2.fromSpec_preimage_self).symm.le
  have e3 : (⊤ : (Spec (CommRingCat.of R)).Opens)
      ≤ (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec) ⁻¹ᵁ W.1 := by
    intro x _; exact e4 (Set.mem_univ _)

  have hR : p'.appLE W.1 V h ≫ t.app V
      = W.2.fromSpec.appLE W.1 ⊤ e4
        ≫ (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R))).appTop
        ≫ sY.appLE ⊤ (t ⁻¹ᵁ V) le_top := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hY.w,
      ← Scheme.Hom.appLE_comp_appLE sY _ W.1 ⊤ (t ⁻¹ᵁ V) e3 le_top,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R))) W.2.fromSpec
        W.1 ⊤ ⊤ e4 le_top]
    rfl

  have hF : W.2.fromSpec.appLE W.1 ⊤ e4 = (Scheme.ΓSpecIso (P.presheaf.obj (Opposite.op W.1))).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le W.2 W.1 le_rfl, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    have h1 : (homOfLE (le_refl W.1)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]
    have h2 : ((homOfLE (le_top : W.2.fromSpec ⁻¹ᵁ W.1 ≤ ⊤)).op ≫ (homOfLE e4).op) = 𝟙 _ := Subsingleton.elim _ _
    rw [h2, CategoryTheory.Functor.map_id, Category.comp_id]

  change (sY.appLE ⊤ (t ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((CommRingCat.ofHom (algebraMap Γ(P, W.1) R)).hom a)) = (p'.appLE W.1 V h ≫ t.app V).hom a
  rw [hR, hF]
  have nat := congrArg (fun f => f.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat ⊢
  rw [nat]
  rfl

theorem torsion_of_frame
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) :
    ∃ N : ℕ,
      (∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, a • x = 0) ∧
      (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N,
          ∃ x : L, ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = algebraMap Γ(P, W.1) R a • c j) := by
  classical
  obtain ⟨-, -, h4c⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk hRc sY t hY hta G hGc hGq ε hεr hεβ θ hθs hθr hθφ hθε hθo hθk
  have h5 :=
    AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk sY t hY hta G hGc hGq ε hεr hεβ

  let D : (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) →ₗ[R]
      (∀ p : K'.ι × K'.ι, G.obj (t ⁻¹ᵁ ((OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2)))) :=
    LinearMap.pi fun p =>
      (G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2) ≤ _))).comp
          (LinearMap.proj p.1) -
        (G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2) ≤ _))).comp
          (LinearMap.proj p.2)
  let H : Submodule R (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) := LinearMap.ker D
  have memH : ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)), c ∈ H ↔ (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) := by
    intro c
    simp only [H, D, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero, Prod.forall]

  let u0 : L →ₗ[R] (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) := LinearMap.pi fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))
  have hu0 : ∀ x : L, u0 x ∈ H := fun x => (memH _).2 fun j j' => by
    simp only [u0, LinearMap.pi_apply]
    rw [hεr, hεr]
  let uu : L →ₗ[R] H := LinearMap.codRestrict H u0 hu0
  have huu : ∀ (x : L) (j : K'.ι), ((uu x : H) : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) j = ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x :=
    fun x j => rfl

  haveI : IsNoetherianRing Γ(P, W.1) := by
    haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
    exact IsLocallyNoetherian.component_noetherian W
  obtain ⟨S0, hS0⟩ := (isNoetherianRing_iff_ideal_fg Γ(P, W.1)).mp inferInstance ((Scheme.IdealSheafData.vanishingIdeal T').ideal W)
  let S : Finset R := S0.image (algebraMap Γ(P, W.1) R)
  let J : Ideal R := ((Scheme.IdealSheafData.vanishingIdeal T').ideal W).map (algebraMap Γ(P, W.1) R)
  have hSJ : Ideal.span (S : Set R) = J := by
    simp only [S, J, Finset.coe_image]
    rw [← Ideal.map_span, hS0]
  have hS0mem : ∀ a ∈ S0, a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W := fun a ha => hS0 ▸ Ideal.subset_span ha

  haveI : IsNoetherian R L := isNoetherian_of_isNoetherianRing_of_finite R L
  have hkerfg : (LinearMap.ker uu).FG := IsNoetherian.noetherian _
  have hHfg : H.FG := by
    obtain ⟨s, hs1, hs2⟩ := h4c
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun c hc => (memH c).2 (hs1 c hc)) fun c hc => hs2 c ((memH c).1 hc)⟩
  haveI : Module.Finite R H := Module.Finite.iff_fg.mpr hHfg
  have hcoker : Module.Finite R (H ⧸ LinearMap.range uu) := inferInstance

  have hk : ∀ a ∈ S, ∀ x : L, uu x = 0 → ∃ k : ℕ, a ^ k • x = 0 := by
    intro a ha x hx
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk⟩ := (h5 a0 (hS0mem a0 ha0)).1 x fun j => by
      rw [← huu x j, hx]; rfl
    exact ⟨k, by rw [← map_pow, algebraMap_smul]; exact hk⟩
  have hc : ∀ a ∈ S, ∀ y : H, ∃ (k : ℕ) (x : L), uu x = a ^ k • y := by
    intro a ha y
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, x, hx⟩ := (h5 a0 (hS0mem a0 ha0)).2 y.1 ((memH _).1 y.2)
    refine ⟨k, x, Subtype.ext (funext fun j => ?_)⟩
    rw [huu, hx j]
    rfl
  obtain ⟨N, hN1, hN2⟩ :=
    Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul S J hSJ uu hkerfg hcoker hk hc
  have hmemJ : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, algebraMap Γ(P, W.1) R a ∈ J ^ N := fun a ha => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  refine ⟨N, fun x hx a ha => ?_, fun c hcc a ha => ?_⟩
  · have h1 : uu x = 0 := Subtype.ext (funext fun j => by rw [huu, hx j]; rfl)
    have := hN1 x h1 _ (hmemJ a ha)
    rwa [algebraMap_smul] at this
  · obtain ⟨x, hx⟩ := hN2 ⟨c, (memH c).2 hcc⟩ _ (hmemJ a ha)
    exact ⟨x, fun j => by rw [← huu x j, hx]; rfl⟩

theorem threads_of_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    (hprt : ∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n)
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1))))
    (N : ℕ)
    (hk : ∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, a • x = 0)
    (hc : ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N,
          ∃ x : L, ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = algebraMap Γ(P, W.1) R a • c j) :
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0) := by
  classical
  obtain ⟨h4a, h4b, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk hRc sY t hY hta G hGc hGq ε hεr hεβ θ hθs hθr hθφ hθε hθo hθk

  have hvθ : ∀ (n : ℕ) (x : L) (j : K'.ι),
      ((v n).app W (pr n x)).1 j
        = θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j)
            (ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) := by
    intro n x j
    rw [hvη, hθε]
  refine ⟨?_, ?_⟩
  ·
    intro ℓ hℓ a ha
    obtain ⟨c, hcc, hcθ⟩ := h4a ℓ hℓ
    obtain ⟨x, hx⟩ := hc c hcc a ha
    refine ⟨fun n => pr n x, fun n => hprc n x, fun n => ?_⟩
    apply OModulePresheaf.cechPushforward.ext
    intro j
    rw [hvθ, hx j, OModulePresheaf.cechPushforward.coe_sectionsSMul, ← hcθ n j,
      algebraMap_smul_eq_app_appLE_smul (g ≫ i) W R sY t hY G _
        (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) a (c j),
      hθs]
  ·
    intro m hm hv0 a ha n
    obtain ⟨x, hx⟩ := hprt m hm
    have hcc : (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) ((fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) ((fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) j')) := fun j j' => by
      simp only []
      rw [hεr, hεr]
    have hzero := h4b (fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) hcc fun n j => by
      simp only []
      rw [← hvθ, hx n, hv0 n]
      rfl
    have hux : ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0 := fun j => congr_fun hzero j
    have hax : a • x = 0 := hk x hux a ha
    rw [← hx n, ← map_smul, hax, map_zero]

theorem exists_frame
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)
    (W : P.affineOpens) (J : Ideal Γ(P, W.1)) (hJ : J = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module Γ(P, W.1) L) (_ : Module (AdicCompletion J Γ(P, W.1)) L)
      (_ : IsScalarTower Γ(P, W.1) (AdicCompletion J Γ(P, W.1)) L) (_ : Module.Finite (AdicCompletion J Γ(P, W.1)) L)
      (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1),
      (∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x) ∧
      (∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0) ∧
      (∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n) ∧
      (∀ n : ℕ, Function.Surjective (pr n)) ∧
      (∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L)) ∧
      IsAdicComplete (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) (AdicCompletion J Γ(P, W.1)) ∧
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (CommRingCat.of (AdicCompletion J Γ(P, W.1)))) (_ : IsProper sY) (t : Y ⟶ V'),
      IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1)))) ≫ W.2.fromSpec) ∧
      (∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1)) ∧
      ∃ (G : OModulePresheaf sY) (ε : ∀ U : Y.Opens, L →ₗ[(AdicCompletion J Γ(P, W.1))] G.obj U)
        (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x) ∧
        (∀ U : Y.affineOpens,
          letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
          ∃ β : Γ(Y, U.1) ⊗[(AdicCompletion J Γ(P, W.1))] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
          (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y) ∧
        (∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
          (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
          (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          (φ' n).app V (θ (n + 1) V h y) = θ n V h y) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
          θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule (AdicCompletion J Γ(P, W.1)) (G.obj (t ⁻¹ᵁ V.1)))) := by
  classical
  have hIfg : I.FG := (isNoetherianRing_iff_ideal_fg A).mp inferInstance I
  have hJfg : J.FG := by rw [hJ]; exact hIfg.map _

  let tB : ∀ n : ℕ, (F (n + 1)).obj W.1 →ₗ[Γ(P, W.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (φ n).app W x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W a x }
  have htB : ∀ (n : ℕ) (x : (F (n + 1)).obj W.1), tB n x = (φ n).app W x := fun n x => rfl
  have htBs : ∀ n : ℕ, Function.Surjective (tB n) := fun n => hφs n W

  have htBk : ∀ n : ℕ, LinearMap.ker (tB n) = J ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) ((F (n + 1)).obj W.1)) := by
    intro n
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1
    have hsc : ∀ x : (F (n + 1)).obj W.1,
        x ∈ J ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) ((F (n + 1)).obj W.1)) ↔
          x ∈ I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj W.1)) := by
      intro x
      rw [hJ, ← Ideal.map_pow,
        show (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) = algebraMap A Γ(P, W.1) from rfl,
        ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    ext x
    rw [LinearMap.mem_ker, htB, hsc, ← LinearMap.mem_ker, hφk]
  have hfin0 : Module.Finite Γ(P, W.1) ((F 0).obj W.1) := hFc 0 W
  obtain ⟨L, i1, i2, i3, i4, i5, pr, hprc, hpri, hprt, hprs, hprk⟩ :=
    AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
      J hJfg (fun n => (F n).obj W.1) tB htBs htBk hfin0
  have hprc' : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x :=
    fun n x => (htB n _).symm.trans (hprc n x)
  have hprt' : ∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) →
      ∃ x : L, ∀ n : ℕ, pr n x = m n := fun m hm => hprt m fun n => (htB n _).trans (hm n)
  have hprk' : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L) := by
    intro n; rw [hprk n, hJ]
  have hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) (AdicCompletion J Γ(P, W.1)) := by
    rw [← Ideal.map_map, ← hJ]
    exact AdicCompletion.isAdicComplete_map_algebraMap_of_fg J hJfg
  obtain ⟨Y, sY, hsY, t, hY, hta, G, ε, θ, hrest⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W (AdicCompletion J Γ(P, W.1)) L pr hprc' hpri hprs hprk'
  exact ⟨L, i1, i2, i3, i4, i5, pr, hprc', hpri, hprt', hprs, hprk', hRc, Y, sY, hsY, t, hY, hta, G, ε, θ, hrest⟩

end W_ASM

open W_ASM in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x) :
    ∀ W₀ : P.affineOpens, ∃ N : ℕ, ∀ W : P.affineOpens, W.1 ≤ W₀.1 →
        (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
          (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∃ m : ∀ n, (F n).obj W.1,
              (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
        (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
          (∀ n, (v n).app W (m n) = 0) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∀ n, a • m n = 0) := by
  classical
  intro W₀
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI hB₀ : IsNoetherianRing Γ(P, W₀.1) := IsLocallyNoetherian.component_noetherian W₀

  obtain ⟨L₀, _, _, _, _, _, pr₀, hprc₀, hpri₀, hprt₀, hprs₀, hprk₀, hRc₀, Y₀, sY₀, hsY₀, t₀, hY₀, hta₀, G₀, ε₀, θ₀,
      hGc₀, hGq₀, hεr₀, hεβ₀, hθs₀, hθr₀, hθφ₀, hθε₀, hθo₀, hθk₀⟩ :=
    exists_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W₀ (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) rfl
  haveI := hsY₀
  haveI : IsNoetherianRing (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  obtain ⟨N, hk₀, hc₀⟩ :=
    torsion_of_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W₀ (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) L₀ pr₀ hprc₀ hpri₀ hprs₀ hprk₀
      hRc₀ sY₀ t₀ hY₀ hta₀ G₀ hGc₀ hGq₀ ε₀ hεr₀ hεβ₀ θ₀ hθs₀ hθr₀ hθφ₀ hθε₀ hθo₀ hθk₀
  refine ⟨N, fun W hW => ?_⟩
  haveI hB : IsNoetherianRing Γ(P, W.1) := IsLocallyNoetherian.component_noetherian W

  letI algW : Algebra Γ(P, W₀.1) Γ(P, W.1) := (P.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have hresLE : (𝟙 P : P ⟶ P).appLE W₀.1 W.1 hW = P.presheaf.map (homOfLE hW).op := by
    rw [Scheme.Hom.appLE]
    have hid : (𝟙 P : P ⟶ P).app W₀.1 = 𝟙 _ := rfl
    rw [hid]
    exact Category.id_comp _
  haveI : Module.Flat Γ(P, W₀.1) Γ(P, W.1) := by
    have h := HasRingHomProperty.appLE @Flat (𝟙 P) inferInstance W₀ W hW
    rwa [hresLE] at h
  haveI : Algebra.FiniteType Γ(P, W₀.1) Γ(P, W.1) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (𝟙 P) inferInstance W₀ W hW
    rwa [hresLE] at h

  have hJ : (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1)) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) := by
    rw [Ideal.map_map]
    congr 1
    change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top) ≫ P.presheaf.map (homOfLE hW).op).hom
      = _
    rw [Category.assoc, Scheme.Hom.appLE_map]
  obtain ⟨L, _, _, _, _, _, pr, hprc, hpri, hprt, hprs, hprk, hRc, Y, sY, hsY, t, hY, hta, G, ε, θ,
      hGc, hGq, hεr, hεβ, hθs, hθr, hθφ, hθε, hθo, hθk⟩ :=
    exists_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) hJ
  haveI := hsY
  haveI : IsNoetherianRing (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _

  obtain ⟨f, hf, hflat⟩ :=
    AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
      (B₀ := Γ(P, W₀.1)) (B := Γ(P, W.1)) (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom)
  letI algR : Algebra (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1))
      (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) := f.toAlgebra
  haveI : Module.Flat (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1))
      (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) := hflat

  letI modn : ∀ n : ℕ, Module Γ(P, W₀.1) ((F n).obj W.1) := fun n =>
    Module.compHom ((F n).obj W.1) (algebraMap Γ(P, W₀.1) Γ(P, W.1))
  haveI towern : ∀ n : ℕ, IsScalarTower Γ(P, W₀.1) Γ(P, W.1) ((F n).obj W.1) := fun n =>
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  let κ : ∀ n : ℕ, (F n).obj W₀.1 →ₗ[Γ(P, W₀.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (F n).res hW x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        rw [(F n).res_smul hW a x]
        rfl }
  have hκ : ∀ n : ℕ, IsBaseChange Γ(P, W.1) (κ n) := by
    intro n
    obtain ⟨β, hβ1⟩ :=
      AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
        (F n) (hFq n) W₀ W hW
    exact IsBaseChange.of_equiv β fun x => hβ1 x

  let tB₀ : ∀ n : ℕ, (F (n + 1)).obj W₀.1 →ₗ[Γ(P, W₀.1)] (F n).obj W₀.1 := fun n =>
    { toFun := fun x => (φ n).app W₀ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W₀ a x }
  let tB : ∀ n : ℕ, (F (n + 1)).obj W.1 →ₗ[Γ(P, W.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (φ n).app W x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W a x }
  have hκt : ∀ (n : ℕ) (x : (F (n + 1)).obj W₀.1), tB n (κ (n + 1) x) = κ n (tB₀ n x) := by
    intro n x
    exact (φ n).naturality_apply (U := W) (U' := W₀) hW x

  have hprk' : ∀ n : ℕ, LinearMap.ker (pr n)
      = ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L) := by
    intro n; rw [hprk n, hJ]
  obtain ⟨e, heb, he⟩ :=
    AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
      (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) ((isNoetherianRing_iff_ideal_fg A).mp inferInstance I |>.map _)
      (fun n => (F n).obj W₀.1) tB₀ (fun n => (F n).obj W.1) tB κ hκ hκt
      L₀ pr₀ (fun n x => hprc₀ n x) hpri₀ (fun m hm => hprt₀ m hm) hprs₀ hprk₀
      L pr (fun n x => hprc n x) hpri (fun m hm => hprt m hm) hprs hprk' f hf

  obtain ⟨hk, hc⟩ :=
    AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη
      W₀ (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) L₀ pr₀ hprc₀ hpri₀ hprs₀ hprk₀ sY₀ t₀ hY₀ hta₀ G₀ hGc₀ hGq₀ ε₀ hεr₀ hεβ₀
      W (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) L pr hprc hpri hprs hprk
        sY t hY hta G hGc hGq ε hεr hεβ
      hW (fun b => hf b) e heb (fun n x₀ => he n x₀) N hk₀ hc₀
  exact threads_of_torsion I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W _ L pr hprc hpri hprs hprk hprt hRc sY t hY hta G hGc hGq ε hεr hεβ
    θ hθs hθr hθφ hθε hθo hθk N hk hc

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x) :
    ∀ W₀ : P.affineOpens, ∃ N : ℕ, ∀ W : P.affineOpens, W.1 ≤ W₀.1 →
        (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
          (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∃ m : ∀ n, (F n).obj W.1,
              (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
        (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
          (∀ n, (v n).app W (m n) = 0) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∀ n, a • m n = 0) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~ChowDatum~ChowDatumProj TopologicalSpace"
open scoped TensorProduct

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (G' : OModulePresheaf ((g ≫ i) ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward (g ≫ i) q K' G') (Ps k))
    (hψPs : ∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ψP k).app W))
    (hψPk : ∀ (k : ℕ) (W : P.affineOpens),
      LinearMap.ker ((ψP k).app W)
        = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward (g ≫ i) q K' G').obj W.1)))
    (hψPc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (ψP (k + 1)).app W = (ψP k).app W)
    (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hνc : ∀ (k : ℕ) (W : P.affineOpens),
      ((φ' k).cechPushforward (g ≫ i) q K').app W ∘ₗ (ν (k + 1)).app W = (ν k).app W ∘ₗ (π k).app W)
    (hνψP : ∀ (k : ℕ) (W : P.affineOpens),
      (ν k).app W ∘ₗ (ψP k).app W = ((ψ' k).cechPushforward (g ≫ i) q K').app W)
    (hνi : ∀ (W : P.affineOpens) (k : ℕ), ∃ c : ℕ,
      LinearMap.ker ((ν (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj W.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (u (k + 1)).app W = (u k).app W ∘ₗ (φ k).app W)
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by
  have hloc := AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη
  have hunif := AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη hloc
  exact AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu hunif

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory TopologicalSpace open _root_.AlgebraicGeometry hiding ChowDatum ChowDatumProj
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (G' : OModulePresheaf ((g ≫ i) ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward (g ≫ i) q K' G') (Ps k))
    (hψPs : ∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ψP k).app W))
    (hψPk : ∀ (k : ℕ) (W : P.affineOpens),
      LinearMap.ker ((ψP k).app W)
        = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward (g ≫ i) q K' G').obj W.1)))
    (hψPc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (ψP (k + 1)).app W = (ψP k).app W)
    (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hνc : ∀ (k : ℕ) (W : P.affineOpens),
      ((φ' k).cechPushforward (g ≫ i) q K').app W ∘ₗ (ν (k + 1)).app W = (ν k).app W ∘ₗ (π k).app W)
    (hνψP : ∀ (k : ℕ) (W : P.affineOpens),
      (ν k).app W ∘ₗ (ψP k).app W = ((ψ' k).cechPushforward (g ≫ i) q K').app W)
    (hνi : ∀ (W : P.affineOpens) (k : ℕ), ∃ c : ℕ,
      LinearMap.ker ((ν (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj W.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (u (k + 1)).app W = (u k).app W ∘ₗ (φ k).app W)
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.ι_image_le Scheme.Opens.topIso_inv Surjective IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact LocallyOfFiniteType Spec Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE IsAffineOpen.isoSpec_hom_appTop IsSeparated IsLocallyNoetherian.component_noetherian Scheme.Opens.mem_basicOpen_toScheme IsAffineOpen IsNoetherian Scheme.Hom.preimage_iSup Scheme.Opens Scheme.Hom.coe_image Scheme.Hom.appLE_map Scheme.Opens.opensRange_ι morphismRestrict_appLE Scheme.ΓSpecIso Scheme.OrderedAffineCover Scheme.OrderedAffineCover.inter Scheme.OrderedAffineCover.face_val Scheme.OrderedAffineCover.inter_le OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.OrderedAffineCover.fiberAffineOpen OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_refl_apply res_res cochain d d_apply H0 IsCoherent IsQuasicoherent res res_smul res_refl isScalarTower module obj res_comp addCommGroup moduleSections Hom exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper"
namespace Rebase
p2m_open "AlgebraicGeometry.OModulePresheaf~pow~ker AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P) (W : P.affineOpens)

abbrev pW : V'.Opens := p ⁻¹ᵁ (W : P.Opens)

def qW : ((pW p W) : Scheme.{u}) ⟶ Spec (CommRingCat.of Γ(P, (W : P.Opens))) :=
  (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom

theorem qW_def : qW p W = (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom := rfl

abbrev Bch : Type u := Γ(P, (W : P.Opens))

abbrev ΓW (O : ((pW p W) : Scheme.{u}).Opens) : Type u := Γ(((pW p W) : Scheme.{u}), O)

scoped instance isProper_qW [IsProper p] : IsProper (qW p W) := by
  unfold qW; infer_instance

theorem isNoetherian_of_isProper [IsNoetherianRing A] [IsProper q] : IsNoetherian P := by
  haveI : LocallyOfFiniteType q := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  exact {}

theorem isNoetherianRing_chart [IsNoetherianRing A] [IsProper q] : IsNoetherianRing Γ(P, (W : P.Opens)) := by
  haveI := isNoetherian_of_isProper q
  exact IsLocallyNoetherian.component_noetherian W

theorem ΓSpecIso_inv_qW_app_map (O : ((pW p W) : Scheme.{u}).Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).app ⊤ ≫
        ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := by
  rw [show (qW p W).app ⊤ ≫ ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      W.2.isoSpec.hom.appTop ≫ (p ∣_ (W : P.Opens)).appLE ⊤ O le_top from
      Scheme.Hom.comp_appLE _ _ ⊤ O le_top,
    IsAffineOpen.isoSpec_hom_appTop,
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv = (Scheme.ΓSpecIso Γ(P, (W : P.Opens))).inv
      from rfl,
    Category.assoc (obj := CommRingCat), Iso.inv_hom_id_assoc, morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.map_appLE]

theorem algebraMap_qW_eq (O : ((pW p W) : Scheme.{u}).Opens) (b : Γ(P, (W : P.Opens))) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
     algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) =
      (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b := by
  have h := ΓSpecIso_inv_qW_app_map p W O
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) b

theorem map_algebraMap_qW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (b : Γ(P, (W : P.Opens))) :
    (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O'
         algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O') b) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
       algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) := by
  show (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O' le_top).hom b) =
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O le_top).hom b
  rw [← Scheme.Hom.appLE_map (qW p W) (le_top : O' ≤ (qW p W) ⁻¹ᵁ ⊤) (homOfLE h).op]
  rfl

theorem appLE_algebraMap_chart (O : ((pW p W) : Scheme.{u}).Opens) (a : A) :
    (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
         algebraMap A Γ(P, (W : P.Opens)) a) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
       algebraMap A Γ(V', (pW p W).ι ''ᵁ O) a) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (W : P.Opens) le_top ≫
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p ≫ q).appLE ⊤ ((pW p W).ι ''ᵁ O) le_top).hom a
  rw [Scheme.Hom.appLE_comp_appLE]

section Datum

variable (G : OModulePresheaf (p ≫ q))

abbrev modSec (O : ((pW p W) : Scheme.{u}).Opens) : Module (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  G.moduleSections ((pW p W).ι ''ᵁ O)

attribute [local instance] modSec

abbrev modB (O : ((pW p W) : Scheme.{u}).Opens) : Module (Bch W) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  Module.compHom (G.obj ((pW p W).ι ''ᵁ O)) (algebraMap (Bch W) (ΓW p W O))

attribute [local instance] modB

theorem modB_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O; algebraMap (Bch W) (ΓW p W O) b) • x :=
  rfl

theorem modB_smul_def' (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b • x := by
  rw [modB_smul_def, algebraMap_qW_eq]

theorem isScalarTower_modB (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
    IsScalarTower (Bch W) (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem res_smul_piece {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    G.res ((pW p W).ι.image_mono h) (a • x) =
      (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • G.res ((pW p W).ι.image_mono h) x :=
  G.res_smul _ a x

def resW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') :
    G.obj ((pW p W).ι ''ᵁ O') →ₗ[Bch W] G.obj ((pW p W).ι ''ᵁ O) :=
  { toFun := G.res ((pW p W).ι.image_mono h)
    map_add' := map_add _
    map_smul' := fun b x => by
      rw [RingHom.id_apply, modB_smul_def, modB_smul_def, res_smul_piece q p W G h, map_algebraMap_qW] }

theorem resW_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h x = G.res ((pW p W).ι.image_mono h) x := rfl

theorem resW_smul {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h (a • x) = (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • resW q p W G h x :=
  G.res_smul _ a x

theorem resW_refl (O : ((pW p W) : Scheme.{u}).Opens) : resW q p W G (le_refl O) = LinearMap.id :=
  LinearMap.ext fun x => G.res_refl_apply _ x

theorem resW_comp {O O' O'' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (h' : O' ≤ O'') :
    resW q p W G (h.trans h') = resW q p W G h ∘ₗ resW q p W G h' :=
  LinearMap.ext fun x => (G.res_res _ _ x).symm

def GW : OModulePresheaf (qW p W) where
  obj O := G.obj ((pW p W).ι ''ᵁ O)
  addCommGroup _ := G.addCommGroup _
  module O := modB q p W G O
  moduleSections O := modSec q p W G O
  isScalarTower O := isScalarTower_modB q p W G O
  res h := resW q p W G h
  res_smul h a x := resW_smul q p W G h a x
  res_refl O := resW_refl q p W G O
  res_comp h h' := resW_comp q p W G h h'

theorem GW_obj (O : ((pW p W) : Scheme.{u}).Opens) : (GW q p W G).obj O = G.obj ((pW p W).ι ''ᵁ O) := rfl

theorem GW_res_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : (GW q p W G).obj O') :
    (GW q p W G).res h x = G.res ((pW p W).ι.image_mono h) (show G.obj ((pW p W).ι ''ᵁ O') from x) := rfl

theorem GW_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : (GW q p W G).obj O) :
    b • x = (show (GW q p W G).obj O from
        (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b •
          (show G.obj ((pW p W).ι ''ᵁ O) from x)) :=
  modB_smul_def' q p W G O b x

abbrev modA (O : ((pW p W) : Scheme.{u}).Opens) : Module A ((GW q p W G).obj O) := G.module ((pW p W).ι ''ᵁ O)

attribute [local instance] modA

theorem algebraMap_smul_GW (O : ((pW p W) : Scheme.{u}).Opens) (a : A) (x : (GW q p W G).obj O) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     algebraMap A (Bch W) a • x) = a • x := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
  rw [GW_smul_def, appLE_algebraMap_chart]
  exact algebraMap_smul Γ(V', (pW p W).ι ''ᵁ O) a (show G.obj ((pW p W).ι ''ᵁ O) from x)

theorem isScalarTower_GW (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    IsScalarTower A (Bch W) ((GW q p W G).obj O) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  IsScalarTower.of_algebraMap_smul fun a x => algebraMap_smul_GW q p W G O a x

end Datum

section Cover

variable (K' : V'.OrderedAffineCover)

def KW [IsSeparated q] : Scheme.OrderedAffineCover ((pW p W) : Scheme.{u}) where
  ι := K'.ι
  U i := (pW p W).ι ⁻¹ᵁ K'.U i
  isAffineOpen i := by
    rw [← (pW p W).ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm]
    exact Scheme.OrderedAffineCover.fiberAffineOpen p q (K'.isAffineOpen i) W.2
  iSup_eq_top := by
    rw [← Scheme.Hom.preimage_iSup, K'.iSup_eq_top]
    rfl

theorem KW_ι [IsSeparated q] : (KW q p W K').ι = K'.ι := rfl

theorem KW_U [IsSeparated q] (i : K'.ι) : (KW q p W K').U i = (pW p W).ι ⁻¹ᵁ K'.U i := rfl

theorem image_KW_U [IsSeparated q] (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').U i = K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens) := by
  rw [KW_U, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

end Cover

section Transfer

variable (G : OModulePresheaf (p ≫ q))

theorem presheaf_res_res {O₁ O₂ O₃ : V'.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V', O₃)) :
    (V'.presheaf.map (homOfLE h12).op).hom ((V'.presheaf.map (homOfLE h23).op).hom x) =
      (V'.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V'.presheaf.map_comp]; rfl

theorem ι_image_basicOpen_piece (O : ((pW p W) : Scheme.{u}).Opens) (r : ΓW p W O) :
    (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen r) = V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O) from r) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Scheme.Opens.mem_basicOpen_toScheme.1 hy
  · intro hx
    have hxW : x ∈ (pW p W : V'.Opens) :=
      Scheme.Opens.ι_image_le _ _ (V'.basicOpen_le (show Γ(V', (pW p W).ι ''ᵁ O) from r) hx)
    exact ⟨⟨x, hxW⟩, Scheme.Opens.mem_basicOpen_toScheme.2 hx, rfl⟩

theorem isCoherent_GW (hc : G.IsCoherent) : (GW q p W G).IsCoherent := fun O =>
  hc ⟨(pW p W).ι ''ᵁ O.1, O.2.image_of_isOpenImmersion _⟩

theorem isQuasicoherent_GW (hqc : G.IsQuasicoherent) : (GW q p W G).IsQuasicoherent := by
  intro O f
  have hO' : IsAffineOpen ((pW p W).ι ''ᵁ O.1) := O.2.image_of_isOpenImmersion _
  obtain ⟨h1, h2⟩ := hqc ⟨(pW p W).ι ''ᵁ O.1, hO'⟩ (show Γ(V', (pW p W).ι ''ᵁ O.1) from f)
  have e := ι_image_basicOpen_piece p W O.1 f

  have hle₁ : (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen f) ≤ (pW p W).ι ''ᵁ O.1 :=
    (pW p W).ι.image_mono (((pW p W) : Scheme.{u}).basicOpen_le f)
  have hle₂ : V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O.1) from f) ≤ (pW p W).ι ''ᵁ O.1 := V'.basicOpen_le _
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 (G.res e.ge x)
    refine ⟨n, y, ?_⟩
    have hy' := congrArg (G.res e.le) hy
    rw [G.res_res, G.res_smul, G.res_res, presheaf_res_res] at hy'
    rw [GW_res_apply]
    refine (hy'.trans ?_)
    congr 1
    exact G.res_refl_apply _ x
  · intro y hy0
    apply h2 y
    show G.res hle₂ y = 0
    have : G.res hle₂ y = G.res e.ge (G.res hle₁ y) := (G.res_res _ _ y).symm
    rw [this]
    exact (congrArg (G.res e.ge) hy0).trans (map_zero _)

end Transfer

section Powers

attribute [local instance] modSec modB modA

theorem mem_smul_top_pi_iff {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (I : Ideal R) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule R (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  constructor
  · intro hx i
    have h := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := M) i) hx
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h := Submodule.mem_map_of_mem (f := LinearMap.single R M i) (hx i)
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h

theorem smul_top_mem_map {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_map_smul_top_iff {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (x : M) :
    x ∈ I.map (algebraMap R S) • (⊤ : Submodule S M) ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

variable (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover) (I : Ideal A)

theorem cochain_mem_pow_smul_top_iff [IsSeparated q] (n m : ℕ)
    (x : (GW q p W G).cochain (KW q p W K') n) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     x ∈ (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') n))) ↔
      ∀ s, (x s : G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s)) ∈
        I ^ m • (⊤ : Submodule A (G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s))) := by
  classical
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  rw [← Ideal.map_pow, mem_smul_top_pi_iff]
  refine forall_congr' fun s => ?_
  haveI := isScalarTower_GW q p W G ((KW q p W K').inter s)
  exact mem_map_smul_top_iff (I ^ m) (x s)

end Powers

section Bridge0

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

def σ (i : K'.ι) : (KW q p W K').Idx 0 := ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by omega)⟩

@[scoped simp] theorem σ_val (i : K'.ι) (k : Fin 1) : (σ q p W K' i).1 k = i := rfl

theorem inter_σ (i : K'.ι) : (KW q p W K').inter (σ q p W K' i) = (KW q p W K').U i := by
  simp only [Scheme.OrderedAffineCover.inter, σ_val]
  exact iInf_const

theorem image_inter_σ (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i) = (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [inter_σ, image_KW_U]

theorem image_inter_le {b : ℕ} (s : (KW q p W K').Idx b) (k : Fin (b + 1)) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 k) ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [← image_KW_U q p W K' (s.1 k)]
  exact (pW p W).ι.image_mono (Scheme.OrderedAffineCover.inter_le _ s k)

theorem image_inf (O₁ O₂ : ((pW p W) : Scheme.{u}).Opens) :
    (pW p W).ι ''ᵁ (O₁ ⊓ O₂) = (pW p W).ι ''ᵁ O₁ ⊓ (pW p W).ι ''ᵁ O₂ := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_inf]
  exact Set.image_inter (pW p W).ι.isOpenEmbedding.injective

theorem chW_inf_le_image_inter (s : (KW q p W K').Idx 1) :
    (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤ (pW p W).ι ''ᵁ (KW q p W K').inter s := by
  rw [← image_KW_U q p W K' (s.1 0), ← image_KW_U q p W K' (s.1 1), ← image_inf]
  refine (pW p W).ι.image_mono (le_iInf fun k => ?_)
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

theorem image_inter_le_inf (s : (KW q p W K').Idx 1) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) :=
  le_inf (image_inter_le q p W K' s 0) (image_inter_le q p W K' s 1)

def e0 (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) : G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) :=
  G.res (image_inter_σ q p W K' i).ge
    (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i))

theorem e0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' x i = G.res (image_inter_σ q p W K' i).ge
      (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i)) := rfl

theorem e0_add (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x + y) = e0 q p W G K' x + e0 q p W G K' y :=
  funext fun _ => map_add (G.res _) _ _

theorem e0_zero : e0 q p W G K' (0 : (GW q p W G).cochain (KW q p W K') 0) = 0 :=
  funext fun _ => map_zero (G.res _)

theorem e0_neg (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (-x) = -e0 q p W G K' x :=
  funext fun _ => map_neg (G.res _) _

theorem e0_sub (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x - y) = e0 q p W G K' x - e0 q p W G K' y :=
  funext fun _ => map_sub (G.res _) _ _

def e0Hom : (GW q p W G).cochain (KW q p W K') 0 →+ (∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) where
  toFun := e0 q p W G K'
  map_zero' := e0_zero q p W G K'
  map_add' := e0_add q p W G K'

@[scoped simp] theorem e0Hom_apply (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0Hom q p W G K' x = e0 q p W G K' x := rfl

theorem e0_smulB (b : Bch W) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (b • x) i =
      (p.appLE (W : P.Opens) ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right).hom b • e0 q p W G K' x i := by
  rw [e0_apply, e0_apply, Pi.smul_apply, GW_smul_def]
  erw [G.res_smul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem e0_smulA (a : A) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (fun s => (letI := modA q p W G ((KW q p W K').inter s); a • x s)) i =
      a • e0 q p W G K' x i :=
  LinearMap.map_smul (G.res _) a _

def e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : (GW q p W G).cochain (KW q p W K') 0 :=
  fun s => show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s) from
    G.res (image_inter_le q p W K' s 0) (y (s.1 0))

theorem e0_e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : e0 q p W G K' (e0inv q p W G K' y) = y := by
  funext i
  show G.res _ (G.res _ (y i)) = y i
  rw [G.res_res]
  exact G.res_refl_apply _ _

theorem e0_surjective : Function.Surjective (e0 q p W G K') :=
  fun y => ⟨e0inv q p W G K' y, e0_e0inv q p W G K' y⟩

theorem res_congr_idx (x : (GW q p W G).cochain (KW q p W K') 0) {t t' : (KW q p W K').Idx 0} (h : t = t')
    {O : V'.Opens} (h1 : O ≤ (pW p W).ι ''ᵁ (KW q p W K').inter t) :
    G.res h1 (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t) from x t) =
      G.res (h ▸ h1) (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t') from x t') := by
  subst h; rfl

theorem face_zero_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 0 = σ q p W K' (s.1 1) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem face_one_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 1 = σ q p W K' (s.1 0) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem d0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (s : (KW q p W K').Idx 1) :
    (GW q p W G).d (KW q p W K') 0 x s =
      (GW q p W G).res ((KW q p W K').inter_le_inter_face s 0) (x ((KW q p W K').face s 0)) -
        (GW q p W G).res ((KW q p W K').inter_le_inter_face s 1) (x ((KW q p W K').face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]

def σ₂ {i j : K'.ι} (hij : i < j) : (KW q p W K').Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exact hij⟩

theorem σ₂_fst {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 0 = i := rfl
theorem σ₂_snd {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 1 = j := rfl

theorem d0_eq_zero_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    (GW q p W G).d (KW q p W K') 0 x = 0 ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  constructor
  · intro hd i j
    have key : ∀ s : (KW q p W K').Idx 1,
        G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
            (e0 q p W G K' x (s.1 0))
          = G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
            (e0 q p W G K' x (s.1 1)) := by
      intro s
      have hs := congrFun hd s
      rw [Pi.zero_apply, d0_apply, sub_eq_zero] at hs
      rw [GW_res_apply, GW_res_apply] at hs
      rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)] at hs
      rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)] at hs
      have hs' := congrArg (G.res (chW_inf_le_image_inter q p W K' s)) hs
      rw [G.res_res, G.res_res] at hs'
      rw [e0_apply, e0_apply, G.res_res, G.res_res]
      exact hs'.symm
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key (σ₂ q p W K' hij)
    · rfl
    · have hk : G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
              (e0 q p W G K' x j)
            = G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x i) := key (σ₂ q p W K' hji)
      have h := congrArg (G.res (le_inf inf_le_right inf_le_left :
          (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤
            (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) hk
      rw [G.res_res, G.res_res] at h
      exact h.symm
  · intro h
    funext s
    have hs := congrArg (G.res (image_inter_le_inf q p W K' s)) (h (s.1 0) (s.1 1))
    rw [e0_apply, e0_apply, G.res_res, G.res_res, G.res_res, G.res_res] at hs
    rw [Pi.zero_apply, d0_apply, sub_eq_zero]
    rw [GW_res_apply, GW_res_apply]
    rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)]
    rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)]
    exact hs.symm

theorem mem_H0_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    x ∈ (GW q p W G).H0 (KW q p W K') ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  rw [LinearMap.mem_ker, d0_eq_zero_iff]

end Bridge0

section Deg1

attribute [local instance] modSec modB modA

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

theorem d0_apply_eq_neg_res (x : (GW q p W G).cochain (KW q p W K') 0) (s : (KW q p W K').Idx 1) :
    ((GW q p W G).d (KW q p W K') 0 x s : G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s)) =
      - G.res (image_inter_le_inf q p W K' s)
          (G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
              (e0 q p W G K' x (s.1 0)) -
            G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x (s.1 1))) := by
  rw [map_sub, neg_sub, e0_apply, e0_apply]
  simp only [G.res_res]
  rw [d0_apply, GW_res_apply, GW_res_apply,
    res_congr_idx q p W G K' x (face_zero_eq q p W K' s), res_congr_idx q p W G K' x (face_one_eq q p W K' s)]

variable (I : Ideal A)

theorem d0_mem_pow_smul_top_of_forall (m : ℕ) (x : (GW q p W G).cochain (KW q p W K') 0)
    (h : ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
          - G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x j)
        ∈ I ^ m • (⊤ : Submodule A (G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)))))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    (GW q p W G).d (KW q p W K') 0 x ∈
      (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 1)) := by
  rw [cochain_mem_pow_smul_top_iff]
  intro s
  rw [d0_apply_eq_neg_res]
  exact Submodule.neg_mem _ (smul_top_mem_map (I ^ m) (G.res (image_inter_le_inf q p W K' s)) (h (s.1 0) (s.1 1)))

theorem e0_mem_pow_smul_top (m : ℕ) (x : (GW q p W G).cochain (KW q p W K') 0)
    (hx : letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
      x ∈ (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 0)))
    (i : K'.ι) :
    e0 q p W G K' x i ∈ I ^ m • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) := by
  rw [cochain_mem_pow_smul_top_iff] at hx
  rw [e0_apply]
  exact smul_top_mem_map (I ^ m) (G.res _) (hx (σ q p W K' i))

theorem e0inv_mem_pow_smul_top (m : ℕ) (y : ∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))
    (hy : ∀ i, y i ∈ I ^ m • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    e0inv q p W G K' y ∈
      (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 0)) := by
  rw [cochain_mem_pow_smul_top_iff]
  intro s
  exact smul_top_mem_map (I ^ m) (G.res (image_inter_le q p W K' s 0)) (hy (s.1 0))

end Deg1

end AlgebraicGeometry.OModulePresheaf.Rebase
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf.Rebase"
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf.Rebase"

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
          = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) →
      (∀ i : K'.ι, a i ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))))) →
      ∃ (m : ℕ) (r : Fin m → A) (b : Fin m → ∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ l, r l ∈ I ^ n) ∧
        (∀ (l : Fin m) (i j : K'.ι),
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (b l i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (b l j)) ∧
        a = ∑ l, r l • b l := by
  classical
  letI instAlg := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  haveI : IsNoetherianRing (OModulePresheaf.Rebase.Bch W) := OModulePresheaf.Rebase.isNoetherianRing_chart q W
  obtain ⟨c, hcS⟩ := AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
    (I.map (algebraMap A (OModulePresheaf.Rebase.Bch W))) (OModulePresheaf.Rebase.qW p W)
    (OModulePresheaf.Rebase.GW q p W G) (OModulePresheaf.Rebase.isCoherent_GW q p W G hc)
    (OModulePresheaf.Rebase.isQuasicoherent_GW q p W G hqc) (OModulePresheaf.Rebase.KW q p W K') n
  refine ⟨c, fun a hcoc hpow => ?_⟩

  letI instA : ∀ s : (OModulePresheaf.Rebase.KW q p W K').Idx 0,
      Module A ((OModulePresheaf.Rebase.GW q p W G).obj ((OModulePresheaf.Rebase.KW q p W K').inter s)) :=
    fun s => OModulePresheaf.Rebase.modA q p W G _
  haveI : ∀ s : (OModulePresheaf.Rebase.KW q p W K').Idx 0, IsScalarTower A (OModulePresheaf.Rebase.Bch W)
      ((OModulePresheaf.Rebase.GW q p W G).obj ((OModulePresheaf.Rebase.KW q p W K').inter s)) :=
    fun s => OModulePresheaf.Rebase.isScalarTower_GW q p W G _
  set x := OModulePresheaf.Rebase.e0inv q p W G K' a with hxdef
  have hx : OModulePresheaf.Rebase.e0 q p W G K' x = a := OModulePresheaf.Rebase.e0_e0inv q p W G K' a
  have hH0 : x ∈ (OModulePresheaf.Rebase.GW q p W G).H0 (OModulePresheaf.Rebase.KW q p W K') :=
    (OModulePresheaf.Rebase.mem_H0_iff q p W G K' x).2 (by rw [hx]; exact hcoc)
  have hJ := OModulePresheaf.Rebase.e0inv_mem_pow_smul_top q p W G K' I (n + c) a hpow
  have hmem : x ∈ (I.map (algebraMap A (OModulePresheaf.Rebase.Bch W))) ^ n •
      (OModulePresheaf.Rebase.GW q p W G).H0 (OModulePresheaf.Rebase.KW q p W K') :=
    hcS (Submodule.mem_inf.2 ⟨hH0, hJ⟩)

  set H0A := ((OModulePresheaf.Rebase.GW q p W G).H0 (OModulePresheaf.Rebase.KW q p W K')).restrictScalars A
    with hH0A
  have hmemA : x ∈ I ^ n • H0A := by
    rw [hH0A, ← Ideal.smul_restrictScalars, Ideal.map_pow]
    exact hmem
  have hspan : I ^ n • H0A = I ^ n • Submodule.span A (id '' (H0A : Set _)) := by
    rw [Set.image_id, Submodule.span_eq]
  rw [hspan, Submodule.mem_ideal_smul_span_iff_exists_sum'] at hmemA
  obtain ⟨coef, hcoef, hsum⟩ := hmemA

  have e0_smul' : ∀ (r : A) (y : (OModulePresheaf.Rebase.GW q p W G).cochain (OModulePresheaf.Rebase.KW q p W K') 0),
      OModulePresheaf.Rebase.e0 q p W G K' (r • y) = r • OModulePresheaf.Rebase.e0 q p W G K' y :=
    fun r y => funext fun i => OModulePresheaf.Rebase.e0_smulA q p W G K' r y i
  have key : a = ∑ h ∈ coef.support, coef h • OModulePresheaf.Rebase.e0 q p W G K' (h : _) := by
    rw [← hx, ← hsum]
    show OModulePresheaf.Rebase.e0Hom q p W G K' (∑ h ∈ coef.support, coef h • id (h : _)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [OModulePresheaf.Rebase.e0Hom_apply, id, e0_smul']

  set S := coef.support with hS
  let e : Fin S.card ≃ ↥S := S.equivFin.symm
  refine ⟨S.card, fun l => coef (e l), fun l => OModulePresheaf.Rebase.e0 q p W G K' ((e l : ↥S) : _),
    fun l => hcoef _, fun l => (OModulePresheaf.Rebase.mem_H0_iff q p W G K' _).1 (e l).1.2, ?_⟩
  rw [key, ← Finset.sum_coe_sort S]
  exact (Fintype.sum_equiv e _ _ fun l => rfl).symm

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
          = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) →
      (∀ i : K'.ι, a i ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))))) →
      ∃ (m : ℕ) (r : Fin m → A) (b : Fin m → ∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ l, r l ∈ I ^ n) ∧
        (∀ (l : Fin m) (i j : K'.ι),
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (b l i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (b l j)) ∧
        a = ∑ l, r l • b l := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.ι_image_le Scheme.Opens.topIso_inv Surjective IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact LocallyOfFiniteType Spec Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE IsAffineOpen.isoSpec_hom_appTop IsSeparated IsLocallyNoetherian.component_noetherian Scheme.Opens.mem_basicOpen_toScheme IsAffineOpen IsNoetherian Scheme.Hom.preimage_iSup Scheme.Opens Scheme.Hom.coe_image Scheme.Hom.appLE_map Scheme.Opens.opensRange_ι morphismRestrict_appLE Scheme.ΓSpecIso Scheme.OrderedAffineCover Scheme.OrderedAffineCover.inter Scheme.OrderedAffineCover.face_val Scheme.OrderedAffineCover.inter_le OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.OrderedAffineCover.fiberAffineOpen OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_refl_apply res_res cochain d d_apply H0 IsCoherent IsQuasicoherent res res_smul res_refl isScalarTower module obj res_comp addCommGroup moduleSections Hom exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper"
namespace Rebase
p2m_open "AlgebraicGeometry.OModulePresheaf~pow AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P) (W : P.affineOpens)

abbrev pW : V'.Opens := p ⁻¹ᵁ (W : P.Opens)

def qW : ((pW p W) : Scheme.{u}) ⟶ Spec (CommRingCat.of Γ(P, (W : P.Opens))) :=
  (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom

theorem qW_def : qW p W = (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom := rfl

abbrev Bch : Type u := Γ(P, (W : P.Opens))

abbrev ΓW (O : ((pW p W) : Scheme.{u}).Opens) : Type u := Γ(((pW p W) : Scheme.{u}), O)

scoped instance isProper_qW [IsProper p] : IsProper (qW p W) := by
  unfold qW; infer_instance

theorem isNoetherian_of_isProper [IsNoetherianRing A] [IsProper q] : IsNoetherian P := by
  haveI : LocallyOfFiniteType q := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  exact {}

theorem isNoetherianRing_chart [IsNoetherianRing A] [IsProper q] : IsNoetherianRing Γ(P, (W : P.Opens)) := by
  haveI := isNoetherian_of_isProper q
  exact IsLocallyNoetherian.component_noetherian W

theorem ΓSpecIso_inv_qW_app_map (O : ((pW p W) : Scheme.{u}).Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).app ⊤ ≫
        ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := by
  rw [show (qW p W).app ⊤ ≫ ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      W.2.isoSpec.hom.appTop ≫ (p ∣_ (W : P.Opens)).appLE ⊤ O le_top from
      Scheme.Hom.comp_appLE _ _ ⊤ O le_top,
    IsAffineOpen.isoSpec_hom_appTop,
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv = (Scheme.ΓSpecIso Γ(P, (W : P.Opens))).inv
      from rfl,
    Category.assoc (obj := CommRingCat), Iso.inv_hom_id_assoc, morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.map_appLE]

theorem algebraMap_qW_eq (O : ((pW p W) : Scheme.{u}).Opens) (b : Γ(P, (W : P.Opens))) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
     algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) =
      (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b := by
  have h := ΓSpecIso_inv_qW_app_map p W O
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) b

theorem map_algebraMap_qW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (b : Γ(P, (W : P.Opens))) :
    (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O'
         algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O') b) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
       algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) := by
  show (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O' le_top).hom b) =
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O le_top).hom b
  rw [← Scheme.Hom.appLE_map (qW p W) (le_top : O' ≤ (qW p W) ⁻¹ᵁ ⊤) (homOfLE h).op]
  rfl

theorem appLE_algebraMap_chart (O : ((pW p W) : Scheme.{u}).Opens) (a : A) :
    (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
         algebraMap A Γ(P, (W : P.Opens)) a) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
       algebraMap A Γ(V', (pW p W).ι ''ᵁ O) a) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (W : P.Opens) le_top ≫
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p ≫ q).appLE ⊤ ((pW p W).ι ''ᵁ O) le_top).hom a
  rw [Scheme.Hom.appLE_comp_appLE]

section Datum

variable (G : OModulePresheaf (p ≫ q))

abbrev modSec (O : ((pW p W) : Scheme.{u}).Opens) : Module (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  G.moduleSections ((pW p W).ι ''ᵁ O)

attribute [local instance] modSec

abbrev modB (O : ((pW p W) : Scheme.{u}).Opens) : Module (Bch W) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  Module.compHom (G.obj ((pW p W).ι ''ᵁ O)) (algebraMap (Bch W) (ΓW p W O))

attribute [local instance] modB

theorem modB_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O; algebraMap (Bch W) (ΓW p W O) b) • x :=
  rfl

theorem modB_smul_def' (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b • x := by
  rw [modB_smul_def, algebraMap_qW_eq]

theorem isScalarTower_modB (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
    IsScalarTower (Bch W) (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem res_smul_piece {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    G.res ((pW p W).ι.image_mono h) (a • x) =
      (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • G.res ((pW p W).ι.image_mono h) x :=
  G.res_smul _ a x

def resW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') :
    G.obj ((pW p W).ι ''ᵁ O') →ₗ[Bch W] G.obj ((pW p W).ι ''ᵁ O) :=
  { toFun := G.res ((pW p W).ι.image_mono h)
    map_add' := map_add _
    map_smul' := fun b x => by
      rw [RingHom.id_apply, modB_smul_def, modB_smul_def, res_smul_piece q p W G h, map_algebraMap_qW] }

theorem resW_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h x = G.res ((pW p W).ι.image_mono h) x := rfl

theorem resW_smul {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h (a • x) = (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • resW q p W G h x :=
  G.res_smul _ a x

theorem resW_refl (O : ((pW p W) : Scheme.{u}).Opens) : resW q p W G (le_refl O) = LinearMap.id :=
  LinearMap.ext fun x => G.res_refl_apply _ x

theorem resW_comp {O O' O'' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (h' : O' ≤ O'') :
    resW q p W G (h.trans h') = resW q p W G h ∘ₗ resW q p W G h' :=
  LinearMap.ext fun x => (G.res_res _ _ x).symm

def GW : OModulePresheaf (qW p W) where
  obj O := G.obj ((pW p W).ι ''ᵁ O)
  addCommGroup _ := G.addCommGroup _
  module O := modB q p W G O
  moduleSections O := modSec q p W G O
  isScalarTower O := isScalarTower_modB q p W G O
  res h := resW q p W G h
  res_smul h a x := resW_smul q p W G h a x
  res_refl O := resW_refl q p W G O
  res_comp h h' := resW_comp q p W G h h'

theorem GW_obj (O : ((pW p W) : Scheme.{u}).Opens) : (GW q p W G).obj O = G.obj ((pW p W).ι ''ᵁ O) := rfl

theorem GW_res_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : (GW q p W G).obj O') :
    (GW q p W G).res h x = G.res ((pW p W).ι.image_mono h) (show G.obj ((pW p W).ι ''ᵁ O') from x) := rfl

theorem GW_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : (GW q p W G).obj O) :
    b • x = (show (GW q p W G).obj O from
        (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b •
          (show G.obj ((pW p W).ι ''ᵁ O) from x)) :=
  modB_smul_def' q p W G O b x

abbrev modA (O : ((pW p W) : Scheme.{u}).Opens) : Module A ((GW q p W G).obj O) := G.module ((pW p W).ι ''ᵁ O)

attribute [local instance] modA

theorem algebraMap_smul_GW (O : ((pW p W) : Scheme.{u}).Opens) (a : A) (x : (GW q p W G).obj O) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     algebraMap A (Bch W) a • x) = a • x := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
  rw [GW_smul_def, appLE_algebraMap_chart]
  exact algebraMap_smul Γ(V', (pW p W).ι ''ᵁ O) a (show G.obj ((pW p W).ι ''ᵁ O) from x)

theorem isScalarTower_GW (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    IsScalarTower A (Bch W) ((GW q p W G).obj O) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  IsScalarTower.of_algebraMap_smul fun a x => algebraMap_smul_GW q p W G O a x

end Datum

section Cover

variable (K' : V'.OrderedAffineCover)

def KW [IsSeparated q] : Scheme.OrderedAffineCover ((pW p W) : Scheme.{u}) where
  ι := K'.ι
  U i := (pW p W).ι ⁻¹ᵁ K'.U i
  isAffineOpen i := by
    rw [← (pW p W).ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm]
    exact Scheme.OrderedAffineCover.fiberAffineOpen p q (K'.isAffineOpen i) W.2
  iSup_eq_top := by
    rw [← Scheme.Hom.preimage_iSup, K'.iSup_eq_top]
    rfl

theorem KW_ι [IsSeparated q] : (KW q p W K').ι = K'.ι := rfl

theorem KW_U [IsSeparated q] (i : K'.ι) : (KW q p W K').U i = (pW p W).ι ⁻¹ᵁ K'.U i := rfl

theorem image_KW_U [IsSeparated q] (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').U i = K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens) := by
  rw [KW_U, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

end Cover

section Transfer

variable (G : OModulePresheaf (p ≫ q))

theorem presheaf_res_res {O₁ O₂ O₃ : V'.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V', O₃)) :
    (V'.presheaf.map (homOfLE h12).op).hom ((V'.presheaf.map (homOfLE h23).op).hom x) =
      (V'.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V'.presheaf.map_comp]; rfl

theorem ι_image_basicOpen_piece (O : ((pW p W) : Scheme.{u}).Opens) (r : ΓW p W O) :
    (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen r) = V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O) from r) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Scheme.Opens.mem_basicOpen_toScheme.1 hy
  · intro hx
    have hxW : x ∈ (pW p W : V'.Opens) :=
      Scheme.Opens.ι_image_le _ _ (V'.basicOpen_le (show Γ(V', (pW p W).ι ''ᵁ O) from r) hx)
    exact ⟨⟨x, hxW⟩, Scheme.Opens.mem_basicOpen_toScheme.2 hx, rfl⟩

theorem isCoherent_GW (hc : G.IsCoherent) : (GW q p W G).IsCoherent := fun O =>
  hc ⟨(pW p W).ι ''ᵁ O.1, O.2.image_of_isOpenImmersion _⟩

theorem isQuasicoherent_GW (hqc : G.IsQuasicoherent) : (GW q p W G).IsQuasicoherent := by
  intro O f
  have hO' : IsAffineOpen ((pW p W).ι ''ᵁ O.1) := O.2.image_of_isOpenImmersion _
  obtain ⟨h1, h2⟩ := hqc ⟨(pW p W).ι ''ᵁ O.1, hO'⟩ (show Γ(V', (pW p W).ι ''ᵁ O.1) from f)
  have e := ι_image_basicOpen_piece p W O.1 f

  have hle₁ : (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen f) ≤ (pW p W).ι ''ᵁ O.1 :=
    (pW p W).ι.image_mono (((pW p W) : Scheme.{u}).basicOpen_le f)
  have hle₂ : V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O.1) from f) ≤ (pW p W).ι ''ᵁ O.1 := V'.basicOpen_le _
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 (G.res e.ge x)
    refine ⟨n, y, ?_⟩
    have hy' := congrArg (G.res e.le) hy
    rw [G.res_res, G.res_smul, G.res_res, presheaf_res_res] at hy'
    rw [GW_res_apply]
    refine (hy'.trans ?_)
    congr 1
    exact G.res_refl_apply _ x
  · intro y hy0
    apply h2 y
    show G.res hle₂ y = 0
    have : G.res hle₂ y = G.res e.ge (G.res hle₁ y) := (G.res_res _ _ y).symm
    rw [this]
    exact (congrArg (G.res e.ge) hy0).trans (map_zero _)

end Transfer

section Powers

attribute [local instance] modSec modB modA

theorem mem_smul_top_pi_iff {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (I : Ideal R) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule R (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  constructor
  · intro hx i
    have h := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := M) i) hx
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h := Submodule.mem_map_of_mem (f := LinearMap.single R M i) (hx i)
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h

theorem smul_top_mem_map {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_map_smul_top_iff {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (x : M) :
    x ∈ I.map (algebraMap R S) • (⊤ : Submodule S M) ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

variable (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover) (I : Ideal A)

theorem cochain_mem_pow_smul_top_iff [IsSeparated q] (n m : ℕ)
    (x : (GW q p W G).cochain (KW q p W K') n) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     x ∈ (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') n))) ↔
      ∀ s, (x s : G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s)) ∈
        I ^ m • (⊤ : Submodule A (G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s))) := by
  classical
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  rw [← Ideal.map_pow, mem_smul_top_pi_iff]
  refine forall_congr' fun s => ?_
  haveI := isScalarTower_GW q p W G ((KW q p W K').inter s)
  exact mem_map_smul_top_iff (I ^ m) (x s)

end Powers

section Bridge0

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

def σ (i : K'.ι) : (KW q p W K').Idx 0 := ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by omega)⟩

@[scoped simp] theorem σ_val (i : K'.ι) (k : Fin 1) : (σ q p W K' i).1 k = i := rfl

theorem inter_σ (i : K'.ι) : (KW q p W K').inter (σ q p W K' i) = (KW q p W K').U i := by
  simp only [Scheme.OrderedAffineCover.inter, σ_val]
  exact iInf_const

theorem image_inter_σ (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i) = (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [inter_σ, image_KW_U]

theorem image_inter_le {b : ℕ} (s : (KW q p W K').Idx b) (k : Fin (b + 1)) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 k) ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [← image_KW_U q p W K' (s.1 k)]
  exact (pW p W).ι.image_mono (Scheme.OrderedAffineCover.inter_le _ s k)

theorem image_inf (O₁ O₂ : ((pW p W) : Scheme.{u}).Opens) :
    (pW p W).ι ''ᵁ (O₁ ⊓ O₂) = (pW p W).ι ''ᵁ O₁ ⊓ (pW p W).ι ''ᵁ O₂ := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_inf]
  exact Set.image_inter (pW p W).ι.isOpenEmbedding.injective

theorem chW_inf_le_image_inter (s : (KW q p W K').Idx 1) :
    (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤ (pW p W).ι ''ᵁ (KW q p W K').inter s := by
  rw [← image_KW_U q p W K' (s.1 0), ← image_KW_U q p W K' (s.1 1), ← image_inf]
  refine (pW p W).ι.image_mono (le_iInf fun k => ?_)
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

theorem image_inter_le_inf (s : (KW q p W K').Idx 1) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) :=
  le_inf (image_inter_le q p W K' s 0) (image_inter_le q p W K' s 1)

def e0 (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) : G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) :=
  G.res (image_inter_σ q p W K' i).ge
    (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i))

theorem e0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' x i = G.res (image_inter_σ q p W K' i).ge
      (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i)) := rfl

theorem e0_add (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x + y) = e0 q p W G K' x + e0 q p W G K' y :=
  funext fun _ => map_add (G.res _) _ _

theorem e0_zero : e0 q p W G K' (0 : (GW q p W G).cochain (KW q p W K') 0) = 0 :=
  funext fun _ => map_zero (G.res _)

theorem e0_neg (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (-x) = -e0 q p W G K' x :=
  funext fun _ => map_neg (G.res _) _

theorem e0_sub (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x - y) = e0 q p W G K' x - e0 q p W G K' y :=
  funext fun _ => map_sub (G.res _) _ _

def e0Hom : (GW q p W G).cochain (KW q p W K') 0 →+ (∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) where
  toFun := e0 q p W G K'
  map_zero' := e0_zero q p W G K'
  map_add' := e0_add q p W G K'

@[scoped simp] theorem e0Hom_apply (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0Hom q p W G K' x = e0 q p W G K' x := rfl

theorem e0_smulB (b : Bch W) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (b • x) i =
      (p.appLE (W : P.Opens) ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right).hom b • e0 q p W G K' x i := by
  rw [e0_apply, e0_apply, Pi.smul_apply, GW_smul_def]
  erw [G.res_smul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem e0_smulA (a : A) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (fun s => (letI := modA q p W G ((KW q p W K').inter s); a • x s)) i =
      a • e0 q p W G K' x i :=
  LinearMap.map_smul (G.res _) a _

def e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : (GW q p W G).cochain (KW q p W K') 0 :=
  fun s => show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s) from
    G.res (image_inter_le q p W K' s 0) (y (s.1 0))

theorem e0_e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : e0 q p W G K' (e0inv q p W G K' y) = y := by
  funext i
  show G.res _ (G.res _ (y i)) = y i
  rw [G.res_res]
  exact G.res_refl_apply _ _

theorem e0_surjective : Function.Surjective (e0 q p W G K') :=
  fun y => ⟨e0inv q p W G K' y, e0_e0inv q p W G K' y⟩

theorem res_congr_idx (x : (GW q p W G).cochain (KW q p W K') 0) {t t' : (KW q p W K').Idx 0} (h : t = t')
    {O : V'.Opens} (h1 : O ≤ (pW p W).ι ''ᵁ (KW q p W K').inter t) :
    G.res h1 (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t) from x t) =
      G.res (h ▸ h1) (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t') from x t') := by
  subst h; rfl

theorem face_zero_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 0 = σ q p W K' (s.1 1) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem face_one_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 1 = σ q p W K' (s.1 0) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem d0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (s : (KW q p W K').Idx 1) :
    (GW q p W G).d (KW q p W K') 0 x s =
      (GW q p W G).res ((KW q p W K').inter_le_inter_face s 0) (x ((KW q p W K').face s 0)) -
        (GW q p W G).res ((KW q p W K').inter_le_inter_face s 1) (x ((KW q p W K').face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]

def σ₂ {i j : K'.ι} (hij : i < j) : (KW q p W K').Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exact hij⟩

theorem σ₂_fst {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 0 = i := rfl
theorem σ₂_snd {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 1 = j := rfl

theorem d0_eq_zero_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    (GW q p W G).d (KW q p W K') 0 x = 0 ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  constructor
  · intro hd i j
    have key : ∀ s : (KW q p W K').Idx 1,
        G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
            (e0 q p W G K' x (s.1 0))
          = G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
            (e0 q p W G K' x (s.1 1)) := by
      intro s
      have hs := congrFun hd s
      rw [Pi.zero_apply, d0_apply, sub_eq_zero] at hs
      rw [GW_res_apply, GW_res_apply] at hs
      rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)] at hs
      rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)] at hs
      have hs' := congrArg (G.res (chW_inf_le_image_inter q p W K' s)) hs
      rw [G.res_res, G.res_res] at hs'
      rw [e0_apply, e0_apply, G.res_res, G.res_res]
      exact hs'.symm
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key (σ₂ q p W K' hij)
    · rfl
    · have hk : G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
              (e0 q p W G K' x j)
            = G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x i) := key (σ₂ q p W K' hji)
      have h := congrArg (G.res (le_inf inf_le_right inf_le_left :
          (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤
            (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) hk
      rw [G.res_res, G.res_res] at h
      exact h.symm
  · intro h
    funext s
    have hs := congrArg (G.res (image_inter_le_inf q p W K' s)) (h (s.1 0) (s.1 1))
    rw [e0_apply, e0_apply, G.res_res, G.res_res, G.res_res, G.res_res] at hs
    rw [Pi.zero_apply, d0_apply, sub_eq_zero]
    rw [GW_res_apply, GW_res_apply]
    rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)]
    rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)]
    exact hs.symm

theorem mem_H0_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    x ∈ (GW q p W G).H0 (KW q p W K') ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  rw [LinearMap.mem_ker, d0_eq_zero_iff]

end Bridge0

section Deg1

attribute [local instance] modSec modB modA

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

theorem d0_apply_eq_neg_res (x : (GW q p W G).cochain (KW q p W K') 0) (s : (KW q p W K').Idx 1) :
    ((GW q p W G).d (KW q p W K') 0 x s : G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s)) =
      - G.res (image_inter_le_inf q p W K' s)
          (G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
              (e0 q p W G K' x (s.1 0)) -
            G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x (s.1 1))) := by
  rw [map_sub, neg_sub, e0_apply, e0_apply]
  simp only [G.res_res]
  rw [d0_apply, GW_res_apply, GW_res_apply,
    res_congr_idx q p W G K' x (face_zero_eq q p W K' s), res_congr_idx q p W G K' x (face_one_eq q p W K' s)]

variable (I : Ideal A)

theorem d0_mem_pow_smul_top_of_forall (m : ℕ) (x : (GW q p W G).cochain (KW q p W K') 0)
    (h : ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
          - G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x j)
        ∈ I ^ m • (⊤ : Submodule A (G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)))))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    (GW q p W G).d (KW q p W K') 0 x ∈
      (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 1)) := by
  rw [cochain_mem_pow_smul_top_iff]
  intro s
  rw [d0_apply_eq_neg_res]
  exact Submodule.neg_mem _ (smul_top_mem_map (I ^ m) (G.res (image_inter_le_inf q p W K' s)) (h (s.1 0) (s.1 1)))

theorem e0_mem_pow_smul_top (m : ℕ) (x : (GW q p W G).cochain (KW q p W K') 0)
    (hx : letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
      x ∈ (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 0)))
    (i : K'.ι) :
    e0 q p W G K' x i ∈ I ^ m • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) := by
  rw [cochain_mem_pow_smul_top_iff] at hx
  rw [e0_apply]
  exact smul_top_mem_map (I ^ m) (G.res _) (hx (σ q p W K' i))

theorem e0inv_mem_pow_smul_top (m : ℕ) (y : ∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))
    (hy : ∀ i, y i ∈ I ^ m • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    e0inv q p W G K' y ∈
      (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') 0)) := by
  rw [cochain_mem_pow_smul_top_iff]
  intro s
  exact smul_top_mem_map (I ^ m) (G.res (image_inter_le q p W K' s 0)) (hy (s.1 0))

end Deg1

end AlgebraicGeometry.OModulePresheaf.Rebase
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf.Rebase"
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf.Rebase"

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ t : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (t i)
          - G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (t j)
          ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)))))) →
      ∃ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ i j : K'.ι,
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) ∧
        ∀ i : K'.ι, t i - a i ∈ I ^ n • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) := by
  classical
  letI instAlg := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  haveI : IsNoetherianRing (OModulePresheaf.Rebase.Bch W) := OModulePresheaf.Rebase.isNoetherianRing_chart q W
  obtain ⟨c, hc'⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
    (I.map (algebraMap A (OModulePresheaf.Rebase.Bch W))) (OModulePresheaf.Rebase.qW p W)
    (OModulePresheaf.Rebase.GW q p W G) (OModulePresheaf.Rebase.isCoherent_GW q p W G hc)
    (OModulePresheaf.Rebase.isQuasicoherent_GW q p W G hqc) (OModulePresheaf.Rebase.KW q p W K') n
  refine ⟨c, fun t ht => ?_⟩
  set x := OModulePresheaf.Rebase.e0inv q p W G K' t with hxdef
  have hx : OModulePresheaf.Rebase.e0 q p W G K' x = t := OModulePresheaf.Rebase.e0_e0inv q p W G K' t
  have hd := OModulePresheaf.Rebase.d0_mem_pow_smul_top_of_forall q p W G K' I (n + c) x (by rw [hx]; exact ht)
  obtain ⟨a, hda, hxa⟩ := hc' x hd
  refine ⟨OModulePresheaf.Rebase.e0 q p W G K' a, (OModulePresheaf.Rebase.d0_eq_zero_iff q p W G K' a).1 hda,
    fun i => ?_⟩
  rw [← hx, ← Pi.sub_apply, ← OModulePresheaf.Rebase.e0_sub]
  exact OModulePresheaf.Rebase.e0_mem_pow_smul_top q p W G K' I n (x - a) hxa i

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ t : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (t i)
          - G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (t j)
          ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)))))) →
      ∃ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ i j : K'.ι,
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) ∧
        ∀ i : K'.ι, t i - a i ∈ I ^ n • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

def smulHom (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) : Hom (H.pow m) H where
  app U :=
    { toFun := fun x => ∑ l : Fin m, a l • x l
      map_add' := fun x y => by
        show ∑ l : Fin m, a l • (x l + y l) = (∑ l : Fin m, a l • x l) + ∑ l : Fin m, a l • y l
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => smul_add _ _ _
      map_smul' := fun r x => by
        show ∑ l : Fin m, a l • (r • x l) = r • ∑ l : Fin m, a l • x l
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _ }
  app_smul U s x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    show ∑ l : Fin m, a l • (s • x) l = s • ∑ l : Fin m, a l • x l
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show a l • (s • x l) = s • (a l • x l)
    rw [smul_comm]
  naturality h := by
    refine LinearMap.ext fun x => ?_
    show ∑ l : Fin m, a l • ((H.pow m).res h x) l = H.res h (∑ l : Fin m, a l • x l)
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [LinearMap.map_smul, pow_res_apply]

theorem smulHom_app (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) (U : P.Opens) (x : (H.pow m).obj U) :
    (smulHom H a).app U x = ∑ l : Fin m, a l • x l := rfl

theorem range_smulHom_app (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) (U : P.Opens) :
    LinearMap.range ((smulHom H a).app U) = Ideal.span (Set.range a) • (⊤ : Submodule A (H.obj U)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [smulHom_app]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem_smul (Ideal.subset_span ⟨l, rfl⟩) Submodule.mem_top
  · refine Submodule.smul_le.mpr ?_
    intro r hr y _
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨l, rfl⟩ := hr
      refine ⟨Pi.single l y, ?_⟩
      rw [smulHom_app, Finset.sum_eq_single l (fun l' _ h => by rw [Pi.single_eq_of_ne h, smul_zero])
        (fun h => absurd (Finset.mem_univ l) h)]
      rw [Pi.single_eq_same]
    | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
    | add r s _ _ hr hs =>
      obtain ⟨x, hx⟩ := hr; obtain ⟨x', hx'⟩ := hs
      exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩
    | smul t r _ hr =>
      obtain ⟨x, hx⟩ := hr
      exact ⟨t • x, by rw [LinearMap.map_smul, hx, smul_eq_mul, mul_smul]⟩

theorem exists_span_eq_pow [IsNoetherianRing A] (I : Ideal A) (k : ℕ) :
    ∃ (m : ℕ) (a : Fin m → A), Ideal.span (Set.range a) = I ^ (k + 1) := by
  have hfg : (I ^ (k + 1)).FG := IsNoetherian.noetherian _
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  exact ⟨m, a, ha⟩

section Trunc

variable [IsNoetherianRing A] (I : Ideal A)

def genN (k : ℕ) : ℕ := (exists_span_eq_pow I k).choose

def gen (k : ℕ) : Fin (genN I k) → A := (exists_span_eq_pow I k).choose_spec.choose

theorem span_gen (k : ℕ) : Ideal.span (Set.range (gen I k)) = I ^ (k + 1) :=
  (exists_span_eq_pow I k).choose_spec.choose_spec

variable (H : OModulePresheaf q)

def trunc (k : ℕ) : OModulePresheaf q := coker (smulHom H (gen I k))

theorem range_smulHom_gen (k : ℕ) (U : P.Opens) :
    LinearMap.range ((smulHom H (gen I k)).app U) = I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) := by
  rw [range_smulHom_app, span_gen]

def truncProj (k : ℕ) : Hom H (trunc I H k) := (imCokerSES (smulHom H (gen I k))).proj

theorem truncProj_app (k : ℕ) (U : P.Opens) (x : H.obj U) :
    (truncProj I H k).app U x = (show (trunc I H k).obj U from Submodule.Quotient.mk x) := rfl

theorem truncProj_surjective (k : ℕ) (U : P.Opens) : Function.Surjective ((truncProj I H k).app U) :=
  (imCokerSES (smulHom H (gen I k))).surjective U

theorem ker_truncProj (k : ℕ) (U : P.Opens) :
    LinearMap.ker ((truncProj I H k).app U) = I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) := by
  show LinearMap.ker (Submodule.mkQ (LinearMap.range ((smulHom H (gen I k)).app U))) = _
  rw [Submodule.ker_mkQ, range_smulHom_gen]

theorem range_succ_le (k : ℕ) (U : P.Opens) :
    LinearMap.range ((smulHom H (gen I (k + 1))).app U) ≤ LinearMap.range ((smulHom H (gen I k)).app U) := by
  rw [range_smulHom_gen, range_smulHom_gen]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _))

def truncTrans (k : ℕ) : Hom (trunc I H (k + 1)) (trunc I H k) where
  app U := Submodule.mapQ _ _ LinearMap.id (range_succ_le I H k U)
  app_smul U a z := by
    induction z using Submodule.Quotient.induction_on with
    | H x => rfl
  naturality h := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x => rfl

theorem truncTrans_mk (k : ℕ) (U : P.Opens) (x : H.obj U) :
    (truncTrans I H k).app U (show (trunc I H (k + 1)).obj U from Submodule.Quotient.mk x)
      = (show (trunc I H k).obj U from Submodule.Quotient.mk x) := rfl

theorem truncTrans_comp_truncProj (k : ℕ) (U : P.Opens) :
    (truncTrans I H k).app U ∘ₗ (truncProj I H (k + 1)).app U = (truncProj I H k).app U := rfl

theorem truncTrans_surjective (k : ℕ) (U : P.Opens) : Function.Surjective ((truncTrans I H k).app U) := by
  intro z
  obtain ⟨x, rfl⟩ := truncProj_surjective I H k U z
  exact ⟨(truncProj I H (k + 1)).app U x, rfl⟩

theorem smul_top_le_ker_truncProj (k : ℕ) (U : P.Opens) :
    I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) ≤ LinearMap.ker ((truncProj I H k).app U) :=
  (ker_truncProj I H k U).ge

theorem ker_truncTrans (k : ℕ) (U : P.Opens) :
    LinearMap.ker ((truncTrans I H k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((trunc I H (k + 1)).obj U)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := truncProj_surjective I H (k + 1) U z
    have hx : x ∈ LinearMap.ker ((truncProj I H k).app U) := hz
    rw [ker_truncProj] at hx
    have : (truncProj I H (k + 1)).app U x ∈ (I ^ (k + 1) • (⊤ : Submodule A (H.obj U))).map ((truncProj I H (k + 1)).app U) :=
      Submodule.mem_map_of_mem hx
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  · refine Submodule.smul_le.mpr fun r hr z _ => ?_
    obtain ⟨x, rfl⟩ := truncProj_surjective I H (k + 1) U z
    show ((truncTrans I H k).app U ∘ₗ (truncProj I H (k + 1)).app U) (r • x) = 0
    rw [truncTrans_comp_truncProj]
    exact LinearMap.mem_ker.mp ((smul_top_le_ker_truncProj I H k U) (Submodule.smul_mem_smul hr Submodule.mem_top))

theorem isCoherent_trunc (hH : H.IsCoherent) (k : ℕ) : (trunc I H k).IsCoherent :=
  isCoherent_coker _ hH

theorem isQuasicoherent_trunc (hH : H.IsQuasicoherent) (k : ℕ) : (trunc I H k).IsQuasicoherent :=
  isQuasicoherent_coker _ hH (isQuasicoherent_pow _ hH)

end Trunc

section Nu

variable [IsNoetherianRing A] (I : Ideal A) [IsSeparated q]
  {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (G' : OModulePresheaf (p ≫ q)) (ψ' : ∀ k, AffHom G' (F' k))
  (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
    LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))

include hψ'k

theorem cechPush_psi_smul_eq_zero (k : ℕ) (U : P.affineOpens) (r : A) (hr : r ∈ I ^ (k + 1))
    (x : (cechPushforward p q K' G').obj U.1) :
    ((ψ' k).cechPushforward p q K').app U (r • x) = 0 := by
  apply cechPushforward.ext; intro i
  rw [AffHom.coe_cechPushforward_app, cechPushforward.coe_smul]
  have hmem : r • x.1 i ∈ LinearMap.ker ((ψ' k).app (AffHom.affineChart p q K' U i)) := by
    rw [hψ'k]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact LinearMap.mem_ker.mp hmem

theorem range_smulHom_le_ker (k : ℕ) (U : P.affineOpens) :
    LinearMap.range ((smulHom (cechPushforward p q K' G') (gen I k)).app U.1)
      ≤ LinearMap.ker (((ψ' k).cechPushforward p q K').app U) := by
  rw [range_smulHom_gen]
  exact Submodule.smul_le.mpr fun r hr x _ => cechPush_psi_smul_eq_zero I p K' F' G' ψ' hψ'k k U r hr x

def nu (k : ℕ) : AffHom (trunc I (cechPushforward p q K' G') k) (cechPushforward p q K' (F' k)) where
  app U := (LinearMap.range ((smulHom (cechPushforward p q K' G') (gen I k)).app U.1)).liftQ
    (((ψ' k).cechPushforward p q K').app U) (range_smulHom_le_ker I p K' F' G' ψ' hψ'k k U)
  app_smul U a z := by
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ((ψ' k).cechPushforward p q K').app_smul U a x
  naturality {U U'} h := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ((ψ' k).cechPushforward p q K').naturality_apply h x

theorem nu_mk (k : ℕ) (U : P.affineOpens) (x : (cechPushforward p q K' G').obj U.1) :
    (nu I p K' F' G' ψ' hψ'k k).app U
        (show (trunc I (cechPushforward p q K' G') k).obj U.1 from Submodule.Quotient.mk x)
      = ((ψ' k).cechPushforward p q K').app U x := rfl

theorem nu_comp_truncProj (k : ℕ) (U : P.affineOpens) :
    (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (truncProj I (cechPushforward p q K' G') k).app U.1
      = ((ψ' k).cechPushforward p q K').app U := rfl

theorem nu_compat (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (k : ℕ) (U : P.affineOpens) :
    ((φ' k).cechPushforward p q K').app U ∘ₗ (nu I p K' F' G' ψ' hψ'k (k + 1)).app U
      = (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (truncTrans I (cechPushforward p q K' G') k).app U.1 := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := truncProj_surjective I (cechPushforward p q K' G') (k + 1) U.1 z
  apply cechPushforward.ext; intro i
  show (((φ' k).cechPushforward p q K').app U (((ψ' (k + 1)).cechPushforward p q K').app U x)).1 i
    = (((ψ' k).cechPushforward p q K').app U x).1 i
  rw [AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app]
  exact LinearMap.congr_fun (hψ'c k (AffHom.affineChart p q K' U i)) (x.1 i)

theorem nu_shift [IsProper q] [IsProper p] (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (U : P.affineOpens) (k : ℕ) :
    ∃ c : ℕ, LinearMap.ker ((nu I p K' F' G' ψ' hψ'k (k + c)).app U)
      ≤ I ^ (k + 1) • (⊤ : Submodule A ((trunc I (cechPushforward p q K' G') (k + c)).obj U.1)) := by
  obtain ⟨c, hc⟩ :=
    exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper I q p G' hG'c hG'q K' U (k + 1)
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨n, rfl⟩ := truncProj_surjective I (cechPushforward p q K' G') (k + c) U.1 z
  have h0 : ((ψ' (k + c)).cechPushforward p q K').app U n = 0 := hz
  have hcomp : ∀ i : K'.ι, n.1 i ∈ I ^ (k + 1 + c) •
      (⊤ : Submodule A (G'.obj (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)))) := fun i => by
    have hi : (ψ' (k + c)).app (AffHom.affineChart p q K' U i) (n.1 i) = 0 := by
      rw [← AffHom.coe_cechPushforward_app, h0]; rfl
    rw [← LinearMap.mem_ker, hψ'k, show k + c + 1 = k + 1 + c by omega] at hi
    exact hi
  obtain ⟨m, r, b, hr, hb, hn⟩ := hc n.1 ((cechPushforward.mem_cocycles_iff p q K' G' U.1 n.1).mp n.2) hcomp
  let b' : Fin m → (cechPushforward p q K' G').obj U.1 := fun l =>
    ⟨b l, (cechPushforward.mem_cocycles_iff p q K' G' U.1 (b l)).mpr (hb l)⟩
  have hn' : n = ∑ l, r l • b' l := by
    apply cechPushforward.ext; intro i
    have hsum : (∑ l, r l • b' l).1 = ∑ l, (r l • b' l).1 :=
      map_sum (cechPushforward.cocycles p q K' G' U.1).subtype _ _
    rw [hsum, hn]
    simp only [Finset.sum_apply]
    rfl
  show (truncProj I (cechPushforward p q K' G') (k + c)).app U.1 n ∈ _
  rw [hn', map_sum]
  exact Submodule.sum_mem _ fun l _ => by
    rw [LinearMap.map_smul]; exact Submodule.smul_mem_smul (hr l) Submodule.mem_top

end Nu

end AlgebraicGeometry.OModulePresheaf.C2Head

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

section Threads

variable (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))

def IsThread (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) : Prop := ∀ n, (φ n).app U (s (n + 1)) = s n

def seq0 (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (y : (F 0).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) y (fun m prev => Classical.choose (hφs m U prev)) m

def seqMod (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) (x 0)
    (fun m prev => if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else Classical.choose (hφs m U prev)) m

theorem seqMod_succ (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) (m : ℕ) :
    seqMod F φ hφs U n x y (m + 1) = (if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else
        Classical.choose (hφs m U (seqMod F φ hφs U n x y m))) := rfl

theorem seqMod_of_le (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    ∀ m, m ≤ n → seqMod F φ hφs U n x y m = x m
  | 0, _ => rfl
  | m + 1, hm => by rw [seqMod_succ, if_pos hm]

theorem seqMod_at (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    seqMod F φ hφs U n x y (n + 1) = y := by
  rw [seqMod_succ, if_neg (Nat.not_succ_le_self n), dif_pos rfl]

theorem exists_isThread (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) : ∀ (k : ℕ) (y : (F k).obj U.1), ∃ s : ∀ n, (F n).obj U.1, IsThread F φ U s ∧ s k = y := by
  intro k
  induction k with
  | zero =>
    intro y
    exact ⟨seq0 F φ hφs U y, fun m => Classical.choose_spec (hφs m U (seq0 F φ hφs U y m)), rfl⟩
  | succ n ih =>
    intro y
    obtain ⟨x, hx, hxn⟩ := ih ((φ n).app U y)
    refine ⟨seqMod F φ hφs U n x y, fun m => ?_, seqMod_at F φ hφs U n x y⟩
    rw [seqMod_succ]
    split_ifs with h1 h2
    · rw [seqMod_of_le F φ hφs U n x y m (Nat.le_of_succ_le h1)]
      exact hx m
    · subst h2
      rw [seqMod_of_le F φ hφs U m x y m le_rfl, ← hxn]
    · exact Classical.choose_spec (hφs m U (seqMod F φ hφs U n x y m))

theorem IsThread.sub_mem (I : Ideal A)
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    {U : P.affineOpens} {s s' : ∀ n, (F n).obj U.1} (hs : IsThread F φ U s) (hs' : IsThread F φ U s')
    {k : ℕ} (h : s k = s' k) : ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h, sub_self]; exact Submodule.zero_mem _
  | succ n hn ih =>

    have himg : (φ n).app U (s (n + 1) - s' (n + 1)) ∈
        Submodule.map ((φ n).app U) (I ^ (k + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hφs n U), map_sub, hs n, hs' n]
      exact ih
    obtain ⟨w, hw, hφw⟩ := himg
    have hker : s (n + 1) - s' (n + 1) - w ∈ LinearMap.ker ((φ n).app U) := by
      rw [LinearMap.mem_ker, map_sub, hφw, sub_self]
    rw [hφk] at hker
    have hle : I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    have := Submodule.add_mem _ (hle hker) hw
    rwa [sub_add_cancel] at this

end Threads

section Adapted

variable [IsSeparated q] {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (G' : OModulePresheaf (p ≫ q)) (ψ' : ∀ k, AffHom G' (F' k))
  (F : ℕ → OModulePresheaf q) (v : ∀ k, AffHom (F k) (cechPushforward p q K' (F' k)))

def Adapted (U : P.affineOpens) (L : ℕ) (a : (cechPushforward p q K' G').obj U.1) (z : (F L).obj U.1) : Prop :=
  ((ψ' L).cechPushforward p q K').app U a = (v L).app U z

theorem psi_cechPushforward_compat (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (k : ℕ) (U : P.affineOpens) :
    ((φ' k).cechPushforward p q K').app U ∘ₗ ((ψ' (k + 1)).cechPushforward p q K').app U
      = ((ψ' k).cechPushforward p q K').app U := by
  refine LinearMap.ext fun x => cechPushforward.ext p q K' (F' k) fun i => ?_
  show (((φ' k).cechPushforward p q K').app U (((ψ' (k + 1)).cechPushforward p q K').app U x)).1 i = _
  rw [AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app]
  exact LinearMap.congr_fun (hψ'c k (AffHom.affineChart p q K' U i)) (x.1 i)

theorem Adapted.down (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {s : ∀ n, (F n).obj U.1}
    (ha : Adapted p K' F' G' ψ' F v U (L + 1) a (s (L + 1))) (hs : IsThread F φ U s) :
    Adapted p K' F' G' ψ' F v U L a (s L) := by
  unfold Adapted at ha ⊢
  rw [← psi_cechPushforward_compat p K' F' G' ψ' φ' hψ'c L U, LinearMap.comp_apply, ha, ← hs L]
  exact LinearMap.congr_fun (hvc L U) (s (L + 1))

theorem psi_eq_of_thread (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    {U : P.affineOpens} {s : ∀ n, (F n).obj U.1} (hs : IsThread F φ U s) (i : K'.ι)
    (t : G'.obj (cechPushforward.chart p K' U.1 i)) {N : ℕ}
    (hN : (ψ' N).app (AffHom.affineChart p q K' U i) t = ((v N).app U (s N)).1 i) :
    ∀ (d n : ℕ), n + d = N → (ψ' n).app (AffHom.affineChart p q K' U i) t = ((v n).app U (s n)).1 i := by
  intro d
  induction d with
  | zero => intro n h; rw [Nat.add_zero] at h; subst h; exact hN
  | succ d ih =>
    intro n h
    have h' := ih (n + 1) (by omega)
    rw [← LinearMap.congr_fun (hψ'c n (AffHom.affineChart p q K' U i)) t, LinearMap.comp_apply, h',
      ← AffHom.coe_cechPushforward_app, ← LinearMap.comp_apply, hvc n U, LinearMap.comp_apply, hs n]

theorem exists_adapted (I : Ideal A) [IsNoetherianRing A] [IsProper q] [IsProper p]
    (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    (U : P.affineOpens) (L : ℕ) (s : ∀ n, (F n).obj U.1) (hs : IsThread F φ U s) :
    ∃ a : (cechPushforward p q K' G').obj U.1, Adapted p K' F' G' ψ' F v U L a (s L) := by
  classical
  haveI : IsSeparated (p ≫ q) := inferInstance
  obtain ⟨c, hc⟩ :=
    exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
      I q p G' hG'c hG'q K' U (L + 1)

  have ht : ∀ i : K'.ι, ∃ t : G'.obj (cechPushforward.chart p K' U.1 i),
      (ψ' (L + c)).app (AffHom.affineChart p q K' U i) t = ((v (L + c)).app U (s (L + c))).1 i :=
    fun i => hψ's (L + c) (AffHom.affineChart p q K' U i) _
  choose t ht using ht

  have hCC : ∀ i j, IsAffineOpen (cechPushforward.chart p K' U.1 i ⊓ cechPushforward.chart p K' U.1 j) :=
    fun i j => Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (p ≫ q)
      (AffHom.affineChart p q K' U i).2 (AffHom.affineChart p q K' U j).2
  have hdiff : ∀ i j : K'.ι,
      G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_left (t i)
        - G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_right (t j)
        ∈ I ^ (L + 1 + c) • (⊤ : Submodule A
          (G'.obj ((K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))))) := by
    intro i j
    have hw := (cechPushforward.mem_cocycles_iff p q K' (F' (L + c)) U.1 _).mp
      ((v (L + c)).app U (s (L + c))).2 i j
    have hker : G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_left (t i)
        - G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_right (t j)
        ∈ LinearMap.ker ((ψ' (L + c)).app ⟨_, hCC i j⟩) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero,
        (ψ' (L + c)).naturality_apply (U := ⟨_, hCC i j⟩) (U' := AffHom.affineChart p q K' U i) inf_le_left,
        (ψ' (L + c)).naturality_apply (U := ⟨_, hCC i j⟩) (U' := AffHom.affineChart p q K' U j) inf_le_right,
        ht i, ht j]
      exact hw
    rw [hψ'k, show L + c + 1 = L + 1 + c by omega] at hker
    exact hker
  obtain ⟨a, ha, hta⟩ := hc t hdiff
  refine ⟨⟨a, (cechPushforward.mem_cocycles_iff p q K' G' U.1 a).mpr ha⟩, ?_⟩
  refine cechPushforward.ext p q K' (F' L) fun i => ?_
  rw [AffHom.coe_cechPushforward_app]

  have hat : (ψ' L).app (AffHom.affineChart p q K' U i) (t i - a i) = 0 := by
    rw [← LinearMap.mem_ker, hψ'k]
    exact hta i
  rw [map_sub, sub_eq_zero] at hat
  rw [← hat]
  exact psi_eq_of_thread p K' F' G' ψ' F v φ' φ hψ'c hvc hs i (t i) (ht i) c L rfl

end Adapted

end AlgebraicGeometry.OModulePresheaf.C2Head

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section U

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
  {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
  (G' : OModulePresheaf (p ≫ q))
  (ψ' : ∀ k, AffHom G' (F' k))
  (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
    LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
  (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (v : ∀ k, AffHom (F k) (cechPushforward p q K' (F' k)))

  (hPC : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ ((ψ' (k + 1)).cechPushforward p q K').app U
      = ((ψ' k).cechPushforward p q K').app U)
  (hvc : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)

  (hT1 : ∀ (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1),
    ∃ s : ∀ n, (F n).obj U.1, (∀ n, (φ n).app U (s (n + 1)) = s n) ∧ s k = y)

  (hT2 : ∀ (U : P.affineOpens) (k : ℕ) (s s' : ∀ n, (F n).obj U.1),
    (∀ n, (φ n).app U (s (n + 1)) = s n) → (∀ n, (φ n).app U (s' (n + 1)) = s' n) → s k = s' k →
      ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)))

  (hA2 : ∀ (U : P.affineOpens) (L : ℕ) (s : ∀ n, (F n).obj U.1), (∀ n, (φ n).app U (s (n + 1)) = s n) →
    ∃ a : (cechPushforward p q K' G').obj U.1, ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L))

def Good (U : P.affineOpens) (k L : ℕ) : Prop :=
  k ≤ L ∧ ∀ a : (cechPushforward p q K' G').obj U.1, ((ψ' L).cechPushforward p q K').app U a = 0 →
    a ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1))

theorem mem_smul_top_of_apply_mem {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ J • (⊤ : Submodule R M)) {x : M} (hx : f x ∈ J • (⊤ : Submodule R N)) :
    x ∈ J • (⊤ : Submodule R M) := by
  have htop : (⊤ : Submodule R N) = (⊤ : Submodule R M).map f := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 hf]
  rw [htop, ← Submodule.map_smul''] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  have hk : x - b ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, map_sub, hbx, sub_self]
  have := Submodule.add_mem _ hb (hker hk)
  rwa [add_sub_cancel] at this

include hψ'k in

theorem good_exists (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent) (U : P.affineOpens) (k : ℕ) :
    ∃ c, Good I p K' F' G' ψ' U k (k + c) := by
  obtain ⟨c, hc⟩ := nu_shift I p K' F' G' ψ' hψ'k hG'c hG'q U k
  refine ⟨c, Nat.le_add_right k c, fun a ha => ?_⟩
  refine mem_smul_top_of_apply_mem (I ^ (k + 1)) ((truncProj I (cechPushforward p q K' G') (k + c)).app U.1)
    (truncProj_surjective I _ (k + c) U.1) ?_ (hc ?_)
  · rw [ker_truncProj]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  · rw [LinearMap.mem_ker]
    exact ha

include hPC in

theorem good_succ {U : P.affineOpens} {k L : ℕ} (h : Good I p K' F' G' ψ' U k L) :
    Good I p K' F' G' ψ' U k (L + 1) := by
  refine ⟨h.1.trans (Nat.le_succ L), fun a ha => h.2 a ?_⟩
  rw [← hPC L U, LinearMap.comp_apply, ha, map_zero]

include hPC in
theorem good_of_le {U : P.affineOpens} {k L L' : ℕ} (h : Good I p K' F' G' ψ' U k L) (hL : L ≤ L') :
    Good I p K' F' G' ψ' U k L' := by
  induction hL with
  | refl => exact h
  | step _ ih => exact good_succ I p K' F' φ' G' ψ' hPC ih

theorem good_of_succ_k {U : P.affineOpens} {k L : ℕ} (h : Good I p K' F' G' ψ' U (k + 1) L) :
    Good I p K' F' G' ψ' U k L :=
  ⟨(Nat.le_succ k).trans h.1, fun a ha => Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (h.2 a ha)⟩

include hPC hvc in

theorem adapted_pred (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) (m : ℕ)
    (ha : ((ψ' (m + 1)).cechPushforward p q K').app U a = (v (m + 1)).app U (s (m + 1))) :
    ((ψ' m).cechPushforward p q K').app U a = (v m).app U (s m) := by
  rw [← hPC m U, LinearMap.comp_apply, ha, ← LinearMap.comp_apply, hvc m U, LinearMap.comp_apply, hs m]

include hPC hvc in
theorem adapted_of_le (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) (d : ℕ) :
    ∀ n : ℕ, ((ψ' (n + d)).cechPushforward p q K').app U a = (v (n + d)).app U (s (n + d)) →
      ((ψ' n).cechPushforward p q K').app U a = (v n).app U (s n) := by
  induction d with
  | zero => intro n ha; exact ha
  | succ d ih => intro n ha; exact ih n (adapted_pred p K' F' φ' G' ψ' F φ v hPC hvc U s hs a (n + d) ha)

include hPC hvc in
theorem adapted_of_le' (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) {n L : ℕ} (hnL : n ≤ L)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L)) :
    ((ψ' n).cechPushforward p q K').app U a = (v n).app U (s n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnL
  exact adapted_of_le p K' F' φ' G' ψ' F φ v hPC hvc U s hs a d n ha

include hT1 hA2 in

theorem exists_adapted_of_mem_smul (U : P.affineOpens) (k L : ℕ) (d : (F L).obj U.1)
    (hd : d ∈ I ^ (k + 1) • (⊤ : Submodule A ((F L).obj U.1))) :
    ∃ m : (cechPushforward p q K' G').obj U.1,
      m ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1)) ∧
        ((ψ' L).cechPushforward p q K').app U m = (v L).app U d := by
  refine Submodule.smul_induction_on hd ?_ ?_
  · intro r hr w _
    obtain ⟨t, ht, htL⟩ := hT1 U L w
    obtain ⟨b, hb⟩ := hA2 U L t ht
    exact ⟨r • b, Submodule.smul_mem_smul hr Submodule.mem_top, by rw [LinearMap.map_smul, LinearMap.map_smul, hb, htL]⟩
  · intro x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
    exact ⟨m₁ + m₂, Submodule.add_mem _ hm₁ hm₂, by rw [map_add, map_add, e₁, e₂]⟩

include hT1 hT2 hA2 in

theorem wit_unique {U : P.affineOpens} {k L : ℕ} (hgood : Good I p K' F' G' ψ' U k L)
    (s s' : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (hs' : ∀ n, (φ n).app U (s' (n + 1)) = s' n) (hss' : s k = s' k)
    (a a' : (cechPushforward p q K' G').obj U.1)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L))
    (ha' : ((ψ' L).cechPushforward p q K').app U a' = (v L).app U (s' L)) :
    (truncProj I (cechPushforward p q K' G') k).app U.1 a = (truncProj I (cechPushforward p q K' G') k).app U.1 a' := by
  have hd : s L - s' L ∈ I ^ (k + 1) • (⊤ : Submodule A ((F L).obj U.1)) := hT2 U k s s' hs hs' hss' L hgood.1
  obtain ⟨m, hm, hem⟩ := exists_adapted_of_mem_smul I p K' F' G' ψ' F φ v hT1 hA2 U k L _ hd
  have hz : ((ψ' L).cechPushforward p q K').app U (a - a' - m) = 0 := by
    rw [map_sub, map_sub, ha, ha', hem, map_sub, sub_self]
  have hmem := hgood.2 _ hz
  have hmem' : a - a' ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1)) := by
    have := Submodule.add_mem _ hmem hm
    rwa [sub_add_cancel] at this
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_truncProj]
  exact hmem'

include hPC hvc hT1 hT2 hA2 in

theorem wit_compare {U : P.affineOpens} {k L₁ L₂ : ℕ} (hg₁ : Good I p K' F' G' ψ' U k L₁)
    (hg₂ : Good I p K' F' G' ψ' U k L₂)
    (s₁ s₂ : ∀ n, (F n).obj U.1) (hs₁ : ∀ n, (φ n).app U (s₁ (n + 1)) = s₁ n)
    (hs₂ : ∀ n, (φ n).app U (s₂ (n + 1)) = s₂ n) (hk : s₁ k = s₂ k)
    (a₁ a₂ : (cechPushforward p q K' G').obj U.1)
    (ha₁ : ((ψ' L₁).cechPushforward p q K').app U a₁ = (v L₁).app U (s₁ L₁))
    (ha₂ : ((ψ' L₂).cechPushforward p q K').app U a₂ = (v L₂).app U (s₂ L₂)) :
    (truncProj I (cechPushforward p q K' G') k).app U.1 a₁ = (truncProj I (cechPushforward p q K' G') k).app U.1 a₂ := by
  obtain ⟨b₁, hb₁⟩ := hA2 U (L₁ + L₂) s₁ hs₁
  obtain ⟨b₂, hb₂⟩ := hA2 U (L₁ + L₂) s₂ hs₂
  have e₁ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2 hg₁ s₁ s₁ hs₁ hs₁ rfl a₁ b₁ ha₁
    (adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U s₁ hs₁ b₁ (Nat.le_add_right L₁ L₂) hb₁)
  have e₂ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2 hg₂ s₂ s₂ hs₂ hs₂ rfl a₂ b₂ ha₂
    (adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U s₂ hs₂ b₂ (Nat.le_add_left L₂ L₁) hb₂)
  have e₃ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2
    (good_of_le I p K' F' φ' G' ψ' hPC hg₁ (Nat.le_add_right L₁ L₂)) s₁ s₂ hs₁ hs₂ hk b₁ b₂ hb₁ hb₂
  rw [e₁, e₃, ← e₂]

section Defu

variable (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)

include hψ'k hG'c hG'q in

def lvl (U : P.affineOpens) (k : ℕ) : ℕ := k + (good_exists I p K' F' G' ψ' hψ'k hG'c hG'q U k).choose

theorem good_lvl (U : P.affineOpens) (k : ℕ) :
    Good I p K' F' G' ψ' U k (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) :=
  (good_exists I p K' F' G' ψ' hψ'k hG'c hG'q U k).choose_spec

def thr (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : ∀ n, (F n).obj U.1 := (hT1 U k y).choose

theorem thr_thread (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) (n : ℕ) :
    (φ n).app U (thr F φ hT1 U k y (n + 1)) = thr F φ hT1 U k y n := (hT1 U k y).choose_spec.1 n

theorem thr_at (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : thr F φ hT1 U k y k = y :=
  (hT1 U k y).choose_spec.2

def adp (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : (cechPushforward p q K' G').obj U.1 :=
  (hA2 U (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)).choose

theorem adp_spec (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) :
    ((ψ' (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)).cechPushforward p q K').app U
        (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) =
      (v (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)).app U
        (thr F φ hT1 U k y (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)) :=
  (hA2 U (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)).choose_spec

def uFun (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : (trunc I (cechPushforward p q K' G') k).obj U.1 :=
  (truncProj I (cechPushforward p q K' G') k).app U.1 (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)

include hPC hvc hT2 in

theorem uFun_eq {U : P.affineOpens} {k : ℕ} (y : (F k).obj U.1) {L : ℕ} (hg : Good I p K' F' G' ψ' U k L)
    (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (hsk : s k = y)
    (a : (cechPushforward p q K' G').obj U.1)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L)) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y =
      (truncProj I (cechPushforward p q K' G') k).app U.1 a :=
  wit_compare I p K' F' φ' G' ψ' F φ v hPC hvc hT1 hT2 hA2 (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) hg
    (thr F φ hT1 U k y) s (thr_thread F φ hT1 U k y) hs ((thr_at F φ hT1 U k y).trans hsk.symm)
    _ a (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) ha

end Defu

section Algebra

omit hψ'k hPC hvc hT1 hT2 hA2

theorem thread_add {U : P.affineOpens} {s s' : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (hs' : ∀ n, (φ n).app U (s' (n + 1)) = s' n) :
    ∀ n, (φ n).app U ((s + s') (n + 1)) = (s + s') n := fun n => by
  rw [Pi.add_apply, Pi.add_apply, map_add, hs, hs']

theorem thread_smul {U : P.affineOpens} {s : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (r : A) :
    ∀ n, (φ n).app U ((r • s) (n + 1)) = (r • s) n := fun n => by
  rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hs]

theorem thread_smulΓ {U : P.affineOpens} {s : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (g : Γ(P, U.1)) :
    ∀ n, (φ n).app U ((fun m => g • s m) (n + 1)) = (fun m => g • s m) n := fun n => by
  show (φ n).app U (g • s (n + 1)) = g • s n
  rw [(φ n).app_smul, hs]

theorem thread_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) {s : ∀ n, (F n).obj U'.1}
    (hs : ∀ n, (φ n).app U' (s (n + 1)) = s n) :
    ∀ n, (φ n).app U ((fun m => (F m).res h (s m)) (n + 1)) = (fun m => (F m).res h (s m)) n := fun n => by
  show (φ n).app U ((F (n + 1)).res h (s (n + 1))) = (F n).res h (s n)
  rw [(φ n).naturality_apply, hs]

theorem adapted_add {U : P.affineOpens} {L : ℕ} {a a' : (cechPushforward p q K' G').obj U.1} {z z' : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z)
    (ha' : ((ψ' L).cechPushforward p q K').app U a' = (v L).app U z') :
    ((ψ' L).cechPushforward p q K').app U (a + a') = (v L).app U (z + z') := by
  rw [map_add, map_add, ha, ha']

theorem adapted_smul {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {z : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z) (r : A) :
    ((ψ' L).cechPushforward p q K').app U (r • a) = (v L).app U (r • z) := by
  rw [LinearMap.map_smul, LinearMap.map_smul, ha]

theorem adapted_smulΓ {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {z : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z) (g : Γ(P, U.1)) :
    ((ψ' L).cechPushforward p q K').app U (g • a) = (v L).app U (g • z) := by
  rw [AffHom.app_smul, AffHom.app_smul, ha]

theorem adapted_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) {L : ℕ} {a : (cechPushforward p q K' G').obj U'.1}
    {z : (F L).obj U'.1} (ha : ((ψ' L).cechPushforward p q K').app U' a = (v L).app U' z) :
    ((ψ' L).cechPushforward p q K').app U ((cechPushforward p q K' G').res h a) = (v L).app U ((F L).res h z) := by
  rw [AffHom.naturality_apply, AffHom.naturality_apply, ha]

end Algebra

section Props

variable (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)

include hPC hvc hT2 in
theorem uFun_add (U : P.affineOpens) (k : ℕ) (y₁ y₂ : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (y₁ + y₂) =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₁ + uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₂ := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (y₁ + y₂)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) _
    (thread_add F φ (thr_thread F φ hT1 U k y₁) (thr_thread F φ hT1 U k y₂))
    (by rw [Pi.add_apply, thr_at, thr_at]) _
    (adapted_add p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₁)
      (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₂))]
  exact map_add _ _ _

include hPC hvc hT2 in
theorem uFun_smul (U : P.affineOpens) (k : ℕ) (r : A) (y : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (r • y) =
      r • uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (r • y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) _
    (thread_smul F φ (thr_thread F φ hT1 U k y) r) (by rw [Pi.smul_apply, thr_at]) _
    (adapted_smul p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) r)]
  exact LinearMap.map_smul _ _ _

include hPC hvc hT2 in
theorem uFun_smulΓ (U : P.affineOpens) (k : ℕ) (g : Γ(P, U.1)) (y : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (g • y) =
      g • uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (g • y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (fun m => g • thr F φ hT1 U k y m)
    (thread_smulΓ F φ (thr_thread F φ hT1 U k y) g) (by show g • thr F φ hT1 U k y k = g • y; rw [thr_at]) _
    (adapted_smulΓ p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) g)]
  exact (truncProj I (cechPushforward p q K' G') k).app_smul U.1 g _

include hPC hvc hT2 in

theorem uFun_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) (k : ℕ) (y : (F k).obj U'.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((F k).res h y) =
      (trunc I (cechPushforward p q K' G') k).res h (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U' k y) := by

  set L := lvl I p K' F' G' ψ' hψ'k hG'c hG'q U' k + lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k with hL
  obtain ⟨b, hb⟩ := hA2 U' L (thr F φ hT1 U' k y) (thr_thread F φ hT1 U' k y)
  have e' : uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U' k y =
      (truncProj I (cechPushforward p q K' G') k).app U'.1 b :=
    uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q y
      (good_of_le I p K' F' φ' G' ψ' hPC (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U' k) (Nat.le_add_right _ _))
      _ (thr_thread F φ hT1 U' k y) (thr_at F φ hT1 U' k y) b hb
  have e : uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((F k).res h y) =
      (truncProj I (cechPushforward p q K' G') k).app U.1 ((cechPushforward p q K' G').res h b) :=
    uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q ((F k).res h y)
      (good_of_le I p K' F' φ' G' ψ' hPC (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (Nat.le_add_left _ _))
      (fun m => (F m).res h (thr F φ hT1 U' k y m)) (thread_res F φ h (thr_thread F φ hT1 U' k y))
      (by show (F k).res h (thr F φ hT1 U' k y k) = (F k).res h y; rw [thr_at]) _
      (adapted_res p K' F' G' ψ' F v h hb)
  rw [e, e', (truncProj I (cechPushforward p q K' G') k).naturality_apply h b]

include hPC hvc hT2 in

theorem uFun_compat (U : P.affineOpens) (k : ℕ) (y : (F (k + 1)).obj U.1) :
    (truncTrans I (cechPushforward p q K' G') k).app U.1 (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U (k + 1) y) =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((φ k).app U y) := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q ((φ k).app U y)
    (good_of_succ_k I p K' F' G' ψ' (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U (k + 1)))
    (thr F φ hT1 U (k + 1) y) (thr_thread F φ hT1 U (k + 1) y) (by rw [← thr_thread F φ hT1 U (k + 1) y k, thr_at])
    _ (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U (k + 1) y)]
  exact LinearMap.congr_fun (truncTrans_comp_truncProj I (cechPushforward p q K' G') k U.1) _

include hPC hvc in

theorem uFun_pin (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) :
    (nu I p K' F' G' ψ' hψ'k k).app U (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) = (v k).app U y := by
  have h := adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)
    (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k).1 (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)
  rw [thr_at] at h
  exact (LinearMap.congr_fun (nu_comp_truncProj I p K' F' G' ψ' hψ'k k U) _).trans h

def uHom (k : ℕ) : AffHom (F k) (trunc I (cechPushforward p q K' G') k) where
  app U :=
    { toFun := uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k
      map_add' := uFun_add I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k
      map_smul' := uFun_smul I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k }
  app_smul U g y := uFun_smulΓ I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k g y
  naturality h := LinearMap.ext fun y => uFun_res I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q h k y

theorem uHom_app (k : ℕ) (U : P.affineOpens) (y : (F k).obj U.1) :
    (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U y =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := rfl

theorem uHom_compat (k : ℕ) (U : P.affineOpens) :
    (truncTrans I (cechPushforward p q K' G') k).app U.1 ∘ₗ
        (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (k + 1)).app U =
      (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U ∘ₗ (φ k).app U :=
  LinearMap.ext fun y => uFun_compat I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k y

theorem uHom_pin (k : ℕ) (U : P.affineOpens) :
    (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U =
      (v k).app U :=
  LinearMap.ext fun y => uFun_pin I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hA2 hG'c hG'q U k y

end Props

end U

end AlgebraicGeometry.OModulePresheaf.C2Head

end

p2m_open "CategoryTheory AlgebraicGeometry ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.AlgebraicGeometry"
open AlgebraicGeometry.OModulePresheaf.C2Head

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
    (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (G' : OModulePresheaf (p ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward p q K' (F' k)))
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U) :
    (OModulePresheaf.cechPushforward p q K' G').IsCoherent ∧
    (OModulePresheaf.cechPushforward p q K' G').IsQuasicoherent ∧
    ∃ (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
      (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward p q K' G') (Ps k))
      (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward p q K' (F' k)))
      (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k)),
      (∀ k, (Ps k).IsCoherent) ∧ (∀ k, (Ps k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψP k).app U)
          = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward p q K' G').obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        ((φ' k).cechPushforward p q K').app U ∘ₗ (ν (k + 1)).app U = (ν k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        (ν k).app U ∘ₗ (ψP k).app U = ((ψ' k).cechPushforward p q K').app U) ∧
      (∀ (U : P.affineOpens) (k : ℕ), ∃ c : ℕ,
        LinearMap.ker ((ν (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ν k).app U ∘ₗ (u k).app U = (v k).app U) := by
  have hGPc : (OModulePresheaf.cechPushforward p q K' G').IsCoherent :=
    AlgebraicGeometry.OModulePresheaf.isCoherent_cechPushforward_of_isProper q p K' G' hG'c hG'q
  have hGPq : (OModulePresheaf.cechPushforward p q K' G').IsQuasicoherent :=
    AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated q p K' G' hG'q
  have hPC := psi_cechPushforward_compat p K' F' G' ψ' φ' hψ'c
  refine ⟨hGPc, hGPq, fun k => trunc I (OModulePresheaf.cechPushforward p q K' G') k,
    fun k => (truncTrans I (OModulePresheaf.cechPushforward p q K' G') k).toAffHom,
    fun k => (truncProj I (OModulePresheaf.cechPushforward p q K' G') k).toAffHom,
    fun k => nu I p K' F' G' ψ' hψ'k k,
    fun k => uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc
      (fun U k y => exists_isThread F φ hφs U k y)
      (fun U k s s' hs hs' h => IsThread.sub_mem F φ I hφs hφk hs hs' h)
      (fun U L s hs => exists_adapted p K' F' G' ψ' F v I φ' hG'c hG'q hψ's hψ'k hψ'c φ hvc U L s hs) hG'c hG'q k,
    fun k => isCoherent_trunc I _ hGPc k, fun k => isQuasicoherent_trunc I _ hGPq k,
    fun k U => truncTrans_surjective I _ k U.1, fun k U => ker_truncTrans I _ k U.1,
    fun k U => truncProj_surjective I _ k U.1, fun k U => ker_truncProj I _ k U.1,
    fun k U => truncTrans_comp_truncProj I _ k U.1,
    fun k U => nu_compat I p K' F' G' ψ' hψ'k φ' hψ'c k U,
    fun k U => nu_comp_truncProj I p K' F' G' ψ' hψ'k k U,
    fun U k => nu_shift I p K' F' G' ψ' hψ'k hG'c hG'q U k,
    fun k U => uHom_compat I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc _ _ _ hG'c hG'q k U,
    fun k U => uHom_pin I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc _ _ _ hG'c hG'q k U⟩

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
    (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (G' : OModulePresheaf (p ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward p q K' (F' k)))
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U) :
    (OModulePresheaf.cechPushforward p q K' G').IsCoherent ∧
    (OModulePresheaf.cechPushforward p q K' G').IsQuasicoherent ∧
    ∃ (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
      (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward p q K' G') (Ps k))
      (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward p q K' (F' k)))
      (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k)),
      (∀ k, (Ps k).IsCoherent) ∧ (∀ k, (Ps k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψP k).app U)
          = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward p q K' G').obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        ((φ' k).cechPushforward p q K').app U ∘ₗ (ν (k + 1)).app U = (ν k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        (ν k).app U ∘ₗ (ψP k).app U = ((ψ' k).cechPushforward p q K').app U) ∧
      (∀ (U : P.affineOpens) (k : ℕ), ∃ c : ℕ,
        LinearMap.ker ((ν (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ν k).app U ∘ₗ (u k).app U = (v k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
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
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w :=
  FormalGAGAFiniteSqZeroAux.main I hc hq K n

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace _root_.AlgebraicGeometry

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

theorem exists_cocycle (m : ℕ) :
    ∃ z : S.H.cochain S.K 0, S.H.d S.K 0 z = 0 ∧
      ∀ s : S.K.Idx 0, z s - S.rep (S.Us s) m ∈ I ^ (m + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
  obtain ⟨c, hc⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper I S.H
    S.H_coh_qc.1 S.H_coh_qc.2 S.K (m + 1)
  obtain ⟨w', hw'mem, hw'd⟩ := hc (S.hcoch (m + c)) fun t => by
    have e : m + 1 + c = m + c + 1 := by omega
    rw [e]
    exact S.d_hcoch_mem (m + c) t
  refine ⟨S.hcoch (m + c) - w', ?_, fun s => ?_⟩
  · rw [map_sub, hw'd, sub_self]
  · have e : (S.hcoch (m + c) - w') s - S.rep (S.Us s) m =
        (S.rep (S.Us s) (m + c) - S.rep (S.Us s) m) - w' s := by
      change (S.rep (S.Us s) (m + c) - w' s) - S.rep (S.Us s) m = _
      abel
    rw [e]
    exact Submodule.sub_mem _ (S.rep_sub_rep_of_le (S.Us s) (by omega)) (hw'mem s)

def zc (m : ℕ) : S.H.cochain S.K 0 := (S.exists_cocycle m).choose

theorem d_zc (m : ℕ) : S.H.d S.K 0 (S.zc m) = 0 := (S.exists_cocycle m).choose_spec.1

theorem zc_sub_rep (m : ℕ) (s : S.K.Idx 0) :
    S.zc m s - S.rep (S.Us s) m ∈ I ^ (m + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
  (S.exists_cocycle m).choose_spec.2 s

theorem zc_mem_H0 (m : ℕ) : S.zc m ∈ S.H.H0 S.K := LinearMap.mem_ker.mpr (S.d_zc m)

theorem zc_succ_sub_zc_mem (m : ℕ) :
    S.zc (m + 1) - S.zc m ∈ S.H.H0 S.K ⊓ I ^ (m + 1) • (⊤ : Submodule R (S.H.cochain S.K 0)) := by
  refine ⟨Submodule.sub_mem _ (S.zc_mem_H0 (m + 1)) (S.zc_mem_H0 m), ?_⟩
  classical
  refine pi_mem_smul_top _ _ fun s => ?_
  have e : (S.zc (m + 1) - S.zc m) s = (S.zc (m + 1) s - S.rep (S.Us s) (m + 1)) +
      (S.rep (S.Us s) (m + 1) - S.rep (S.Us s) m) - (S.zc m s - S.rep (S.Us s) m) := by
    change S.zc (m + 1) s - S.zc m s = _
    abel
  rw [e]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ (S.rep_succ_sub_rep (S.Us s) m)) (S.zc_sub_rep m s)
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (S.zc_sub_rep (m + 1) s)

def cAR (k : ℕ) : ℕ :=
  (AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I f S.H S.H_coh_qc.1
    S.H_coh_qc.2 S.K k).choose

theorem cAR_spec (k : ℕ) :
    S.H.H0 S.K ⊓ I ^ (k + S.cAR k) • (⊤ : Submodule R (S.H.cochain S.K 0)) ≤ I ^ k • S.H.H0 S.K :=
  (AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I f S.H S.H_coh_qc.1
    S.H_coh_qc.2 S.K k).choose_spec

def Nm (k : ℕ) : ℕ := (Finset.range (k + 1)).sup fun j => j + S.cAR j

theorem le_Nm (k : ℕ) : k + S.cAR k ≤ S.Nm k :=
  Finset.le_sup (f := fun j => j + S.cAR j) (Finset.mem_range.mpr (Nat.lt_succ_self k))

theorem Nm_mono : Monotone S.Nm := fun k l hkl =>
  Finset.sup_mono (Finset.range_subset_range.mpr (by omega))

theorem zc_sub_zc_mem (k a b : ℕ) (ha : S.Nm k ≤ a) (hab : a ≤ b) :
    S.zc b - S.zc a ∈ I ^ k • S.H.H0 S.K := by
  induction b, hab using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ b hab ih =>
    have e : S.zc (b + 1) - S.zc a = (S.zc (b + 1) - S.zc b) + (S.zc b - S.zc a) := by abel
    rw [e]
    refine Submodule.add_mem _ (S.cAR_spec k ⟨(S.zc_succ_sub_zc_mem b).1, ?_⟩) ih
    have hle : k + S.cAR k ≤ b + 1 := by have := S.le_Nm k; omega
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hle) (S.zc_succ_sub_zc_mem b).2

def gseq (k : ℕ) : S.H.H0 S.K := ⟨S.zc (S.Nm k), S.zc_mem_H0 _⟩

theorem gseq_cauchy {k l : ℕ} (hkl : k ≤ l) :
    S.gseq k ≡ S.gseq l [SMOD I ^ k • (⊤ : Submodule R (S.H.H0 S.K))] := by
  rw [SModEq.sub_mem]
  have h : (S.gseq l - S.gseq k : S.H.H0 S.K) ∈ I ^ k • (⊤ : Submodule R (S.H.H0 S.K)) :=
    mem_smul_top_of_coe_mem _ _ _ (S.zc_sub_zc_mem k (S.Nm k) (S.Nm l) le_rfl (S.Nm_mono hkl))
  rw [← neg_sub]
  exact Submodule.neg_mem _ h

scoped instance finite_H0 : Module.Finite R (S.H.H0 S.K) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper S.H S.H_coh_qc.1 S.H_coh_qc.2 S.K).1

scoped instance isAdicComplete_H0 : IsAdicComplete I (S.H.H0 S.K) :=
  IsAdicComplete.of_finite_of_isNoetherianRing I (S.H.H0 S.K)

theorem exists_limit :
    ∃ L : S.H.H0 S.K, ∀ k : ℕ, S.gseq k ≡ L [SMOD I ^ k • (⊤ : Submodule R (S.H.H0 S.K))] :=
  IsPrecomplete.prec' S.gseq fun {k l} hkl => S.gseq_cauchy hkl

def L : S.H.H0 S.K := S.exists_limit.choose

theorem gseq_sub_L (k : ℕ) : S.gseq k - S.L ∈ I ^ k • (⊤ : Submodule R (S.H.H0 S.K)) :=
  SModEq.sub_mem.mp (S.exists_limit.choose_spec k)

set_option maxHeartbeats 3200000 in

theorem L_sub_rep_mem (n : ℕ) (s : S.K.Idx 0) :
    (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by

  have h0 : ((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.cochain S.K 0)) :=
    coe_mem_of_mem_smul_top (I ^ (n + 1)) (S.H.H0 S.K) _ (S.gseq_sub_L (n + 1))
  have h1 : ((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) s ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
    apply_mem_smul_top (M := fun s : S.K.Idx 0 => S.H.obj (S.K.inter s)) (I ^ (n + 1)) h0 s
  have hN : n ≤ S.Nm (n + 1) := by have := S.le_Nm (n + 1); omega
  have h2 : S.zc (S.Nm (n + 1)) s - S.rep (S.Us s) (S.Nm (n + 1)) ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (S.zc_sub_rep (S.Nm (n + 1)) s)
  have h3 := S.rep_sub_rep_of_le (S.Us s) hN
  have e : (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n =
      -(((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) s) +
        (S.zc (S.Nm (n + 1)) s - S.rep (S.Us s) (S.Nm (n + 1))) +
        (S.rep (S.Us s) (S.Nm (n + 1)) - S.rep (S.Us s) n) := by
    change (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n =
      -((S.zc (S.Nm (n + 1)) s - (S.L : S.H.cochain S.K 0) s)) + _ + _
    abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ h1) h2) h3

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
    refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper I S.H
      S.H_coh_qc.1 S.H_coh_qc.2 S.K δ hδ0 fun k s => ?_
    cases k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ n => exact hδmem n s
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
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys"

end HomCompleteAux
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux"

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

end P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
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
      ∀ φ' : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

namespace C5vAux

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G : OModulePresheaf π} (a b : OModulePresheaf.AffHom F G) (h : ∀ U : V.affineOpens, a.app U = b.app U) :
    a = b := by
  obtain ⟨appa, sa, na⟩ := a
  obtain ⟨appb, sb, nb⟩ := b
  have : appa = appb := funext h
  subst this
  rfl

theorem affHom_comp_app {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G H : OModulePresheaf π} (a : OModulePresheaf.AffHom F G) (b : OModulePresheaf.AffHom G H)
    (U : V.affineOpens) : (b.comp a).app U = b.app U ∘ₗ a.app U := rfl

theorem restrictScalars_map_pow_smul_top {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    {X : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X] (n : ℕ) :
    ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B X)).restrictScalars A = I ^ n • (⊤ : Submodule A X) := by
  rw [← Ideal.map_pow]
  generalize I ^ n = J
  have hB : ∀ (c : B) (y : X), y ∈ (J • (⊤ : Submodule A X) : Submodule A X) →
      c • y ∈ (J • (⊤ : Submodule A X) : Submodule A X) := by
    intro c y hy
    refine Submodule.smul_induction_on (p := fun y => c • y ∈ (J • (⊤ : Submodule A X) : Submodule A X)) hy ?_ ?_
    · intro a ha x _
      rw [smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro x y hx hy
      rw [smul_add]; exact Submodule.add_mem _ hx hy
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on (p := fun x => x ∈ (J • (⊤ : Submodule A X) : Submodule A X)) hx ?_ ?_
    · intro b hb x _
      rw [Ideal.map, Submodule.mem_span_iff_exists_finset_subset] at hb
      obtain ⟨f, t, ht, hf, rfl⟩ := hb
      rw [Finset.sum_smul]
      refine Submodule.sum_mem _ fun b' hb' => ?_
      obtain ⟨a, ha, rfl⟩ := ht hb'
      rw [smul_eq_mul, mul_smul, algebraMap_smul]
      exact hB _ _ (Submodule.smul_mem_smul ha Submodule.mem_top)
    · intro x y hx hy; exact Submodule.add_mem _ hx hy
  · refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a x]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

theorem restrictScalars_ker {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y] (f : X →ₗ[B] Y) :
    (LinearMap.ker f).restrictScalars A = LinearMap.ker (f.restrictScalars A) := rfl

theorem restrictScalars_range {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y] (f : X →ₗ[B] Y) :
    (LinearMap.range f).restrictScalars A = LinearMap.range (f.restrictScalars A) := by
  ext y
  simp [Submodule.restrictScalars_mem, LinearMap.mem_range]

end C5vAux

namespace C5v

theorem eq_of_compatible_of_apply_eq
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (a b : ∀ k, E k) (ha : ∀ k, τ k (a (k + 1)) = a k) (hb : ∀ k, τ k (b (k + 1)) = b k)
    (hab : ∀ k, u k (a k) = u k (b k)) : a = b := by
  have hp : ∀ k, π k (u (k + 1) (a (k + 1))) = u k (a k) := fun k => by
    have h := LinearMap.congr_fun (huc k) (a (k + 1))
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [h, ha]
  have hpθ : ∀ k, θ k (u k (a k)) = 0 := fun k => by
    have : u k (a k) ∈ LinearMap.ker (θ k) := by rw [← hur k]; exact LinearMap.mem_range_self _ _
    exact this
  obtain ⟨e, -, huniq⟩ :=
    Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul I E τ hτs hτk P π C θ u huc hur hui
      (fun k => u k (a k)) hp hpθ
  exact (huniq a ⟨ha, fun _ => rfl⟩).trans (huniq b ⟨hb, fun k => (hab k).symm⟩).symm

theorem eq_of_compatible_of_comp_eq
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    {X : Type u} [AddCommGroup X] [Module R X]
    (a b : ∀ k, X →ₗ[R] E k) (ha : ∀ k, τ k ∘ₗ a (k + 1) = a k) (hb : ∀ k, τ k ∘ₗ b (k + 1) = b k)
    (hab : ∀ k, u k ∘ₗ a k = u k ∘ₗ b k) : a = b := by
  funext k
  ext x
  have h := eq_of_compatible_of_apply_eq I E τ hτs hτk P π C θ u huc hur hui
    (fun j => a j x) (fun j => b j x)
    (fun j => LinearMap.congr_fun (ha j) x) (fun j => LinearMap.congr_fun (hb j) x)
    (fun j => LinearMap.congr_fun (hab j) x)
  exact congrFun h k

end C5v

namespace C5vAux2
open _root_.AlgebraicGeometry
theorem appSections_restrictScalars {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G) (U : V.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    (φ.appSections U).restrictScalars R = φ.app U :=
  LinearMap.ext fun _ => rfl
end C5vAux2

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (Cs : ℕ → OModulePresheaf q) (hCsc : ∀ k, (Cs k).IsCoherent) (hCsq : ∀ k, (Cs k).IsQuasicoherent)
    (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
    (hγs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U))
    (hγk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1)))
    (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k))
    (hθc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U)
    (u : ∀ k, OModulePresheaf.AffHom (E k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (τ k).app U)
    (hur : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((u k).app U) = LinearMap.ker ((θ k).app U))
    (hui : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)))
    (GP : OModulePresheaf q) (hGPc : GP.IsCoherent) (hGPq : GP.IsQuasicoherent)
    (ψP : ∀ k, OModulePresheaf.AffHom GP (Ps k))
    (hψPs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U))
    (hψPk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψP k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GP.obj U.1)))
    (hψPc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U)
    (GC : OModulePresheaf q) (hGCc : GC.IsCoherent) (hGCq : GC.IsQuasicoherent)
    (ψC : ∀ k, OModulePresheaf.AffHom GC (Cs k))
    (hψCs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψC k).app U))
    (hψCk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψC k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GC.obj U.1)))
    (hψCc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (ψC (k + 1)).app U = (ψC k).app U) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (E k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  classical

  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q

  have e1 : ∀ n, (γ n).comp (ψC (n + 1)) = ψC n := fun n => C5vAux.affHom_ext _ _ (fun U => hψCc n U)
  have e2 : ∀ n, (γ n).comp ((θ (n + 1)).comp (ψP (n + 1))) = (θ n).comp (ψP n) := fun n =>
    C5vAux.affHom_ext _ _ (fun U => by
      show (γ n).app U ∘ₗ ((θ (n + 1)).app U ∘ₗ (ψP (n + 1)).app U) = (θ n).app U ∘ₗ (ψP n).app U
      rw [← LinearMap.comp_assoc, hθc n U, LinearMap.comp_assoc, hψPc n U])
  obtain ⟨ρ, hρ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I q GP GC hGPc hGPq hGCc hGCq
      Cs γ ψC hψCs hψCk e1 (fun n => (θ n).comp (ψP n)) e2
  have hρU : ∀ (n : ℕ) (U : P.affineOpens), (ψC n).app U ∘ₗ ρ.app U = (θ n).app U ∘ₗ (ψP n).app U :=
    fun n U => congrArg (fun a => OModulePresheaf.AffHom.app a U) (hρ n)

  obtain ⟨G, ιG, hGcoh, hGq, hιi, hιr⟩ :=
    AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker hGPq hGCq ρ
  have hGc : G.IsCoherent := hGcoh inferInstance hGPc

  have main : ∀ U : P.affineOpens, ∃ ψU : ∀ k, G.obj U.1 →ₗ[A] (E k).obj U.1,
      (∀ (k : ℕ) (a : Γ(P, U.1)) (x : G.obj U.1), ψU k (a • x) = a • ψU k x) ∧
      (∀ k, Function.Surjective (ψU k)) ∧
      (∀ k, LinearMap.ker (ψU k) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ k, (τ k).app U ∘ₗ ψU (k + 1) = ψU k) ∧
      (∀ k, (u k).app U ∘ₗ ψU k = (ψP k).app U ∘ₗ ιG.app U) := by
    intro U
    letI alg : Algebra A Γ(P, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
    haveI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : Module.Finite Γ(P, U.1) (GP.obj U.1) := hGPc U
    haveI : Module.Finite Γ(P, U.1) (GC.obj U.1) := hGCc U
    set J : Ideal Γ(P, U.1) := I.map (algebraMap A Γ(P, U.1)) with hJ

    have brK : ∀ {X Y : OModulePresheaf q} (φ : OModulePresheaf.AffHom X Y) (n : ℕ),
        LinearMap.ker (φ.app U) = I ^ n • (⊤ : Submodule A (X.obj U.1)) →
        LinearMap.ker (φ.appSections U) = J ^ n • (⊤ : Submodule Γ(P, U.1) (X.obj U.1)) := by
      intro X Y φ n h
      apply Submodule.restrictScalars_injective A
      rw [C5vAux.restrictScalars_ker, C5vAux2.appSections_restrictScalars, hJ, C5vAux.restrictScalars_map_pow_smul_top]
      exact h
    have brR : ∀ {X Y Z : OModulePresheaf q} (φ : OModulePresheaf.AffHom X Y) (φ' : OModulePresheaf.AffHom Y Z),
        LinearMap.range (φ.app U) = LinearMap.ker (φ'.app U) →
        LinearMap.range (φ.appSections U) = LinearMap.ker (φ'.appSections U) := by
      intro X Y Z φ φ' h
      apply Submodule.restrictScalars_injective A
      rw [C5vAux.restrictScalars_ker, C5vAux.restrictScalars_range, C5vAux2.appSections_restrictScalars,
        C5vAux2.appSections_restrictScalars]
      exact h
    have brC : ∀ {X Y Z : OModulePresheaf q} (a : OModulePresheaf.AffHom X Y) (b : OModulePresheaf.AffHom Y Z)
        (c : OModulePresheaf.AffHom X Z), b.app U ∘ₗ a.app U = c.app U →
        b.appSections U ∘ₗ a.appSections U = c.appSections U := by
      intro X Y Z a b c h
      exact LinearMap.ext fun x => LinearMap.congr_fun h x
    have brC2 : ∀ {X Y Y' Z : OModulePresheaf q} (a : OModulePresheaf.AffHom X Y) (b : OModulePresheaf.AffHom Y Z)
        (a' : OModulePresheaf.AffHom X Y') (b' : OModulePresheaf.AffHom Y' Z), b.app U ∘ₗ a.app U = b'.app U ∘ₗ a'.app U →
        b.appSections U ∘ₗ a.appSections U = b'.appSections U ∘ₗ a'.appSections U := by
      intro X Y Y' Z a b a' b' h
      exact LinearMap.ext fun x => LinearMap.congr_fun h x
    obtain ⟨c, hcU⟩ := hui U
    have hui' : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker ((u (k + c)).appSections U) ≤
        J ^ (k + 1) • (⊤ : Submodule Γ(P, U.1) ((E (k + c)).obj U.1)) := by
      refine ⟨c, fun k x hx => ?_⟩
      have hx' : x ∈ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)) := hcU k hx
      rw [← C5vAux.restrictScalars_map_pow_smul_top (B := Γ(P, U.1)) I (k + 1)] at hx'
      rwa [hJ]
    obtain ⟨ψB, hBs, hBk, hBc, hBl⟩ :=
      Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker (R := Γ(P, U.1)) J
        (ρ.appSections U) (ιG.appSections U) (hιi U) (brR ιG ρ (hιr U))
        (fun k => (E k).obj U.1) (fun k => (τ k).appSections U) (fun k => hτs k U) (fun k => brK (τ k) (k + 1) (hτk k U))
        (fun k => (Ps k).obj U.1) (fun k => (π k).appSections U)
        (fun k => (ψP k).appSections U) (fun k => hψPs k U) (fun k => brK (ψP k) (k + 1) (hψPk k U))
        (fun k => brC (ψP (k + 1)) (π k) (ψP k) (hψPc k U))
        (fun k => (Cs k).obj U.1) (fun k => (γ k).appSections U)
        (fun k => (ψC k).appSections U) (fun k => hψCs k U) (fun k => brK (ψC k) (k + 1) (hψCk k U))
        (fun k => brC (ψC (k + 1)) (γ k) (ψC k) (hψCc k U))
        (fun k => (θ k).appSections U) (fun k => brC2 (ψP k) (θ k) ρ (ψC k) (hρU k U).symm)
        (fun k => (u k).appSections U) (fun k => brC2 (u (k + 1)) (π k) (τ k) (u k) (huc k U))
        (fun k => brR (u k) (θ k) (hur k U)) hui'
    refine ⟨fun k => (ψB k).restrictScalars A, fun k a x => (ψB k).map_smul a x, fun k => hBs k, fun k => ?_, fun k => ?_, fun k => ?_⟩
    · rw [← C5vAux.restrictScalars_ker, hBk, hJ, C5vAux.restrictScalars_map_pow_smul_top]
    · exact LinearMap.ext fun x => LinearMap.congr_fun (hBc k) x
    · exact LinearMap.ext fun x => LinearMap.congr_fun (hBl k) x
  choose ψU hsm hs hk hc hl using main

  have hnat : ∀ (k : ℕ) {U U' : P.affineOpens} (h : U.1 ≤ U'.1), ψU U k ∘ₗ G.res h = (E k).res h ∘ₗ ψU U' k := by
    intro k U U' h
    have key := C5v.eq_of_compatible_of_comp_eq (R := A) I
      (fun k => (E k).obj U.1) (fun k => (τ k).app U) (fun k => hτs k U) (fun k => hτk k U)
      (fun k => (Ps k).obj U.1) (fun k => (π k).app U) (fun k => (Cs k).obj U.1) (fun k => (θ k).app U)
      (fun k => (u k).app U) (fun k => huc k U) (fun k => hur k U) (hui U)
      (fun k => ψU U k ∘ₗ G.res h) (fun k => (E k).res h ∘ₗ ψU U' k)
      (fun k => by
        show (τ k).app U ∘ₗ (ψU U (k + 1) ∘ₗ G.res h) = ψU U k ∘ₗ G.res h
        rw [← LinearMap.comp_assoc, hc U k])
      (fun k => by
        show (τ k).app U ∘ₗ ((E (k + 1)).res h ∘ₗ ψU U' (k + 1)) = (E k).res h ∘ₗ ψU U' k
        rw [← LinearMap.comp_assoc, (τ k).naturality h, LinearMap.comp_assoc, hc U' k])
      (fun k => by
        show (u k).app U ∘ₗ (ψU U k ∘ₗ G.res h) = (u k).app U ∘ₗ ((E k).res h ∘ₗ ψU U' k)
        rw [← LinearMap.comp_assoc, hl U k, LinearMap.comp_assoc, ιG.naturality h, ← LinearMap.comp_assoc,
          (ψP k).naturality h]
        conv_rhs => rw [← LinearMap.comp_assoc, (u k).naturality h, LinearMap.comp_assoc, hl U' k]
        rw [LinearMap.comp_assoc])
    exact congrFun key k
  exact ⟨G, fun k => ⟨fun U => ψU U k, fun U a x => hsm U k a x, fun h => hnat k h⟩, hGc, hGq,
    fun k U => hs U k, fun k U => hk U k, fun k U => hc U k⟩

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (Cs : ℕ → OModulePresheaf q) (hCsc : ∀ k, (Cs k).IsCoherent) (hCsq : ∀ k, (Cs k).IsQuasicoherent)
    (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
    (hγs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U))
    (hγk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1)))
    (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k))
    (hθc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U)
    (u : ∀ k, OModulePresheaf.AffHom (E k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (τ k).app U)
    (hur : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((u k).app U) = LinearMap.ker ((θ k).app U))
    (hui : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)))
    (GP : OModulePresheaf q) (hGPc : GP.IsCoherent) (hGPq : GP.IsQuasicoherent)
    (ψP : ∀ k, OModulePresheaf.AffHom GP (Ps k))
    (hψPs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U))
    (hψPk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψP k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GP.obj U.1)))
    (hψPc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U)
    (GC : OModulePresheaf q) (hGCc : GC.IsCoherent) (hGCq : GC.IsQuasicoherent)
    (ψC : ∀ k, OModulePresheaf.AffHom GC (Cs k))
    (hψCs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψC k).app U))
    (hψCk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψC k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GC.obj U.1)))
    (hψCc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (ψC (k + 1)).app U = (ψC k).app U) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (E k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
attribute [-simp] DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mProjExistSol

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~coker"

section Generic

variable {A : Type*} [CommRing A]

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    g x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem map_smul_top_of_surjective {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g) :
    (J • (⊤ : Submodule A M)).map g = J • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]

theorem pow_smul_top_eq_bot {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g)
    (hk : LinearMap.ker g = J • (⊤ : Submodule A M)) : J • (⊤ : Submodule A M') = ⊥ := by
  rw [← map_smul_top_of_surjective J g hg, ← hk]
  exact le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr (by rw [Submodule.comap_bot]))

end Generic

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (a b : AffHom F G) (h : ∀ (W : V.affineOpens) (x : F.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

section Trunc

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (.of A)}
variable (E : OModulePresheaf q)

def T (k : ℕ) (U : P.Opens) : Submodule A (E.obj U) := I ^ (k + 1) • ⊤

theorem T_def (k : ℕ) (U : P.Opens) : T I E k U = I ^ (k + 1) • (⊤ : Submodule A (E.obj U)) := rfl

theorem T_smul_mem (k : ℕ) (U : P.Opens) (a : Γ(P, U)) {x : E.obj U} (hx : x ∈ T I E k U) :
    a • x ∈ T I E k U := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  haveI : IsScalarTower A Γ(P, U) (E.obj U) := E.isScalarTower U
  refine Submodule.smul_induction_on hx (fun i hi y _ => ?_) (fun x y hx hy => ?_)
  · rw [T_def, smul_algebra_smul_comm i a y]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · rw [smul_add]; exact add_mem hx hy

theorem T_res {U U' : P.Opens} (hle : U ≤ U') (k : ℕ) {x : E.obj U'} (hx : x ∈ T I E k U') :
    E.res hle x ∈ T I E k U :=
  map_mem_smul_top _ (E.res hle) hx

theorem T_anti (k : ℕ) (U : P.Opens) : T I E (k + 1) U ≤ T I E k U :=
  Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ _)) le_rfl

@[reducible] noncomputable def truncModuleSections (k : ℕ) (U : P.Opens) :
    Module Γ(P, U) (E.obj U ⧸ T I E k U) :=
  letI : SMul Γ(P, U) (E.obj U ⧸ T I E k U) :=
    ⟨fun a => Quotient.map' (a • ·) fun x y hxy => (Submodule.quotientRel_def _).mpr <| by
      rw [← smul_sub]; exact T_smul_mem I E k U a ((Submodule.quotientRel_def _).mp hxy)⟩
  Function.Surjective.module Γ(P, U) ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

noncomputable def trunc (k : ℕ) : OModulePresheaf q where
  obj U := E.obj U ⧸ T I E k U
  module U := inferInstance
  moduleSections U := truncModuleSections I E k U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    letI := truncModuleSections I E k U
    exact ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk (smul_assoc r a x)⟩
  res {U U'} hle := Submodule.mapQ _ _ (E.res hle) fun x hx => T_res I E hle k hx
  res_smul {U U'} hle a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk (E.res_smul hle a x)
  res_refl U := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_refl U) x)
  res_comp {U U' U''} hle hle' := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_comp hle hle') x)

theorem trunc_obj (k : ℕ) (U : P.Opens) : (trunc I E k).obj U = (E.obj U ⧸ T I E k U) := rfl

theorem trunc_res_mk (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') (x : E.obj U') :
    (trunc I E k).res hle (Submodule.Quotient.mk x) = Submodule.Quotient.mk (E.res hle x) := rfl

theorem trunc_smul_mk (k : ℕ) (U : P.Opens) (a : Γ(P, U)) (x : E.obj U) :
    (a • (show (trunc I E k).obj U from Submodule.Quotient.mk x))
      = (show (trunc I E k).obj U from Submodule.Quotient.mk (a • x)) := rfl

noncomputable def truncπ (k : ℕ) : AffHom E (trunc I E k) where
  app U := (T I E k U.1).mkQ
  app_smul _ _ _ := rfl
  naturality _ := rfl

theorem truncπ_app (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncπ I E k).app U x = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) := rfl

theorem truncπ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncπ I E k).app U) :=
  Submodule.mkQ_surjective _

theorem ker_truncπ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncπ I E k).app U) = I ^ (k + 1) • (⊤ : Submodule A (E.obj U.1)) :=
  Submodule.ker_mkQ _

noncomputable def truncτ (k : ℕ) : AffHom (trunc I E (k + 1)) (trunc I E k) where
  app U := Submodule.mapQ (T I E (k + 1) U.1) (T I E k U.1) LinearMap.id (T_anti I E k U.1)
  app_smul _ _ z := z.inductionOn' fun _ => rfl
  naturality _ := LinearMap.ext fun z => z.inductionOn' fun _ => rfl

theorem truncτ_app_mk (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncτ I E k).app U (Submodule.Quotient.mk x) = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) :=
  rfl

theorem truncτ_truncπ (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncτ I E k).app U ((truncπ I E (k + 1)).app U x) = (truncπ I E k).app U x := rfl

theorem truncτ_comp_truncπ (k : ℕ) : (truncτ I E k).comp (truncπ I E (k + 1)) = truncπ I E k :=
  affHom_ext _ _ fun _ _ => rfl

theorem truncτ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncτ I E k).app U) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem ker_truncτ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncτ I E k).app U)
      = I ^ (k + 1) • (⊤ : Submodule A ((trunc I E (k + 1)).obj U.1)) := by

  have h1 : LinearMap.ker ((truncτ I E k).app U) = (T I E k U.1).map ((truncπ I E (k + 1)).app U) := by
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk x : E.obj U.1 ⧸ T I E k U.1) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hd : y - x ∈ T I E (k + 1) U.1 := (Submodule.Quotient.eq _).mp hyx
      have : x = y - (y - x) := by abel
      rw [this]
      exact sub_mem hy (T_anti I E k U.1 hd)
  rw [h1, T_def, map_smul_top_of_surjective _ _ (truncπ_surjective I E (k + 1) U)]

theorem isCoherent_trunc (hEc : E.IsCoherent) (k : ℕ) : (trunc I E k).IsCoherent := by
  intro U
  haveI := hEc U
  let f : E.obj U.1 →ₗ[Γ(P, U.1)] (trunc I E k).obj U.1 :=
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective f (Submodule.Quotient.mk_surjective _)

theorem isQuasicoherent_trunc (hEq : E.IsQuasicoherent) (k : ℕ) : (trunc I E k).IsQuasicoherent := by
  intro U f
  obtain ⟨hE1, hE2⟩ := hEq U f
  have hDf : IsAffineOpen (P.basicOpen f) := U.2.basicOpen f
  set D : P.affineOpens := ⟨P.basicOpen f, hDf⟩ with hD

  set fD : ℕ → Γ(P, P.basicOpen f) := fun n => (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom (f ^ n)
    with hfD
  have hfD_add : ∀ a b, fD (a + b) = fD a * fD b := fun a b => by
    simp only [hfD, pow_add, map_mul]
  have hres_pow : ∀ (n : ℕ) (y : E.obj U.1),
      E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y) = fD n • E.res (P.basicOpen_le f) y :=
    fun n y => E.res_smul _ _ _
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨n, y, hy⟩ := hE1 x
    refine ⟨n, Submodule.Quotient.mk y, ?_⟩
    show Submodule.Quotient.mk (E.res _ y) = Submodule.Quotient.mk (_ • x)
    rw [hy]
  · intro z hz
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hmem : E.res (P.basicOpen_le f) y ∈ T I E k (P.basicOpen f) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz

    have key : ∀ x ∈ T I E k (P.basicOpen f),
        ∃ (n : ℕ) (w : E.obj U.1), w ∈ T I E k U.1 ∧ E.res (P.basicOpen_le f) w = fD n • x := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun i hi x _ => ?_) (fun x x' hx hx' => ?_)
      · obtain ⟨n, w, hw⟩ := hE1 x
        refine ⟨n, i • w, Submodule.smul_mem_smul hi Submodule.mem_top, ?_⟩
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q (P.basicOpen f)
        haveI : IsScalarTower A Γ(P, P.basicOpen f) (E.obj (P.basicOpen f)) := E.isScalarTower _
        rw [LinearMap.map_smul, hw]
        exact (smul_algebra_smul_comm i (fD n) x).symm
      · obtain ⟨n, w, hw, hwx⟩ := hx
        obtain ⟨n', w', hw', hwx'⟩ := hx'
        refine ⟨n + n', (f ^ n' : Γ(P, U.1)) • w + (f ^ n : Γ(P, U.1)) • w',
          add_mem (T_smul_mem I E k U.1 _ hw) (T_smul_mem I E k U.1 _ hw'), ?_⟩
        rw [map_add, hres_pow, hres_pow, hwx, hwx', smul_smul, smul_smul, ← hfD_add, ← hfD_add,
          Nat.add_comm n' n, smul_add]
    obtain ⟨n, w, hw, hwy⟩ := key _ hmem
    have h0 : E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y - w) = 0 := by
      rw [map_sub, hres_pow, hwy, sub_self]
    obtain ⟨m, hm⟩ := hE2 _ h0
    refine ⟨m + n, ?_⟩
    show Submodule.Quotient.mk ((f ^ (m + n) : Γ(P, U.1)) • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    rw [hm]
    exact T_smul_mem I E k U.1 _ hw

end Trunc

section Card

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  [IsClosedImmersion ι]

theorem main
    (F : ℕ → OModulePresheaf (ι ≫ ProjSpace.π A r)) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf (ι ≫ ProjSpace.π A r)) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by

  haveI : IsProper (ι ≫ ProjSpace.π A r) := inferInstance
  haveI : LocallyOfFiniteType (ι ≫ ProjSpace.π A r) := inferInstance

  obtain ⟨E, θ, hEc, hEq, hθs, hθc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
      I ι rfl F hc hq φ hφs hφk

  have hFk : ∀ (k : ℕ) (U : P.affineOpens), I ^ (k + 1) • (⊤ : Submodule A ((F k).obj U.1)) = ⊥ :=
    fun k U => pow_smul_top_eq_bot _ ((φ k).app U) (hφs k U) (hφk k U)
  have hTθ : ∀ (k : ℕ) (U : P.affineOpens), T I E k U.1 ≤ LinearMap.ker ((θ k).app U) := by
    intro k U x hx
    rw [LinearMap.mem_ker, ← (Submodule.mem_bot A), ← hFk k U]
    exact map_mem_smul_top _ ((θ k).app U) hx
  let θb : ∀ k, AffHom (trunc I E k) (F k) := fun k =>
    { app := fun U => (T I E k U.1).liftQ ((θ k).app U) (hTθ k U)
      app_smul := fun U a z => z.inductionOn' fun x => (θ k).app_smul U a x
      naturality := fun {U U'} hle => LinearMap.ext fun z => z.inductionOn' fun x =>
        (θ k).naturality_apply hle x }
  have θb_mk : ∀ (k : ℕ) (U : P.affineOpens) (x : E.obj U.1),
      (θb k).app U ((truncπ I E k).app U x) = (θ k).app U x := fun _ _ _ => rfl
  have hθbs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θb k).app U) := by
    intro k U y
    obtain ⟨x, rfl⟩ := hθs k U y
    exact ⟨(truncπ I E k).app U x, rfl⟩
  have hθbc : ∀ (k : ℕ) (U : P.affineOpens),
      (φ k).app U ∘ₗ (θb (k + 1)).app U = (θb k).app U ∘ₗ (truncτ I E k).app U := by
    intro k U
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    show (φ k).app U ((θ (k + 1)).app U x) = (θ k).app U x
    rw [← LinearMap.comp_apply, hθc]

  obtain ⟨K, κ, j, hKc, hKq, hκs, hκk, hjc, hjr⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top I
      (fun k => trunc I E k) F (fun k => isCoherent_trunc I E hEc k) (fun k => isQuasicoherent_trunc I E hEq k)
      hc hq (fun k => truncτ I E k) (fun k => truncτ_surjective I E k) (fun k => ker_truncτ I E k)
      φ hφs hφk θb hθbs hθbc

  obtain ⟨H, lam, hHc, hHq, hls, hlc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
      I ι rfl K hKc hKq κ hκs hκk
  let ψ' : ∀ n, AffHom H (trunc I E n) := fun n => (j n).comp (lam n)
  have hψ' : ∀ n, (truncτ I E n).comp (ψ' (n + 1)) = ψ' n := by
    intro n
    refine affHom_ext _ _ fun U x => ?_
    show ((truncτ I E n).app U ∘ₗ (j (n + 1)).app U) ((lam (n + 1)).app U x)
      = (j n).app U ((lam n).app U x)
    rw [hjc n U, LinearMap.comp_apply, ← LinearMap.comp_apply ((κ n).app U), hlc n U]
  obtain ⟨h, hh, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I
      (ι ≫ ProjSpace.π A r) H E hHc hHq hEc hEq (fun n => trunc I E n) (fun n => truncτ I E n)
      (fun n => truncπ I E n) (fun n => truncπ_surjective I E n) (fun n => ker_truncπ I E n)
      (fun n => truncτ_comp_truncπ I E n) ψ' hψ'
  have hh_app : ∀ (n : ℕ) (U : P.affineOpens) (x : H.obj U.1),
      (truncπ I E n).app U (h.app U x) = (j n).app U ((lam n).app U x) := by
    intro n U x
    have := congrArg (fun (g : AffHom H (trunc I E n)) => g.app U x) (hh n)
    exact this

  have hker : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((θ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (E.obj U.1)) := by
    intro k U

    have hfac : (θ k).app U = (θb k).app U ∘ₗ (truncπ I E k).app U := LinearMap.ext fun _ => rfl

    have hkb : LinearMap.ker ((θb k).app U) = (LinearMap.range (h.app U)).map ((truncπ I E k).app U) := by
      rw [← hjr k U, ← LinearMap.range_comp]
      have hsurj : LinearMap.range ((j k).app U)
          = LinearMap.range ((j k).app U ∘ₗ (lam k).app U) := by
        rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (hls k U), Submodule.map_top]
      rw [hsurj]
      congr 1
      exact LinearMap.ext fun x => (hh_app k U x).symm
    rw [hfac, LinearMap.ker_comp, hkb, Submodule.comap_map_eq, ker_truncπ, sup_comm]
  obtain ⟨G, ρ, ψ, hGc, hGq, -, -, -, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
      I hHq hEc hEq h F φ θ hθs hker hθc
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

end Card

end P2mProjExistSol

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  subst hιq
  exact P2mProjExistSol.main I ι F hc hq φ hφs hφk

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
attribute [-simp] DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

namespace RedX1

theorem mem_smul_top_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (f : M →ₗ[R] M') {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I • (⊤ : Submodule R M') := by
  have h : f x ∈ (I • (⊤ : Submodule R M)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_map_pow_smul_top_iff {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (m : ℕ) (x : M) :
    x ∈ (I.map (algebraMap R S)) ^ m • (⊤ : Submodule S M) ↔ x ∈ I ^ m • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem mem_smul_top_sup_of_mkQ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (p : Submodule R M) (x : M) (h : p.mkQ x ∈ I • (⊤ : Submodule R (M ⧸ p))) : x ∈ I • (⊤ : Submodule R M) ⊔ p := by
  have e : (I • (⊤ : Submodule R (M ⧸ p))) = (I • (⊤ : Submodule R M)).map p.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [e] at h
  have h' : x ∈ (Submodule.map p.mkQ (I • ⊤)).comap p.mkQ := h
  rw [Submodule.comap_map_mkQ] at h'
  rwa [sup_comm]

def e {B : Type*} [CommRing B] {r : ℕ} (m : Fin r) : Fin r → B := fun j => if m = j then 1 else 0

theorem e_map {B C : Type*} [CommRing B] [CommRing C] (f : B →+* C) {r : ℕ} (m j : Fin r) :
    f (e m j) = e m j := by
  unfold e; split_ifs <;> simp

theorem apply_eq_sum_e {B : Type*} [CommRing B] {r : ℕ} {N : Type*} [AddCommGroup N] [Module B N]
    (g : (Fin r → B) →ₗ[B] N) (v : Fin r → B) : g v = ∑ m, v m • g (e m) :=
  LinearMap.pi_apply_eq_sum_univ g v

section Theta

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C]
variable {GEU GKU FU : Type u} [AddCommGroup GEU] [Module C GEU] [AddCommGroup GKU] [Module C GKU]
  [AddCommGroup FU] [Module C FU] [Module A FU]
variable {r : ℕ} (pU : (Fin r → C) →ₗ[C] GEU) (dU : ↥(LinearMap.ker pU) →ₗ[C] GKU)
  (lamC : GKU →ₗ[C] FU) (w : Fin r → FU)
  (h : ∀ s : ↥(LinearMap.ker pU), lamC (dU s) = Fintype.linearCombination C w (s : Fin r → C))

noncomputable def thetaC : LinearMap.ExtPushout pU dU →ₗ[C] FU :=
  LinearMap.ExtPushout.lift pU dU lamC (Fintype.linearCombination C w) h

theorem thetaC_inl (n : GKU) : thetaC pU dU lamC w h (LinearMap.ExtPushout.inl pU dU n) = lamC n :=
  LinearMap.ExtPushout.lift_inl pU dU _ _ h n

theorem thetaC_inr (v : Fin r → C) : thetaC pU dU lamC w h (LinearMap.ExtPushout.inr pU dU v) = ∑ m, v m • w m := by
  rw [thetaC, LinearMap.ExtPushout.lift_inr, Fintype.linearCombination_apply]

variable (alg : Algebra A C)

noncomputable def theta (hst : letI := alg; IsScalarTower A C FU) :
    letI : Module A (LinearMap.ExtPushout pU dU) := Module.compHom _ alg.algebraMap
    LinearMap.ExtPushout pU dU →ₗ[A] FU :=
  letI : Module A (LinearMap.ExtPushout pU dU) := Module.compHom _ alg.algebraMap
  letI := alg
  { toFun := thetaC pU dU lamC w h
    map_add' := (thetaC pU dU lamC w h).map_add
    map_smul' := fun a x => by
      change thetaC pU dU lamC w h (alg.algebraMap a • x) = a • thetaC pU dU lamC w h x
      rw [map_smul]
      exact algebraMap_smul C a _ }

theorem theta_apply (hst : letI := alg; IsScalarTower A C FU) (x : LinearMap.ExtPushout pU dU) :
    theta pU dU lamC w h alg hst x = thetaC pU dU lamC w h x := rfl

end Theta

theorem isScalarTower_compHom {A C M : Type*} [CommRing A] [CommRing C] (alg : Algebra A C)
    [AddCommGroup M] [Module C M] :
    letI : Module A M := Module.compHom M alg.algebraMap
    letI := alg
    IsScalarTower A C M :=
  letI : Module A M := Module.compHom M alg.algebraMap
  letI := alg
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

section Simplices

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev vtx (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by have ha := a.isLt; have hb := b.isLt; omega)⟩

theorem le_inter_vtx (i : K.ι) : K.U i ≤ K.inter (vtx K i) := le_iInf fun _ => le_rfl

theorem strictMono_pair {i j : K.ι} (hij : i < j) : StrictMono ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd hab (lt_irrefl _)
  · simpa using hij
  · exact absurd hab (by decide)
  · exact absurd hab (lt_irrefl _)

def edge {i j : K.ι} (hij : i < j) : K.Idx 1 := ⟨![i, j], strictMono_pair K hij⟩

theorem edge_val_zero {i j : K.ι} (hij : i < j) : (edge K hij).1 0 = i := rfl
theorem edge_val_one {i j : K.ι} (hij : i < j) : (edge K hij).1 1 = j := rfl

theorem face_edge_zero {i j : K.ι} (hij : i < j) : K.face (edge K hij) 0 = vtx K j :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

theorem face_edge_one {i j : K.ι} (hij : i < j) : K.face (edge K hij) 1 = vtx K i :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

theorem le_inter_edge {i j : K.ι} (hij : i < j) {W : V.Opens} (hi : W ≤ K.U i) (hj : W ≤ K.U j) :
    W ≤ K.inter (edge K hij) :=
  le_iInf fun k => by
    fin_cases k
    · exact hi
    · exact hj

end Simplices

theorem res_vtx_eq_of_d_eq_zero {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (X : OModulePresheaf π) (K : V.OrderedAffineCover) (a : X.cochain K 0) (hda : X.d K 0 a = 0)
    (i j : K.ι) {W : V.Opens} (hi : W ≤ K.inter (vtx K i)) (hj : W ≤ K.inter (vtx K j)) :
    X.res hi (a (vtx K i)) = X.res hj (a (vtx K j)) := by
  have tr : ∀ {s s' : K.Idx 0} (_ : s = s') {W : V.Opens} (h : W ≤ K.inter s) (h' : W ≤ K.inter s'),
      X.res h (a s) = X.res h' (a s') := by
    intro s s' e; subst e; intro W h h'; rfl
  have key : ∀ (i j : K.ι) (hij : i < j) {W : V.Opens} (hi : W ≤ K.inter (vtx K i)) (hj : W ≤ K.inter (vtx K j)),
      X.res hi (a (vtx K i)) = X.res hj (a (vtx K j)) := by
    intro i j hij W hi hj
    have h0 := congr_fun hda (edge K hij)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.zero_apply] at h0
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, add_neg_eq_zero] at h0
    have hW : W ≤ K.inter (edge K hij) :=
      le_inter_edge K hij (hi.trans (K.inter_le (vtx K i) 0)) (hj.trans (K.inter_le (vtx K j) 0))
    have h1 := congrArg (X.res hW) h0
    rw [X.res_res, X.res_res] at h1
    exact (tr (face_edge_one K hij) _ hi).symm.trans (h1.symm.trans (tr (face_edge_zero K hij) _ hj))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact key i j hij hi hj
  · rfl
  · exact (key j i hji hj hi).symm

set_option maxHeartbeats 4000000 in
theorem stageA
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] [IsLocallyNoetherian P]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ')) :
    ∃ (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
      (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
      (hpr : ∀ i : K.ι, Function.Surjective (pr i))
      (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
      (ℓ' : ∀ (i : K.ι) (k : ℕ), (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F k).obj (K.U i)),
      (∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
        X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j)))) ∧
      (∀ (i : K.ι) (k : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (φ k).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ' i (k + 1) v) = ℓ' i k v) ∧
      (∀ (i : K.ι) (k : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (ε k).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ' i k v) = (ψE k).app ⟨K.U i, K.isAffineOpen i⟩ (pr i v)) ∧
      (∀ (i : K.ι) (k : ℕ) (s : ↥(LinearMap.ker (pr i))),
        ℓ' i k (s : Fin (rk i) → Γ(P, K.U i)) = (lam k).app ⟨K.U i, K.isAffineOpen i⟩ (δ i s)) := by
  classical
  obtain ⟨K, rk, pr, hpr, ℓ, δs, t, ha, hb, hc, hd, he, hf, hg⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq
      lam hlamc hlamr hlami X hXc hXq εX hXf
  have hFF := AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
      I q X hXc hXq K t hf hg
  obtain ⟨a, ha', _⟩ := hFF
  have hda : X.d K 0 a = 0 := ha'.1
  have hat : ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 0)) := ha'.2

  have hrep : ∀ i : K.ι, ∃ δi : ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i),
      (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk δi) =
        X.res (le_inter_vtx K i) (a (vtx K i)) := fun i => by
    obtain ⟨δi, hδi⟩ := Quotient.exists_rep
      (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i) (X.res (le_inter_vtx K i) (a (vtx K i))))
    exact ⟨δi, by rw [LinearEquiv.symm_apply_eq]; exact hδi⟩
  choose δ hδa using hrep

  have hX1c : ∀ i : K.ι, ∃ ℓ' : ∀ k : ℕ, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F k).obj (K.U i),
      (∀ k, ((φ k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ((ε k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ ℓ' k = ((ψE k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ pr i) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker (pr i)).subtype = ((lam k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ δ i) := by
    intro i
    letI algi : Algebra A Γ(P, K.U i) := Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)
    haveI : IsNoetherianRing Γ(P, K.U i) := IsLocallyNoetherian.component_noetherian ⟨K.U i, K.isAffineOpen i⟩
    haveI : Module.Finite Γ(P, K.U i) (GK.obj (K.U i)) := hGKc ⟨K.U i, K.isAffineOpen i⟩
    refine LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
      (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) (pr i) (hpr i)
      (fun k => (F k).obj (K.U i)) (fun k => (E k).obj (K.U i))
      (fun k => (φ k).appSections ⟨K.U i, K.isAffineOpen i⟩) (fun k => hφs k ⟨K.U i, K.isAffineOpen i⟩) ?_
      (fun k => (ε k).appSections ⟨K.U i, K.isAffineOpen i⟩) (fun k => (ψE k).appSections ⟨K.U i, K.isAffineOpen i⟩)
      (fun k => (lam k).appSections ⟨K.U i, K.isAffineOpen i⟩) ?_ ?_
      (ℓ i) (fun n => LinearMap.ext fun v => ha i n v) (fun n => LinearMap.ext fun v => hb i n v)
      (δs i) (fun n => LinearMap.ext fun s => hc i n s) (hd i) (δ i) ?_
    ·
      intro k
      ext x
      rw [LinearMap.mem_ker, OModulePresheaf.AffHom.appSections_apply, ← LinearMap.mem_ker, hφk k ⟨K.U i, K.isAffineOpen i⟩]
      exact (mem_map_pow_smul_top_iff I (k + 1) x).symm
    · intro k
      exact LinearMap.ext fun x => LinearMap.congr_fun (hlamc k ⟨K.U i, K.isAffineOpen i⟩) x
    · intro k
      ext x
      have h := SetLike.ext_iff.mp (hlamr k ⟨K.U i, K.isAffineOpen i⟩) x
      simp only [LinearMap.mem_range, LinearMap.mem_ker] at h
      simp only [LinearMap.mem_range, LinearMap.mem_ker, OModulePresheaf.AffHom.appSections_apply]
      exact h
    ·
      intro n
      have h1 : (a - t n) (vtx K i) ∈ I ^ (n + 1) • (⊤ : Submodule A (X.obj (K.inter (vtx K i)))) :=
        mem_smul_top_map (I ^ (n + 1)) (LinearMap.proj (vtx K i)) (hat n)
      have e1 : X.res (le_inter_vtx K i) (t n (vtx K i)) =
          (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δs i n)) := by
        rw [he n (vtx K i), X.res_res]
        exact X.res_refl_apply _ _
      have h3 : (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i)) -
          (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δs i n)) ∈
          I ^ (n + 1) • (⊤ : Submodule A (X.obj (K.U i))) := by
        rw [hδa i, ← e1, ← map_sub]
        exact mem_smul_top_map _ _ h1
      have h4 : (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm
          (Submodule.Quotient.mk (δ i) - Submodule.Quotient.mk (δs i n)) ∈
          (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) ^ (n + 1) •
            (⊤ : Submodule Γ(P, K.U i) (X.obj (K.U i))) := by
        rw [map_sub]
        exact (mem_map_pow_smul_top_iff I (n + 1) _).mpr h3
      have h5 := mem_smul_top_map _ (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).toLinearMap h4
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← Submodule.Quotient.mk_sub] at h5
      exact mem_smul_top_sup_of_mkQ _ _ _ h5
  choose ℓ' hℓ'1 hℓ'2 hℓ'3 using hX1c
  refine ⟨K, rk, pr, hpr, δ, ℓ', ?_, ?_, ?_, ?_⟩
  · intro i j W hi hj
    rw [hδa i, hδa j, X.res_res, X.res_res]
    exact res_vtx_eq_of_d_eq_zero X K a hda i j _ _
  · intro i k v; exact LinearMap.congr_fun (hℓ'1 i k) v
  · intro i k v; exact LinearMap.congr_fun (hℓ'2 i k) v
  · intro i k s; exact LinearMap.congr_fun (hℓ'3 i k) s

end RedX1

open RedX1 in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (K : P.OrderedAffineCover)
      (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U))
      (iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U))
      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
      (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
          res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
      (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
      (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : M i U), res i (h.trans h') x = res i h (res i h' x))
      (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
              res i (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
      (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
      (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
      (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
      (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
      (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
      (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
          θF i k U (a • x) = a • θF i k U x)
      (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ i U' (GK.res h x) = res i h (ϑ i U x))
      (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θE i U' (res i h x) = GE.res h (θE i U x))
      (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θF i k U' (res i h x) = (F k).res h (θF i k U x))
      (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
      (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
      (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
      (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
      (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
      (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
      (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
          letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
      (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x),
      ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x := by
  classical
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨X, εX, hXc, hXq, hXf⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent q GE GK hGEc hGEq hGKc hGKq
  obtain ⟨K, rk, pr, hpr, δ, ℓ', hδ, hℓ'φ, hℓ'ε, hℓ'δ⟩ :=
    RedX1.stageA I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc
      GK hGKc hGKq lam hlamc hlamr hlami X hXc hXq εX hXf
  obtain ⟨prU, hprU, hprUs, gU, hgU, δU, hδU, hgUspan, hst, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE,
      hϑs, hθEs, hϑn, hθEn, hexact, hsurj, hϑi, u, hub, hus, hun, huϑ, huθE, hϑinl, hθEproj, hresinl, hresinr⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq
      q GE hGEc hGEq GK hGKc hGKq X hXc hXq εX hXf K rk pr hpr δ hδ
  letI instA : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
    fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap

  have split : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
      ∃ (n : GK.obj U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        x = LinearMap.ExtPushout.inl (prU i U) (δU i U) n + LinearMap.ExtPushout.inr (prU i U) (δU i U) v := by
    intro i U x
    obtain ⟨⟨n, v⟩, rfl⟩ := LinearMap.ExtPushout.mk_surjective (prU i U) (δU i U) x
    exact ⟨n, v, LinearMap.ExtPushout.mk_eq_inl_add_inr _ _ n v⟩

  have hprUe : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (m : Fin (rk i)),
      prU i U (e m) = GE.res U.2 (pr i (e m)) := by
    intro i U m
    have h := hprU i U (e m)
    rwa [show (fun m' => (P.presheaf.map (homOfLE U.2).op).hom (e m m')) = e m from
      funext fun m' => e_map _ m m'] at h

  have hspan_top : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      Submodule.span Γ(P, U.1.1) (Set.range (gU i U)) = ⊤ := by
    intro i U
    apply Submodule.map_injective_of_injective (LinearMap.ker (prU i U)).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
    exact hgUspan i U

  let w : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Fin (rk i) → (F k).obj U.1.1 :=
    fun i k U m => (F k).res U.2 (ℓ' i k (e m))
  have w_def : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (m : Fin (rk i)),
      w i k U m = (F k).res U.2 (ℓ' i k (e m)) := fun _ _ _ _ => rfl

  have compat' : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      ((lam k).appSections U.1) ∘ₗ (δU i U) =
        (Fintype.linearCombination _ (w i k U)) ∘ₗ (LinearMap.ker (prU i U)).subtype := by
    intro i k U
    refine LinearMap.ext_on_range (hspan_top i U) fun s₀ => ?_
    simp only [LinearMap.comp_apply, OModulePresheaf.AffHom.appSections_apply, Submodule.subtype_apply,
      Fintype.linearCombination_apply]
    rw [hδU, (lam k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, ← hℓ'δ,
      apply_eq_sum_e (ℓ' i k) (s₀ : Fin (rk i) → Γ(P, K.U i)), map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [w_def, hgU, (F k).res_smul]
  have compat : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (prU i U))),
      (lam k).appSections U.1 (δU i U s) = Fintype.linearCombination _ (w i k U) (s : Fin (rk i) → Γ(P, U.1.1)) :=
    fun i k U s => LinearMap.congr_fun (compat' i k U) s

  let θF := fun (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) =>
    theta (prU i U) (δU i U) ((lam k).appSections U.1) (w i k U) (compat i k U)
      (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1) ((F k).isScalarTower U.1.1)
  have θF_apply : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
      θF i k U x = thetaC (prU i U) (δU i U) ((lam k).appSections U.1) (w i k U) (compat i k U) x := fun _ _ _ _ => rfl
  have θinl : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (n : GK.obj U.1.1),
      θF i k U (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = (lam k).app U.1 n := by
    intro i k U n; rw [θF_apply, thetaC_inl]; rfl
  have θinr : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, U.1.1)),
      θF i k U (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) = ∑ m, v m • (F k).res U.2 (ℓ' i k (e m)) := by
    intro i k U v; rw [θF_apply, thetaC_inr]
  refine ⟨K, fun i U => LinearMap.ExtPushout (prU i U) (δU i U), fun i U => inferInstance,
    instA, fun i U => inferInstance,
    fun i U => isScalarTower_compHom (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1), res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF,
    hϑs, hθEs, ?_, hϑn, hθEn, ?_, hexact, hsurj, hϑi, ?_, ?_, ?_, u, hub, hus, hun, huϑ, huθE⟩
  ·
    intro i k U a x
    rw [θF_apply, θF_apply]
    exact map_smul _ a x
  ·
    intro i k U U' h x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [map_add, hresinl, hresinr, θinl, θinr]
    rw [(lam k).naturality_apply (U := U'.1) (U' := U.1) h, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(F k).res_smul, (F k).res_res]
  ·
    intro i k U
    apply LinearMap.ext
    intro x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [LinearMap.comp_apply, map_add, θinl, θinr]
    have h1 := LinearMap.congr_fun (hlamc k U.1) n
    rw [LinearMap.comp_apply] at h1
    rw [h1, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(φ k).app_smul, (φ k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hℓ'φ]
  ·
    intro i k U
    exact LinearMap.ext fun x => by rw [LinearMap.comp_apply, hϑinl, θinl]
  ·
    intro i k U
    apply LinearMap.ext
    intro x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [LinearMap.comp_apply, map_add, θinl, θinr, hθEproj, LinearMap.ExtPushout.proj_inl,
      LinearMap.ExtPushout.proj_inr, map_zero, zero_add]
    have h0 : (ε k).app U.1 ((lam k).app U.1 n) = 0 := by
      have hm : (lam k).app U.1 n ∈ LinearMap.range ((lam k).app U.1) := ⟨n, rfl⟩
      rw [hlamr k U.1] at hm
      exact hm
    rw [h0, zero_add, map_sum, apply_eq_sum_e (prU i U) v, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(ε k).app_smul, (ψE k).app_smul, (ε k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hℓ'ε,
      ← (ψE k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hprUe]

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (K : P.OrderedAffineCover)
      (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U))
      (iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U))
      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
      (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
          res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
      (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
      (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : M i U), res i (h.trans h') x = res i h (res i h' x))
      (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
              res i (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
      (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
      (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
      (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
      (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
      (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
      (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
          θF i k U (a • x) = a • θF i k U x)
      (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ i U' (GK.res h x) = res i h (ϑ i U x))
      (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θE i U' (res i h x) = GE.res h (θE i U x))
      (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θF i k U' (res i h x) = (F k).res h (θF i k U x))
      (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
      (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
      (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
      (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
      (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
      (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
      (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
          letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
      (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x),
      ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry"

noncomputable section

namespace ThickeningTransportAux

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
  have h__af := (D hq).toBase_preimage_eq_opensRange_ι U
  simp at h__af
  exact h__af

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

lemma Ψ_Φ (i : ℕ) (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) : Ψ hq K i (Φ hq K i c) = c := by
  funext s; exact (eY hq K s).symm_apply_apply (c s)

def dT (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) (s : K.Idx (i + 1)) : T F (K.inter s) :=
  ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • ρ F (K.inter_le_inter_face s j) (c (K.face s j))

lemma snd_dT (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) (s : K.Idx (i + 1)) :
    (dT K i c s).snd = F.d K i (fun t => (c t).snd) s := by
  rw [OModulePresheaf.d_apply, dT, snd_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (snd_smul _ _).trans (by rw [snd_ρ])

lemma fst_dT_inr (i : ℕ) (w : ∀ s : K.Idx i, F.obj (K.inter s)) (s : K.Idx (i + 1)) :
    (dT K i (fun t => inr (w t)) s).fst = 0 := by
  rw [dT, fst_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact (fst_smul _ _).trans (by rw [fst_ρ, fst_inr, map_zero, smul_zero])

lemma snd_dT_inr (i : ℕ) (w : ∀ s : K.Idx i, F.obj (K.inter s)) (s : K.Idx (i + 1)) :
    (dT K i (fun t => inr (w t)) s).snd = F.d K i w s := by
  rw [snd_dT]; rfl

lemma dT_inr (i : ℕ) (w : ∀ s : K.Idx i, F.obj (K.inter s)) (s : K.Idx (i + 1)) :
    dT K i (fun t => inr (w t)) s = inr (F.d K i w s) :=
  TrivSqZeroExt.ext (by rw [fst_dT_inr, fst_inr]) (by rw [snd_dT_inr, snd_inr])

lemma Φ_d (i : ℕ) (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) :
    Φ hq K (i + 1) ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) i c) = dT K i (Φ hq K i c) := by
  funext s
  rw [Φ, OModulePresheaf.d_apply, dT]
  change eY hq K s (∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
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

def L (i : ℕ) : F.cochain K i →ₗ[A] (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i where
  toFun z := Ψ hq K i fun s => inr (z s)
  map_add' z z' := by
    funext s
    change (eY hq K s).symm (inr (z s + z' s)) = (eY hq K s).symm (inr (z s)) + (eY hq K s).symm (inr (z' s))
    rw [inr_add, map_add]
  map_smul' a z := by
    funext s
    change (eY hq K s).symm (inr (a • z s)) = (show Γ(Y hq, (KY hq K).inter s) from
      a • (show (OModulePresheaf.unit (p hq ≫ q)).obj ((KY hq K).inter s) from (eY hq K s).symm (inr (z s))))
    rw [← σT_mul_inr, eY_symm_σT_mul]

lemma L_apply (i : ℕ) (z : F.cochain K i) : L hq K i z = Ψ hq K i fun s => inr (z s) := rfl

def Q (i : ℕ) : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i →ₗ[A] F.cochain K i where
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

lemma Q_apply (i : ℕ) (v : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) (s : K.Idx i) :
    Q hq K i v s = (Φ hq K i v s).snd := rfl

lemma Q_L (i : ℕ) (z : F.cochain K i) : Q hq K i (L hq K i z) = z := by
  funext s
  change (eY hq K s ((eY hq K s).symm (inr (z s)))).snd = z s
  rw [RingEquiv.apply_symm_apply, snd_inr]

lemma d_L (i : ℕ) (z : F.cochain K i) :
    (OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) i (L hq K i z) = L hq K (i + 1) (F.d K i z) := by
  have h1 : Φ hq K (i + 1) ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) i (L hq K i z)) =
      fun s => inr (F.d K i z s) := by
    rw [Φ_d, L_apply, Φ_Ψ]
    funext s
    rw [dT_inr]
  have h2 := congrArg (Ψ hq K (i + 1)) h1
  rw [Ψ_Φ] at h2
  rw [h2, L_apply]

lemma d_Q (i : ℕ) (v : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) :
    F.d K i (Q hq K i v) = Q hq K (i + 1) ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) i v) := by
  funext s
  change F.d K i (fun t => (Φ hq K i v t).snd) s = (Φ hq K (i + 1) ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) i v) s).snd
  rw [← snd_dT, ← Φ_d]

end Transport

end ThickeningTransportAux
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux"

open ThickeningTransportAux in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent) (K : P.OrderedAffineCover) :
    ∃ (Y : Scheme.{u}) (q' : Y ⟶ Spec (CommRingCat.of A)) (_ : IsProper q') (K' : Y.OrderedAffineCover)
      (L : ∀ j : ℕ, F.cochain K j →ₗ[A] (OModulePresheaf.unit q').cochain K' j)
      (Q : ∀ j : ℕ, (OModulePresheaf.unit q').cochain K' j →ₗ[A] F.cochain K j),
      (∀ (j : ℕ) (x : F.cochain K j), Q j (L j x) = x) ∧
      (∀ (j : ℕ) (x : F.cochain K j), (OModulePresheaf.unit q').d K' j (L j x) = L (j + 1) (F.d K j x)) ∧
      (∀ (j : ℕ) (y : (OModulePresheaf.unit q').cochain K' j),
        F.d K j (Q j y) = Q (j + 1) ((OModulePresheaf.unit q').d K' j y)) := by
  haveI : IsFinite (p (F := F) hqc) := isFinite_p hqc hc
  exact ⟨Y (F := F) hqc, p hqc ≫ q, inferInstance, KY hqc K, fun j => ThickeningTransportAux.L hqc K j,
    fun j => ThickeningTransportAux.Q hqc K j, fun j x => Q_L hqc K j x, fun j x => d_L hqc K j x, fun j y => d_Q hqc K j y⟩

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent) (K : P.OrderedAffineCover) :
    ∃ (Y : Scheme.{u}) (q' : Y ⟶ Spec (CommRingCat.of A)) (_ : IsProper q') (K' : Y.OrderedAffineCover)
      (L : ∀ j : ℕ, F.cochain K j →ₗ[A] (OModulePresheaf.unit q').cochain K' j)
      (Q : ∀ j : ℕ, (OModulePresheaf.unit q').cochain K' j →ₗ[A] F.cochain K j),
      (∀ (j : ℕ) (x : F.cochain K j), Q j (L j x) = x) ∧
      (∀ (j : ℕ) (x : F.cochain K j), (OModulePresheaf.unit q').d K' j (L j x) = L (j + 1) (F.d K j x)) ∧
      (∀ (j : ℕ) (y : (OModulePresheaf.unit q').cochain K' j),
        F.d K j (Q j y) = Q (j + 1) ((OModulePresheaf.unit q').d K' j y)) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, LinearMap.ker (F.d K (i + 1)) ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) ≤
      I ^ n • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
  classical
  obtain ⟨Y, q', hq', K', L, Q, hQL, hdL, hdQ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper q F hc hqc K
  haveI := hq'
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper I q' K' i n
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨hzZ, hzI⟩ := Submodule.mem_inf.mp hz

  have h1 : L (i + 1) z ∈ LinearMap.ker ((OModulePresheaf.unit q').d K' (i + 1)) ⊓
      I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').cochain K' (i + 1))) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, hdL, LinearMap.mem_ker.mp hzZ, map_zero]
    · have : (I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1)))).map (L (i + 1)) ≤
          I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').cochain K' (i + 1))) := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this (Submodule.mem_map_of_mem hzI)
  have h2 := hc' h1

  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
  have hzQ : z = Q (i + 1) u + Q (i + 1) v := by rw [← map_add, huv, hQL]
  rw [hzQ]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · have : (I ^ n • LinearMap.ker ((OModulePresheaf.unit q').d K' (i + 1))).map (Q (i + 1)) ≤
        I ^ n • LinearMap.ker (F.d K (i + 1)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [LinearMap.mem_ker, hdQ, LinearMap.mem_ker.mp hy, map_zero]
    exact this (Submodule.mem_map_of_mem hu)
  · obtain ⟨w, rfl⟩ := hv
    exact ⟨Q i w, (hdQ i w)⟩

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, LinearMap.ker (F.d K (i + 1)) ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) ≤
      I ^ n • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace D2Sol

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

end D2Sol

open D2Sol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (a : F.cochain K (i + 1)) (ha : F.d K (i + 1) a = 0)
    (h : ∀ n : ℕ, a ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    a ∈ LinearMap.range (F.d K i) := by
  classical
  set Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker (F.d K (i + 1)) with hZ
  set B : Submodule A (F.cochain K (i + 1)) := LinearMap.range (F.d K i) with hB
  have hdd : ∀ y : F.cochain K i, F.d K (i + 1) (F.d K i y) = 0 := fun y => by
    have := congrArg (fun φ => φ y) (AlgebraicGeometry.OModulePresheaf.d_comp_d F K i)
    simpa using this
  have hBZ : B ≤ Z := by
    rintro _ ⟨y, rfl⟩
    exact (LinearMap.mem_ker).mpr (hdd y)

  haveI : Module.Finite A (F.HSucc K i) := (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).2 i
  have hH : IsHausdorff I (F.HSucc K i) := IsHausdorff.of_le_jacobson I _ (IsAdicComplete.le_jacobson_bot I)

  have step : ∀ n : ℕ, a ∈ I ^ n • Z ⊔ B := by
    intro n
    obtain ⟨c, hc'⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper I q F hc hqc K i n
    obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.mp (h (n + c))
    have hu' : u ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _)) hu
    have huZ : u ∈ Z := by
      rw [LinearMap.mem_ker]
      have hbZ : b ∈ Z := hBZ hb
      rw [LinearMap.mem_ker] at hbZ
      have : u = a - b := by rw [← hub]; abel
      rw [this, map_sub, ha, hbZ, sub_zero]
    have := hc' ⟨huZ, hu'⟩
    rw [← hub]
    exact Submodule.add_mem _ this (Submodule.mem_sup_right hb)

  let W : Submodule A Z := B.comap Z.subtype
  let ahat : Z := ⟨a, (LinearMap.mem_ker).mpr ha⟩
  have hcls : ∀ n : ℕ, (Submodule.Quotient.mk ahat : Z ⧸ W) ∈ I ^ n • (⊤ : Submodule A (Z ⧸ W)) := by
    intro n
    obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.mp (step n)
    have hzZ : z ∈ Z := (Submodule.smul_le_right : I ^ n • Z ≤ Z) hz
    have hzhat : (⟨z, hzZ⟩ : Z) ∈ I ^ n • (⊤ : Submodule A Z) := (coe_mem_smul_iff (I ^ n) Z ⟨z, hzZ⟩).mp hz
    have hq : (Submodule.Quotient.mk ahat : Z ⧸ W) = Submodule.Quotient.mk ⟨z, hzZ⟩ := by
      rw [Submodule.Quotient.eq]
      show Z.subtype (ahat - ⟨z, hzZ⟩) ∈ B
      have : Z.subtype (ahat - ⟨z, hzZ⟩) = b := by
        simp only [map_sub, Submodule.coe_subtype]
        show a - z = b
        rw [← hzb]; abel
      rw [this]; exact hb
    rw [hq]
    have := Submodule.mem_map_of_mem (f := W.mkQ) hzhat
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
  have hzero : (Submodule.Quotient.mk ahat : Z ⧸ W) = 0 :=
    IsHausdorff.haus hH _ (fun n => by rw [SModEq.sub_mem, sub_zero]; exact hcls n)
  have hmem : ahat ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hzero
  exact hmem

end P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (a : F.cochain K (i + 1)) (ha : F.d K (i + 1) a = 0)
    (h : ∀ n : ℕ, a ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    a ∈ LinearMap.range (F.d K i) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem RedY1.cocycle_of_regimes {ι : Type*} [LinearOrder ι] (N : ι → Type*)
    (w : ∀ i j : ι, N i → N j)
    (v : ∀ i j : ι, i < j → N i → N j) (vi : ∀ i j : ι, i < j → N j → N i)
    (hlt : ∀ (i j : ι) (h : i < j) (x : N i), w i j x = v i j h x)
    (hgt : ∀ (i j : ι) (h : j < i) (x : N i), w i j x = vi j i h x)
    (heq : ∀ (i : ι) (x : N i), w i i x = x)
    (hvcoc : ∀ (i j l : ι) (h : i < j) (h' : j < l) (x : N i), v j l h' (v i j h x) = v i l (h.trans h') x)
    (hvi_v : ∀ (i j : ι) (h : i < j) (x : N i), vi i j h (v i j h x) = x)
    (hv_vi : ∀ (i j : ι) (h : i < j) (z : N j), v i j h (vi i j h z) = z) :
    ∀ (i j l : ι) (x : N i), w j l (w i j x) = w i l x := by

  have hgt₁ : ∀ (i j : ι) (h : j < i) (x : N i), v j i h (w i j x) = x := fun i j h x => by
    rw [hgt i j h, hv_vi]
  have hgt₂ : ∀ (i j : ι) (h : j < i) (y : N j), w i j (v j i h y) = y := fun i j h y => by
    rw [hgt i j h, hvi_v]
  intro i j l x
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    ·
      rw [hlt i j hij, hlt j l hjl, hlt i l (hij.trans hjl), hvcoc]
    ·
      rw [heq]
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        rw [hlt i j hij, hlt i l hil, ← hvcoc i l j hil hlj, hgt₂ j l hlj]
      ·
        rw [heq, hlt i j hij, hgt₂ j i hij]
      ·
        rw [hlt i j hij]
        have hx : x = v l i hli (w i l x) := (hgt₁ i l hli x).symm
        conv_lhs => rw [hx, hvcoc l i j hli hij, hgt₂ j l (hli.trans hij)]
  ·
    rw [heq]
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        rw [hlt j l hjl, hlt i l hil]
        have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
        conv_rhs => rw [hx, hvcoc j i l hji hil]
      ·
        rw [heq, hlt j i hji, hgt₁ i j hji]
      ·
        have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
        rw [hlt j l hjl]
        conv_rhs => rw [hx, ← hvcoc j l i hjl hli, hgt₂ i l hli]
    ·
      rw [heq]
    ·
      have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
      have hy : w i j x = v l j hlj (w j l (w i j x)) := (hgt₁ j l hlj _).symm
      have h3 : v l i (hlj.trans hji) (w j l (w i j x)) = x := by
        rw [← hvcoc l j i hlj hji, ← hy, ← hx]
      conv_rhs => rw [← h3]
      rw [hgt₂ i l (hlj.trans hji)]

theorem RedY1.cocAux {G : Type*} [AddCommGroup G] (a b c d e : G) (h : c - d + e = a - b) :
    a - c - e = b - d := by
  have h' : a = c - d + e + b := by rw [h, sub_add_cancel]
  rw [h']; abel

set_option maxHeartbeats 4000000 in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u' i j W hj (a • x) = a • u' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u' j l ⟨W.1, hj⟩ hl (u' i j W hj x) = u' i l W hl x) := by
  classical
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨hHc, hHq, -⟩ := OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq q GE GK hGEc hGEq hGKc hGKq
  obtain ⟨g, hg⟩ := AlgebraicGeometry.OModulePresheaf.exists_cochain_internalHom_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE
  have hdg := AlgebraicGeometry.OModulePresheaf.d_eq_zero_of_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE g hg
  have hform := AlgebraicGeometry.OModulePresheaf.mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE g hg
  obtain ⟨β, hβ⟩ := _root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    I q (OModulePresheaf.internalHom GE GK) hHc hHq K 1 g hdg hform
  let pr : ∀ (i j : K.ι), i < j → K.Idx 1 := fun i j h => ⟨![i, j], Fin.strictMono_iff_lt_succ.2 (fun a => by
    fin_cases a; simpa using h)⟩
  let tr : ∀ (i j l : K.ι), i < j → j < l → K.Idx 2 := fun i j l h h' => ⟨![i, j, l], Fin.strictMono_iff_lt_succ.2 (fun a => by
    fin_cases a
    · simpa using h
    · simpa using h')⟩
  have hpr : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens), W.1 ≤ K.U i → W.1 ≤ K.U j → W.1 ≤ K.inter (pr i j h) := by
    intro i j h W hi hj
    refine le_iInf fun a => ?_
    fin_cases a
    · exact hi
    · exact hj
  have htr : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens),
      W.1 ≤ K.U i → W.1 ≤ K.U j → W.1 ≤ K.U l → W.1 ≤ K.inter (tr i j l h h') := by
    intro i j l h h' W hi hj hl
    refine le_iInf fun a => ?_
    fin_cases a
    · exact hi
    · exact hj
    · exact hl
  have hface0 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 0 = pr j l h' := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hface1 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 1 = pr i l (h.trans h') := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hface2 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 2 = pr i j h := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hcomp : ∀ (s s' : K.Idx 1) (e : s = s') (W : P.affineOpens) (hW : W.1 ≤ K.inter s) (hW' : W.1 ≤ K.inter s'),
      (β s).1 ⟨W, hW⟩ = (β s').1 ⟨W, hW'⟩ := by
    intro s s' e W hW hW'; subst e; rfl
  have hres : ∀ {U U' : P.Opens} (h : U ≤ U') (c : (OModulePresheaf.internalHom GE GK).obj U')
      (W : {U₀ : P.affineOpens // U₀.1 ≤ U}),
      ((OModulePresheaf.internalHom GE GK).res h c).1 W = c.1 ⟨W.1, W.2.trans h⟩ := fun _ _ _ => rfl
  let βp : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens), W.1 ≤ K.U i → W.1 ≤ K.U j → (GE.obj W.1 →ₗ[A] GK.obj W.1) :=
    fun i j h W hi hj => (β (pr i j h)).1 ⟨W, hpr i j h W hi hj⟩
  have hkey : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hl : W.1 ≤ K.U l) (x : M i ⟨W, hi⟩),
      ϑ l ⟨W, hl⟩ (βp j l h' W hj hl (θE i ⟨W, hi⟩ x)) - ϑ l ⟨W, hl⟩ (βp i l (h.trans h') W hi hl (θE i ⟨W, hi⟩ x)) +
        ϑ l ⟨W, hl⟩ (βp i j h W hi hj (θE i ⟨W, hi⟩ x)) =
      u j l ⟨W, hj⟩ hl (u i j ⟨W, hi⟩ hj x) - u i l ⟨W, hi⟩ hl x := by
    intro i j l h h' W hi hj hl x
    have e1 := hg (tr i j l h h') ⟨W, htr i j l h h' W hi hj hl⟩ x
    rw [← hβ, OModulePresheaf.d_apply, Fin.sum_univ_three] at e1
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, pow_two, neg_mul, neg_neg, one_mul,
      one_smul, neg_smul] at e1
    change ϑ l ⟨W, hl⟩ ((((β (K.face (tr i j l h h') 0)).1 ⟨W, _⟩ + -((β (K.face (tr i j l h h') 1)).1 ⟨W, _⟩)) +
        (β (K.face (tr i j l h h') 2)).1 ⟨W, _⟩) (θE i ⟨W, hi⟩ x)) =
      u j l ⟨W, hj⟩ hl (u i j ⟨W, hi⟩ hj x) - u i l ⟨W, hi⟩ hl x at e1
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.neg_apply, map_add, map_add, map_neg,
      hcomp _ _ (hface0 i j l h h') W _ (hpr j l h' W hj hl), hcomp _ _ (hface1 i j l h h') W _ (hpr i l (h.trans h') W hi hl),
      hcomp _ _ (hface2 i j l h h') W _ (hpr i j h W hi hj)] at e1
    rw [← e1]
    simp only [βp]
    abel
  have hβps : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (y : GE.obj W.1), βp i j h W hi hj (a • y) = a • βp i j h W hi hj y :=
    fun i j h W hi hj a y => (β (pr i j h)).2.1 ⟨W, hpr i j h W hi hj⟩ a y
  have hβpn : ∀ (i j : K.ι) (h : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (hW : W'.1 ≤ W.1) (y : GE.obj W.1),
      βp i j h W' hi' hj' (GE.res hW y) = GK.res hW (βp i j h W hi hj y) :=
    fun i j h W W' hi hj hi' hj' hW y => (β (pr i j h)).2.2 ⟨W', hpr i j h W' hi' hj'⟩ ⟨W, hpr i j h W hi hj⟩ hW y
  clear_value βp

  have hθEϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (y : GK.obj U.1.1), θE i U (ϑ i U y) = 0 := by
    intro i U y
    have : ϑ i U y ∈ LinearMap.ker (θE i U) := by rw [← hexact]; exact ⟨y, rfl⟩
    exact this

  have huθE' : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (u i j ⟨W, hi⟩ hj x) = θE i ⟨W, hi⟩ x := fun i j W hi hj x => huθE i j ⟨W, hi⟩ hj x
  have huϑ' : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      u i j ⟨W, hi⟩ hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := fun i j W hi hj y => huϑ i j ⟨W, hi⟩ hj y

  have hfive : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (w : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩),
      (∀ y, w (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y) → (∀ x, θE j ⟨W, hj⟩ (w x) = θE i ⟨W, hi⟩ x) →
      Function.Bijective w := by
    intro i j W hi hj w hwϑ hwθ
    constructor
    · intro x x' hxx'
      rw [← sub_eq_zero] at hxx' ⊢
      rw [← map_sub] at hxx'
      have hk : x - x' ∈ LinearMap.ker (θE i ⟨W, hi⟩) := by
        rw [LinearMap.mem_ker, ← hwθ, hxx', map_zero]
      rw [← hexact] at hk
      obtain ⟨y, hy⟩ := hk
      rw [← hy] at hxx' ⊢
      rw [hwϑ] at hxx'
      rw [hϑi j ⟨W, hj⟩ (hxx'.trans (map_zero _).symm), map_zero]
    · intro z
      obtain ⟨x₀, hx₀⟩ := hsurj i ⟨W, hi⟩ (θE j ⟨W, hj⟩ z)
      have hk : z - w x₀ ∈ LinearMap.ker (θE j ⟨W, hj⟩) := by
        rw [LinearMap.mem_ker, map_sub, hwθ, hx₀, sub_self]
      rw [← hexact] at hk
      obtain ⟨y, hy⟩ := hk
      refine ⟨x₀ + ϑ i ⟨W, hi⟩ y, ?_⟩
      rw [map_add, hwϑ, hy, add_sub_cancel]

  let v : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩ :=
    fun i j h W hi hj => u i j ⟨W, hi⟩ hj - (ϑ j ⟨W, hj⟩ ∘ₗ βp i j h W hi hj ∘ₗ θE i ⟨W, hi⟩)
  have hv : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      v i j h W hi hj x = u i j ⟨W, hi⟩ hj x - ϑ j ⟨W, hj⟩ (βp i j h W hi hj (θE i ⟨W, hi⟩ x)) := fun _ _ _ _ _ _ _ => rfl
  clear_value v
  have hvϑ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      v i j h W hi hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := by
    intro i j h W hi hj y
    rw [hv i j h W hi hj, huϑ' i j W hi hj y, hθEϑ, map_zero, map_zero, sub_zero]
  have hvθ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (v i j h W hi hj x) = θE i ⟨W, hi⟩ x := by
    intro i j h W hi hj x
    rw [hv i j h W hi hj x, map_sub, huθE' i j W hi hj x, hθEϑ, sub_zero]
  have hvbij : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      Function.Bijective (v i j h W hi hj) :=
    fun i j h W hi hj => hfive i j W hi hj _ (hvϑ i j h W hi hj) (hvθ i j h W hi hj)

  have hvcoc : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hl : W.1 ≤ K.U l) (x : M i ⟨W, hi⟩),
      v j l h' W hj hl (v i j h W hi hj x) = v i l (h.trans h') W hi hl x := by
    intro i j l h h' W hi hj hl x
    have k := hkey i j l h h' W hi hj hl x
    rw [hv i j h W hi hj x, (v j l h' W hj hl).map_sub, hvϑ j l h' W hj hl, hv j l h' W hj hl, hv i l (h.trans h') W hi hl x,
      huθE' i j W hi hj x]
    exact RedY1.cocAux _ _ _ _ _ k

  obtain ⟨vi, hvi_v, hv_vi⟩ : ∃ vi : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      M j ⟨W, hj⟩ →ₗ[A] M i ⟨W, hi⟩,
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
        vi i j h W hi hj (v i j h W hi hj x) = x) ∧
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (z : M j ⟨W, hj⟩),
        v i j h W hi hj (vi i j h W hi hj z) = z) := by
    refine ⟨fun i j h W hi hj =>
        ((LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm : M j ⟨W, hj⟩ →ₗ[A] M i ⟨W, hi⟩), ?_, ?_⟩
    · intro i j h W hi hj x
      change (LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm (v i j h W hi hj x) = x
      rw [← LinearEquiv.ofBijective_apply (v i j h W hi hj) (hf := hvbij i j h W hi hj) x]
      exact LinearEquiv.symm_apply_apply _ _
    · intro i j h W hi hj z
      change v i j h W hi hj ((LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm z) = z
      rw [← LinearEquiv.ofBijective_apply (v i j h W hi hj) (hf := hvbij i j h W hi hj)]
      exact LinearEquiv.apply_symm_apply _ _
  have hviϑ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      vi i j h W hi hj (ϑ j ⟨W, hj⟩ y) = ϑ i ⟨W, hi⟩ y := by
    intro i j h W hi hj y
    apply (hvbij i j h W hi hj).1
    rw [hv_vi, hvϑ]
  have hviθ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (z : M j ⟨W, hj⟩),
      θE i ⟨W, hi⟩ (vi i j h W hi hj z) = θE j ⟨W, hj⟩ z := by
    intro i j h W hi hj z
    conv_rhs => rw [← hv_vi i j h W hi hj z]
    rw [hvθ]

  have hvs : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (x : M i ⟨W, hi⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      v i j h W hi hj (a • x) = a • v i j h W hi hj x := by
    intro i j h W hi hj a x
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    rw [hv, hv, hus i j ⟨W, hi⟩ hj a x, hθEs i ⟨W, hi⟩ a x, hβps i j h W hi hj a, hϑs j ⟨W, hj⟩ a, smul_sub]
  have hvis : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (z : M j ⟨W, hj⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      vi i j h W hi hj (a • z) = a • vi i j h W hi hj z := by
    intro i j h W hi hj a z
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    apply (hvbij i j h W hi hj).1
    rw [hv_vi, hvs, hv_vi]
  have hvn : ∀ (i j : K.ι) (hij : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (h : W'.1 ≤ W.1) (x : M i ⟨W, hi⟩),
      v i j hij W' hi' hj' (res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h x) =
        res j (U := ⟨W, hj⟩) (U' := ⟨W', hj'⟩) h (v i j hij W hi hj x) := by
    intro i j hij W W' hi hj hi' hj' h x
    rw [hv, hv, map_sub (res j _), hun i j ⟨W, hi⟩ ⟨W', hi'⟩ hj h x, hθEn i ⟨W, hi⟩ ⟨W', hi'⟩ h x,
      hβpn i j hij W W' hi hj hi' hj' h, hϑn j ⟨W, hj⟩ ⟨W', hj'⟩ h]
  have hvin : ∀ (i j : K.ι) (hij : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (h : W'.1 ≤ W.1) (z : M j ⟨W, hj⟩),
      vi i j hij W' hi' hj' (res j (U := ⟨W, hj⟩) (U' := ⟨W', hj'⟩) h z) =
        res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h (vi i j hij W hi hj z) := by
    intro i j hij W W' hi hj hi' hj' h z
    apply (hvbij i j hij W' hi' hj').1
    rw [hv_vi, hvn i j hij W W' hi hj hi' hj' h, hv_vi]

  have hEU : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (b : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩), (∀ y, b (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y) → (∀ x, θE j ⟨W, hj⟩ (b x) = θE i ⟨W, hi⟩ x) →
      ∃! γ : GE.obj W.1 →ₗ[A] GK.obj W.1, u i j ⟨W, hi⟩ hj - b = ϑ j ⟨W, hj⟩ ∘ₗ γ ∘ₗ θE i ⟨W, hi⟩ := by
    intro i j W hi hj b hbϑ hbθ
    refine LinearMap.existsUnique_sub_eq_comp_comp_of_extension (ϑ i ⟨W, hi⟩) (θE i ⟨W, hi⟩) (ϑ j ⟨W, hj⟩) (θE j ⟨W, hj⟩)
      (hsurj _ _) (hexact _ _) (hϑi _ _) (hexact _ _) _ _ ?_ ?_
    · ext y; simp only [LinearMap.coe_comp, Function.comp_apply]; rw [huϑ', hbϑ]
    · ext y; simp only [LinearMap.coe_comp, Function.comp_apply]; rw [huθE', hbθ]
  have hdiag : ∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i),
      ∃! γ : GE.obj W.1 →ₗ[A] GK.obj W.1,
        u i i ⟨W, hi⟩ hj - LinearMap.id = ϑ i ⟨W, hj⟩ ∘ₗ γ ∘ₗ θE i ⟨W, hi⟩ :=
    fun i W hi hj => hEU i i W hi hj LinearMap.id (fun _ => rfl) (fun _ => rfl)

  obtain ⟨βt, hβt_lt, hβt_gt, hβt_eq⟩ : ∃ βt : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      GE.obj W.1 →ₗ[A] GK.obj W.1,
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        βt i j W hi hj = βp i j h W hi hj) ∧
      (∀ (i j : K.ι) (h : j < i) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        u i j ⟨W, hi⟩ hj - vi j i h W hj hi = ϑ j ⟨W, hj⟩ ∘ₗ βt i j W hi hj ∘ₗ θE i ⟨W, hi⟩) ∧
      (∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i),
        u i i ⟨W, hi⟩ hj - LinearMap.id = ϑ i ⟨W, hj⟩ ∘ₗ βt i i W hi hj ∘ₗ θE i ⟨W, hi⟩) := by
    refine ⟨fun i j W hi hj =>
      if hij : i < j then βp i j hij W hi hj
      else if hji : j < i then
        (hEU i j W hi hj (vi j i hji W hj hi) (hviϑ j i hji W hj hi) (hviθ j i hji W hj hi)).exists.choose
      else (hdiag i W hi ((le_antisymm (not_lt.mp hji) (not_lt.mp hij)) ▸ hj)).exists.choose, ?_, ?_, ?_⟩
    · intro i j h W hi hj
      simp only [dif_pos h]
    · intro i j h W hi hj
      simp only [dif_neg (not_lt_of_gt h), dif_pos h]
      exact (hEU i j W hi hj (vi j i h W hj hi) (hviϑ j i h W hj hi) (hviθ j i h W hj hi)).exists.choose_spec
    · intro i W hi hj
      simp only [dif_neg (lt_irrefl i)]
      exact (hdiag i W hi hj).exists.choose_spec
  clear hdiag

  obtain ⟨u', hu'⟩ : ∃ u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j),
      M i W →ₗ[A] M j ⟨W.1, hj⟩,
      ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
        u' i j ⟨W, hi⟩ hj x = u i j ⟨W, hi⟩ hj x - ϑ j ⟨W, hj⟩ (βt i j W hi hj (θE i ⟨W, hi⟩ x)) :=
    ⟨fun i j W hj => u i j W hj - (ϑ j ⟨W.1, hj⟩ ∘ₗ βt i j W.1 W.2 hj ∘ₗ θE i W), fun _ _ _ _ _ _ => rfl⟩

  have hu'_lt : ∀ (i j : K.ι) (hij : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      u' i j ⟨W, hi⟩ hj x = v i j hij W hi hj x := by
    intro i j hij W hi hj x
    rw [hu', hβt_lt i j hij, hv]
  have hu'_gt : ∀ (i j : K.ι) (hji : j < i) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      u' i j ⟨W, hi⟩ hj x = vi j i hji W hj hi x := by
    intro i j hji W hi hj x
    have e := congrArg (fun f : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩ => f x) (hβt_gt i j hji W hi hj)
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at e
    rw [hu', ← e, sub_sub_cancel]
  have hu'_eq : ∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i) (x : M i ⟨W, hi⟩), u' i i ⟨W, hi⟩ hj x = x := by
    intro i W hi hj x
    have e := congrArg (fun f : M i ⟨W, hi⟩ →ₗ[A] M i ⟨W, hj⟩ => f x) (hβt_eq i W hi hj)
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at e
    rw [hu', ← e, sub_sub_cancel]

  have hu'ϑ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      u' i j ⟨W, hi⟩ hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := by
    intro i j W hi hj y
    rw [hu', huϑ' i j W hi hj, hθEϑ, map_zero, map_zero, sub_zero]
  have hu'θ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (u' i j ⟨W, hi⟩ hj x) = θE i ⟨W, hi⟩ x := by
    intro i j W hi hj x
    rw [hu', map_sub, huθE' i j W hi hj, hθEϑ, sub_zero]
  have hu'bij : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      Function.Bijective (u' i j ⟨W, hi⟩ hj) :=
    fun i j W hi hj => hfive i j W hi hj _ (hu'ϑ i j W hi hj) (hu'θ i j W hi hj)

  have hu's : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (a : Γ(P, W.1))
      (x : M i ⟨W, hi⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      u' i j ⟨W, hi⟩ hj (a • x) = a • u' i j ⟨W, hi⟩ hj x := by
    intro i j W hi hj a x
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hu'_lt i j hij, hu'_lt i j hij, hvs]
    · rw [hu'_eq, hu'_eq]
    · rw [hu'_gt i j hji, hu'_gt i j hji, hvis]

  have hu'n : ∀ (i j : K.ι) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (hi' : W'.1 ≤ K.U i)
      (h : W'.1 ≤ W.1) (x : M i ⟨W, hi⟩),
      u' i j ⟨W', hi'⟩ (h.trans hj) (res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h x) =
        res j (U := ⟨W, hj⟩) (U' := ⟨W', h.trans hj⟩) h (u' i j ⟨W, hi⟩ hj x) := by
    intro i j W W' hi hj hi' h x
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hu'_lt i j hij, hu'_lt i j hij]; exact hvn i j hij W W' hi hj hi' (h.trans hj) h x
    · rw [hu'_eq, hu'_eq]
    · rw [hu'_gt i j hji, hu'_gt i j hji]; exact hvin j i hji W W' hj hi (h.trans hj) hi' h x

  have hcoc : ∀ (i j l : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (hl : W.1 ≤ K.U l)
      (x : M i ⟨W, hi⟩), u' j l ⟨W, hj⟩ hl (u' i j ⟨W, hi⟩ hj x) = u' i l ⟨W, hi⟩ hl x := by
    intro i j l W hi hj hl x
    exact RedY1.cocycle_of_regimes (ι := {i : K.ι // W.1 ≤ K.U i}) (fun i => M i.1 ⟨W, i.2⟩)
      (fun i j => u' i.1 j.1 ⟨W, i.2⟩ j.2) (fun i j h => v i.1 j.1 h W i.2 j.2) (fun i j h => vi i.1 j.1 h W i.2 j.2)
      (fun i j h x => hu'_lt i.1 j.1 h W i.2 j.2 x) (fun i j h x => hu'_gt i.1 j.1 h W i.2 j.2 x)
      (fun i x => hu'_eq i.1 W i.2 i.2 x)
      (fun i j l h h' x => hvcoc i.1 j.1 l.1 h h' W i.2 j.2 l.2 x)
      (fun i j h x => hvi_v i.1 j.1 h W i.2 j.2 x) (fun i j h z => hv_vi i.1 j.1 h W i.2 j.2 z)
      ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hl⟩ x
  refine ⟨u', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i j ⟨W, hi⟩ hj; exact hu'bij i j W hi hj
  · rintro i j ⟨W, hi⟩ hj a x; exact hu's i j W hi hj a x
  · rintro i j ⟨W, hi⟩ ⟨W', hi'⟩ hj h x; exact hu'n i j W W' hi hj hi' h x
  · rintro i j ⟨W, hi⟩ hj y; exact hu'ϑ i j W hi hj y
  · rintro i j ⟨W, hi⟩ hj x; exact hu'θ i j W hi hj x
  · rintro i j l ⟨W, hi⟩ hj hl x; exact hcoc i j l W hi hj hl x

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u' i j W hj (a • x) = a • u' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u' j l ⟨W.1, hj⟩ hl (u' i j W hj x) = u' i l W hl x) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace G2Sol

theorem apply_mem_smul_top {A : Type*} [CommRing A] {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i} (hx : x ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    x i ∈ J • (⊤ : Submodule A (M i)) := by
  have := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (∀ i, M i) →ₗ[A] M i)) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem mem_smul_top_of_forall {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ J • (⊤ : Submodule A (M i))) : x ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  have hsum : x = ∑ i, (LinearMap.single A M i) (x i) := by
    ext j
    simp [Finset.sum_apply, LinearMap.single_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := Submodule.mem_map_of_mem (f := (LinearMap.single A M i : M i →ₗ[A] ∀ i, M i)) (hx i)
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem map_mem_smul_top {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (J : Ideal A) {x : M}
    (hx : x ∈ J • (⊤ : Submodule A M)) : f x ∈ J • (⊤ : Submodule A N) := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end G2Sol

open G2Sol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K (i + 1),
      (∀ s : K.Idx (i + 2), F.d K (i + 1) w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K (i + 1),
        (∀ s : K.Idx (i + 1), w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K (i + 1) w' = F.d K (i + 1) w := by
  classical
  obtain ⟨Y, q', hq', K', L, Q, hQL, hdL, hdQ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper q F hc hq K
  haveI : IsProper q' := hq'
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper I q' K' i n
  refine ⟨c, fun w hw => ?_⟩
  have hdw : F.d K (i + 1) w ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1 + 1))) :=
    mem_smul_top_of_forall _ hw
  have h1 : ∀ s : K'.Idx (i + 2), (OModulePresheaf.unit q').d K' (i + 1) (L (i + 1) w) s ∈
      I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').obj (K'.inter s))) := by
    intro s
    rw [hdL]
    exact apply_mem_smul_top _ (map_mem_smul_top (L (i + 1 + 1)) _ hdw) s
  obtain ⟨v', hv'1, hv'2⟩ := hc' (L (i + 1) w) h1
  refine ⟨Q (i + 1) v', fun s => ?_, ?_⟩
  · exact apply_mem_smul_top _ (map_mem_smul_top (Q (i + 1)) _ (mem_smul_top_of_forall _ hv'1)) s
  · rw [hdQ, hv'2, hdL, hQL]

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K (i + 1),
      (∀ s : K.Idx (i + 2), F.d K (i + 1) w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K (i + 1),
        (∀ s : K.Idx (i + 1), w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K (i + 1) w' = F.d K (i + 1) w := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace G1Sol

theorem apply_mem_smul_top {A : Type*} [CommRing A] {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i} (hx : x ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    x i ∈ J • (⊤ : Submodule A (M i)) := by
  have := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (∀ i, M i) →ₗ[A] M i)) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem mem_smul_top_of_forall {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ J • (⊤ : Submodule A (M i))) : x ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  have hsum : x = ∑ i, (LinearMap.single A M i) (x i) := by
    ext j
    simp [Finset.sum_apply, LinearMap.single_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := Submodule.mem_map_of_mem (f := (LinearMap.single A M i : M i →ₗ[A] ∀ i, M i)) (hx i)
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end G1Sol

open G1Sol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K (i + 1),
      F.d K (i + 1) t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 2))) →
      ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
        t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K (i + 1))) := by
  classical
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper I F hc hqc K i n
  refine ⟨c, fun t ht => ?_⟩
  obtain ⟨w', hw'1, hw'2⟩ := hc' t (fun s => apply_mem_smul_top (I ^ (n + c)) ht s)
  refine ⟨t - w', ?_, ?_⟩
  · rw [map_sub, hw'2, sub_self]
  · rw [sub_sub_cancel]
    exact mem_smul_top_of_forall (I ^ n) hw'1

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K (i + 1),
      F.d K (i + 1) t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 2))) →
      ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
        t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K (i + 1))) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈
      I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i) := by
  classical

  set d1 := F.d K (i + 1) with hd1
  set d0 := F.d K i with hd0
  let Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker d1
  let B : Submodule A (F.cochain K (i + 1)) := LinearMap.range d0
  let S : ℕ → Submodule A (F.cochain K (i + 1)) := fun n => I ^ (n + 1) • ⊤ ⊔ B
  have hBZ : B ≤ Z := by
    rintro _ ⟨c, rfl⟩
    show d1 (d0 c) = 0
    have := LinearMap.congr_fun (AlgebraicGeometry.OModulePresheaf.d_comp_d F K i) c
    rw [hd1, hd0]
    simpa using this
  have hSanti : ∀ {n m : ℕ}, n ≤ m → S m ≤ S n := fun {n m} h =>
    sup_le_sup_right (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _

  have htt : ∀ (n m : ℕ), n ≤ m → t m - t n ∈ S n := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ m hnm ih =>
      have h1 : t (m + 1) - t m ∈ S n := hSanti hnm (ht m)
      have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
      rw [this]; exact add_mem h1 ih

  have hG1 : ∀ n : ℕ, ∃ z : F.cochain K (i + 1), d1 z = 0 ∧ z - t n ∈ S n := by
    intro n
    obtain ⟨c₁, hc₁⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
      I q F hc hqc K i (n + 1)
    have hdt : F.d K (i + 1) (t (n + c₁)) ∈ I ^ (n + 1 + c₁) • (⊤ : Submodule A (F.cochain K (i + 2))) := by
      have := hd (n + c₁); rwa [show n + c₁ + 1 = n + 1 + c₁ by omega] at this
    obtain ⟨a, ha, hta⟩ := hc₁ (t (n + c₁)) hdt
    refine ⟨a, by rw [hd1]; exact ha, ?_⟩
    have h1 : a - t (n + c₁) ∈ S n := by
      refine Submodule.mem_sup_left ?_
      rw [← neg_sub]; exact Submodule.neg_mem _ hta
    have h2 : t (n + c₁) - t n ∈ S n := htt n (n + c₁) (Nat.le_add_right n c₁)
    have : a - t n = (a - t (n + c₁)) + (t (n + c₁) - t n) := by abel
    rw [this]; exact add_mem h1 h2
  choose z hz hzt using hG1
  have hzz : ∀ (n m : ℕ), n ≤ m → z m - z n ∈ S n := by
    intro n m hnm
    have : z m - z n = (z m - t m) + (t m - t n) - (z n - t n) := by abel
    rw [this]
    exact sub_mem (add_mem (hSanti hnm (hzt m)) (htt n m hnm)) (hzt n)

  have hG3 := fun k : ℕ =>
    AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper I q F hc hqc K i k
  choose c₃ hc₃ using hG3
  let cm : ℕ → ℕ := fun k => Nat.rec (c₃ 0) (fun k ih => max ih (c₃ (k + 1))) k
  have hcm0 : cm 0 = c₃ 0 := rfl
  have hcms : ∀ k, cm (k + 1) = max (cm k) (c₃ (k + 1)) := fun k => rfl
  have hcm_ge : ∀ k, c₃ k ≤ cm k := by
    intro k; cases k with
    | zero => rw [hcm0]
    | succ k => rw [hcms]; exact le_max_right _ _
  have hcm_mono : ∀ k, cm k ≤ cm (k + 1) := fun k => by rw [hcms]; exact le_max_left _ _
  let Mx : ℕ → ℕ := fun k => k + cm k
  have hMmono : ∀ k, Mx k ≤ Mx (k + 1) := fun k => by
    show k + cm k ≤ k + 1 + cm (k + 1); have := hcm_mono k; omega
  have hMge : ∀ k, k ≤ Mx k := fun k => Nat.le_add_right k _
  have hG3' : ∀ (k : ℕ) (y : F.cochain K (i + 1)), d1 y = 0 →
      y ∈ (I ^ (k + cm k) • ⊤ : Submodule A (F.cochain K (i + 1))) →
      y ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k y hy hmem
    apply hc₃ k
    refine ⟨by rw [← hd1]; exact hy, ?_⟩
    exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by have := hcm_ge k; omega))) hmem

  let w : ℕ → F.cochain K (i + 1) := fun k => z (Mx k)
  have hwz : ∀ k, d1 (w k) = 0 := fun k => hz (Mx k)
  have hw : ∀ k, w (k + 1) - w k ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k
    have hy : w (k + 1) - w k ∈ S (Mx k) := hzz (Mx k) (Mx (k + 1)) (hMmono k)
    obtain ⟨v, hv, b, hb, hvb⟩ := Submodule.mem_sup.mp hy
    have hb0 : d1 b = 0 := hBZ hb
    have hvZ : d1 v = 0 := by
      have hv' : v = (w (k + 1) - w k) - b := by rw [← hvb]; abel
      rw [hv', map_sub, map_sub, hb0, sub_zero, hwz, hwz, sub_self]
    have hvmem : v ∈ (I ^ (k + cm k) • ⊤ : Submodule A (F.cochain K (i + 1))) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by change k + cm k ≤ k + cm k + 1; omega))) hv
    rw [← hvb]
    exact add_mem (hG3' k v hvZ hvmem) (Submodule.mem_sup_right hb)

  let Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker (F.d K (i + 1))
  let B' : Submodule A Z := (LinearMap.range (F.d K i)).comap Z.subtype
  have hZsmul : ∀ k : ℕ, I ^ k • LinearMap.ker (F.d K (i + 1)) =
      Submodule.map Z.subtype (I ^ k • (⊤ : Submodule A Z)) := fun k => by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  have hHsmul : ∀ k : ℕ, (I ^ k • (⊤ : Submodule A (F.HSucc K i))) =
      Submodule.map (Submodule.mkQ B') (I ^ k • (⊤ : Submodule A Z)) := fun k => by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

  have T1 : ∀ (k : ℕ) (x : Z), (x : F.cochain K (i + 1)) ∈
      I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) →
      (Submodule.mkQ B' x : F.HSucc K i) ∈ I ^ k • (⊤ : Submodule A (F.HSucc K i)) := by
    intro k x hx
    obtain ⟨v, hv, b, hb, hvb⟩ := Submodule.mem_sup.mp hx
    rw [hZsmul] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    have hxv : x - v' ∈ B' := by
      show Z.subtype (x - v') ∈ LinearMap.range (F.d K i)
      have : Z.subtype (x - v') = b := by
        rw [map_sub]
        simp only [Submodule.coe_subtype]
        rw [← hvb]
        simp
      rw [this]; exact hb
    have hx' : Submodule.mkQ B' x = Submodule.mkQ B' v' := by
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxv
    rw [hx', hHsmul]
    exact ⟨v', hv', rfl⟩

  have T2 : ∀ (k : ℕ) (x : Z), (Submodule.mkQ B' x : F.HSucc K i) ∈ I ^ k • (⊤ : Submodule A (F.HSucc K i)) →
      (x : F.cochain K (i + 1)) ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k x hx
    rw [hHsmul] at hx
    obtain ⟨v', hv', hvx⟩ := hx
    have hxv : x - v' ∈ B' := by
      rw [← Submodule.Quotient.eq]
      exact hvx.symm
    have hb : (Z.subtype x) - (Z.subtype v') ∈ LinearMap.range (F.d K i) := by
      rw [← map_sub]; exact hxv
    have hv : (Z.subtype v') ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) := by
      rw [hZsmul]; exact ⟨v', hv', rfl⟩
    have : (x : F.cochain K (i + 1)) = Z.subtype v' + (Z.subtype x - Z.subtype v') := by simp
    rw [this]
    exact add_mem (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hb)
  haveI hfin : Module.Finite A (F.HSucc K i) :=
    (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).2 i
  have hcomplete : IsAdicComplete I (F.HSucc K i) := IsAdicComplete.of_module_finite I (F.HSucc K i)

  let ζ : ℕ → Z := fun k => ⟨w k, LinearMap.mem_ker.mpr (by rw [← hd1]; exact hwz k)⟩
  let g : ℕ → F.HSucc K i := fun k => Submodule.mkQ B' (ζ k)
  have hg : ∀ k, g k ≡ g (k + 1) [SMOD (I ^ k • ⊤ : Submodule A (F.HSucc K i))] := by
    intro k
    rw [SModEq.sub_mem]
    show Submodule.mkQ B' (ζ k) - Submodule.mkQ B' (ζ (k + 1)) ∈ _
    rw [← map_sub]
    apply T1
    have : ((ζ k - ζ (k + 1) : Z) : F.cochain K (i + 1)) = -(w (k + 1) - w k) := by
      simp [ζ]
    rw [this]
    exact Submodule.neg_mem _ (hw k)
  have hcau : AdicCompletion.IsAdicCauchy I (F.HSucc K i) g := (AdicCompletion.isAdicCauchy_iff I _ g).mpr hg
  obtain ⟨L, hL⟩ := hcomplete.toIsPrecomplete.prec hcau
  obtain ⟨ζL, hζL⟩ := Submodule.Quotient.mk_surjective B' L

  refine ⟨(ζL : F.cochain K (i + 1)), ζL.2, fun n => ?_⟩
  have h1 : (w (n + 1) - (ζL : F.cochain K (i + 1))) ∈ S n := by
    have hmem : (Submodule.mkQ B' (ζ (n + 1) - ζL) : F.HSucc K i) ∈
        I ^ (n + 1) • (⊤ : Submodule A (F.HSucc K i)) := by
      rw [map_sub]
      have := (SModEq.sub_mem).mp (hL (n + 1))
      rw [← hζL] at this
      exact this
    have h := T2 (n + 1) (ζ (n + 1) - ζL) hmem
    have hcoe : ((ζ (n + 1) - ζL : Z) : F.cochain K (i + 1)) = w (n + 1) - (ζL : F.cochain K (i + 1)) := by
      simp [ζ]
    rw [hcoe] at h
    have hle : I ^ (n + 1) • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) ≤ S n :=
      sup_le_sup_right (smul_mono_right _ le_top) _
    exact hle h
  have h2 : w (n + 1) - t n ∈ S n := by
    have : w (n + 1) - t n = (z (Mx (n + 1)) - t (Mx (n + 1))) + (t (Mx (n + 1)) - t n) := by
      show z (Mx (n + 1)) - t n = _; abel
    rw [this]
    have hle : n ≤ Mx (n + 1) := by have := hMge (n + 1); omega
    exact add_mem (hSanti hle (hzt _)) (htt n _ hle)
  have : (ζL : F.cochain K (i + 1)) - t n = -(w (n + 1) - (ζL : F.cochain K (i + 1))) + (w (n + 1) - t n) := by
    abel
  rw [this]
  exact add_mem (Submodule.neg_mem _ h1) h2

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈
      I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace D1sAux

def env (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => c 0
  | n + 1 => max (env c n) (c (n + 1))

theorem le_env (c : ℕ → ℕ) : ∀ n, c n ≤ env c n
  | 0 => le_rfl
  | _ + 1 => le_max_right _ _

theorem env_mono (c : ℕ → ℕ) : Monotone (env c) :=
  monotone_nat_of_le_succ fun n => show env c n ≤ max (env c n) (c (n + 1)) from le_max_left _ _

end D1sAux

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) :
    ∃ (a : F.cochain K (i + 1)) (Y : ℕ → F.cochain K i), F.d K (i + 1) a = 0 ∧
      (∀ n : ℕ, t n - a - F.d K i (Y n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) ∧
      (∀ n : ℕ, Y (n + 1) - Y n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K i))) := by
  classical

  let J : ℕ → Submodule A (F.cochain K (i + 1)) := fun n => I ^ n • ⊤
  have hJ : ∀ {m n : ℕ}, m ≤ n → J n ≤ J m := fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  let J₀ : ℕ → Submodule A (F.cochain K i) := fun n => I ^ n • ⊤
  have hJ₀ : ∀ {m n : ℕ}, m ≤ n → J₀ n ≤ J₀ m := fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

  have htele : ∀ {n m : ℕ}, n ≤ m → t m - t n ∈ J (n + 1) := by
    intro n m h
    induction h with
    | refl => simp
    | @step m hnm ih =>
      have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
      rw [this]
      exact Submodule.add_mem _ (hJ (Nat.succ_le_succ hnm) (ht m)) ih

  have hML : ∀ n : ℕ, ∃ c : ℕ, ∀ w : (F.cochain K i), F.d K i w ∈ J (n + c) →
      ∃ z : (F.cochain K i), F.d K i z = 0 ∧ w - z ∈ J₀ n := by
    intro n
    cases i with
    | zero =>
      exact AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper I q F hc hqc K n
    | succ j =>
      exact AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper I q F hc hqc K j n
  choose c hc' using hML

  obtain ⟨a, hda, ha⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
      I q F hc hqc K i t hd (fun n => Submodule.mem_sup_left (ht n))
  have hy : ∀ n, ∃ y : (F.cochain K i), t n - a - F.d K i y ∈ J (n + 1) := by
    intro n
    obtain ⟨e, he, b, ⟨y, rfl⟩, heb⟩ := Submodule.mem_sup.mp (ha n)
    refine ⟨-y, ?_⟩
    have : t n - a - F.d K i (-y) = -(a - t n - F.d K i y) := by rw [map_neg]; abel
    rw [this]
    refine Submodule.neg_mem _ ?_
    have : a - t n - F.d K i y = e := by rw [← heb]; abel
    rw [this]; exact he
  choose y hy' using hy

  let m : ℕ → ℕ := D1sAux.env fun n => n + 1 + c (n + 1)
  have hm : ∀ n, n + 1 + c (n + 1) ≤ m n := fun n => D1sAux.le_env (fun k => k + 1 + c (k + 1)) n
  have hmn : ∀ n, n ≤ m n := fun n => le_trans (by omega) (hm n)
  have hmmono : Monotone m := D1sAux.env_mono (fun k => k + 1 + c (k + 1))

  have hz : ∀ n, ∃ z : (F.cochain K i), F.d K i z = 0 ∧ (y (m (n + 1)) - y (m n)) - z ∈ J₀ (n + 1) := by
    intro n
    refine hc' (n + 1) _ ?_
    have h1 : F.d K i (y (m (n + 1)) - y (m n)) =
        (t (m (n + 1)) - t (m n)) - (t (m (n + 1)) - a - F.d K i (y (m (n + 1)))) + (t (m n) - a - F.d K i (y (m n))) := by
      rw [map_sub]; abel
    rw [h1]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact hJ (by have := hm n; omega) (htele (hmmono (Nat.le_add_right n 1)))
    · exact hJ (by have := hm n; have := hmmono (Nat.le_add_right n 1); omega) (hy' (m (n + 1)))
    · exact hJ (by have := hm n; omega) (hy' (m n))
  choose z hdz hz' using hz

  refine ⟨a, fun n => y (m n) - ∑ k ∈ Finset.range n, z k, hda, fun n => ?_, fun n => ?_⟩
  · have hdsum : F.d K i (∑ k ∈ Finset.range n, z k) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun k _ => hdz k
    have : t n - a - F.d K i (y (m n) - ∑ k ∈ Finset.range n, z k)
        = (t n - t (m n)) + (t (m n) - a - F.d K i (y (m n))) := by
      rw [map_sub, hdsum]; abel
    rw [this]
    refine Submodule.add_mem _ ?_ (hJ (Nat.succ_le_succ (hmn n)) (hy' (m n)))
    have : t n - t (m n) = -(t (m n) - t n) := by abel
    rw [this]; exact Submodule.neg_mem _ (htele (hmn n))
  · have : (y (m (n + 1)) - ∑ k ∈ Finset.range (n + 1), z k) - (y (m n) - ∑ k ∈ Finset.range n, z k)
        = (y (m (n + 1)) - y (m n)) - z n := by
      rw [Finset.sum_range_succ]; abel
    rw [this]; exact hz' n

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) :
    ∃ (a : F.cochain K (i + 1)) (Y : ℕ → F.cochain K i), F.d K (i + 1) a = 0 ∧
      (∀ n : ℕ, t n - a - F.d K i (Y n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) ∧
      (∀ n : ℕ, Y (n + 1) - Y n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K i))) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    :
    ∃ (θF'' : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1),
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF'' i k U (a • x) = a • θF'' i k U x) ∧
      (∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF'' i k U' (res i h x) = (F k).res h (θF'' i k U x)) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF'' i (k + 1) U = θF'' i k U) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF'' i k U ∘ₗ ϑ i U = (lam k).app U.1) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF'' i k U = (ψE k).app U.1 ∘ₗ θE i U) ∧
    ∃ (u'' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u'' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u'' i j W hj (a • x) = a • u'' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u'' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u'' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u'' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u'' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u'' j l ⟨W.1, hj⟩ hl (u'' i j W hj x) = u'' i l W hl x) ∧
      (∀ (i j : K.ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θF'' j k ⟨W.1, hj⟩ (u'' i j W hj x) = θF'' i k W x) := by
  classical

  obtain ⟨t, ht, hdt, htt⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
      I q F hFc hFq φ hφs hφk E ε GE hGEc hGEq ψE GK hGKc hGKq lam hlamc hlamr hlami K M res ϑ θE θF
      hϑs hθEs hθFs hθEn hθFn hexact hsurj hc1 hc2 hc3 u hus hun huϑ huθE hcocy

  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨hHc, hHq, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq q GE GK hGEc hGEq hGKc hGKq

  obtain ⟨z, Y, hz, hzt, hY⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
      I q (OModulePresheaf.internalHom GE GK) hHc hHq K 0 t hdt htt

  refine
    AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
      K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3
      u hub hus hun huϑ huθE hcocy t ht z hz (fun k => -Y k) (fun k => ?_) (fun k => ?_)
  ·
    have h := hzt k
    have : z - t k - (OModulePresheaf.internalHom GE GK).d K 0 (-Y k) =
        -(t k - z - (OModulePresheaf.internalHom GE GK).d K 0 (Y k)) := by
      rw [map_neg]; abel
    rw [this]
    exact Submodule.neg_mem _ h
  · have h := hY k
    have : -Y (k + 1) - -Y k = -(Y (k + 1) - Y k) := by abel
    rw [this]
    exact Submodule.neg_mem _ h

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    :
    ∃ (θF'' : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1),
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF'' i k U (a • x) = a • θF'' i k U x) ∧
      (∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF'' i k U' (res i h x) = (F k).res h (θF'' i k U x)) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF'' i (k + 1) U = θF'' i k U) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF'' i k U ∘ₗ ϑ i U = (lam k).app U.1) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF'' i k U = (ψE k).app U.1 ∘ₗ θE i U) ∧
    ∃ (u'' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u'' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u'' i j W hj (a • x) = a • u'' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u'' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u'' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u'' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u'' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u'' j l ⟨W.1, hj⟩ hl (u'' i j W hj x) = u'' i l W hl x) ∧
      (∀ (i j : K.ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θF'' j k ⟨W.1, hj⟩ (u'' i j W hj x) = θF'' i k W x) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by
  obtain ⟨u', hub', hus', hun', huϑ', huθE', hcocy'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
      K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE
  obtain ⟨θF'', hθFs'', hθFn'', hc1'', hc2'', hc3'', u'', hub'', hus'', hun'', huϑ'', huθE'', hcocy'', huθF''⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
      K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u' hub' hus' hun' huϑ' huθE' hcocy'
  exact AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
      K M res res_smul res_refl res_comp hqc hfg ϑ θE θF'' hϑs hθEs hθFs'' hϑn hθEn hθFn'' hexact hsurj hϑi hc1'' hc2'' hc3'' u'' hub'' hus'' hun'' huϑ'' huθE'' hcocy'' huθF''

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by
  obtain ⟨K, M, i1, i2, iΓ, i4, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF, hϑs, hθEs, hθFs, hϑn, hθEn, hθFn,
    hexact, hsurj, hϑi, hc1, hc2, hc3, u, hub, hus, hun, huϑ, huθE⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  letI := i1; letI := i2; letI := iΓ; letI := i4
  exact AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete
    I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
    K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3
    u hub hus hun huϑ huθE

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace RedC6bSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

section FSide

variable (F : OModulePresheaf π)

theorem eq_of_forall_isLocalizedModule_eq {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (f : ∀ i, M →ₗ[S] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    (x y : M) (h : ∀ i, f i x = f i y) : x = y := by
  classical
  have hex : ∀ i, ∃ n : ℕ, g i ^ n • x = g i ^ n • y := fun i => by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp (h i)
    exact ⟨n, hn⟩
  choose n hn using hex
  let N := Finset.univ.sup n
  have hN : ∀ i, g i ^ N • x = g i ^ N • y := fun i => by
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm, mul_smul, mul_smul, hn i]
  have hspan : Ideal.span (Set.range fun i => g i ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N
    rw [← Set.range_comp] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ Submodule.mem_top (x := (1 : S)))
  calc x = (1 : S) • x := (one_smul S x).symm
    _ = (∑ i, c i * g i ^ N) • x := by rw [hc]
    _ = ∑ i, c i • (g i ^ N • x) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = ∑ i, c i • (g i ^ N • y) := by simp_rw [hN]
    _ = (∑ i, c i * g i ^ N) • y := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = y := by rw [hc, one_smul]

def FO (O : V.Opens) (W : V.Opens) (h : W ≤ O) : Type u := F.obj W

scoped instance instACG_FO (O W : V.Opens) (h : W ≤ O) : AddCommGroup (FO F O W h) :=
  inferInstanceAs (AddCommGroup (F.obj W))

scoped instance instMod_FO (O W : V.Opens) (h : W ≤ O) : Module Γ(V, O) (FO F O W h) :=
  Module.compHom (F.obj W) (V.presheaf.map (homOfLE h).op).hom

theorem FO_smul_def (O W : V.Opens) (h : W ≤ O) (a : Γ(V, O)) (x : FO F O W h) :
    a • x = (show FO F O W h from (V.presheaf.map (homOfLE h).op).hom a • (show F.obj W from x)) := rfl

def FresO (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) :
    FO F O W hW →ₗ[Γ(V, O)] FO F O W' hW' where
  toFun x := (show FO F O W' hW' from F.res h (show F.obj W from x))
  map_add' x y := map_add (F.res h) _ _
  map_smul' a x := by
    show F.res h ((V.presheaf.map (homOfLE hW).op).hom a • (show F.obj W from x)) =
      (V.presheaf.map (homOfLE hW').op).hom a • F.res h _
    rw [F.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl

theorem FresO_apply (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) (x : FO F O W hW) :
    FresO F O hW hW' h x = (show FO F O W' hW' from F.res h (show F.obj W from x)) := rfl

def Fres₀ (O : V.Opens) {W : V.Opens} (hW : W ≤ O) : F.obj O →ₗ[Γ(V, O)] FO F O W hW where
  toFun x := (show FO F O W hW from F.res hW x)
  map_add' x y := map_add (F.res hW) _ _
  map_smul' a x := F.res_smul hW a x

theorem Fres₀_apply (O : V.Opens) {W : V.Opens} (hW : W ≤ O) (x : F.obj O) :
    Fres₀ F O hW x = (show FO F O W hW from F.res hW x) := rfl

variable {F}

theorem isLocalizedModule_FresO (hF : F.IsQuasicoherent) (O : V.Opens) (W : V.affineOpens) (hW : W.1 ≤ O)
    (g : Γ(V, O)) :
    IsLocalizedModule (Submonoid.powers g)
      (FresO F O hW ((V.basicOpen_le _).trans hW)
        (V.basicOpen_le ((V.presheaf.map (homOfLE hW).op).hom g))) := by
  set gW := (V.presheaf.map (homOfLE hW).op).hom g with hgW
  have hq := hF W gW
  have hres : ∀ n : ℕ, (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) =
      (V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom (gW ^ n) := fun n => by
    rw [hgW, ← map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom gW) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen gW
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n)) := by
      rw [hres, map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen gW) =>
        (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    refine ⟨((show FO F O W.1 hW from x), ⟨g ^ n, n, rfl⟩), ?_⟩
    show (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • (show F.obj _ from y) = F.res _ x
    rw [hres]; exact hx.symm
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le gW) ((show F.obj W.1 from x₁) - (show F.obj W.1 from x₂)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₁) =
      (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₂)
    rw [map_pow, ← hgW, ← sub_eq_zero, ← smul_sub, hn]

theorem isLocalizedModule_Fres₀ (hF : F.IsQuasicoherent) (U : V.affineOpens) (g : Γ(V, U.1)) :
    IsLocalizedModule (Submonoid.powers g) (Fres₀ F U.1 (V.basicOpen_le g)) := by
  have hq := hF U g
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom g) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
      rw [map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen g) =>
        (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    exact ⟨(x, ⟨g ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le g) (x₁ - x₂) = 0 := by rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show g ^ n • x₁ = g ^ n • x₂
    rw [← sub_eq_zero, ← smul_sub, hn]

theorem F_eq_of_forall_res_basicOpen_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type*} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤) (x y : F.obj U.1)
    (h : ∀ i, F.res (V.basicOpen_le (g i)) x = F.res (V.basicOpen_le (g i)) y) : x = y :=
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  eq_of_forall_isLocalizedModule_eq g hg (fun i => Fres₀ F U.1 (V.basicOpen_le (g i))) x y h

theorem F_exists_of_forall_res_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type u} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i, F.obj (V.basicOpen (g i)))
    (hx : ∀ i j, F.res (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))) (x i) =
      F.res (by rw [Scheme.basicOpen_res]; exact inf_le_right) (x j)) :
    ∃ m : F.obj U.1, ∀ i, F.res (V.basicOpen_le (g i)) m = x i := by
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  let Ui : ι → V.affineOpens := fun i => ⟨V.basicOpen (g i), U.2.basicOpen (g i)⟩
  haveI := fun i j => isLocalizedModule_FresO hF U.1 (Ui i) (V.basicOpen_le (g i)) (g j)
  obtain ⟨m, hm⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hg
    (fun i => Fres₀ F U.1 (V.basicOpen_le (g i)))
    (fun i j => FresO F U.1 (V.basicOpen_le (g i)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))))
    (fun i j => FresO F U.1 (V.basicOpen_le (g j)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (by rw [Scheme.basicOpen_res]; exact inf_le_right))
    (fun i j => LinearMap.ext fun m => by
      show F.res _ (F.res _ m) = F.res _ (F.res _ m)
      rw [F.res_res, F.res_res])
    (fun i => (show FO F U.1 _ _ from x i)) (fun i j => hx i j)
  exact ⟨m, hm⟩

end FSide

section Hom

variable {F₁ F₂ : OModulePresheaf π}

def appO (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) : F₁.obj U.1 →ₗ[Γ(V, U.1)] F₂.obj U.1 where
  toFun x := Φ.app U x
  map_add' x y := map_add _ x y
  map_smul' a x := Φ.app_smul U a x

theorem appO_apply (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (x : F₁.obj U.1) : appO Φ U x = Φ.app U x := rfl

abbrev bU (U : V.affineOpens) (g : Γ(V, U.1)) : V.affineOpens := ⟨V.basicOpen g, U.2.basicOpen g⟩

def appB (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    FO F₁ U.1 (V.basicOpen g) (V.basicOpen_le g) →ₗ[Γ(V, U.1)] FO F₂ U.1 (V.basicOpen g) (V.basicOpen_le g) where
  toFun x := (show FO F₂ U.1 _ _ from Φ.app (bU U g) (show F₁.obj (V.basicOpen g) from x))
  map_add' x y := map_add (Φ.app (bU U g)) _ _
  map_smul' a x := Φ.app_smul (bU U g) _ _

theorem appB_comp (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    appB Φ U g ∘ₗ Fres₀ F₁ U.1 (V.basicOpen_le g) = Fres₀ F₂ U.1 (V.basicOpen_le g) ∘ₗ appO Φ U := by
  refine LinearMap.ext fun x => ?_
  show Φ.app (bU U g) (F₁.res (V.basicOpen_le g) x) = F₂.res (V.basicOpen_le g) (Φ.app U x)
  have := Φ.naturality (U := bU U g) (U' := U) (V.basicOpen_le g)
  exact (LinearMap.congr_fun this x)

theorem map_eq_appB (hF₁ : F₁.IsQuasicoherent) (hF₂ : F₂.IsQuasicoherent)
    (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    haveI := isLocalizedModule_Fres₀ hF₁ U g
    haveI := isLocalizedModule_Fres₀ hF₂ U g
    IsLocalizedModule.map (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g)) (Fres₀ F₂ U.1 (V.basicOpen_le g))
      (appO Φ U) = appB Φ U g := by
  haveI := isLocalizedModule_Fres₀ hF₁ U g
  haveI := isLocalizedModule_Fres₀ hF₂ U g
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g))
    (Fres₀ F₂ U.1 (V.basicOpen_le g))
  rw [IsLocalizedModule.map_comp, appB_comp]

theorem app_eq_of_forall_basicOpen (hF₂ : F₂.IsQuasicoherent) (Φ Ψ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens)
    (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (h : ∀ g ∈ T, Φ.app (bU U g) = Ψ.app (bU U g)) (x : F₁.obj U.1) : Φ.app U x = Ψ.app U x := by
  classical
  have hrange : Set.range (fun g : ↥T => (g.1 : Γ(V, U.1))) = (T : Set Γ(V, U.1)) := by
    ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  refine F_eq_of_forall_res_basicOpen_eq hF₂ U (fun g : ↥T => (g.1 : Γ(V, U.1))) (by rw [hrange]; exact hT) _ _ fun g => ?_
  show F₂.res (V.basicOpen_le g.1) (Φ.app U x) = F₂.res (V.basicOpen_le g.1) (Ψ.app U x)
  rw [← Φ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x,
    ← Ψ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x, h g.1 g.2]

end Hom

theorem exists_cover (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1) (U : V.affineOpens) :
    ∃ T : Finset Γ(V, U.1), Ideal.span (T : Set Γ(V, U.1)) = ⊤ ∧ ∀ g ∈ T, bU U g ∈ B := by
  classical
  let s : Set Γ(V, U.1) := {g | bU U g ∈ B}
  have hs : Ideal.span s = ⊤ := by
    rw [← U.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => V.basicOpen_le _) ?_
    intro x hx
    obtain ⟨W, hWB, hxW⟩ := hcov x
    obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hx
    have hf : f ∈ s := hdown W (bU U f) hfW hWB
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨T, hTs, hT⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  exact ⟨T, (Ideal.eq_top_iff_one _).mpr hT, fun g hg => hTs hg⟩

end RedC6bSol
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

open RedC6bSol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by
  classical
  obtain ⟨B, hdown, hcov, M, i1, i2, i3, i4, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF,
    hϑs, hθEs, hθFs, hϑn, hθEn, hθFn, hexact, hsurj, hc1, hc2, hc3⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨G, e, hGc, hGq, he_smul, he_res, hout, hin⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis q B hdown hcov M res
      res_smul res_refl res_comp hqc hfg
  obtain ⟨α, hα, -⟩ := hin GK hGKq ϑ hϑs hϑn
  obtain ⟨β, hβ, -⟩ := hout GE hGEq θE hθEs hθEn
  choose ψ hψ using fun k => (hout (F k) (hFq k) (θF k) (hθFs k) (hθFn k)).exists

  have hβW : ∀ (W : ↥B) (x : G.obj W.1.1), β.app W.1 x = θE W (e W x) := hβ
  have hαW : ∀ (W : ↥B) (x : GK.obj W.1.1), α.app W.1 x = (e W).symm (ϑ W x) := fun W x => by
    rw [← hα W x, LinearEquiv.symm_apply_apply]
  refine ⟨G, α, β, ψ, hGc, hGq, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGKq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have hrange : Set.range (fun g : ↥T => (g.1 : Γ(P, U.1))) = (T : Set Γ(P, U.1)) := by
      ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    have key : Function.Exact (appO α U) (appO β U) := by
      refine exact_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GK U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GK U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO α U) (appO β U) fun g => ?_
      rw [map_eq_appB hGKq hGq α U g.1, map_eq_appB hGq hGEq β U g.1]

      intro y
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      show β.app W.1 y = 0 ↔ y ∈ Set.range (fun x => α.app W.1 x)
      rw [hβW W, ← LinearMap.mem_ker, ← hexact W, LinearMap.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        show α.app W.1 x = y
        rw [hαW W, hx, LinearEquiv.symm_apply_apply]
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        change α.app W.1 x = y at hx
        rw [← hx, hαW W, LinearEquiv.apply_symm_apply]
    have key' : Function.Exact (α.app U) (β.app U) := key
    exact (LinearMap.exact_iff.mp key').symm
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have key : Function.Surjective (appO β U) := by
      refine surjective_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO β U) fun g => ?_
      rw [map_eq_appB hGq hGEq β U g.1]
      intro z
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      obtain ⟨m, hm⟩ := hsurj W (show GE.obj W.1.1 from z)
      refine ⟨(show FO G U.1 _ _ from (e W).symm m), ?_⟩
      show β.app W.1 ((e W).symm m) = z
      rw [hβW W, LinearEquiv.apply_symm_apply, hm]
    exact key
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((φ k).comp (ψ (k + 1))).app U x = (ψ k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (φ k).app W.1 ((ψ (k + 1)).app W.1 y) = (ψ k).app W.1 y
    rw [hψ (k + 1) W, hψ k W]
    exact LinearMap.congr_fun (hc1 k W) (e W y)
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ψ k).comp α).app U x = (lam k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ψ k).app W.1 (α.app W.1 y) = (lam k).app W.1 y
    rw [hψ k W, hαW W, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (hc2 k W) y
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ε k).comp (ψ k)).app U x = ((ψE k).comp β).app U x
    refine app_eq_of_forall_basicOpen (hEq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ε k).app W.1 ((ψ k).app W.1 y) = (ψE k).app W.1 (β.app W.1 y)
    rw [hψ k W, hβW W]
    exact LinearMap.congr_fun (hc3 k W) (e W y)

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  obtain ⟨G, α, β, ψ, hGc, hGq, hαβ, hβs, hψc, hψα, hψβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  exact AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
    I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami G hGc hGq α β hαβ hβs ψ hψc hψα hψβ

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory open _root_.AlgebraicGeometry hiding ChowDatum

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open TopologicalSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace GEDriver

theorem support_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).support = T :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal T)

theorem radical_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).radical = Scheme.IdealSheafData.vanishingIdeal T := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal T
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover (fun U => ?_)
  have hrad : (I.ideal U).IsRadical := by
    rw [← Ideal.radical_eq_iff]
    have := congrArg (fun J : X.IdealSheafData => J.ideal U) (radical_vanishingIdeal T)
    simp [Scheme.IdealSheafData.radical_ideal] at this
    exact this
  haveI : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := (Ideal.isRadical_iff_quotient_reduced _).1 hrad
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  infer_instance

theorem irreducibleSpace_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme :=
  Subtype.irreducibleSpace hT

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  haveI := isReduced_subscheme_vanishingIdeal T
  haveI := irreducibleSpace_subscheme_vanishingIdeal T hT
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem compactSpace_of_isProper {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    [IsProper q] : CompactSpace P :=
  QuasiCompact.compactSpace_of_compactSpace q

theorem isNoetherian_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : IsNoetherian P :=
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := compactSpace_of_isProper q
  {}

theorem noetherianSpace_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : NoetherianSpace P :=
  haveI := isNoetherian_of_isProper q
  inferInstance

theorem isProper_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) : IsProper I.subschemeι := inferInstance

theorem isProper_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] : IsProper (f ≫ g) :=
  inferInstance

theorem isSeparated_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsSeparated f := inferInstance

theorem idealAnnihilates_ker_subschemeι {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (J : P.IdealSheafData) (F : ℕ → OModulePresheaf q)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ J.ideal U ^ 1, ∀ x : (F k).obj U.1, a • x = 0) :
    ∀ k, OModulePresheaf.IdealAnnihilates q J.subschemeι.ker (F k) := by
  intro k U a ha x
  rw [Scheme.IdealSheafData.ker_subschemeι] at ha
  exact hS k U a (by rwa [pow_one]) x

private theorem _root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.GEDriver.nonempty_orderedAffineCover_of_compactSpace_univ (X : Scheme.{u}) [CompactSpace X] :
    Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

p2m_export "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.GEDriver" "nonempty_orderedAffineCover_of_compactSpace_univ"

theorem exists_closeds_lt_sup_eq {X : Type*} [TopologicalSpace X] (T : Closeds X) (hne : (T : Set X).Nonempty)
    (hT : ¬ IsIrreducible (T : Set X)) : ∃ T₁ T₂ : Closeds X, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
  have hpre : ¬ IsPreirreducible (T : Set X) := fun h => hT ⟨hne, h⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  push Not at hpre
  obtain ⟨z₁, z₂, hz₁, hz₂, hsub, h₁, h₂⟩ := hpre
  refine ⟨T ⊓ ⟨z₁, hz₁⟩, T ⊓ ⟨z₂, hz₂⟩, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => h₁ ?_
    have : (T : Set X) ∩ z₁ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · refine lt_of_le_of_ne inf_le_left fun h => h₂ ?_
    have : (T : Set X) ∩ z₂ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · apply Closeds.ext
    show (T : Set X) = (T : Set X) ∩ z₁ ∪ (T : Set X) ∩ z₂
    rw [← Set.inter_union_distrib_left]
    exact (Set.inter_eq_left.2 hsub).symm

theorem vanishingIdeal_sup_pow_mul_le {X : Scheme.{u}} (T₁ T₂ : Closeds X) (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal T₂).ideal U ^ 1 * (Scheme.IdealSheafData.vanishingIdeal T₁).ideal U
      ≤ (Scheme.IdealSheafData.vanishingIdeal (T₁ ⊔ T₂)).ideal U ^ 1 := by
  rw [pow_one, pow_one, Scheme.IdealSheafData.vanishingIdeal_sup, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
  exact Ideal.mul_le_inf.trans (by rw [inf_comm])

theorem vanishingIdeal_top_ideal_le_radical_bot {X : Scheme.{u}} (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).ideal U ≤ ((⊥ : X.IdealSheafData).ideal U).radical := by
  rw [Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.radical_bot,
    Scheme.IdealSheafData.radical_ideal]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]

structure AdicSys where
  F : ℕ → OModulePresheaf q
  hc : ∀ k, (F k).IsCoherent
  hq : ∀ k, (F k).IsQuasicoherent
  φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k)
  hs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U)
  hk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))

variable {I q}

def AdicSys.Algebraised (S : AdicSys I q) : Prop :=
  ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (S.F k)),
    G.IsCoherent ∧ G.IsQuasicoherent ∧
    (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
    (∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
    (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)

theorem algebraised_of_quot_of_ker (S : AdicSys I q) (𝓙 : P.IdealSheafData)
    (hQ : ∀ Q : AdicSys I q, (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q.F k)) → Q.Algebraised)
    (hK : ∀ (K : AdicSys I q) (j : ∀ k, OModulePresheaf.AffHom (K.F k) (S.F k)),
      (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (K.φ k).app U) →
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙 (S.F k) 1 U.1) →
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K.F (k + c)).obj U.1))) →
      K.Algebraised) :
    S.Algebraised := by
  classical

  obtain ⟨Q, τ, ε, hQc, hQq, hτs, hτk, hεc, hεs, hεk, hann⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
      I 𝓙 S.F S.hc S.hq S.φ S.hs S.hk
  let QS : AdicSys I q := ⟨Q, hQc, hQq, τ, hτs, hτk⟩

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, hsurj, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεc
  let KS : AdicSys I q := ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
  have hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = LinearMap.ker ((ε k).app U) := hsurj hεs

  obtain ⟨GQ, ψQ, hGQc, hGQq, hψQs, hψQk, hψQc⟩ := hQ QS hann
  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    hK KS j hjc (fun k U => (hjr k U).trans (hεk k U)) (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεs hεc GQ hGQc hGQq ψQ hψQs hψQk hψQc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U)
          = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact hjr k U)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 : (ψK (k + c)).app U x ∈ I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) :=
          (hc k).2 hx'

        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

def AdicSys.KilledBy (S : AdicSys I q) (𝓙 : P.IdealSheafData) (t : ℕ) : Prop :=
  ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ t, ∀ x : (S.F k).obj U.1, a • x = 0

theorem AdicSys.killedBy_one_iff (S : AdicSys I q) (𝓙 : P.IdealSheafData) :
    S.KilledBy 𝓙 1 ↔ ∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (S.F k) := by
  simp [AdicSys.KilledBy, OModulePresheaf.IdealAnnihilates, pow_one]

noncomputable abbrev idealOf (T : Closeds P) : P.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T

theorem AdicSys.algebraised_of_forall_eq_zero (S : AdicSys I q)
    (h : ∀ (k : ℕ) (U : P.affineOpens) (x : (S.F k).obj U.1), x = 0) : S.Algebraised := by
  have hcoh : (OModulePresheaf.zero q).IsCoherent := fun U => Module.Finite.of_finite
  have hqc : (OModulePresheaf.zero q).IsQuasicoherent := fun U f =>
    ⟨fun x => ⟨0, 0, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨OModulePresheaf.zero q, fun k => OModulePresheaf.AffHom.zeroFrom (S.F k), hcoh, hqc,
    fun k U y => ⟨0, by rw [h k U y]; exact map_zero _⟩, fun k U => ?_, fun k U => ?_⟩
  · haveI : Subsingleton (Submodule A ((OModulePresheaf.zero q).obj U.1)) := (Submodule.subsingleton_iff A).2 inferInstance
    exact Subsingleton.elim _ _
  · exact LinearMap.ext fun x => (h k U _).trans (h k U _).symm

theorem AdicSys.algebraised_of_killedBy_zero (S : AdicSys I q) (𝓙 : P.IdealSheafData) (h : S.KilledBy 𝓙 0) :
    S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have := h k U 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial) x
    rwa [one_smul] at this)

theorem AdicSys.algebraised_of_killedBy_coe_eq_empty (S : AdicSys I q) (T : Closeds P) (hT : (T : Set P) = ∅)
    (h : S.KilledBy (idealOf T) 1) : S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have h1 : (1 : Γ(P, U.1)) ∈ (idealOf T).ideal U ^ 1 := by
      have hT' : T = ⊥ := Closeds.ext (by simpa using hT)
      subst hT'
      rw [pow_one, show idealOf (⊥ : Closeds P) = ⊤ from Scheme.IdealSheafData.vanishingIdeal_bot,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply]
      trivial
    have := h k U 1 h1 x
    rwa [one_smul] at this)

theorem stepC
    (T : Closeds P) (hTirr : IsIrreducible (T : Set P))
    (ih : ∀ T' : Closeds P, T' < T → ∀ (t : ℕ) (S : AdicSys I q), S.KilledBy (idealOf T') t → S.Algebraised)
    (S : AdicSys I q) (hS : S.KilledBy (idealOf T) 1) : S.Algebraised := by
  classical

  let Z : Scheme.{u} := (idealOf T).subscheme
  let i : Z ⟶ P := (idealOf T).subschemeι
  haveI : IsIntegral Z := isIntegral_subscheme_vanishingIdeal T hTirr
  haveI : IsProper i := isProper_subschemeι _
  haveI : IsProper (i ≫ q) := inferInstance
  obtain ⟨cd⟩ := AlgebraicGeometry.ChowDatumProj.nonempty_of (i ≫ q)
    (AlgebraicGeometry.ChowDatum.nonempty (i ≫ q))
  haveI : IsProper (cd.p ≫ i) := inferInstance
  haveI : IsSeparated (cd.p ≫ i) := inferInstance
  haveI : IsProper ((cd.p ≫ i) ≫ q) := inferInstance
  haveI : CompactSpace cd.V' := compactSpace_of_isProper ((cd.p ≫ i) ≫ q)
  obtain ⟨K'⟩ := AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ cd.V'
  have hSZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (S.F k) :=
    idealAnnihilates_ker_subschemeι q (idealOf T) S.F hS

  obtain ⟨F', φ', η, hF'c, hF'q, hφ's, hφ'k, hηs, hηV, hηU, hηφ, hβ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom I q (cd.p ≫ i) S.F S.hc S.hq S.φ S.hs S.hk

  have hιq : cd.ιN ≫ ProjSpace.π A cd.Nd = (cd.p ≫ i) ≫ q := by rw [cd.hoverN, Category.assoc]
  obtain ⟨G', ψ', hG'c, hG'q, hψ's, hψ'k, hψ'c⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete I cd.ιN hιq F' hF'c hF'q φ' hφ's hφ'k

  obtain ⟨v, hvη, hvc⟩ : ∃ v : ∀ k, OModulePresheaf.AffHom (S.F k)
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' (F' k)),
      (∀ (k : ℕ) (U₀ : P.affineOpens) (x : (S.F k).obj U₀.1) (jx : K'.ι),
        ((v k).app U₀ x).1 jx = η k U₀ (OModulePresheaf.AffHom.affineChart (cd.p ≫ i) q K' U₀ jx)
          (OModulePresheaf.cechPushforward.chart_le_preimage (cd.p ≫ i) K' U₀.1 jx) x) ∧
      (∀ (k : ℕ) (U₀ : P.affineOpens),
        ((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ∘ₗ (v (k + 1)).app U₀ = (v k).app U₀ ∘ₗ (S.φ k).app U₀) :=
    by
      choose v hv using fun k =>
        AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
          q (cd.p ≫ i) K' (S.F k) (F' k) (η k) (hηs k) (hηV k) (hηU k)
      refine ⟨v, hv, fun k U₀ => ?_⟩
      apply LinearMap.ext
      intro x
      apply OModulePresheaf.cechPushforward.ext
      intro jx
      show (((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ((v (k + 1)).app U₀ x)).1 jx
        = ((v k).app U₀ ((S.φ k).app U₀ x)).1 jx
      rw [OModulePresheaf.AffHom.coe_cechPushforward_app, hv, hv, hηφ]

  obtain ⟨hGPc, hGPq, Ps, π, ψP, ν, u, hPsc, hPsq, hπs, hπk, hψPs, hψPk, hψPc, hνc, hνψP, hνi, huc, hνu⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper I q (cd.p ≫ i) K' F' φ' G' hG'c hG'q ψ' hψ's hψ'k hψ'c S.F S.φ S.hs S.hk v hvc

  have hZne : Nonempty Z := by
    haveI := irreducibleSpace_subscheme_vanishingIdeal T hTirr
    infer_instance
  have hrange : Set.range i.base = (T : Set P) := by
    show Set.range (idealOf T).subschemeι.base = (T : Set P)
    rw [Scheme.IdealSheafData.range_subschemeι, support_vanishingIdeal]
  obtain ⟨T', hT'lt, hT'⟩ :=
    AlgebraicGeometry.exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
      i T hrange cd.U (cd.hU_dense.nonempty)
  obtain ⟨N, hcoker, hker⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
      I q i cd.p K' cd.U cd.hp_isoU T' hT' S.F S.hc S.hq S.φ S.hs S.hk hSZ F' φ' η hηs hηV hηU hηφ hβ
      G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, -, hCc, hCq, hγs, hγk, hθc, hθs, hθk⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Ps hPsc hPsq π hπs hπk u huc

  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    ih T' hT'lt N ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
      (AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
        I S.F S.φ S.hs S.hk Ks κ hκs hκk j hjc (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)
        Ps u huj (idealOf T') N hker)
  obtain ⟨GC, ψC, hGCc, hGCq, hψCs, hψCk, hψCc⟩ :=
    ih T' hT'lt N ⟨Cs, hCc, hCq, γ, hγs, hγk⟩ (by
      intro k U a ha z
      obtain ⟨y, rfl⟩ := hθs k U z
      obtain ⟨x, hx⟩ := hcoker k U a ha y
      rw [← (θ k).app_smul, ← hx]
      have hmem : (u k).app U x ∈ LinearMap.ker ((θ k).app U) := by
        rw [hθk]; exact LinearMap.mem_range_self _ x
      exact LinearMap.mem_ker.mp hmem)

  obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, huEr, huEi⟩ :
      ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
        (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((τ k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens),
          LinearMap.ker ((τ k).app W) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj W.1))) ∧
        ∃ ε : ∀ k, OModulePresheaf.AffHom (S.F k) (E k),
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ε k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens), (τ k).app W ∘ₗ (ε (k + 1)).app W = (ε k).app W ∘ₗ (S.φ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.ker ((ε k).app W) = LinearMap.range ((j k).app W)) ∧
        ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
        (∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (uE (k + 1)).app W = (uE k).app W ∘ₗ (τ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.range ((uE k).app W) = LinearMap.ker ((θ k).app W)) ∧
        (∀ W : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
          LinearMap.ker ((uE (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj W.1))) :=
    by
      obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, -, huEc, huEr, huEi⟩ :=
        AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
          I S.F S.hc S.hq S.φ S.hs S.hk Ks hKq κ hκs j hjc Ps π u huc huj
          (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).1⟩)
      exact ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, fun k U => (huEr k U).trans (hθk k U).symm, huEi⟩

  obtain ⟨GE, ψE, hGEc, hGEq, hψEs, hψEk, hψEc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q E hEc hEq τ hτs hτk Ps hPsc hPsq π hπs hπk Cs hCc hCq γ hγs hγk θ hθc uE huEc huEr huEi
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' G') hGPc hGPq ψP hψPs hψPk hψPc GC hGCc hGCq ψC hψCs hψCk hψCc

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U) = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact (hεk k U).symm)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 := (hc k).2 hx'
        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

theorem algebraised_of_killedBy
    (T : Closeds P) (t : ℕ) (S : AdicSys I q) (hS : S.KilledBy (idealOf T) t) : S.Algebraised := by
  haveI : NoetherianSpace P := noetherianSpace_of_isProper q
  induction T using (wellFounded_lt (α := Closeds P)).induction generalizing t S with
  | _ T ih =>

  have h1 : ∀ S : AdicSys I q, S.KilledBy (idealOf T) 1 → S.Algebraised := by
    intro S hS1
    by_cases hirr : IsIrreducible (T : Set P)
    · exact stepC T hirr ih S hS1
    ·
      by_cases hT : (T : Set P) = ∅
      · exact AdicSys.algebraised_of_killedBy_coe_eq_empty S T hT hS1
      ·
        obtain ⟨T₁, T₂, hT₁, hT₂, hT12⟩ : ∃ T₁ T₂ : Closeds P, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
          exact exists_closeds_lt_sup_eq T (Set.nonempty_iff_ne_empty.2 hT) hirr
        refine algebraised_of_quot_of_ker S (idealOf T₁)
          (fun Q hQ => ih T₁ hT₁ 1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
        intro K j hjc hjr hji
        refine ih T₂ hT₂ 1 K ?_
        exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
          I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T₁) (idealOf T₂) 1 1 hjr hji
          (fun U => by rw [hT12]; exact vanishingIdeal_sup_pow_mul_le T₁ T₂ U) hS1

  induction t generalizing S with
  | zero =>
    exact AdicSys.algebraised_of_killedBy_zero S _ hS
  | succ t iht =>
    refine algebraised_of_quot_of_ker S (idealOf T)
      (fun Q hQ => h1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
    intro K j hjc hjr hji
    refine iht K ?_
    exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
      I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T) (idealOf T) (t + 1) t hjr hji
      (fun U => by rw [pow_succ]) hS

end GEDriver

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  haveI : IsNoetherian P := GEDriver.isNoetherian_of_isProper q

  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds P)) ⊥ (GEDriver.vanishingIdeal_top_ideal_le_radical_bot)
  exact GEDriver.algebraised_of_killedBy (I := I) (q := q) ⊤ e ⟨F, hc, hq, φ, hφs, hφk⟩ (by
    intro k U a ha x
    have ha' : a ∈ (⊥ : P.IdealSheafData).ideal U := he U ha
    rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot] at ha'
    rw [ha', zero_smul])

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub
attribute [-instance] AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val
attribute [-simp] AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-instance] AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace _root_.AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GraphAlgAux

open _root_.AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

section MkAffHom

variable {M N : OModulePresheaf f}

def linR (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) : M.obj U.1 →ₗ[R] N.obj U.1 where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
    haveI := M.isScalarTower U.1
    haveI := N.isScalarTower U.1
    change g (r • x) = r • g x
    rw [← algebraMap_smul (A := A U) r x, g.map_smul, algebraMap_smul]

@[scoped simp] theorem linR_apply (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) (x : M.obj U.1) :
    linR U g x = g x := rfl

def mkAffHom (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (h : U.1 ≤ U'.1) (x : M.obj U'.1), app U (M.res h x) = N.res h (app U' x)) :
    AffHom M N where
  app U := linR U (app U)
  app_smul U a x := (app U).map_smul a x
  naturality h := LinearMap.ext fun x => nat _ _ h x

@[scoped simp] theorem mkAffHom_app (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens)
    (x : M.obj U.1) : (mkAffHom app nat).app U x = app U x := rfl

theorem affHom_ext (a b : AffHom M N) (h : ∀ (W : X.affineOpens) (x : M.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

end MkAffHom

theorem unit_isCoherent : (unit f).IsCoherent := fun U => Module.Finite.self (A U)

theorem unit_isQuasicoherent : (unit f).IsQuasicoherent := by
  intro U r
  haveI := U.2.isLocalization_basicOpen r
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (show Γ(X, X.basicOpen r) from x)
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, y, ?_⟩
    change (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y =
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ n) * (show Γ(X, X.basicOpen r) from x)
    have e : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) = (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom := rfl
    have hn' : r ^ n = s.1 := hn
    rw [← e, hn', mul_comm]
    exact hs.symm
  · have hy' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (show Γ(X, U.1) from y) = 0 := hy
    obtain ⟨⟨m, k, hk⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers r) Γ(X, X.basicOpen r) _).mp hy'
    refine ⟨k, ?_⟩
    have hk' : r ^ k = m := hk
    change r ^ k * (show Γ(X, U.1) from y) = 0
    rw [hk']
    exact hm

structure Sys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R)
  hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))
  tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))
  htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n
  xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1))
  hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n)
  hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n
  Y : ℕ → Scheme.{u}
  g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)
  hg : ∀ n : ℕ, IsFinite (g n)
  yn : ∀ n : ℕ, Y n ⟶ Y (n + 1)
  hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)

variable [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R] [IsProper f] (S : Sys I f)

namespace Sys

abbrev h (n : ℕ) : S.Y n ⟶ X := S.g n ≫ pullback.fst f (S.sR n)

abbrev B (n : ℕ) : OModulePresheaf f := pushforwardUnit f (S.h n)

abbrev BΓ (n : ℕ) (U : X.Opens) : Type u := (S.Y n).presheaf.obj (op ((S.h n) ⁻¹ᵁ U))

abbrev bapp (n : ℕ) (U : X.Opens) : Γ(X, U) →+* S.BΓ n U := ((S.h n).appLE U ((S.h n) ⁻¹ᵁ U) le_rfl).hom

theorem yn_comp_h (n : ℕ) : S.yn n ≫ S.h (n + 1) = S.h n := by
  change S.yn n ≫ S.g (n + 1) ≫ pullback.fst f (S.sR (n + 1)) = S.g n ≫ pullback.fst f (S.sR n)
  rw [← Category.assoc, (S.hY n).w, Category.assoc, S.hxn₁]

theorem pre_le (n : ℕ) (U : X.Opens) : (S.h n) ⁻¹ᵁ U ≤ (S.yn n) ⁻¹ᵁ ((S.h (n + 1)) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, S.yn_comp_h]

abbrev ynapp (n : ℕ) (U : X.Opens) : S.BΓ (n + 1) U →+* S.BΓ n U :=
  ((S.yn n).appLE ((S.h (n + 1)) ⁻¹ᵁ U) ((S.h n) ⁻¹ᵁ U) (S.pre_le n U)).hom

scoped instance isFinite_g (n : ℕ) : IsFinite (S.g n) := S.hg n

theorem B_smul (n : ℕ) (U : X.Opens) (a : Γ(X, U)) (z : (S.B n).obj U) :
    (a • z : (S.B n).obj U) = (show (S.B n).obj U from S.bapp n U a * (show S.BΓ n U from z)) := rfl

theorem B_res (n : ℕ) {U U' : X.Opens} (hU : U ≤ U') (z : (S.B n).obj U') :
    ((S.B n).res hU z : S.BΓ n U) =
      ((S.Y n).presheaf.map (homOfLE ((Opens.map (S.h n).base).monotone hU)).op).hom (show S.BΓ n U' from z) := rfl

theorem B_coh_qc (n : ℕ) : (S.B n).IsCoherent ∧ (S.B n).IsQuasicoherent :=
  (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).1 n

theorem B_coh (n : ℕ) : (S.B n).IsCoherent := (S.B_coh_qc n).1
theorem B_qc (n : ℕ) : (S.B n).IsQuasicoherent := (S.B_coh_qc n).2

theorem exists_τ : ∃ τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n),
    (∀ (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1),
      (τ n).app U z = (show (S.B n).obj U.1 from S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z))) ∧
    (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
    (∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1))) := by
  obtain ⟨τ, hτ, hs, hk⟩ :=
    (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
      R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).2.2
  exact ⟨τ, hτ, hs, hk⟩

def τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n) := S.exists_τ.choose

theorem τ_app (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1) :
    ((S.τ n).app U z : S.BΓ n U.1) = S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z) :=
  S.exists_τ.choose_spec.1 n U z

theorem τ_surj (n : ℕ) (U : X.affineOpens) : Function.Surjective ((S.τ n).app U) :=
  S.exists_τ.choose_spec.2.1 n U

theorem τ_ker (n : ℕ) (U : X.affineOpens) :
    LinearMap.ker ((S.τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1)) :=
  S.exists_τ.choose_spec.2.2 n U

def u (n : ℕ) : AffHom (unit f) (S.B n) :=
  mkAffHom
    (fun U =>
      { toFun := fun a => show (S.B n).obj U.1 from S.bapp n U.1 (show A U from a)
        map_add' := fun a b => map_add _ _ _
        map_smul' := fun a b => by
          change S.bapp n U.1 (a * (show A U from b)) = a • (show (S.B n).obj U.1 from S.bapp n U.1 (show A U from b))
          rw [B_smul, map_mul] })
    (fun U U' hU a => by
      change S.bapp n U.1 ((X.presheaf.map (homOfLE hU).op).hom a) =
        (S.B n).res hU (show (S.B n).obj U'.1 from S.bapp n U'.1 a)
      rw [B_res, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])

theorem u_app (n : ℕ) (U : X.affineOpens) (a : A U) :
    ((S.u n).app U (show (unit f).obj U.1 from a) : S.BΓ n U.1) = S.bapp n U.1 a := rfl

theorem ynapp_bapp (n : ℕ) (U : X.Opens) (a : Γ(X, U)) : S.ynapp n U (S.bapp (n + 1) U a) = S.bapp n U a := by
  change ((S.h (n + 1)).appLE U _ le_rfl ≫ (S.yn n).appLE _ _ (S.pre_le n U)).hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (k : S.Y n ⟶ X) (hk : k = S.h n) (e : (S.h n) ⁻¹ᵁ U ≤ k ⁻¹ᵁ U),
      (k.appLE U ((S.h n) ⁻¹ᵁ U) e).hom a = S.bapp n U a := by
    rintro k rfl e; rfl
  exact key _ (S.yn_comp_h n) _

theorem hτu (n : ℕ) : (S.τ n).comp (S.u (n + 1)) = S.u n :=
  affHom_ext _ _ fun U a => by
    rw [AffHom.comp_app]
    exact (S.τ_app n U _).trans (S.ynapp_bapp n U.1 a)

theorem k42 (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ρ : ∀ n : ℕ, AffHom F (S.B n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hτρ : ∀ n : ℕ, (S.τ n).comp (ρ (n + 1)) = ρ n)
    (M : OModulePresheaf f) (hMc : M.IsCoherent) (hMq : M.IsQuasicoherent)
    (ψ : ∀ n : ℕ, AffHom M (S.B n)) (hψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : AffHom M F, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : AffHom M F, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ :=
  AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I f M F hMc hMq
    hFc hFq S.B S.τ ρ hρs hρk hτρ ψ hψ

end Sys
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

section IdealLemmas

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem comap_map_of_isClosedImmersion {Z W : Scheme.{u}} (ι : Z ⟶ W) [IsClosedImmersion ι]
    (K : Z.IdealSheafData) : (K.map ι).comap ι = K := by
  have h1 : K.map ι = (K.subschemeι ≫ ι).ker := by
    rw [← Scheme.IdealSheafData.map_ker, ker_subschemeι]
  rw [h1, ← ker_fst_of_isClosedImmersion]
  have h2 : pullback.fst ι (K.subschemeι ≫ ι) = pullback.snd ι (K.subschemeι ≫ ι) ≫ K.subschemeι := by
    rw [← cancel_mono ι, Category.assoc, pullback.condition]
  rw [h2, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

theorem comap_sup_ker {Z W : Scheme.{u}} (ι : Z ⟶ W) (J : W.IdealSheafData) :
    (J ⊔ ι.ker).comap ι = J.comap ι := by
  have h : ι.ker.comap ι = ⊥ :=
    le_bot_iff.mp (by rw [← Scheme.IdealSheafData.map_bot]; exact comap_map_le _ _)
  rw [Scheme.IdealSheafData.comap_sup, h, sup_bot_eq]

end IdealLemmas
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

theorem appLE_ΓSpecIso_inv_eq_zero {Zn : Scheme.{u}} (𝔞 : Ideal R) (t : Zn ⟶ Spec (.of (R ⧸ 𝔞)))
    (W : Zn.Opens) (r : R) (hr : r ∈ 𝔞)
    (k : Zn ⟶ Spec (.of R)) (hk : k = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))
    (e : W ≤ k ⁻¹ᵁ ⊤) :
    (k.appLE ⊤ W e).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) = 0 := by
  subst hk
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top, CommRingCat.comp_apply]
  have : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (.of (R ⧸ 𝔞))).inv.hom (Ideal.Quotient.mk 𝔞 r) := by
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appTop).hom r = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]

end GraphAlgAux
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux"

open GraphAlgAux _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by

  have Hle : ∀ n : ℕ, Jn (n + 1) ≤ (Jn n).map (adicThickeningTransition p I n) := fun n =>
    le_map_iff_comap_le.mpr (hJn n).le
  let S : Sys I p :=
    { sR := fun n => adicThickeningBase I n
      hsR := fun n => rfl
      tR := fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))
      htR := fun n => adicThickeningBase_succ_comp I n
      xn := fun n => adicThickeningTransition p I n
      hxn₁ := fun n => adicThickeningTransition_ι p I n
      hxn₂ := fun n => adicThickeningTransition_toBase p I n
      Y := fun n => (Jn n).subscheme
      g := fun n => (Jn n).subschemeι
      hg := fun n => (inferInstance : IsFinite (Jn n).subschemeι)
      yn := fun n => subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n)
      hY := fun n => (isPullback_of_isClosedImmersion (Jn n).subschemeι (Jn (n + 1)).subschemeι
        (subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n))
        (adicThickeningTransition p I n) (by rw [subschemeMap_subschemeι])
        (by rw [ker_subschemeι, ker_subschemeι, hJn])).flip }

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
      I p S.B S.B_coh S.B_qc S.τ S.τ_surj S.τ_ker
  have hτψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n := fun n =>
    affHom_ext _ _ fun U x => by
      rw [AffHom.comp_app]
      exact congrFun (congrArg DFunLike.coe (hψc n U)) x

  obtain ⟨η, hη, -⟩ := S.k42 G hGc hGq ψ hψs hψk hτψ (unit p) unit_isCoherent unit_isQuasicoherent S.u S.hτu

  have hbapp : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective (S.bapp n U.1) := fun n U => by
    haveI : IsClosedImmersion (S.h n) :=
      (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
    have e : (S.h n).app U.1 = (S.h n).appLE U.1 _ le_rfl := Scheme.Hom.app_eq_appLE _
    have := (S.h n).app_surjective U.1 U.2
    rw [e] at this
    exact this
  have hηs : ∀ U : P.affineOpens, Function.Surjective (η.app U) := fun U =>
    AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
      I (IsAdicComplete.le_jacobson_bot I) unit_isQuasicoherent hGc hGq η (fun U => by
        refine eq_top_iff.mpr fun m _ => ?_
        obtain ⟨a, ha⟩ := hbapp 0 U ((ψ 0).app U m : S.BΓ 0 U.1)
        have h1 : (ψ 0).app U (η.app U (show (unit p).obj U.1 from a)) = (ψ 0).app U m := by
          have := congrArg (fun θ : AffHom (unit p) (S.B 0) => θ.app U (show (unit p).obj U.1 from a)) (hη 0)
          dsimp only at this
          rw [AffHom.comp_app] at this
          rw [this]
          exact ha
        have h2 : m - η.app U (show (unit p).obj U.1 from a) ∈ LinearMap.ker ((ψ 0).app U) := by
          rw [LinearMap.mem_ker, map_sub, h1, sub_self]
        rw [hψk 0 U, pow_one] at h2
        have : m = η.app U (show (unit p).obj U.1 from a) + (m - η.app U (show (unit p).obj U.1 from a)) := by
          abel
        rw [this]
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) h2) U

  have hnat : ∀ (U U' : P.affineOpens) (hU : U.1 ≤ U'.1) (a : Γ(P, U'.1)),
      η.app U (show (unit p).obj U.1 from (P.presheaf.map (homOfLE hU).op).hom a) =
        G.res hU (η.app U' (show (unit p).obj U'.1 from a)) := fun U U' hU a =>
    η.naturality_apply (U := U) (U' := U') hU _
  have hmul : ∀ (U : P.affineOpens) (a b : Γ(P, U.1)),
      η.app U (show (unit p).obj U.1 from a * b) = a • η.app U (show (unit p).obj U.1 from b) := fun U a b =>
    η.app_smul U a (show (unit p).obj U.1 from b)
  let Jideal : ∀ U : P.affineOpens, Ideal Γ(P, U.1) := fun U =>
    { carrier := {a | η.app U (show (unit p).obj U.1 from a) = 0}
      add_mem' := fun {a b} ha hb => by
        change η.app U (show (unit p).obj U.1 from a + b) = 0
        rw [show (show (unit p).obj U.1 from a + b) = (show (unit p).obj U.1 from a) + (show (unit p).obj U.1 from b)
          from rfl, map_add]
        rw [Set.mem_setOf_eq] at ha hb
        rw [ha, hb, add_zero]
      zero_mem' := map_zero (η.app U)
      smul_mem' := fun a b hb => by
        rw [Set.mem_setOf_eq] at hb ⊢
        rw [smul_eq_mul, hmul, hb, smul_zero] }
  have hJmem : ∀ (U : P.affineOpens) (a : Γ(P, U.1)),
      a ∈ Jideal U ↔ η.app U (show (unit p).obj U.1 from a) = 0 := fun U a => Iff.rfl
  have hJbasic : ∀ (U : P.affineOpens) (r : Γ(P, U.1)),
      (Jideal U).map (P.presheaf.map (homOfLE <| P.basicOpen_le r).op).hom = Jideal (P.affineBasicOpen r) := by
    intro U r
    haveI := U.2.isLocalization_basicOpen r
    have eρ : algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) = (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom := rfl
    apply le_antisymm
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap]
      refine (hJmem (P.affineBasicOpen r) _).mpr ?_
      rw [hJmem] at ha
      exact (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) a).trans (by rw [ha, map_zero])
    · intro x hx
      replace hx := (hJmem (P.affineBasicOpen r) x).mp hx
      obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) x
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      simp only at hs hn

      have hy0 : η.app (P.affineBasicOpen r)
          (show (unit p).obj (P.basicOpen r) from algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) y) = 0 := by
        rw [← hs, mul_comm]
        exact (hmul (P.affineBasicOpen r) _ x).trans (by rw [hx, smul_zero])
      have hy1 : G.res (P.basicOpen_le r) (η.app U (show (unit p).obj U.1 from y)) = 0 :=
        (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) y).symm.trans hy0
      obtain ⟨k, hk⟩ := (hGq U r).2 _ hy1

      have hmem : r ^ k * y ∈ Jideal U := by rw [hJmem, hmul]; exact hk
      have hunit : IsUnit (algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1)))) :=
        IsLocalization.map_units (M := Submonoid.powers r) _
          ⟨r ^ k * (s : Γ(P, U.1)), (Submonoid.mem_powers_iff _ _).mpr ⟨k + n, by rw [pow_add, hn]⟩⟩
      obtain ⟨v, hv⟩ := hunit.exists_left_inv
      have hx' : x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
        calc x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1))) * x := by
                rw [hv, one_mul]
          _ = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
                rw [map_mul, map_mul, mul_assoc, mul_assoc, ← hs, mul_comm x]
      rw [hx', eρ]
      exact Ideal.mul_mem_left _ v (Ideal.mem_map_of_mem _ hmem)
  let J : P.IdealSheafData := ⟨Jideal, hJbasic, _, rfl⟩
  have hJideal : ∀ U : P.affineOpens, J.ideal U = Jideal U := fun U => rfl
  refine ⟨J, fun n => ?_⟩

  haveI : IsClosedImmersion (S.h n) :=
    (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
  have step3 : J ⊔ (adicThickeningι p I n).ker = (Jn n).map (adicThickeningι p I n) := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, hJideal, Scheme.Hom.ker_apply, ideal_map_of_isAffineHom]

    have hJn : (Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩ =
        RingHom.ker ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom := by
      conv_lhs => rw [← ker_subschemeι (Jn n)]
      rw [Scheme.Hom.ker_apply]
    have hcomp : ∀ a : Γ(P, U.1), ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom
        (((adicThickeningι p I n).app U.1).hom a) = S.bapp n U.1 a := by
      intro a
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_app]
      change ((S.h n).app U.1).hom a = _
      rw [Scheme.Hom.app_eq_appLE]

    have hR : ∀ a : Γ(P, U.1), a ∈ ((Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩).comap
        ((adicThickeningι p I n).app U.1).hom ↔
        η.app U (show (unit p).obj U.1 from a) ∈ I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)) := by
      intro a
      rw [Ideal.mem_comap, hJn, RingHom.mem_ker, hcomp, ← hψk n U, LinearMap.mem_ker]
      have := congrArg (fun θ : AffHom (unit p) (S.B n) => θ.app U (show (unit p).obj U.1 from a)) (hη n)
      dsimp only at this
      rw [AffHom.comp_app] at this
      rw [this]
      exact Iff.rfl
    apply le_antisymm
    · refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [hR]; rw [hJmem] at ha; rw [ha]; exact Submodule.zero_mem _
      · rw [Ideal.mem_comap, hJn, RingHom.mem_ker]
        rw [RingHom.mem_ker] at ha
        rw [ha, map_zero]
    · intro a ha
      rw [hR] at ha

      have hrange : (I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))) =
          (I ^ (n + 1) • (⊤ : Submodule R ((unit p).obj U.1))).map (η.app U) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hηs U)]
      rw [hrange] at ha
      obtain ⟨b, hb, hηb⟩ := ha
      have hab : (show Γ(P, U.1) from a) - (show Γ(P, U.1) from b) ∈ Jideal U := by
        rw [hJmem]
        change η.app U ((show (unit p).obj U.1 from a) - b) = 0
        rw [map_sub, hηb, sub_self]
      have hbker : (show Γ(P, U.1) from b) ∈ RingHom.ker ((adicThickeningι p I n).app U.1).hom := by
        refine Submodule.smul_induction_on hb (fun r hr c _ => ?_) (fun x y hx hy => ?_)
        · rw [RingHom.mem_ker]
          letI := Scheme.TwoAffineOpenCover.algebraOfHom p U.1
          letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι p I n ≫ p) ((adicThickeningι p I n) ⁻¹ᵁ U.1)
          change ((adicThickeningι p I n).app U.1).hom (algebraMap R Γ(P, U.1) r * (show Γ(P, U.1) from c)) = 0
          rw [map_mul, Scheme.Hom.app_eq_appLE, appLE_algebraMap]
          rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
            appLE_ΓSpecIso_inv_eq_zero (I ^ (n + 1)) (adicThickeningToBase p I n) _ r hr _
              (adicThickeningι_comp p I n), zero_mul]
        · exact Ideal.add_mem _ hx hy
      have : a = ((show Γ(P, U.1) from a) - (show Γ(P, U.1) from b)) + (show Γ(P, U.1) from b) := by
        change a = a - _ + _; abel
      rw [this]
      exact Submodule.add_mem_sup hab hbker
  calc J.comap (adicThickeningι p I n)
      = (J ⊔ (adicThickeningι p I n).ker).comap (adicThickeningι p I n) := (comap_sup_ker _ J).symm
    _ = ((Jn n).map (adicThickeningι p I n)).comap (adicThickeningι p I n) := by rw [step3]
    _ = Jn n := comap_map_of_isClosedImmersion _ _

end
end P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open _root_.AlgebraicGeometry hiding OModulePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsProper g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by

  have hgr : ∀ n : ℕ, adicThickeningι f I n ≫ f = (φ n ≫ adicThickeningι g I n) ≫ g := by
    intro n
    rw [adicThickeningι_comp, Category.assoc, adicThickeningι_comp, ← Category.assoc, hφ n]
  have hgrp : ∀ n : ℕ, pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) ≫ (pullback.fst f g ≫ f) =
      adicThickeningToBase f I n ≫ adicThickeningBase I n := by
    intro n
    rw [← Category.assoc, pullback.lift_fst, adicThickeningι_comp]
  obtain ⟨γ, hγdef⟩ : ∃ γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n, ∀ n, γ n =
      pullback.lift (pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n)) (adicThickeningToBase f I n) (hgrp n) :=
    ⟨_, fun n => rfl⟩
  have hγ0 : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n =
      pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) := fun n => by
    rw [hγdef]; exact pullback.lift_fst _ _ _
  have hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_fst]
  have hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_snd]
  have hGK := AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph I f g φ hφ hφt γ hγ₁ hγ₂

  obtain ⟨J, hJ⟩ := AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isProper I
    (pullback.fst f g ≫ f) (fun n => (γ n).ker) (fun n => (hGK n).2)

  have hζw : ∀ n : ℕ, (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) ≫ f =
      adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ adicThickeningBase I n := by
    intro n
    rw [Category.assoc, Category.assoc, adicThickeningι_comp]
  let ζ : ∀ n : ℕ, adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n := fun n =>
    pullback.lift (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g)
      (adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n) (hζw n)
  have hζ : ∀ n : ℕ, ζ n ≫ adicThickeningι f I n =
      adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g := fun n => by
    rw [adicThickeningι_def]; exact pullback.lift_fst _ _ _
  have hζ' : ∀ n : ℕ, ζ n ≫ adicThickeningToBase f I n = adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n := fun n => by
    rw [adicThickeningToBase_def]; exact pullback.lift_snd _ _ _
  have hGT := fun n : ℕ => AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq I f g J γ
    (fun n => (hGK n).1) hJ hγ₁ n (ζ n) (hζ n)

  have hiso : IsIso (J.subschemeι ≫ pullback.fst f g) := by
    apply AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
      R I f (J.subschemeι ≫ pullback.fst f g) (adicThickeningBase I) (fun _ => rfl)
    intro n
    let e := J.subschemeι ≫ pullback.fst f g
    have t : IsPullback (adicThickeningToBase f I n) (adicThickeningι f I n)
        (adicThickeningBase I n) f := (IsPullback.of_hasPullback _ _).flip
    have s : IsPullback (ζ n ≫ adicThickeningToBase f I n)
        (adicThickeningι (e ≫ f) I n) (adicThickeningBase I n) (e ≫ f) := by
      rw [hζ']; exact (IsPullback.of_hasPullback _ _).flip
    have hp := (IsPullback.of_right s (hζ n) t).flip
    haveI : IsIso (ζ n) := (hGT n).1
    change IsIso (pullback.snd e (adicThickeningι f I n))
    rw [← hp.isoPullback_inv_snd]
    infer_instance

  refine ⟨inv (J.subschemeι ≫ pullback.fst f g) ≫ J.subschemeι ≫ pullback.snd f g, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
  · intro n
    haveI := (hGT n).1
    have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
        (J.subschemeι ≫ pullback.fst f g) := by
      rw [IsIso.eq_inv_comp, hζ n]
    rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
      Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]
  · rintro ψ' ⟨hψ'g, hψ'n⟩
    apply AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete R I f g (adicThickeningBase I) (fun _ => rfl) ψ' _ hψ'g
    · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
    · intro n
      haveI := (hGT n).1
      have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
          (J.subschemeι ≫ pullback.fst f g) := by
        rw [IsIso.eq_inv_comp, hζ n]
      change adicThickeningι f I n ≫ ψ' = adicThickeningι f I n ≫ _
      rw [hψ'n n]
      conv_rhs => rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
        Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]

end P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open _root_.AlgebraicGeometry 

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsProper g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry

noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Formal restrictions determine a morphism from the whole proper model. -/
theorem hom_ext (M : Model k T) (hM : IsModel k T M)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (PowerSeries k))) [IsSeparated p]
    {f f' : M.X ⟶ Y} (hf : f ≫ p = M.p) (hf' : f' ≫ p = M.p)
    (h : ∀ n, M.inclusion n ≫ f = M.inclusion n ≫ f') : f = f' := by
  letI : IsProper M.p := hM.1
  apply AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
    (PowerSeries k) (Ideal.span {PowerSeries.X}) M.p p
    (baseInclusion k) (fun _ => rfl) f f' hf hf'
  intro n
  rw [← (hM.2.2.1 n).isoPullback_inv_fst]
  simp only [Category.assoc, h n]

/-- Inverses of a compatible family remain compatible over the same base. -/
theorem compatible_symm (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X)
    (hg : CompatibleAutos k T g) : CompatibleAutos k T (fun n => (g n).symm) := by
  constructor
  · intro n
    change (g n).inv ≫ (T.atlas n).p = (T.atlas n).p
    rw [Iso.inv_comp_eq]
    exact (hg.1 n).symm
  · intro n N h
    change T.transition n N h ≫ (g N).inv = (g n).inv ≫ T.transition n N h
    apply (cancel_epi (g n).hom).mp
    apply (cancel_mono (g N).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using (hg.2 n N h).symm

/-- There is at most one automorphism with the prescribed restrictions. -/
theorem algebraizes_unique (M : Model k T) (hM : IsModel k T M)
    {g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X} {f f' : M.X ≅ M.X}
    (hf : Algebraizes k M g f) (hf' : Algebraizes k M g f') : f = f' := by
  letI : IsProper M.p := hM.1
  apply Iso.ext
  exact hom_ext k M hM M.p hf.1 hf'.1 (fun n => (hf.2 n).trans (hf'.2 n).symm)

/-- Transport the given stage automorphisms through the actual cartesian
squares and algebraize their graphs on the proper model. -/
theorem hom_effectivity (M : Model k T) (hM : IsModel k T M)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (hg : CompatibleAutos k T g) :
    ∃ F : M.X ⟶ M.X, F ≫ M.p = M.p ∧
      ∀ n, M.inclusion n ≫ F = (g n).hom ≫ M.inclusion n := by
  letI : IsProper M.p := hM.1
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  let e (n : ℕ) : (T.atlas n).X ≅ adicThickening M.p I n :=
    (hM.2.2.1 n).isoPullback
  have he₁ (n : ℕ) : (e n).hom ≫ adicThickeningι M.p I n = M.inclusion n :=
    (hM.2.2.1 n).isoPullback_hom_fst
  have he₂ (n : ℕ) : (e n).hom ≫ adicThickeningToBase M.p I n = (T.atlas n).p :=
    (hM.2.2.1 n).isoPullback_hom_snd
  have hei₂ (n : ℕ) : (e n).inv ≫ (T.atlas n).p = adicThickeningToBase M.p I n :=
    (hM.2.2.1 n).isoPullback_inv_snd
  have het (n : ℕ) : T.transition n (n+1) (Nat.le_succ n) ≫ (e (n+1)).hom =
      (e n).hom ≫ adicThickeningTransition M.p I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι M.p I (n+1) = _ ≫ adicThickeningι M.p I (n+1)
      rw [Category.assoc, he₁, hM.2.2.2, Category.assoc, adicThickeningTransition_ι, he₁]
    · change _ ≫ adicThickeningToBase M.p I (n+1) = _ ≫ adicThickeningToBase M.p I (n+1)
      rw [Category.assoc, he₂, (T.transition_spec n (n+1) (Nat.le_succ n)).1,
        Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, he₂]
      rfl
  let φ (n : ℕ) : adicThickening M.p I n ⟶ adicThickening M.p I n :=
    (e n).inv ≫ (g n).hom ≫ (e n).hom
  have hφ (n : ℕ) : φ n ≫ adicThickeningToBase M.p I n = adicThickeningToBase M.p I n := by
    simp only [φ, Category.assoc, he₂, hg.1, hei₂]
  have hφt (n : ℕ) : adicThickeningTransition M.p I n ≫ φ (n+1) =
      φ n ≫ adicThickeningTransition M.p I n := by
    apply (cancel_epi (e n).hom).mp
    dsimp only [φ]
    rw [← Category.assoc, ← het]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← het]
    rw [← Category.assoc, hg.2 n (n+1) (Nat.le_succ n), Category.assoc]
  obtain ⟨F, hF, -⟩ :=
    CoherentEffectivity.AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
      I M.p M.p φ hφ hφt
  refine ⟨F, hF.1, fun n => ?_⟩
  rw [← he₁ n, Category.assoc, hF.2 n]
  simp only [φ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Algebraizing a family and its inverse gives inverse morphisms on the
whole model, by proper adic faithfulness. -/
theorem exists_unique_algebraizes (M : Model k T) (hM : IsModel k T M)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (hg : CompatibleAutos k T g) :
    ∃! f : M.X ≅ M.X, Algebraizes k M g f := by
  letI : IsProper M.p := hM.1
  obtain ⟨F, hFp, hF⟩ := hom_effectivity k M hM g hg
  obtain ⟨G, hGp, hG⟩ := hom_effectivity k M hM (fun n => (g n).symm) (compatible_symm k g hg)
  have hFG : F ≫ G = 𝟙 M.X := by
    apply hom_ext k M hM M.p (by rw [Category.assoc, hGp, hFp]) (Category.id_comp _)
    intro n
    rw [← Category.assoc, hF, Category.assoc, hG]
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Category.comp_id]
  have hGF : G ≫ F = 𝟙 M.X := by
    apply hom_ext k M hM M.p (by rw [Category.assoc, hFp, hGp]) (Category.id_comp _)
    intro n
    rw [← Category.assoc, hG, Category.assoc, hF]
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc, Category.comp_id]
  let f : M.X ≅ M.X := ⟨F, G, hFG, hGF⟩
  have hf : Algebraizes k M g f := ⟨hFp, hF⟩
  exact ⟨f, hf, fun f' hf' => algebraizes_unique k M hM hf' hf⟩

end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137

namespace ArithmeticThetaModelSymmetriesR0137
open CategoryTheory AlgebraicGeometry

/-- Every compatible family of stage automorphisms algebraizes uniquely on
every proper-flat model of the specified polygon tower. -/
theorem proper_tower_automorphism_effectivity :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∀ (g : ∀ n : ℕ, (T.atlas n).X ≅ (T.atlas n).X),
    CompatibleAutos k T g → ∃! f : M.X ≅ M.X, Algebraizes k M g f := by
  intro k _ _ r hr _ T M hM g hg
  exact ProperTowerAutomorphismEffectivityR0137.exists_unique_algebraizes k M hM g hg

end ArithmeticThetaModelSymmetriesR0137

#print axioms ArithmeticThetaModelSymmetriesR0137.proper_tower_automorphism_effectivity
