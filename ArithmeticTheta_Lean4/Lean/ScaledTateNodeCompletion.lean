import ScaledTateNodeAlgebra
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateBridgeR0046

open MvPolynomial MvPowerSeries

namespace CompletionNoetherian

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)

noncomputable abbrev XI : Ideal (MvPolynomial (Fin n) R) :=
  MvPolynomial.idealOfVars (Fin n) R

noncomputable abbrev ev : MvPolynomial (Fin n) R →+* R :=
  (MvPolynomial.aeval f).toRingHom

lemma ev_surjective : Function.Surjective (ev f) :=
  fun r => ⟨C r, by simp [ev]⟩

lemma ev_C (r : R) : ev f (C r) = r := by simp [ev]

lemma map_XI_eq : Ideal.map (ev f) (XI) = Ideal.span (Set.range f) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [ev]

variable (hf : Ideal.span (Set.range f) = I)
include hf

lemma XI_pow_le_comap (k : ℕ) :
    (XI : Ideal (MvPolynomial (Fin n) R)) ^ k ≤ (I ^ k).comap (ev f) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_XI_eq, hf]

lemma map_XI_pow_eq (k : ℕ) : Ideal.map (ev f) (XI ^ k) = I ^ k := by
  rw [Ideal.map_pow, map_XI_eq, hf]

noncomputable def phi (k : ℕ) : MvPowerSeries (Fin n) R →+* R ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (ev f) (XI_pow_le_comap I f hf k)).comp
    (MvPowerSeries.truncTotalAlgHom (Fin n) R k).toRingHom

lemma phi_apply (k : ℕ) (p : MvPowerSeries (Fin n) R) :
    phi I f hf k p = Ideal.Quotient.mk (I ^ k) (ev f (truncTotal k p)) := by
  simp [phi, Ideal.quotientMap_mk]

lemma phi_eq_of_sub_mem (k : ℕ) (p : MvPowerSeries (Fin n) R)
    (P : MvPolynomial (Fin n) R)
    (h : truncTotal k p - P ∈ (XI : Ideal (MvPolynomial (Fin n) R)) ^ k) :
    phi I f hf k p = Ideal.Quotient.mk (I ^ k) (ev f P) := by
  rw [phi_apply, Ideal.Quotient.eq, ← map_sub]
  exact XI_pow_le_comap I f hf k h

lemma phi_compat {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorPow I hkl).comp (phi I f hf l) = phi I f hf k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, phi_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact XI_pow_le_comap I f hf k
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hkl le_rfl _)

noncomputable def Phi : MvPowerSeries (Fin n) R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (fun k => phi I f hf k) (fun hkl => phi_compat I f hf hkl)

lemma evalₐ_Phi (k : ℕ) (p : MvPowerSeries (Fin n) R) :
    AdicCompletion.evalₐ I k (Phi I f hf p) = phi I f hf k p :=
  AdicCompletion.evalₐ_liftRingHom I _ _ k p

lemma Phi_surjective : Function.Surjective (Phi I f hf) := by
  intro y
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R y
  have hd : ∀ j : ℕ, a.val (j + 1) - a.val j ∈ I ^ j := by
    intro j
    have h := a.property (Nat.le_succ j)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [← neg_sub]
    exact neg_mem h
  have hP : ∀ j : ℕ, ∃ P : MvPolynomial (Fin n) R,
      P ∈ (XI : Ideal (MvPolynomial (Fin n) R)) ^ j ∧
        ev f P = a.val (j + 1) - a.val j := by
    intro j
    have hmem : a.val (j + 1) - a.val j ∈ Ideal.map (ev f) (XI ^ j) := by
      rw [map_XI_pow_eq I f hf]
      exact hd j
    exact (Ideal.mem_map_iff_of_surjective _ (ev_surjective f)).mp hmem
  choose P hPmem hPev using hP
  let g : MvPowerSeries (Fin n) R :=
    fun x => ∑ j ∈ Finset.range (Finsupp.degree x + 1),
      MvPolynomial.coeff x (P j)
  refine ⟨g + MvPowerSeries.C (a.val 0), ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [map_add, map_add, evalₐ_Phi, evalₐ_Phi, AdicCompletion.evalₐ_mk]
  have hg : truncTotal k g - ∑ j ∈ Finset.range k, P j ∈
      (XI : Ideal (MvPolynomial (Fin n) R)) ^ k := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hx, MvPolynomial.coeff_sum, sub_eq_zero]
    change (∑ j ∈ Finset.range (Finsupp.degree x + 1), MvPolynomial.coeff x (P j)) = _
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro j hj hj'
    simp only [Finset.mem_range, not_lt] at hj hj'
    exact (MvPolynomial.mem_pow_idealOfVars_iff' j (P j)).mp (hPmem j) x (by omega)
  rw [phi_eq_of_sub_mem I f hf k g _ hg, map_sum]
  simp_rw [hPev]
  rw [Finset.sum_range_sub (fun j => a.val j) k]
  have hC : phi I f hf k (MvPowerSeries.C (a.val 0)) =
      Ideal.Quotient.mk (I ^ k) (a.val 0) := by
    rw [phi_eq_of_sub_mem I f hf k _ (MvPolynomial.C (a.val 0)) ?_, ev_C]
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hx, MvPowerSeries.coeff_C,
      MvPolynomial.coeff_C, sub_eq_zero]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  rw [hC, ← map_add, sub_add_cancel]

end CompletionNoetherian

private theorem noetherian_adic_completion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) : IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) A) _
    (CompletionNoetherian.Phi I f hf)
    (CompletionNoetherian.Phi_surjective I f hf)

private lemma completion_eval_kernel {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext z
  have hf : Function.Injective (Ideal.Quotient.factor
      (show I ^ n • (⊤ : Ideal R) ≤ I ^ n by simp)) := by
    have h : I ^ n • (⊤ : Ideal R) = I ^ n := by simp
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      using Ideal.map_mk_eq_bot_of_le (le_of_eq h.symm)
  rw [← Ideal.map_pow]
  change AdicCompletion.evalₐ I n z = 0 ↔
    z ∈ (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n)).restrictScalars R
  rw [← Ideal.smul_top_eq_map]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I z (by simp)]
  exact map_eq_zero_iff _ hf

theorem completion_reductions :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      Function.Injective (toCompleted k r) ∧
      IsNoetherianRing (CompletedNode k r) ∧
      parameter k r ≠ 0 ∧ t k r ≠ 0 ∧ completedParameter k r ≠ 0 ∧
      Function.Injective (fun a : CompletedNode k r => completedParameter k r * a) ∧
      ∀ (n : ℕ) (z : CompletedNode k r), ∃ p : PolynomialChart k,
        z - toCompleted k r (quotientMap k r p) ∈ completedPower k r n := by
  intro k _ _ r hr
  obtain ⟨hdom, hnoeth, hfinite, hflat, hparam, ht⟩ := node_algebra k r hr
  let : IsDomain (Node k r) := hdom
  let : IsNoetherianRing (Node k r) := hnoeth
  have hproper : nodeIdeal k r ≠ ⊤ := by
    intro htop
    have htunit : IsUnit (t k r) := by
      simpa [nodeIdeal, Ideal.span_singleton_eq_top] using htop
    let origin : PolynomialChart k →+* k :=
      MvPolynomial.eval₂Hom PowerSeries.constantCoeff (fun _ => 0)
    have horigin : origin (relation k r) = 0 := by
      simp [origin, relation, parameter, hr.ne']
    let nodeOrigin : Node k r →+* k :=
      Ideal.Quotient.lift (relationIdeal k r) origin (by
        intro p hp
        exact (show relationIdeal k r ≤ RingHom.ker origin from Ideal.span_le.mpr (by
          intro q hq
          rcases Set.mem_singleton_iff.mp hq with rfl
          exact horigin)) hp)
    have himage : nodeOrigin (t k r) = 0 := by
      change nodeOrigin (quotientMap k r (MvPolynomial.C (parameter k r))) = 0
      simp [nodeOrigin, quotientMap, origin, parameter, hr.ne']
    exact not_isUnit_zero (himage ▸ htunit.map nodeOrigin)
  let : IsHausdorff (nodeIdeal k r) (Node k r) :=
    IsHausdorff.of_isDomain (nodeIdeal k r) hproper
  have hinj : Function.Injective (toCompleted k r) :=
    AdicCompletion.of_injective (nodeIdeal k r) (Node k r)
  have hcompnoeth : IsNoetherianRing (CompletedNode k r) :=
    noetherian_adic_completion (Node k r) (nodeIdeal k r)
  have hcp : completedParameter k r ≠ 0 := by
    intro hz
    exact ht (hinj (hz.trans (map_zero (toCompleted k r)).symm))
  have hmul : Function.Injective
      (fun a : CompletedNode k r => completedParameter k r * a) := by
    change Function.Injective (fun a : CompletedNode k r =>
      toCompleted k r (t k r) * a)
    exact smul_right_injective (M := CompletedNode k r) ht
  refine ⟨hinj, hcompnoeth, hparam, ht, hcp, hmul, ?_⟩
  intro n z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (nodeIdeal k r) n z)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨p, ?_⟩
  have hfg : (nodeIdeal k r).FG := Submodule.fg_span (by simp)
  have hpower : completedPower k r n =
      ((nodeIdeal k r).map (toCompleted k r)) ^ n := by
    simp [completedPower, nodeIdeal, completedParameter, toCompleted, Ideal.map_span]
  rw [hpower]
  rw [← Ideal.map_pow]
  change z - toCompleted k r (quotientMap k r p) ∈
    Ideal.map (algebraMap (Node k r) (CompletedNode k r)) (nodeIdeal k r ^ n)
  have hk : RingHom.ker (AdicCompletion.evalₐ (nodeIdeal k r) n).toRingHom =
      Ideal.map (algebraMap (Node k r) (CompletedNode k r)) (nodeIdeal k r ^ n) := by
    simpa only [Ideal.map_pow] using completion_eval_kernel (nodeIdeal k r) hfg n
  rw [← hk]
  change AdicCompletion.evalₐ (nodeIdeal k r) n
    (z - toCompleted k r (quotientMap k r p)) = 0
  simpa [toCompleted, quotientMap, AdicCompletion.evalₐ_of] using sub_eq_zero.mpr ha.symm

end ArithmeticThetaScaledTateBridgeR0046
