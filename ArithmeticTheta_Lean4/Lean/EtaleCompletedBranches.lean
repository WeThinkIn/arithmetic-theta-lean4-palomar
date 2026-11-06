import SectionCompletionDefinitions
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom

/-! Unique lifts of prescribed branches and compatible local completions. -/
universe u v w
noncomputable section
namespace ArithmeticThetaGeometricPrerequisites

/-- A prescribed residual branch lifts uniquely to any adically complete algebra. -/
theorem formally_etale_unique_adic_lift
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FormallyEtale R A] (S : Type w) [CommRing S] [Algebra R S]
    (I : Ideal S) [IsAdicComplete I S] (f₀ : A →ₐ[R] S ⧸ I) :
    ∃! f : A →ₐ[R] S, (Ideal.Quotient.mkₐ R I).comp f = f₀ := by
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f₀
  refine ⟨f, hf, fun g hg => ?_⟩
  apply Algebra.FormallyUnramified.ext_of_iInf I
  · simpa using (IsHausdorff.iInf_pow_smul (I := I) (M := S) inferInstance)
  · exact AlgHom.congr_fun (hg.trans hf.symm)

/-- The prescribed branch lifted into the actual completion. -/
lemma exists_completion_lift
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra.FormallyEtale R A] [Algebra R S]
    (I : Ideal S) (hI : I.FG) (f₀ : A →ₐ[R] S ⧸ I) :
    ∃ f : A →ₐ[R] AdicCompletion I S,
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp f = f₀ := by
  let E := (AdicCompletion.evalOneₐ I).restrictScalars R
  let K := RingHom.ker E.toRingHom
  have hK : K = I.map (algebraMap S (AdicCompletion I S)) :=
    AdicCompletion.ker_evalOneₐ_eq_map I hI
  have : IsAdicComplete K (AdicCompletion I S) := by
    rw [hK]
    exact AdicCompletion.isAdicComplete_self I hI
  let e : (AdicCompletion I S ⧸ K) ≃ₐ[R] S ⧸ I :=
    Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  obtain ⟨f, hf, _⟩ := formally_etale_unique_adic_lift R A
    (AdicCompletion I S) K (e.symm.toAlgHom.comp f₀)
  refine ⟨f, ?_⟩
  ext x
  have H := congrArg e (AlgHom.congr_fun hf x)
  change e (Ideal.Quotient.mk K (f x)) = e (e.symm (f₀ x)) at H
  rw [e.apply_symm_apply] at H
  exact H

open IsLocalRing

lemma exists_residue_inverse_lift
    (R S : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [Algebra.FormallyEtale R S] [IsLocalHom (algebraMap R S)]
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    ∃ h : S →ₐ[R] AdicCompletion (maximalIdeal R) R,
      (ResidueField.map (algebraMap R S)).comp
        ((AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom.comp h.toRingHom) =
      residue S := by

  let e : ResidueField R ≃ₐ[R] ResidueField S :=
    AlgEquiv.ofBijective
      { toRingHom := ResidueField.map (algebraMap R S)
        commutes' := fun r => ResidueField.map_residue (algebraMap R S) r } hres
  obtain ⟨h, hh⟩ := exists_completion_lift (maximalIdeal R)
    (maximalIdeal R).fg_of_isNoetherianRing
    (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (maximalIdeal S)))
  refine ⟨h, ?_⟩
  ext s
  change e (AdicCompletion.evalOneₐ (maximalIdeal R) (h s)) = residue S s
  rw [show AdicCompletion.evalOneₐ (maximalIdeal R) (h s) =
    e.symm (residue S s) from AlgHom.congr_fun hh s]
  exact e.apply_symm_apply _


/-- Compatibility of the actual completion projections. -/
lemma factorPow_eval (R : Type*) [CommRing R] (I : Ideal R)
    {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have h : c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := c.2 hle
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  exact Ideal.Quotient.eq.mpr (by simpa only [neg_sub] using Submodule.neg_mem _ h)

section Levels
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (J : Ideal S)
variable (hmax : I.map (algebraMap R S) = J)

def quotientForward (n : ℕ) : R ⧸ I ^ n →ₐ[R] S ⧸ J ^ n :=
  Ideal.quotientMapₐ (J ^ n) (Algebra.ofId R S) (by
    apply Ideal.map_le_iff_le_comap.mp
    change (I ^ n).map (algebraMap R S) ≤ J ^ n
    rw [Ideal.map_pow, hmax])

@[simp] lemma quotientForward_mk (n : ℕ) (r : R) :
    quotientForward I J hmax n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (J ^ n) (algebraMap R S r) := rfl

variable (h : S →ₐ[R] AdicCompletion I R)

include hmax in
lemma lift_kills_pow (n : ℕ) (s : S) (hs : s ∈ J ^ n) :
    AdicCompletion.evalₐ I n (h s) = 0 := by
  let t := (AdicCompletion.evalₐ I n).comp h
  have ht : t.toRingHom.comp (algebraMap R S) = algebraMap R (R ⧸ I ^ n) :=
    RingHom.ext t.commutes
  have H : (J ^ n).map t.toRingHom = ⊥ := by
    rw [← hmax, ← Ideal.map_pow, Ideal.map_map, ht]
    exact Ideal.map_quotient_self (I ^ n)
  exact Ideal.mem_bot.mp (H ▸ Ideal.mem_map_of_mem t.toRingHom hs)

def quotientBackward (n : ℕ) : S ⧸ J ^ n →ₐ[R] R ⧸ I ^ n :=
  Ideal.Quotient.liftₐ (J ^ n) ((AdicCompletion.evalₐ I n).comp h)
    (lift_kills_pow I J hmax h n)

@[simp] lemma quotientBackward_mk (n : ℕ) (s : S) :
    quotientBackward I J hmax h n (Ideal.Quotient.mk (J ^ n) s) =
      AdicCompletion.evalₐ I n (h s) := rfl

lemma quotientBackward_forward (n : ℕ) :
    (quotientBackward I J hmax h n).comp (quotientForward I J hmax n) =
      AlgHom.id R (R ⧸ I ^ n) := by
  apply Ideal.Quotient.algHom_ext
  ext

lemma factor_forward {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (quotientForward I J hmax n).toRingHom =
      (quotientForward I J hmax m).toRingHom.comp (Ideal.Quotient.factorPow I hmn) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  rfl



lemma quotientForward_backward [Algebra.FormallyUnramified R S]
    (hh : (quotientForward I J hmax 1).comp ((AdicCompletion.evalₐ I 1).comp h) =
      Ideal.Quotient.mkₐ R (J ^ 1)) (n : ℕ) :
    (quotientForward I J hmax n).comp (quotientBackward I J hmax h n) =
      AlgHom.id R (S ⧸ J ^ n) := by
  apply Ideal.Quotient.algHom_ext
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (S ⧸ J ^ 0) := by simp
    exact Subsingleton.elim _ _
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  apply Algebra.FormallyUnramified.lift_unique_of_ringHom (Ideal.Quotient.factorPow J hn)
  · refine ⟨n, ?_⟩
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_ker, ← Ideal.map_pow,
      pow_one, Ideal.map_quotient_self]
    rfl
  · ext s
    change Ideal.Quotient.factorPow J hn
      (quotientForward I J hmax n (AdicCompletion.evalₐ I n (h s))) =
      Ideal.Quotient.factorPow J hn (Ideal.Quotient.mk (J ^ n) s)
    rw [show Ideal.Quotient.factorPow J hn
      (quotientForward I J hmax n (AdicCompletion.evalₐ I n (h s))) =
      quotientForward I J hmax 1
        (Ideal.Quotient.factorPow I hn (AdicCompletion.evalₐ I n (h s))) from
        RingHom.congr_fun (factor_forward I J hmax hn) _]
    rw [factorPow_eval]
    exact AlgHom.congr_fun hh s

lemma forward_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp
      ((quotientForward I J hmax n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) =
    (quotientForward I J hmax m).toRingHom.comp (AdicCompletion.evalₐ I m).toRingHom := by
  rw [← RingHom.comp_assoc, factor_forward, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext (fun x => factorPow_eval R I hmn x)

def completionForward : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (quotientForward I J hmax n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun hmn => forward_compatible I J hmax hmn)

@[simp] lemma eval_completionForward (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionForward I J hmax x) =
      quotientForward I J hmax n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun hmn => forward_compatible I J hmax hmn) _ _

lemma factor_backward {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (quotientBackward I J hmax h n).toRingHom =
      (quotientBackward I J hmax h m).toRingHom.comp (Ideal.Quotient.factorPow J hmn) := by
  apply Ideal.Quotient.ringHom_ext
  ext s
  exact factorPow_eval R I hmn (h s)

lemma backward_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
      ((quotientBackward I J hmax h n).toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) =
    (quotientBackward I J hmax h m).toRingHom.comp (AdicCompletion.evalₐ J m).toRingHom := by
  rw [← RingHom.comp_assoc, factor_backward, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext (fun x => factorPow_eval S J hmn x)

def completionBackward : AdicCompletion J S →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (fun n => (quotientBackward I J hmax h n).toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
    (fun hmn => backward_compatible I J hmax h hmn)

@[simp] lemma eval_completionBackward (n : ℕ) (x : AdicCompletion J S) :
    AdicCompletion.evalₐ I n (completionBackward I J hmax h x) =
      quotientBackward I J hmax h n (AdicCompletion.evalₐ J n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun hmn => backward_compatible I J hmax h hmn) _ _

lemma completionBackward_forward :
    (completionBackward I J hmax h).comp (completionForward I J hmax) =
      RingHom.id (AdicCompletion I R) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ I n
    (completionBackward I J hmax h (completionForward I J hmax x)) = _
  rw [eval_completionBackward, eval_completionForward]
  exact AlgHom.congr_fun (quotientBackward_forward I J hmax h n) _

lemma completionForward_backward [Algebra.FormallyUnramified R S]
    (hh : (quotientForward I J hmax 1).comp ((AdicCompletion.evalₐ I 1).comp h) =
      Ideal.Quotient.mkₐ R (J ^ 1)) :
    (completionForward I J hmax).comp (completionBackward I J hmax h) =
      RingHom.id (AdicCompletion J S) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n
    (completionForward I J hmax (completionBackward I J hmax h x)) = _
  rw [eval_completionForward, eval_completionBackward]
  exact AlgHom.congr_fun (quotientForward_backward I J hmax h hh n) _

end Levels

/-- An essentially etale local map inducing a residue-field isomorphism induces
a base-compatible isomorphism on the actual maximal-ideal completions. -/
theorem etale_residue_trivial_completions
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : Type v) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyEtale R S]
    [IsLocalHom (algebraMap R S)]
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    ∃ e : ArithmeticThetaSectionCompletion.completedLocalRing R ≃+*
        ArithmeticThetaSectionCompletion.completedLocalRing S,
      e.toRingHom.comp (algebraMap R (ArithmeticThetaSectionCompletion.completedLocalRing R)) =
        (algebraMap S (ArithmeticThetaSectionCompletion.completedLocalRing S)).comp (algebraMap R S) := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨h, hh⟩ := exists_residue_inverse_lift R S hres
  have hh₁ : (quotientForward (maximalIdeal R) (maximalIdeal S) hmax 1).comp
      ((AdicCompletion.evalₐ (maximalIdeal R) 1).comp h) =
      Ideal.Quotient.mkₐ R (maximalIdeal S ^ 1) := by
    ext s
    have H := RingHom.congr_fun hh s
    have hc (x : R ⧸ maximalIdeal R ^ 1) :
        Ideal.Quotient.factorₐ R (le_of_eq (pow_one (maximalIdeal S)))
          (quotientForward (maximalIdeal R) (maximalIdeal S) hmax 1 x) =
        ResidueField.map (algebraMap R S)
          (Ideal.Quotient.factorₐ R (le_of_eq (pow_one (maximalIdeal R))) x) := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    apply (Ideal.quotientEquivAlgOfEq R (pow_one (maximalIdeal S))).injective
    change Ideal.Quotient.factorₐ R (le_of_eq (pow_one (maximalIdeal S)))
      (quotientForward (maximalIdeal R) (maximalIdeal S) hmax 1
        (AdicCompletion.evalₐ (maximalIdeal R) 1 (h s))) = residue S s
    rw [hc]
    exact H
  let e := RingEquiv.ofRingHom (completionForward _ _ hmax) (completionBackward _ _ hmax h)
    (completionForward_backward _ _ hmax h hh₁) (completionBackward_forward _ _ hmax h)
  refine ⟨e, ?_⟩
  apply RingHom.ext
  intro r
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ (maximalIdeal S) n
    (completionForward _ _ hmax (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) = _
  rw [eval_completionForward]
  simp only [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, quotientForward_mk, RingHom.comp_apply]

end ArithmeticThetaGeometricPrerequisites
