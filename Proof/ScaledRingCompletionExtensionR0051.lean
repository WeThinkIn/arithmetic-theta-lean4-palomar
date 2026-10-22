module

public import ScaledNormalRecoveryDefinitionsR0051
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import TateCompletedNodeNormal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
universe u

namespace ArithmeticThetaScaledNormalRecoveryR0051

open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaNodeCharts

variable (k : Type u) [Field k]

/-- The adic completion extension for a filtered map of the scaled node into the
unit-thickness node.  The construction uses the cofinal subsequence `r*n` of
powers of the target ideal. -/
theorem ring_extension_exists :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      ∀ f : (ArithmeticThetaScaledTateBridgeR0046.Node k r →+* ArithmeticThetaNodeCharts.Node k),
        ForwardFiltered k r f →
          ∃ F : (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
              ArithmeticThetaNodeCharts.CompletedNode k),
            RingExtension k r f F := by
  intro k _ _ r hr f hf
  let I : Ideal (Node k r) := nodeIdeal k r
  let J : Ideal (ArithmeticThetaNodeCharts.CompletedNode k) :=
    ArithmeticThetaNodeCharts.completedIdeal k
  have hJ : J = (ArithmeticThetaNodeCharts.nodeIdeal k).map
      (ArithmeticThetaNodeCharts.toCompleted k) := by
    simpa [J] using (ArithmeticThetaAnnularGeometry.CompletedNodeSupport.completedIdeal_eq_map k)
  have hJpow (n : ℕ) : J ^ n =
      (ArithmeticThetaNodeCharts.nodeIdeal k ^ n).map
        (ArithmeticThetaNodeCharts.toCompleted k) := by
    rw [hJ, Ideal.map_pow]
  letI : IsAdicComplete J (ArithmeticThetaNodeCharts.CompletedNode k) := by
    rw [hJ]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
      (AdicCompletion.isAdicComplete (Submodule.fg_span (by simp)))
  have hmap (n : ℕ) : I ^ n ≤ RingHom.ker
      ((Ideal.Quotient.mk (J ^ (r * n))).comp
        ((ArithmeticThetaNodeCharts.toCompleted k).comp f)) := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hJpow]
    apply Ideal.mem_map_of_mem
    exact hf n a ha
  let qmap (n : ℕ) : Node k r ⧸ I ^ n →+*
      ArithmeticThetaNodeCharts.CompletedNode k ⧸ J ^ (r * n) :=
    Ideal.Quotient.lift (I ^ n)
      ((Ideal.Quotient.mk (J ^ (r * n))).comp
        ((ArithmeticThetaNodeCharts.toCompleted k).comp f)) (hmap n)
  have qmap_mk (n : ℕ) (a : Node k r) : qmap n (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk (J ^ (r * n)) ((ArithmeticThetaNodeCharts.toCompleted k) (f a)) := by
    rfl
  have hstrict : StrictMono (fun n : ℕ => r * n) := by
    intro m n hmn
    exact (Nat.mul_lt_mul_left hr).mpr hmn
  let fam (n : ℕ) : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
      ArithmeticThetaNodeCharts.CompletedNode k ⧸ J ^ (r * n) :=
    (qmap n).comp (AdicCompletion.evalₐ I n).toRingHom
  have hq : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J (Nat.mul_le_mul_left r hmn)).comp (qmap n) =
        (qmap m).comp (Ideal.Quotient.factorPow I hmn) := by
    intro m n hmn
    apply RingHom.ext
    intro z
    refine Quotient.inductionOn' z ?_
    intro z
    rfl
  have hfam : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J (hstrict.monotone hmn)).comp (fam n) = fam m := by
    intro m n hmn
    ext z
    apply AdicCompletion.induction_on I (Node k r) z
    intro a
    change (Ideal.Quotient.factorPow J (hstrict.monotone hmn))
        (qmap n (AdicCompletion.evalₐ I n (AdicCompletion.mk I (Node k r) a))) =
      qmap m (AdicCompletion.evalₐ I m (AdicCompletion.mk I (Node k r) a))
    simp only [AdicCompletion.evalₐ_mk]
    change ((Ideal.Quotient.factorPow J (hstrict.monotone hmn)).comp (qmap n))
        ((Ideal.Quotient.mk (I ^ n)) (a.val n)) =
      (qmap m) ((Ideal.Quotient.mk (I ^ m)) (a.val m))
    rw [show hstrict.monotone hmn = Nat.mul_le_mul_left r hmn by rfl, hq hmn]
    have hz : (Ideal.Quotient.factorPow I hmn)
        ((Ideal.Quotient.mk (I ^ n)) (a.val n)) =
        (Ideal.Quotient.mk (I ^ m)) (a.val m) := by
      rw [Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hmem := (SModEq.sub_mem.mp (a.property hmn))
      have hmem' : (a.val m : Node k r) - a.val n ∈ I ^ m := by
        simpa only [smul_eq_mul, Ideal.mul_top] using hmem
      simpa [sub_eq_add_neg, add_comm] using (I ^ m).neg_mem hmem'
    simpa only [RingHom.comp_apply] using congrArg (qmap m) hz
  let F : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
      ArithmeticThetaNodeCharts.CompletedNode k :=
    IsAdicComplete.StrictMono.liftRingHom J hstrict fam (fun {m} => hfam (Nat.le_succ m))
  refine ⟨F, ?_⟩
  constructor
  · intro a
    have hagree : F.comp (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) =
        (ArithmeticThetaNodeCharts.toCompleted k).comp f := by
      apply DFunLike.coe_injective
      apply IsHausdorff.StrictMono.funext' J hstrict
      intro n z
      change (Ideal.Quotient.mk (J ^ (r * n)))
          ((IsAdicComplete.StrictMono.liftRingHom J hstrict fam
            (fun {m} => hfam (Nat.le_succ m)))
            (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z)) = _
      rw [IsAdicComplete.StrictMono.mk_liftRingHom J hstrict fam
        (fun {m} => hfam (Nat.le_succ m))]
      change qmap n (AdicCompletion.evalₐ I n
        (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z)) = _
      have hev : AdicCompletion.evalₐ I n
          (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z) =
            Ideal.Quotient.mk (I ^ n) z := by
        change AdicCompletion.evalₐ I n (AdicCompletion.of I (Node k r) z) = _
        exact AdicCompletion.evalₐ_of I n z
      rw [hev]
      exact qmap_mk n z
    exact RingHom.congr_fun hagree a
  · intro n a ha
    have hpow : ArithmeticThetaScaledTateBridgeR0046.completedPower k r n =
        (I.map (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r)) ^ n := by
      simp [ArithmeticThetaScaledTateBridgeR0046.completedPower, I,
        ArithmeticThetaScaledTateBridgeR0046.completedParameter,
        ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
        ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
    have ha' : a ∈ I ^ n • (⊤ : Submodule (Node k r)
        (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r)) := by
      rw [Ideal.smul_top_eq_map, Ideal.map_pow]
      exact hpow.symm ▸ ha
    have heval : AdicCompletion.eval I (Node k r) n a = 0 := by
      apply (AdicCompletion.pow_smul_top_le_ker_eval I n) ha'
    have hevalₐ : AdicCompletion.evalₐ I n a = 0 := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ I a (by simp), heval]
      rfl
    have hmk : Ideal.Quotient.mk (J ^ (r * n)) (F a) =
        fam n a := by
      change Ideal.Quotient.mk (J ^ (r * n))
          ((IsAdicComplete.StrictMono.liftRingHom J hstrict fam
            (fun {m} => hfam (Nat.le_succ m))) a) = _
      exact IsAdicComplete.StrictMono.mk_liftRingHom J hstrict fam
        (fun {m} => hfam (Nat.le_succ m)) a
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [hmk]
    change qmap n (AdicCompletion.evalₐ I n a) = 0
    rw [hevalₐ]
    exact map_zero (qmap n)

end ArithmeticThetaScaledNormalRecoveryR0051
