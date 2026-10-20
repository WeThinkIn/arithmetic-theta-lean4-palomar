module

public import ScaledAlgebraicSplitR0051
public import ScaledRingCompletionExtensionR0051
public import ScaledAdditiveCompletionExtensionR0051
public import TateNodeRestrictedPresentation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaScaledNormalRecoveryR0051

open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaNodeCharts

private lemma source_power_eq_map (k : Type u) [Field k] (r n : ℕ) :
    ArithmeticThetaScaledTateBridgeR0046.completedPower k r n =
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r).map
        (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) ^ n := by
  simp [ArithmeticThetaScaledTateBridgeR0046.completedPower,
    ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]

private lemma target_power_eq_map (k : Type u) [Field k] (n : ℕ) :
    ArithmeticThetaNodeCharts.completedIdeal k ^ n =
      (ArithmeticThetaNodeCharts.nodeIdeal k).map
        (ArithmeticThetaNodeCharts.toCompleted k) ^ n := by
  simp [ArithmeticThetaNodeCharts.completedIdeal,
    ArithmeticThetaNodeCharts.nodeIdeal, ArithmeticThetaNodeCharts.toCompleted,
    Ideal.map_span]

private lemma source_mem_eval_zero (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (z : CompletedNode k r)
    (hz : z ∈ completedPower k r n) :
    AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) n z = 0 := by
  have hfg : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r).FG :=
    Submodule.fg_span (by simp)
  have hz' : z ∈ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r).map
      (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) ^ n := by
    rw [← source_power_eq_map k r n]
    exact hz
  have hz'' : z ∈ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n •
      (⊤ : Submodule (Node k r) (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r)) := by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    exact hz'
  have heval : AdicCompletion.eval (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r)
      (Node k r) n z = 0 := by
    apply (AdicCompletion.pow_smul_top_le_ker_eval
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) n)
    exact hz''
  rw [← AdicCompletion.factor_eval_eq_evalₐ
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) z (by simp), heval]
  rfl

private lemma source_approximation (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (n : ℕ) (z : CompletedNode k r) :
    ∃ a : Node k r, z - toCompleted k r a ∈ completedPower k r n := by
  obtain ⟨_, _, _, _, _, _, happrox⟩ :=
    ArithmeticThetaScaledTateBridgeR0046.completion_reductions k r hr
  obtain ⟨p, hp⟩ := happrox n z
  exact ⟨quotientMap k r p, hp⟩

private lemma target_approximation (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (z : ArithmeticThetaNodeCharts.CompletedNode k) :
    ∃ b : ArithmeticThetaNodeCharts.Node k,
      z - ArithmeticThetaNodeCharts.toCompleted k b ∈
        ArithmeticThetaNodeCharts.completedIdeal k ^ n := by
  obtain ⟨red, hred, _⟩ := node_completion_finite_reductions k n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (red (Ideal.Quotient.mk (ArithmeticThetaNodeCharts.completedIdeal k ^ n) z))
  refine ⟨b, ?_⟩
  have hz : Ideal.Quotient.mk (ArithmeticThetaNodeCharts.completedIdeal k ^ n) z =
      Ideal.Quotient.mk _ (ArithmeticThetaNodeCharts.toCompleted k b) :=
    red.injective (hb.symm.trans (hred b).symm)
  exact Ideal.Quotient.eq.mp hz

theorem completed_split_laws :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      ∀ (f : (ArithmeticThetaScaledTateBridgeR0046.Node k r →+* ArithmeticThetaNodeCharts.Node k))
        (p : (ArithmeticThetaNodeCharts.Node k →+ ArithmeticThetaScaledTateBridgeR0046.Node k r))
        (F : (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
          ArithmeticThetaNodeCharts.CompletedNode k))
        (P : (ArithmeticThetaNodeCharts.CompletedNode k →+
          ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r)),
      AlgebraicSplit k r f p → RingExtension k r f F → AdditiveExtension k r p P →
      (∀ a : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r, P (F a) = a) ∧
      (∀ (a : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r)
          (b : ArithmeticThetaNodeCharts.CompletedNode k),
        P (F a * b) = a * P b) := by
  intro k _ _ r hr f p F P hsplit hF hP
  rcases hsplit with ⟨_, _, _, hret, hsemi, _, _, _, _⟩
  have hnode_retract : ∀ a : Node k r,
      P (F (toCompleted k r a)) = toCompleted k r a := by
    intro a
    rw [hF.1 a, hP.1, hret]

  have hretract : ∀ a : CompletedNode k r, P (F a) = a := by
    intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a₀, ha₀⟩ := source_approximation k r hr n a
    have hdiff : F a - F (toCompleted k r a₀) ∈
        ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n) := by
      rw [← map_sub]
      exact hF.2 n (a - toCompleted k r a₀) ha₀
    have hPdiff : P (F a) - P (F (toCompleted k r a₀)) ∈
        completedPower k r n := by
      rw [← map_sub]
      exact hP.2 n _ hdiff
    have hlast : toCompleted k r a₀ - a ∈ completedPower k r n := by
      simpa [sub_eq_add_neg] using (completedPower k r n).neg_mem ha₀
    have hmem : P (F a) - a ∈ completedPower k r n := by
      have hadd := (completedPower k r n).add_mem hPdiff hlast
      convert hadd using 1
      rw [hnode_retract a₀]
      ring
    have hz := source_mem_eval_zero k r n (P (F a) - a) hmem
    have hz' : AdicCompletion.evalₐ (nodeIdeal k r) n (P (F a)) -
        AdicCompletion.evalₐ (nodeIdeal k r) n a = 0 := by
      simpa [map_sub] using hz
    exact sub_eq_zero.mp hz'

  refine ⟨hretract, ?_⟩
  intro a b
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a₀, ha₀⟩ := source_approximation k r hr n a
  obtain ⟨b₀, hb₀⟩ := target_approximation k (r * n) b
  have hfa : F a - F (toCompleted k r a₀) ∈
      ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n) := by
    rw [← map_sub]
    exact hF.2 n (a - toCompleted k r a₀) ha₀
  have hprod : F a * b - F (toCompleted k r a₀) *
      ArithmeticThetaNodeCharts.toCompleted k b₀ ∈
      ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n) := by
    have h1 := (ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n)).mul_mem_left b hfa
    have h2 := (ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n)).mul_mem_left
      (F (toCompleted k r a₀)) hb₀
    rw [sub_eq_add_neg]
    convert (ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n)).add_mem h1 h2 using 1 <;> ring
  have hPprod : P (F a * b) -
      P (F (toCompleted k r a₀) * ArithmeticThetaNodeCharts.toCompleted k b₀) ∈
      completedPower k r n := by
    rw [← map_sub]
    exact hP.2 n _ hprod
  have hnode : P (F (toCompleted k r a₀) *
      ArithmeticThetaNodeCharts.toCompleted k b₀) =
      toCompleted k r a₀ * P (ArithmeticThetaNodeCharts.toCompleted k b₀) := by
    rw [hF.1, ← map_mul, hP.1, hsemi, hP.1, map_mul]
  have hpb : P (ArithmeticThetaNodeCharts.toCompleted k b₀) - P b ∈
      completedPower k r n := by
    rw [← map_sub]
    apply hP.2 n _
    simpa [sub_eq_add_neg] using
      (ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n)).neg_mem hb₀
  have haa : toCompleted k r a₀ - a ∈ completedPower k r n :=
    by simpa [sub_eq_add_neg] using (completedPower k r n).neg_mem ha₀
  have hmul1 := (completedPower k r n).mul_mem_left
    (P (ArithmeticThetaNodeCharts.toCompleted k b₀)) haa
  have hmul2 := (completedPower k r n).mul_mem_left a hpb
  have hmem : P (F a * b) - a * P b ∈ completedPower k r n := by
    have hadd := (completedPower k r n).add_mem hPprod
      ((completedPower k r n).add_mem hmul1 hmul2)
    convert hadd using 1
    rw [hnode]
    ring
  have hz := source_mem_eval_zero k r n (P (F a * b) - a * P b) hmem
  have hz' : AdicCompletion.evalₐ (nodeIdeal k r) n (P (F a * b)) -
      AdicCompletion.evalₐ (nodeIdeal k r) n (a * P b) = 0 := by
    simpa [map_sub] using hz
  exact sub_eq_zero.mp hz'

end ArithmeticThetaScaledNormalRecoveryR0051
