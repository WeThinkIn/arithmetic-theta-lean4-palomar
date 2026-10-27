import CorrectedGammaDataExistsR0061

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

open ArithmeticThetaScaledTateBridgeR0046

private theorem gamma_limit_unique
    (k : Type u) [Field k] [CharZero k] (r j : ℕ)
    (s : ℕ -> Chart k) (a b : Chart k)
    (ha : Converges k r j s a) (hb : Converges k r j s b) :
    a = b := by
  letI : IsAdicComplete (nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff (nodeIdeal k 1) (Chart k)).mpr
      inferInstance
  have hpow (n : ℕ) :
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
        ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) ^ n := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
      completedPower, nodeIdeal, completedParameter, toCompleted, Ideal.map_span]
  letI : IsHausdorff
      ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) (Chart k) :=
    hcomp.1
  apply (IsHausdorff.eq_iff_smodEq
    (I := (nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k)))
    (M := Chart k)).mpr
  intro n
  rw [SModEq.sub_mem]
  rcases ha n with ⟨Na, hNa⟩
  rcases hb n with ⟨Nb, hNb⟩
  let N := max Na Nb
  have ha' : a - s N ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n :=
    hNa N (Nat.le_max_left _ _)
  have hb' : b - s N ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n :=
    hNb N (Nat.le_max_right _ _)
  have hdiff : a - b ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n := by
    have h := (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).sub_mem
      ha' hb'
    convert h using 1 <;> ring
  simpa [hpow, smul_eq_mul, Ideal.mul_top, sub_eq_add_neg] using hdiff

theorem gamma_data_unique :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ), 0 < r -> j < r ->
      ∀ (v₁ u₁ v₂ u₂ : Chart k),
        IsGammaData k r j v₁ u₁ -> IsGammaData k r j v₂ u₂ ->
          v₁ = v₂ ∧ u₁ = u₂ := by
  intro k _ _ r j _ _ v₁ u₁ v₂ u₂ h₁ h₂
  rcases h₁ with ⟨_, htail₁, _, hfactor₁⟩
  rcases h₂ with ⟨_, htail₂, _, hfactor₂⟩
  have hv : v₁ = v₂ :=
    gamma_limit_unique k r j (tailPartial k r j) v₁ v₂ htail₁ htail₂
  refine ⟨hv, ?_⟩
  calc
    u₁ = horizontal k r j * v₁ := hfactor₁
    _ = horizontal k r j * v₂ := by rw [hv]
    _ = u₂ := hfactor₂.symm

end ArithmeticThetaCorrectedGammaR0061
