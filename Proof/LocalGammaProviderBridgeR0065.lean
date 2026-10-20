module

public import GenericOverlapDefinitionsR0065

@[expose] public section

/-! Equality of the local norm gamma provider and the corrected full product.
The node thickness is one; the period is the independent parameter `r`.
Both horizontal endpoint factors remain in the finite products and limits. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaGenericOverlapR0065

open ArithmeticThetaScaledTateBridgeR0046

theorem local_gamma_partial_eq
    (k : Type u) [Field k] [CharZero k] (r j N : ℕ) :
    ArithmeticThetaScaledAnnularR0050.gammaPartial k 1 r j N =
      ArithmeticThetaCorrectedGammaR0061.fullPartial k r j N := by
  simp only [ArithmeticThetaScaledAnnularR0050.gammaPartial,
    ArithmeticThetaScaledAnnularR0050.gammaFactor,
    ArithmeticThetaScaledAnnularR0050.gammaLeftExponent,
    ArithmeticThetaScaledAnnularR0050.gammaRightExponent,
    ArithmeticThetaCorrectedGammaR0061.fullPartial,
    ArithmeticThetaCorrectedGammaR0061.leftPartial,
    ArithmeticThetaCorrectedGammaR0061.rightPartial,
    ArithmeticThetaCorrectedGammaR0061.leftFactor,
    ArithmeticThetaCorrectedGammaR0061.rightFactor,
    ArithmeticThetaCorrectedGammaR0061.leftExponent,
    ArithmeticThetaCorrectedGammaR0061.rightExponent,
    ArithmeticThetaCorrectedGammaR0061.tau,
    ArithmeticThetaCorrectedGammaR0061.cx,
    ArithmeticThetaCorrectedGammaR0061.cy, Finset.prod_mul_distrib]

theorem local_gamma_provider_bridge :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ) (hr : 0 < r) (hj : j < r),
      ArithmeticThetaLocalNormR0054.gammaLocal k r j hr hj =
        ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
          (correctedGamma k r j hr hj) := by
  intro k _ _ r j hr hj
  apply congrArg (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)
  have ha := (Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 r j
      (by omega) (by omega))).1.2.2
  have hb := (Classical.choose_spec (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r j hr hj))).2.2.1
  letI : IsAdicComplete (nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) (Chart k) :=
    (IsAdicComplete.map_algebraMap_iff (nodeIdeal k 1) (Chart k)).mpr inferInstance
  have hpow (n : ℕ) : completedPower k 1 n =
      ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) ^ n := by
    simp [completedPower, nodeIdeal, completedParameter, toCompleted, Ideal.map_span]
  letI : IsHausdorff
      ((nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k))) (Chart k) := hcomp.1
  apply (IsHausdorff.eq_iff_smodEq
    (I := (nodeIdeal k 1).map (algebraMap (Node k 1) (Chart k)))
    (M := Chart k)).mpr
  intro n
  rw [SModEq.sub_mem]
  obtain ⟨Na, hNa⟩ := ha n
  obtain ⟨Nb, hNb⟩ := hb n
  have ha' := hNa (max Na Nb) (Nat.le_max_left _ _)
  have hb' := hNb (max Na Nb) (Nat.le_max_right _ _)
  rw [local_gamma_partial_eq] at ha'
  have hdiff := (completedPower k 1 n).sub_mem ha' hb'
  simp only [sub_sub_sub_cancel_right] at hdiff
  simpa only [ArithmeticThetaLocalNormR0054.gammaHorizontal,
    ArithmeticThetaLocalNormR0054.gammaUnit, correctedGamma,
    hpow, smul_eq_mul, Ideal.mul_top] using hdiff

end ArithmeticThetaGenericOverlapR0065
