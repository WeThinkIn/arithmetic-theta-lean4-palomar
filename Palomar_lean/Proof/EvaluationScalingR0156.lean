module

public import FaithfulAnnularEvaluationR0156
public import SplitNormDefinitionsR0153

@[expose] public section

/-! Compatibility of the full annular evaluation with completed scaling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace EvaluationScaling

variable (k : Type) [Field k] [CharZero k]

private lemma baseSeries_constant (a : k) :
    baseSeries k (PowerSeries.C a) = HahnSeries.C (coefficientMap k a) := by
  simp [baseSeries]

private lemma coordinate_mul (a b : kˣ) (n : ℕ) :
    coordinate k (a * b) n = coefficientMap k (a : k) * coordinate k b n := by
  simp [coordinate, mul_assoc]

private lemma scaling_filtered (a : kˣ)
    (e : Chart k ≃+* Chart k) (he : ArithmeticThetaSplitNormR0153.IsScaling k a e)
    (N : ℕ) (z : Chart k)
    (hz : z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N) :
    e z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N := by
  have ht : e (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := he.1 PowerSeries.X
  have hm := Ideal.mem_map_of_mem e.toRingHom hz
  have hp : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
    ArithmeticThetaScaledTateBridgeR0046.completedPower, hp,
    Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm ⊢
  change e z ∈ Ideal.span {e (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)} ^ N at hm
  rwa [ht] at hm

lemma evaluation_comp_scaling (a b : kˣ) (n : ℕ)
    (e : Chart k ≃+* Chart k) (E : ChartField k ≃+* ChartField k)
    (he : ArithmeticThetaSplitNormR0153.IsScaling k a e)
    (hE : ArithmeticThetaSplitNormR0153.ExtendsScaling k e E)
    (v : ChartField k →+* Series k) (hv : IsEvaluation k b n v) :
    IsEvaluation k (a * b) n (v.comp E.toRingHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    change v (E _) = _
    rw [hE, he.1, hv.1]
  · change v (E _) = _
    rw [hE, he.2.1, map_mul, map_mul, hv.1, hv.2.1,
      baseSeries_constant, coordinate_mul, map_mul]
  · change v (E _) = _
    rw [hE, he.2.2, map_mul, map_mul, hv.1, hv.2.2.1,
      baseSeries_constant, coordinate_mul]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, mul_inv_rev, map_mul]
    ring
  · intro N z hz i hi
    change (v (E _)).coeff i = 0
    rw [hE]
    exact hv.2.2.2 N (e z) (scaling_filtered k a e he N z hz) i hi

end EvaluationScaling

/-- Evaluation at b W^n after actual scaling by a is evaluation at (ab) W^n,
on every element of the completed chart fraction field. -/
theorem evaluation_scaling :
    ∀ (k : Type) [Field k] [CharZero k] (a b : kˣ) (n : ℕ) (hn : 0 < n)
      (e : ArithmeticThetaKatoAnnularR0152.Chart k ≃+* ArithmeticThetaKatoAnnularR0152.Chart k)
      (E : ArithmeticThetaKatoAnnularR0152.ChartField k ≃+* ArithmeticThetaKatoAnnularR0152.ChartField k)
      (he : ArithmeticThetaSplitNormR0153.IsScaling k a e)
      (hE : ArithmeticThetaSplitNormR0153.ExtendsScaling k e E)
      (v w : ChartField k →+* Series k)
      (hv : IsEvaluation k b n v) (hw : IsEvaluation k (a*b) n w),
      ∀ g : ChartField k, v (E g) = w g := by
  intro k _ _ a b n hn e E he hE v w hv hw g
  exact RingHom.congr_fun
    (FaithfulAnnularEvaluation.evaluation_unique k (a*b) n (v.comp E.toRingHom) w
      (EvaluationScaling.evaluation_comp_scaling k a b n e E he hE v hv) hw) g

end ArithmeticThetaAnnularNormBridgeR0156

#print axioms ArithmeticThetaAnnularNormBridgeR0156.evaluation_scaling
