module

public import PeriodOneDiscriminantDefinitionsR0246
public import AllCuspNormalizedPowerIntegralityR0183
public import TateBridgesSeriesSubstitution

@[expose] public section

/-! Full coefficient descent of the specified cubic along Q ↦ t^4.
At the intermediate parameter s=t², changing s to -s exchanges the
two nonconstant two-torsion roots and fixes the third root. Consequently
the symmetric coefficients are even series. No roots of unity are adjoined. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace ArithmeticThetaPeriodOneR0246
namespace CoefficientDescent
open ArithmeticThetaTateSeries
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality.ParameterAction

variable (k : Type) [Field k] [CharZero k]

private def halfCoefficient (j : Fin 3) : PowerSeries k :=
  let a := tateX 2 0 (-1 : k)
  let b := tateX 2 1 (1 : k)
  let c := tateX 2 1 (-1 : k)
  if j.val = 0 then -(a + b + c)
  else if j.val = 1 then a*b + a*c + b*c
  else -(a*b*c)

private lemma half_expand (j : Fin 3) :
    PowerSeries.expand 2 (by decide) (halfCoefficient k j) = ramifiedCoefficient k j := by
  have h0 := (ArithmeticThetaTateBridges.ramified_substitution 2 2 0 (-1 : k)
    (by decide) (by constructor <;> norm_num [Admissible])).1
  have h1 := (ArithmeticThetaTateBridges.ramified_substitution 2 2 1 (1 : k)
    (by decide) (by constructor <;> norm_num [Admissible])).1
  have h2 := (ArithmeticThetaTateBridges.ramified_substitution 2 2 1 (-1 : k)
    (by decide) (by constructor <;> norm_num [Admissible])).1
  norm_num only [Nat.reduceMul] at h0 h1 h2
  fin_cases j <;>
    simp [halfCoefficient, ramifiedCoefficient, ArithmeticThetaCubicModelR0144.rootSeries,
      map_neg, map_add, map_mul, ← h0, ← h1, ← h2]

omit [CharZero k] in
private lemma half_rescale (j : Fin 3) :
    PowerSeries.rescale (-1 : k) (halfCoefficient k j) = halfCoefficient k j := by
  have h0 : PowerSeries.rescale (-1 : k) (tateX 2 0 (-1 : k)) = tateX 2 0 (-1 : k) := by
    simpa using rescale_tateX k (-1 : kˣ) 2 0 (by decide) (by simp) (-1)
  have h1 : PowerSeries.rescale (-1 : k) (tateX 2 1 (1 : k)) = tateX 2 1 (-1 : k) := by
    simpa using rescale_tateX k (-1 : kˣ) 2 1 (by decide) (by simp) 1
  have h2 : PowerSeries.rescale (-1 : k) (tateX 2 1 (-1 : k)) = tateX 2 1 (1 : k) := by
    simpa using rescale_tateX k (-1 : kˣ) 2 1 (by decide) (by simp) (-1)
  fin_cases j <;>
    simp only [halfCoefficient, Nat.reduceEqDiff, ↓reduceIte,
      map_neg, map_add, map_mul, h0, h1, h2] <;> ring

private lemma half_coeff_zero (j : Fin 3) (n : ℕ) (hn : ¬ 2 ∣ n) :
    PowerSeries.coeff n (halfCoefficient k j) = 0 := by
  have h := congrArg (PowerSeries.coeff n) (half_rescale k j)
  rw [PowerSeries.coeff_rescale] at h
  have he : ¬ Even n := by simpa only [even_iff_two_dvd] using hn
  rw [neg_one_pow_eq_ite, if_neg he, neg_one_mul] at h
  have htwo : (2 : k) ≠ 0 := by norm_num
  apply (mul_eq_zero.mp (show (2 : k) * PowerSeries.coeff n (halfCoefficient k j) = 0 by
    linear_combination -h)).resolve_left htwo

private lemma ramified_coeff_zero (j : Fin 3) (n : ℕ) (hn : ¬ 4 ∣ n) :
    PowerSeries.coeff n (ramifiedCoefficient k j) = 0 := by
  rw [← half_expand k j, PowerSeries.coeff_expand]
  split_ifs with h
  · apply half_coeff_zero k j (n / 2)
    intro h2
    apply hn
    obtain ⟨a, ha⟩ := h2
    refine ⟨a, ?_⟩
    have hd := Nat.mul_div_cancel' h
    omega
  · rfl

end CoefficientDescent

/-- Every coefficient of the actual ramified cubic is recovered by expanding
the prescribed period-one coefficient extraction. -/
theorem period_one_coefficient_descent :
    ∀ (k : Type) [Field k] [CharZero k], ∀ j : Fin 3,
      PowerSeries.expand 4 (by decide) (coefficient k j) = ramifiedCoefficient k j := by
  intro k _ _ j
  ext n
  rw [PowerSeries.coeff_expand]
  split_ifs with h
  · simp only [coefficient, PowerSeries.coeff_mk, Nat.mul_div_cancel' h]
  · exact (CoefficientDescent.ramified_coeff_zero k j n h).symm

#print axioms period_one_coefficient_descent
end ArithmeticThetaPeriodOneR0246
