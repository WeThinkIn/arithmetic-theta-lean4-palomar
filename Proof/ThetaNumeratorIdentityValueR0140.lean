module

public import GenericThetaEvaluationDefinitionsR0140
public import AnnularFullSeriesIdentificationR0128

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Complete identity specialization of the actual cleared theta numerator. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaAnnularThetaR0128 ArithmeticThetaSchrodingerR0119
open ArithmeticThetaIdentitySectionsR0138

private lemma theta_at_identity (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) (he : Even m) (ν : Fin m) :
    specialize k 1 (ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he 0 ν) =
      PowerSeries.X * unary k m ν := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  have hv := (theta_identity_hasSum k m he ν).tsum_eq
  change evaluate k (theta k m ν) 0 1 = _ at hv
  rw [annular_full_series_identification]
  simp only [Nat.cast_zero]
  rw [hv]
  simp [shift, ArithmeticThetaScaledAnnularR0050.thetaShift, map_mul,
    HahnSeries.ofPowerSeries_X, monomial]

/-- The complete identity value, including the vertical clearing monomial and
the specified inverse gamma-tail unit, for every coefficient vector. -/
theorem theta_numerator_identity_value :
    ∀ (k : Type u) [Field k] [CharZero k],
    ∀ (m : ℕ) (hm : 0 < m) (he : Even m),
    ∀ w : Fin m → PowerSeries k,
    specialize k 1 (thetaNumerator k m hm he w
      (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))) =
      PowerSeries.X^((2*m)^2) * (↑(commonUnit k m hm) : PowerSeries k) *
        ∑ ν : Fin m, w ν * unary k m ν := by
  intro k _ _ m hm he w
  have ht : specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      PowerSeries.X :=
    (ArithmeticThetaScaledAnnularR0050.specialization_coordinates
      k 1 0 (by decide) (by decide) 1 one_ne_zero).1
  have hx : specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = 1 := by
    simpa only [specialize, ArithmeticThetaAnnularTorsionPrereqR0053.cx,
      Units.val_one, pow_zero, map_one, mul_one] using
      (ArithmeticThetaScaledAnnularR0050.specialization_coordinates
      k 1 0 (by decide) (by decide) 1 one_ne_zero).2.1
  have hb (f : PowerSeries k) :
      specialize k 1 (ArithmeticThetaAnnularTorsionPrereqR0053.base k f) = f :=
    ArithmeticThetaScaledAnnularR0050.specialization_base
      k 1 0 (by decide) (by decide) 1 one_ne_zero f
  have hc : 1 ≤ (2*m)^2 := by nlinarith
  simp only [thetaNumerator, zeroIndex, Nat.zero_mul, pow_zero, one_mul,
    map_mul, map_pow, hx, one_pow, uniformSection, combine, map_sum, hb,
    theta_at_identity, ht, commonShift, shift,
    ArithmeticThetaScaledAnnularR0050.thetaShift, zero_add, one_pow]
  simp only [commonUnit, Units.val_pow_eq_pow_val, Units.coe_map, zeroIndex]
  rw [show (∑ ν : Fin m, w ν * (PowerSeries.X * unary k m ν)) =
      PowerSeries.X * ∑ ν : Fin m, w ν * unary k m ν by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    ring]
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hc]
  change PowerSeries.X ^ ((2*m)^2) * (∑ ν : Fin m, w ν * unary k m ν) *
      (specialize k 1) (↑((gammaTail k (2*m) (Nat.mul_pos (by decide) hm)
        (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)))⁻¹))^m =
    PowerSeries.X ^ ((2*m)^2) *
      ((specialize k 1) (↑((gammaTail k (2*m) (Nat.mul_pos (by decide) hm)
        (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)))⁻¹)))^m *
      (∑ ν : Fin m, w ν * unary k m ν)
  ring

end ArithmeticThetaGenericEvaluationR0140
