module

public import UnaryKatoPowerDefinitionsR0160
public import DiscriminantInitial
public import Mathlib.RingTheory.PowerSeries.Expand

@[expose] public section

/-! Coefficientwise comparison of the two frozen Euler product definitions. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaUnaryKatoPowerR0160
namespace DiscriminantEtaSubstitution

open ArithmeticThetaUnaryProduct ArithmeticThetaDiscriminant

private theorem etaPartial_expand (D N : ℕ) (hD : D ≠ 0) :
    etaPartial D N = PowerSeries.expand D hD (partialEuler (1 : ℤ) N) := by
  simp [etaPartial, partialEuler, map_prod, ← pow_mul]

private theorem etaProduct_expand (D : ℕ) (hD : D ≠ 0) :
    etaProduct D = PowerSeries.expand D hD (euler (1 : ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [etaProduct, PowerSeries.coeff_mk, etaPartial_expand D n hD]
  simp only [PowerSeries.coeff_expand]
  split_ifs
  · exact partial_stable ℤ 1 (n / D) n (Nat.div_le_self n D)
  · rfl

private theorem substituted_eta (k : Type) [Field k] [CharZero k]
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    PowerSeries.map (Int.castRingHom k)
        (PowerSeries.subst (PowerSeries.X ^ d) (etaProduct (24*m^2))) =
      PowerSeries.expand (24*d*m^2) (by positivity)
        (PowerSeries.map (algebraMap ℚ k) P) := by
  have hD : 24*m^2 ≠ 0 := by positivity
  rw [← PowerSeries.expand_apply d (Nat.ne_of_gt hd), etaProduct_expand _ hD,
    PowerSeries.map_expand, PowerSeries.map_expand]
  simp only [euler_map, map_one, P]
  rw [← PowerSeries.expand_mul]
  have h : d*(24*m^2) = 24*d*m^2 := by ring
  simp only [h]

end DiscriminantEtaSubstitution

/-- The literal discriminant product is the 48th power of the cleared eta
series, and is nonzero over every characteristic-zero coefficient field. -/
theorem discriminant_eta_substitution :
    ∀ (k : Type) [Field k] [CharZero k] (d m : ℕ), 0 < d → 0 < m →
      discriminant k (24*d*m^2) =
        (ArithmeticThetaLaurentNormR0064.t k ^ (d*m^2) *
          integerSeries k (PowerSeries.subst (PowerSeries.X^d)
            (ArithmeticThetaUnaryProduct.etaProduct (24*m^2))))^48 ∧
      discriminant k (24*d*m^2) ≠ 0 := by
  intro k _ _ d m hd hm
  have hr : 24*d*m^2 ≠ 0 := by positivity
  let E : PowerSeries k := PowerSeries.expand (24*d*m^2) hr
    (PowerSeries.map (algebraMap ℚ k) ArithmeticThetaDiscriminant.P)
  have he : integerSeries k (PowerSeries.subst (PowerSeries.X^d)
      (ArithmeticThetaUnaryProduct.etaProduct (24*m^2))) =
      (HahnSeries.ofPowerSeries ℤ k) E := by
    exact congrArg (HahnSeries.ofPowerSeries ℤ k)
      (DiscriminantEtaSubstitution.substituted_eta k d m hd hm)
  have ht : (HahnSeries.ofPowerSeries ℤ k) PowerSeries.X =
      ArithmeticThetaLaurentNormR0064.t k := by
    simpa [ArithmeticThetaLaurentNormR0064.t] using
      (HahnSeries.ofPowerSeries_X_pow (Γ := ℤ) (R := k) 1)
  have hvalue : discriminant k (24*d*m^2) =
      (ArithmeticThetaLaurentNormR0064.t k ^ (d*m^2) *
        integerSeries k (PowerSeries.subst (PowerSeries.X^d)
          (ArithmeticThetaUnaryProduct.etaProduct (24*m^2))))^48 := by
    rw [he, discriminant, ← PowerSeries.expand_apply _ hr]
    simp only [map_mul, map_pow, PowerSeries.map_X, PowerSeries.expand_X, ht,
      mul_pow, ← pow_mul]
    change ArithmeticThetaLaurentNormR0064.t k ^ ((24*d*m^2)*2) *
      ((HahnSeries.ofPowerSeries ℤ k) E)^48 = _
    exact congrArg (fun n : ℕ => ArithmeticThetaLaurentNormR0064.t k ^ n *
      ((HahnSeries.ofPowerSeries ℤ k) E)^48) (by ring)
  refine ⟨hvalue, ?_⟩
  rw [hvalue, he]
  apply pow_ne_zero
  apply mul_ne_zero
  · exact pow_ne_zero _ (HahnSeries.single_ne_zero (one_ne_zero : (1 : k) ≠ 0))
  · intro h
    have hz : E = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using h)
    have hc := congrArg PowerSeries.constantCoeff hz
    change PowerSeries.constantCoeff (PowerSeries.expand _ hr _) = 0 at hc
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      ArithmeticThetaDiscriminant.P_constant, map_one] at hc
    exact one_ne_zero hc

end ArithmeticThetaUnaryKatoPowerR0160

#print axioms ArithmeticThetaUnaryKatoPowerR0160.discriminant_eta_substitution
