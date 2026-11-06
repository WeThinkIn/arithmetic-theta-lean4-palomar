import Mathlib

namespace ArithmeticThetaDiscriminant

noncomputable def partialEuler {R : Type*} [CommRing R] (a : R) (N : ℕ) :
    PowerSeries R := ∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (j + 1))

noncomputable def euler {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (partialEuler a d))

noncomputable def swap (F : PowerSeries (PowerSeries ℚ)) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (fun j => PowerSeries.coeff i (PowerSeries.coeff j F)))

noncomputable def zUnit : (PowerSeries ℚ)ˣ where
  val := 1 + PowerSeries.X
  inv := PowerSeries.invOfUnit (1 + PowerSeries.X) 1
  val_inv := PowerSeries.mul_invOfUnit _ _ (by simp)
  inv_val := PowerSeries.invOfUnit_mul _ _ (by simp)

/-- Outer variable Q, with any unit z in the coefficient ring. -/
noncomputable def gammaQ {R : Type*} [CommRing R] (z : Rˣ) : PowerSeries R :=
  PowerSeries.C (1 - (z : R)) * euler (z : R) * euler ((z⁻¹ : Rˣ) : R)

/-- Actual gamma_Q((1+t)^c), written as a t-series with Q-series coefficients. -/
noncomputable def gamma (c : ℕ) : PowerSeries (PowerSeries ℚ) :=
  swap (gammaQ (zUnit ^ c))

noncomputable def P : PowerSeries ℚ := euler 1

abbrev K := LaurentSeries ℚ
abbrev T := LaurentSeries K

noncomputable def qEmbed : PowerSeries ℚ →+* K := HahnSeries.ofPowerSeries ℤ ℚ
noncomputable def tEmbed : PowerSeries (PowerSeries ℚ) →+* T :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map qEmbed)

noncomputable def q : K := qEmbed PowerSeries.X
noncomputable def p : K := qEmbed P
noncomputable def tZ : T :=
  (HahnSeries.ofPowerSeries ℤ K) (1 + PowerSeries.X)

/-- The actual normalized formal product Q^2 (-z)^(-10) gamma(z)^25 / gamma(z^5). -/
noncomputable def f5 : T :=
  HahnSeries.single 0 (q ^ 2) * ((-tZ) ^ 10)⁻¹ * (tEmbed (gamma 1)) ^ 25 /
    tEmbed (gamma 5)

end ArithmeticThetaDiscriminant
