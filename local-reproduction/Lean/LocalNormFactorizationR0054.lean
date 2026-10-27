import LocalNormDefinitionsR0054
import LocalNormExponentR0054
import LocalGammaEndpointR0054
import LocalGammaInteriorR0054
import LocalCoordinateUnitR0054
import PoweredChartPlacementR0054

/-! Association of the literal local numerator and denominator with their
horizontal factors on each completed generic chart. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

open ArithmeticThetaAnnularTorsionPrereqR0053

theorem local_norm_factorization :
    ∀ (k : Type u) [Field k] [CharZero k] (c j : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hj : j < 2*c),
      Associated (localNumerator k c j ζ hc hcop hζ hj)
        (toGeneric k ((gammaHorizontal k (2*c) j) ^ (c^2))) ∧
      Associated (localDenominator k c j ζ hc hcop hζ hj)
        (toGeneric k (horizontal k (2*c) c j)) := by
  intro k _ _ c j ζ hc hcop hζ hj
  let r := 2 * c
  have hr : 0 < r := by dsimp [r]; omega
  have hdiv : c ∣ r := by dsimp [r]; simpa [Nat.mul_comm] using (dvd_mul_right c 2)
  have hex := norm_exponent_integral c hc hcop
  have htpunit : IsUnit (tpower k (((r * (c ^ 2 - 1)) / 12 : ℕ) : ℤ)) := by
    exact ((parameterUnit k) ^ (((r * (c ^ 2 - 1)) / 12 : ℕ) : ℤ)).isUnit
  have hU : IsUnit (toGeneric k (gammaUnit k r j hr hj)) := by
    exact (Classical.choose_spec
      (ArithmeticThetaScaledAnnularR0050.gamma_unit_product
        k 1 r j (by omega) (by omega))).1.1.map (toGeneric k)
  have hU_pow : IsUnit (toGeneric k (gammaUnit k r j hr hj) ^ (c ^ 2)) :=
    hU.pow _
  have hnum_unit : IsUnit
      (tpower k (((r * (c ^ 2 - 1)) / 12 : ℕ) : ℤ) *
        toGeneric k (gammaUnit k r j hr hj) ^ (c ^ 2)) :=
    htpunit.mul hU_pow
  have hnum_eq :
      localNumerator k c j ζ hc hcop hζ hj =
        (tpower k (((r * (c ^ 2 - 1)) / 12 : ℕ) : ℤ) *
          toGeneric k (gammaUnit k r j hr hj) ^ (c ^ 2)) *
          toGeneric k (gammaHorizontal k r j) ^ (c ^ 2) := by
    simp only [localNumerator, r, gammaLocal, map_mul, mul_pow]
    ring
  have hnum : Associated (localNumerator k c j ζ hc hcop hζ hj)
      (toGeneric k ((gammaHorizontal k r j) ^ (c^2))) := by
    rw [hnum_eq]
    simpa only [map_pow] using
      (associated_unit_mul_left
        (toGeneric k (gammaHorizontal k r j) ^ (c ^ 2)) _ hnum_unit)
  have hz : IsUnit (localZ k j) := (local_coordinate_unit k j).1
  have hmon : IsUnit ((-localZ k j) ^ (c * (c - 1) / 2)) :=
    (hz.neg.pow _)
  have hp_assoc :
      Associated (poweredLocal k r c j ζ hr hc hdiv hcop hζ hj)
        (toGeneric k (horizontal k r c j)) := by
    exact (Classical.choose_spec
      (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_local_divisor
        k r c j ζ hr hc hdiv hcop hζ hj)).1.2.1
  have hden_eq :
      localDenominator k c j ζ hc hcop hζ hj =
        (-localZ k j) ^ (c * (c - 1) / 2) *
          poweredLocal k r c j ζ hr hc hdiv hcop hζ hj := by
    rfl
  have hden : Associated (localDenominator k c j ζ hc hcop hζ hj)
      (toGeneric k (horizontal k r c j)) := by
    rw [hden_eq]
    exact (associated_unit_mul_left _ _ hmon).trans (hp_assoc)
  simpa [r] using And.intro hnum hden

end ArithmeticThetaLocalNormR0054
