module

public import RationalTateDiscriminantDefinitionsR0247

@[expose] public section

/-! Coefficient specialization of the actual period-one Tate equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace ArithmeticThetaRationalTateR0247
namespace PresentationProof
open ArithmeticThetaTateSeries ArithmeticThetaPeriodOneR0246

lemma map_inverse {K L : Type} [Field K] [Field L] (f : K →+* L)
    (s : PowerSeries K) : PowerSeries.map f s⁻¹ = (PowerSeries.map f s)⁻¹ := by
  by_cases h : PowerSeries.constantCoeff s = 0
  · rw [PowerSeries.inv_eq_zero.mpr h, map_zero,
      PowerSeries.inv_eq_zero.mpr (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, h, map_zero])]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact fun hz => h (f.injective (hz.trans (map_zero f).symm)))).mpr
    rw [← map_mul, PowerSeries.inv_mul_cancel s h, map_one]

lemma map_monomial {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a : K) (n : ℕ) : PowerSeries.map f (monomial a n) = monomial (f a) n := by
  simp [monomial]

lemma map_xTerm {K L : Type} [Field K] [Field L] (f : K →+* L)
    (s : PowerSeries K) : PowerSeries.map f (xTerm s) = xTerm (PowerSeries.map f s) := by
  simp [xTerm, map_inverse]

lemma map_partialX {K L : Type} [Field K] [Field L] (f : K →+* L)
    (d i : ℕ) (a : K) (N : ℕ) :
    PowerSeries.map f (partialX d i a N) = partialX d i (f a) N := by
  simp [partialX, map_xTerm, map_monomial, map_inverse, map_inv₀, map_ofNat]

lemma map_tateX {K L : Type} [Field K] [Field L] (f : K →+* L)
    (d i : ℕ) (a : K) : PowerSeries.map f (tateX d i a) = tateX d i (f a) := by
  ext n
  simpa only [tateX, PowerSeries.coeff_map, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff n) (map_partialX f d i a (n+1))

lemma map_root (k : Type) [Field k] [CharZero k] (j : Fin 3) :
    PowerSeries.map (algebraMap ℚ k) (ArithmeticThetaCubicModelR0144.rootSeries ℚ 4 j) =
      ArithmeticThetaCubicModelR0144.rootSeries k 4 j := by
  fin_cases j <;> simp [ArithmeticThetaCubicModelR0144.rootSeries, map_tateX]

lemma map_ramified (k : Type) [Field k] [CharZero k] (j : Fin 3) :
    PowerSeries.map (algebraMap ℚ k) (ramifiedCoefficient ℚ j) = ramifiedCoefficient k j := by
  fin_cases j <;> simp [ramifiedCoefficient, map_root]

lemma map_coefficient (k : Type) [Field k] [CharZero k] (j : Fin 3) :
    PowerSeries.map (algebraMap ℚ k) (coefficient ℚ j) = coefficient k j := by
  ext n
  simpa only [coefficient, PowerSeries.coeff_map, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff (4*n)) (map_ramified k j)

lemma map_inclusion (k : Type) [Field k] [CharZero k] (s : PowerSeries ℚ) :
    rationalMap k (HahnSeries.ofPowerSeries ℤ ℚ s) =
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (algebraMap ℚ k) s) := by
  ext n
  change (algebraMap ℚ k) ((s : LaurentSeries ℚ).coeff n) =
    ((PowerSeries.map (algebraMap ℚ k) s : LaurentSeries k).coeff n)
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map]

lemma field_equation (k : Type) [Field k] [CharZero k] :
    equation k = periodOneCurve k := by
  ext1 <;> simp [equation, periodOneCurve, WeierstrassCurve.map, map_inclusion, map_coefficient]

lemma ring_presentation (R : Type) [CommRing R] [Algebra ℚ R] :
    (equation R).IsElliptic ∧ Nonempty (CoordinateComparison (LaurentSeries ℚ)
      (LaurentSeries R) (periodOneCurve ℚ) (equation R) (rationalMap R)) := by
  let := (period_one_geometric_comparison ℚ).1
  refine ⟨inferInstanceAs (((periodOneCurve ℚ).map (rationalMap R)).IsElliptic), ?_⟩
  obtain ⟨b, a, hb, ho, ha, hx, hy, _⟩ :=
    ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_comparison
      (periodOneCurve ℚ) (rationalMap R)
  exact ⟨{ map := b
           cartesian := hb
           pointed := ho
           coefficients := rfl
           chartMap := a
           chart_eq := ha
           x_eq := hx
           y_eq := hy }⟩

end PresentationProof

/-- The rational equation is elliptic over every rational ring, has its actual
pointed Cartesian coefficient comparison, and agrees with the accepted equation
over every characteristic-zero field. -/
theorem rational_tate_presentation :
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], (equation R).IsElliptic ∧
      Nonempty (CoordinateComparison (LaurentSeries ℚ) (LaurentSeries R)
        (ArithmeticThetaPeriodOneR0246.periodOneCurve ℚ) (equation R) (rationalMap R))) ∧
    (∀ (k : Type) [Field k] [CharZero k],
      equation k = ArithmeticThetaPeriodOneR0246.periodOneCurve k) := by
  exact ⟨PresentationProof.ring_presentation, PresentationProof.field_equation⟩

#print axioms rational_tate_presentation
end ArithmeticThetaRationalTateR0247
