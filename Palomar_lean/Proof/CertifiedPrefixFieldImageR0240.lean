module

public import FieldSeriesImageR0233

@[expose] public section

/-! Transfer an actual complete complex kernel certificate, at any prefix,
to the same rational pivot image over every characteristic-zero field. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaScalarExtensionR0240
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaElimination
open ArithmeticThetaFieldImageR0233 ArithmeticThetaArithmeticFieldR0231

namespace CertifiedPrefixFieldImageProof
open ArithmeticThetaFieldImageR0233.FieldSharpKernelProof

/-- A rational prefix relation is a full relation by the supplied complex
certificate and injectivity of the rational coefficient map. -/
lemma rational_relation {n h : ℕ} (A : Matrices n h) (B : ℕ)
    (hcert : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin))
    (c : Fin h → ℚ) (hc : (ArithmeticThetaComputed.coefficientMatrix A B).mulVec c = 0)
    (m : ℕ) : ∑ i, PowerSeries.coeff m (theta ℚ (A i)) * c i = 0 := by
  have hcC : ((ArithmeticThetaComputed.coefficientMatrix A B).map
      (algebraMap ℚ ℂ)).mulVec (fun i => algebraMap ℚ ℂ (c i)) = 0 := by
    ext a
    have he := congrArg (algebraMap ℚ ℂ) (congrFun hc a)
    simpa [Matrix.mulVec, dotProduct] using he
  have hz : ArithmeticThetaComputed.thetaMap A (fun i => algebraMap ℚ ℂ (c i)) = 0 := by
    have hm : (fun i => algebraMap ℚ ℂ (c i)) ∈ LinearMap.ker
        ((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := hcC
    rw [← hcert] at hm
    exact hm
  apply (algebraMap ℚ ℂ).injective
  have he := congrArg (PowerSeries.coeff m) hz
  rw [← complex_combination, coeff_combination] at he
  simpa using he

/-- Rational linear functionals separate each coefficient over an arbitrary
characteristic-zero field; no embedding of that field into ℂ is needed. -/
lemma field_kernel (k : Type) [Field k] [CharZero k] {n h : ℕ}
    (A : Matrices n h) (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) (B : ℕ)
    (hcert : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin)) : Kernel k A B := by
  intro c
  constructor
  · intro hc
    ext a
    have he := congrArg (PowerSeries.coeff a.val) hc
    rw [coeff_combination] at he
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      rational_prefix A hA B, map_zero, Pi.zero_apply] using he
  · intro hc
    ext m
    rw [map_zero, coeff_combination]
    apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
    intro f
    simp only [map_sum, dual_mul]
    apply rational_relation A B hcert
    ext a
    have he := congrArg f (congrFun hc a)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply,
      map_sum, dual_mul, map_zero] using he

end CertifiedPrefixFieldImageProof

/-- Every certified prefix supplies the same full-series pivot image and
unique rational coordinates over every characteristic-zero field, including
zero rank and empty families, without a lower bound on the prefix. -/
theorem certified_prefix_field_image :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ B : ℕ,
      (LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
        LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
          (algebraMap ℚ ℂ)).mulVecLin)) → SeriesImage k A B := by
  intro k _ _ n h A hA B hcert
  classical
  have hk := CertifiedPrefixFieldImageProof.field_kernel k A hA B hcert
  have hc := FieldSeriesImageProof.coordinates k A hA B hk
  refine ⟨hk, FieldSeriesImageProof.independent k A hA B, ?_, hc, ?_⟩
  · intro c
    let d : Fin (pivotCount A B) → k := fun t =>
      ∑ j, c j * algebraMap ℚ k
        (columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t)
    have hd : seriesCombination k A c = seriesPivot k A B d := by
      simp only [seriesCombination]
      simp_rw [hc]
      simp only [seriesPivot, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [d, Finset.sum_smul]
    refine ⟨d, hd, ?_⟩
    intro e he
    exact FieldSeriesImageProof.unique k A hA B e d (he.symm.trans hd)
  · intro j d hd
    have he := FieldSeriesImageProof.unique k A hA B _ _ (hd.symm.trans (hc j))
    ext t
    exact (algebraMap ℚ k).injective (congrFun he t)

#print axioms certified_prefix_field_image
end ArithmeticThetaScalarExtensionR0240
