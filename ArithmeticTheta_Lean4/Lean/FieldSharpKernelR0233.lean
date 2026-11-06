import FieldImageDefinitionsR0233
import SharpMatrixKernelR0195

/-! Sharp coefficient determination over arbitrary characteristic-zero fields.
Rational linear functionals detect each full-series coefficient, so no embedding
of the coefficient field into the complex numbers is required. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaFieldImageR0233
open ArithmeticThetaLatticeSectionsR0188

namespace FieldSharpKernelProof
open ArithmeticThetaArithmeticFieldR0231

lemma coeff_cast (k : Type) [Field k] [CharZero k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) :
    algebraMap ℚ k (PowerSeries.coeff m (theta ℚ A)) =
      PowerSeries.coeff m (theta k A) := by
  simp [theta, integralTheta]

lemma complex_theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    theta ℂ A = ArithmeticThetaComputed.theta A := by
  ext m
  simp [theta, integralTheta, ArithmeticThetaComputed.theta]

lemma complex_combination {n h : ℕ} (A : Matrices n h) (c : Fin h → ℂ) :
    seriesCombination ℂ A c = ArithmeticThetaComputed.thetaMap A c := by
  simp [seriesCombination, ArithmeticThetaComputed.thetaMap, complex_theta]

lemma rational_prefix {n h : ℕ} (A : Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) (B : ℕ)
    (a : Fin (B + 1)) (i : Fin h) :
    ArithmeticThetaComputed.coefficientMatrix A B a i =
      PowerSeries.coeff a.val (theta ℚ (A i)) := by
  apply (algebraMap ℚ ℂ).injective
  rw [coeff_cast, complex_theta]
  exact ArithmeticThetaComputed.computed_coefficient_matrix n h B A hA a i

lemma coeff_combination (k : Type) [Field k] [CharZero k] {n h : ℕ}
    (A : Matrices n h) (c : Fin h → k) (m : ℕ) :
    PowerSeries.coeff m (seriesCombination k A c) =
      ∑ i, algebraMap ℚ k (PowerSeries.coeff m (theta ℚ (A i))) * c i := by
  simp only [seriesCombination, map_sum, PowerSeries.coeff_smul, smul_eq_mul]
  simp_rw [← coeff_cast k]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma rational_relation {n h : ℕ} (hh : 0 < h) (A : Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) (B : ℕ)
    (hB : ArithmeticThetaSharpKernelR0195.cutoff A ≤ B)
    (c : Fin h → ℚ) (hc : (ArithmeticThetaComputed.coefficientMatrix A B).mulVec c = 0)
    (m : ℕ) : ∑ i, PowerSeries.coeff m (theta ℚ (A i)) * c i = 0 := by
  have hcC : ((ArithmeticThetaComputed.coefficientMatrix A B).map
      (algebraMap ℚ ℂ)).mulVec (fun i => algebraMap ℚ ℂ (c i)) = 0 := by
    ext a
    have he := congrArg (algebraMap ℚ ℂ) (congrFun hc a)
    simpa [Matrix.mulVec, dotProduct] using he
  have hz : ArithmeticThetaComputed.thetaMap A (fun i => algebraMap ℚ ℂ (c i)) = 0 := by
    have he := (ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel n h hh A hA).1 B hB
    have hm : (fun i => algebraMap ℚ ℂ (c i)) ∈ LinearMap.ker
        ((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := hcC
    rw [← he] at hm
    exact hm
  apply (algebraMap ℚ ℂ).injective
  have he := congrArg (PowerSeries.coeff m) hz
  rw [← complex_combination, coeff_combination] at he
  simpa using he

lemma dual_mul (k : Type) [Field k] [CharZero k] (f : k →ₗ[ℚ] ℚ)
    (q : ℚ) (x : k) : f (algebraMap ℚ k q * x) = q * f x := by
  simpa [Algebra.smul_def] using f.map_smul q x

lemma field_kernel (k : Type) [Field k] [CharZero k] {n h : ℕ}
    (hh : 0 < h) (A : Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) (B : ℕ)
    (hB : ArithmeticThetaSharpKernelR0195.cutoff A ≤ B) : Kernel k A B := by
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
    apply rational_relation hh A hA B hB
    ext a
    have he := congrArg f (congrFun hc a)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply,
      map_sum, dual_mul, map_zero] using he

lemma rank_zero_theta (k : Type) [Field k] (A : Matrix (Fin 0) (Fin 0) ℤ) :
    theta k A = 1 := by
  ext m
  simp only [theta, integralTheta, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  let e : {x : Fin 0 → ℤ //
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ)} ≃
      {x : Fin 0 → ℤ // (0 : ℕ) = m} :=
    Equiv.subtypeEquivRight fun x => by
      have hz : (fun i => (x i : ℚ)) = (0 : Fin 0 → ℚ) := Subsingleton.elim _ _
      rw [hz, QuadraticMap.map_zero]
      exact_mod_cast (Iff.rfl : (0 : ℕ) = m ↔ 0 = m)
  rw [Nat.card_congr e, ArithmeticThetaElementary.rank_zero_coefficients (fun _ => 0) rfl m]
  by_cases hm : m = 0 <;> simp [hm]

end FieldSharpKernelProof

/-- The same sharp rational prefix determines every full series relation over
every characteristic-zero field, including empty families and zero rank. -/
theorem field_sharp_kernel :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → Kernel k A B) ∧
      (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧
        ∀ c : Fin h → k, seriesCombination k A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro k _ _ n h A hA
  constructor
  · intro B hB
    by_cases hh : h = 0
    · subst h
      intro c
      simp [seriesCombination]
    · exact FieldSharpKernelProof.field_kernel k (Nat.pos_of_ne_zero hh) A hA B hB
  · intro hn
    subst n
    refine ⟨by simp [ArithmeticThetaSharpKernelR0195.cutoff], ?_⟩
    intro c
    simp [seriesCombination, FieldSharpKernelProof.rank_zero_theta, Algebra.smul_def]

#print axioms field_sharp_kernel
end ArithmeticThetaFieldImageR0233
