import ExecutableEnumerationCorrectness
import IntegrationDefinitions

namespace ArithmeticThetaComputed

theorem computed_coefficient_matrix (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hv : ∀ i, validGram (A i))
    (a : Fin (B+1)) (i : Fin h) :
    ((coefficientMatrix A B a i : ℚ) : ℂ) = PowerSeries.coeff a.val (theta (A i)) := by
  have hc := (ArithmeticThetaEnumeration.coefficient_prefix_exact n (A i)
    (hv i).1 (hv i).2.1 (hv i).2.2 B).2 a
  simp only [theta, PowerSeries.coeff_mk, coefficientMatrix]
  exact_mod_cast hc

theorem computed_prefix_map (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hv : ∀ i, validGram (A i)) :
    (prefixMap B).comp (thetaMap A) =
      ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  ext c a
  simp only [prefixMap, thetaMap, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
    map_sum, PowerSeries.coeff_smul, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.map_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← computed_coefficient_matrix n h B A hv a i]
  simp [mul_comm]

end ArithmeticThetaComputed
