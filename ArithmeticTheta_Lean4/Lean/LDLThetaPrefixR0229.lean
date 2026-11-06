import RecursiveEllipsoidEnumerationR0229

/-! The exact LDL enumerator computes the accepted theta shells, prefixes,
coefficient matrix, elimination input and theta truncation map. -/
set_option autoImplicit false
namespace ArithmeticThetaLDLEnumerationR0229
namespace LDLThetaPrefix

private theorem energy_eq_form {n : ℕ} (A : QMatrix n) (x : Fin n → ℚ) :
    energy A x = A.toQuadraticForm' x := by
  simp [energy, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap, mul_comm, mul_left_comm]

private theorem gramHalf_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ) :
    (gramHalf A).toQuadraticForm' x =
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') x := by
  simp [gramHalf, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap, Finset.mul_sum, div_eq_mul_inv,
    mul_assoc, mul_comm]

private theorem gramHalf_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) : (gramHalf A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [gramHalf, hs.apply i j]

private theorem gramHalf_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hv : ArithmeticThetaComputed.validGram A) : (gramHalf A).toQuadraticForm'.PosDef := by
  intro x hx
  rw [gramHalf_form]
  exact hv.2.2 x hx

private theorem filtered_membership {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hv : ArithmeticThetaComputed.validGram A) (B m : ℕ) (hm : m ≤ B)
    (x : Fin n → ℤ) :
    x ∈ (enumerate n (gramHalf A) B).filter
        (fun y => ArithmeticThetaEnumeration.normNumerator A y = 2 * (m : ℤ)) ↔
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ) := by
  rw [Finset.mem_filter, recursive_ellipsoid_enumeration n (gramHalf A)
    (gramHalf_symm A hv.1) (gramHalf_posDef A hv), energy_eq_form, gramHalf_form]
  have hn : (ArithmeticThetaEnumeration.normNumerator A x : ℚ) =
      2 * ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) :=
    by simpa [ArithmeticThetaEnumeration.normNumerator] using
      ArithmeticThetaEnumeration.integer_numerator_identity n A x
  constructor
  · rintro ⟨_, he⟩
    have he' : (ArithmeticThetaEnumeration.normNumerator A x : ℚ) = 2 * (m : ℚ) := by
      exact_mod_cast he
    linarith
  · intro he
    constructor
    · rw [he]
      exact_mod_cast hm
    · have he' : (ArithmeticThetaEnumeration.normNumerator A x : ℚ) = 2 * (m : ℚ) := by
        rw [hn, he]
      exact_mod_cast he'

private theorem filtered_eq_shell {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hv : ArithmeticThetaComputed.validGram A) (B m : ℕ) (hm : m ≤ B) :
    (enumerate n (gramHalf A) B).filter
        (fun x => ArithmeticThetaEnumeration.normNumerator A x = 2 * (m : ℤ)) =
      ArithmeticThetaEnumeration.shellVectors A m := by
  ext x
  exact (filtered_membership A hv B m hm x).trans
    (ArithmeticThetaEnumeration.shell_membership_exact n A hv.1 hv.2.1 hv.2.2 m x).symm

private theorem coefficients_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hv : ArithmeticThetaComputed.validGram A) (B : ℕ) :
    coefficients A B = ArithmeticThetaEnumeration.coefficientsUpTo A B := by
  apply List.ext_getElem
  · simp [coefficients, ArithmeticThetaEnumeration.coefficientsUpTo]
  · intro i hi hj
    have hib : i < B + 1 := by simpa [coefficients] using hi
    have hc := (ArithmeticThetaEnumeration.coefficient_prefix_exact n A hv.1 hv.2.1 hv.2.2 B).2 ⟨i, hib⟩
    rw [List.getD_eq_getElem _ _ hj] at hc
    rw [hc]
    simp only [coefficients, List.getElem_ofFn]
    rw [filtered_eq_shell A hv B i (by omega)]
    exact ArithmeticThetaEnumeration.representation_count_exact n A hv.1 hv.2.1 hv.2.2 i

end LDLThetaPrefix

open LDLThetaPrefix in
theorem ldl_theta_prefix :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ArithmeticThetaComputed.validGram A →
      (∀ m : ℕ, shell A m = ArithmeticThetaEnumeration.shellVectors A m) ∧
      ∀ B : ℕ, coefficients A B = ArithmeticThetaEnumeration.coefficientsUpTo A B ∧
        (coefficients A B).length = B + 1 ∧ ∀ a : Fin (B+1),
          ((coefficients A B).getD a.val 0 : ℂ) =
            PowerSeries.coeff a.val (ArithmeticThetaComputed.theta A) := by
  intro n A hv
  refine ⟨fun m => filtered_eq_shell A hv m m le_rfl, ?_⟩
  intro B
  have he := coefficients_eq A hv B
  have hc := ArithmeticThetaEnumeration.coefficient_prefix_exact n A hv.1 hv.2.1 hv.2.2 B
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact hc.1
  · intro a
    rw [he, hc.2 a]
    simp only [ArithmeticThetaComputed.theta, PowerSeries.coeff_mk]

theorem ldl_coefficient_matrix :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      coefficientMatrix A B = ArithmeticThetaComputed.coefficientMatrix A B ∧
      ArithmeticThetaElimination.run (coefficientMatrix A B) =
        ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B) ∧
      (ArithmeticThetaComputed.prefixMap B).comp (ArithmeticThetaComputed.thetaMap A) =
        ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  intro n h B A hv
  have he : coefficientMatrix A B = ArithmeticThetaComputed.coefficientMatrix A B := by
    ext a i
    simp only [coefficientMatrix, ArithmeticThetaComputed.coefficientMatrix,
      ((ldl_theta_prefix n (A i) (hv i)).2 B).1]
  refine ⟨he, congrArg ArithmeticThetaElimination.run he, ?_⟩
  rw [he]
  exact ArithmeticThetaComputed.computed_prefix_map n h B A hv

end ArithmeticThetaLDLEnumerationR0229

#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix
#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix
