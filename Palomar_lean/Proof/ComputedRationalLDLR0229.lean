module

public import RationalSchurCompletionR0229

@[expose] public section

/-! Correctness of the fixed executable head-first rational LDL recursion. -/
set_option autoImplicit false
namespace ArithmeticThetaLDLEnumerationR0229
namespace ComputedRationalLDL

private theorem factor_entry {n : ℕ} (d : Fin n → ℚ) (U : QMatrix n)
    (i j : Fin n) :
    (U.transpose * Matrix.diagonal d * U) i j =
      ∑ k, U k i * d k * U k j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end ComputedRationalLDL

open ComputedRationalLDL in
/-- The computed factors have positive pivots, are upper unitriangular, and
reconstruct the input matrix, including in dimension zero. -/
theorem computed_rational_ldl (n : ℕ) (A : QMatrix n)
    (hs : A.IsSymm) (hp : A.toQuadraticForm'.PosDef) :
    (∀ i : Fin n, 0 < (ldl n A).1 i) ∧
    (∀ i : Fin n, (ldl n A).2 i i = 1) ∧
    (∀ i j : Fin n, j < i → (ldl n A).2 i j = 0) ∧
    A = (ldl n A).2.transpose * Matrix.diagonal (ldl n A).1 * (ldl n A).2 := by
  induction n with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, ?_⟩
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨ha, hss, hps, _⟩ := rational_schur_completion n A hs hp
    obtain ⟨hd, hu, ht, hf⟩ := ih (schur A) hss hps
    have hne : A 0 0 ≠ 0 := ne_of_gt ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [ldl, Fin.cons_zero] using ha
      · simpa only [ldl, Fin.cons_succ] using hd i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [ldl]
      · simpa only [ldl, Fin.cases_succ, Fin.cons_succ] using hu i
    · intro i j hji
      cases i using Fin.cases with
      | zero => exact (Fin.not_lt_zero j hji).elim
      | succ i =>
        cases j using Fin.cases with
        | zero => simp [ldl]
        | succ j =>
          simpa only [ldl, Fin.cases_succ, Fin.cons_succ] using
            ht i j (Fin.succ_lt_succ_iff.mp hji)
    · ext i j
      rw [factor_entry]
      cases i using Fin.cases <;> cases j using Fin.cases
      · simp [ldl, Fin.sum_univ_succ]
      · simp only [ldl, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
          Fin.cons_zero, Fin.cons_succ, one_mul, zero_mul, Finset.sum_const_zero,
          add_zero]
        field_simp
      · simpa [ldl, Fin.sum_univ_succ, hne] using hs.apply 0 _
      · rename_i i j
        have hij := congrArg (fun M : QMatrix n => M i j) hf
        rw [factor_entry] at hij
        simp only [ldl, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
          Fin.cons_zero, Fin.cons_succ]
        rw [← hij]
        simp only [schur]
        field_simp
        ring

end ArithmeticThetaLDLEnumerationR0229

#print axioms ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl
