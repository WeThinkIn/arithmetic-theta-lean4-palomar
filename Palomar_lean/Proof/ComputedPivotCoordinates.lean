module

public import EliminationReduction

@[expose] public section

namespace ArithmeticThetaElimination

lemma transform_pivot_column {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ)
    (t : Fin (run A).pivots.length) :
    (run A).transform.mulVec (pivotColumn A t) =
      fun i => (run A).reduced i (((run A).pivots.get t).2) := by
  ext i
  rw [(run_transformation m h A).1]
  rfl

lemma reduced_column_expansion {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (j : Fin h) :
    (fun i => (run A).reduced i j) =
      ∑ t : Fin (run A).pivots.length, columnCoordinates A j t •
        (fun i => (run A).reduced i (((run A).pivots.get t).2)) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < (run A).nextRow
  · have ht : i.val < (run A).pivots.length := by rwa [(run_pivot_metadata m h A).1] at hi
    let t : Fin (run A).pivots.length := ⟨i.val, ht⟩
    have hti : ((run A).pivots.get t).1 = i :=
      Fin.ext ((run_pivot_metadata m h A).2.2.2 t)
    simp_rw [reduced_pivot_column]
    rw [← hti]
    simp only [(pivot_rows_injective A).eq_iff]
    simp [columnCoordinates]
  · have hr : (run A).nextRow ≤ i.val := by omega
    rw [(run_rowInvariant A).2.2 i hr j j.isLt]
    symm
    apply Finset.sum_eq_zero
    intro t _
    rw [reduced_pivot_column]
    have hneq : i ≠ ((run A).pivots.get t).1 := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [(run_pivot_metadata m h A).2.2.2 t] at hv
      have htt := t.isLt
      have hlen := (run_pivot_metadata m h A).1
      omega
    simp only [if_neg hneq, mul_zero]

lemma computed_columns_independent {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearIndependent ℚ (pivotColumn A) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz t
  have htrans := congrArg (run A).transform.mulVec hz
  change (run A).transform.mulVec (∑ u, z u • pivotColumn A u) = (run A).transform.mulVec 0 at htrans
  have hlin := congrArg (fun v => v (((run A).pivots.get t).1)) htrans
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, transform_pivot_column,
    Matrix.mulVec_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hlin
  simp only [reduced_pivot_column, (pivot_rows_injective A).eq_iff] at hlin
  simpa using hlin

theorem computed_pivot_coordinates (m h : ℕ) (A : Matrix (Fin m) (Fin h) ℚ) :
    LinearIndependent ℚ (pivotColumn A) ∧ ∀ j : Fin h,
      (∀ i : Fin m, A i j = ∑ t : Fin (run A).pivots.length,
        columnCoordinates A j t * pivotColumn A t i) ∧
      ∀ c : Fin (run A).pivots.length → ℚ,
        (∀ i : Fin m, A i j = ∑ t : Fin (run A).pivots.length, c t * pivotColumn A t i) →
          c = columnCoordinates A j := by
  have hi := computed_columns_independent A
  refine ⟨hi, ?_⟩
  intro j
  have hvec : (fun i => A i j) = ∑ t, columnCoordinates A j t • pivotColumn A t := by
    apply Matrix.mulVec_injective_of_isUnit
      ((run A).transform.isUnit_iff_isUnit_det.mpr (run_transformation m h A).2)
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, transform_pivot_column]
    have hleft : (run A).transform.mulVec (fun i => A i j) = fun i => (run A).reduced i j := by
      ext i
      rw [(run_transformation m h A).1]
      rfl
    rw [hleft]
    exact reduced_column_expansion A j
  refine ⟨?_, ?_⟩
  · intro i
    simpa using congrFun hvec i
  · intro c hc
    have hcvec : (fun i => A i j) = ∑ t, c t • pivotColumn A t := by
      ext i
      simpa using hc i
    have hz : ∑ t, (c t - columnCoordinates A j t) • pivotColumn A t = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [← hcvec, ← hvec, sub_self]
    have hh := Fintype.linearIndependent_iff.mp hi _ hz
    ext t
    exact sub_eq_zero.mp (hh t)

end ArithmeticThetaElimination
