import EliminationAlgorithm
namespace ArithmeticThetaElimination

theorem find_pivot_correct (m h : ℕ) (M : Matrix (Fin m) (Fin h) ℚ) (r : ℕ) (c : Fin h) :
    (findPivot M r c = none ↔ ∀ i : Fin m, r ≤ i.val → M i c = 0) ∧
    ∀ s : Fin m, findPivot M r c = some s → r ≤ s.val ∧ M s c ≠ 0 ∧
      ∀ t : Fin m, r ≤ t.val → t.val < s.val → M t c = 0 := by
  constructor
  · simp [findPivot, List.find?_eq_none]
  · intro s hs
    have hh : ((List.finRange m).find? (fun i => r ≤ i.val && M i c != 0)) = some s := hs
    rw [← List.ofFn_id] at hh
    have he := (List.find?_ofFn_eq_some_of_injective Function.injective_id).mp hh
    simp only [id_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at he
    refine ⟨he.1.1, he.1.2, ?_⟩
    intro t hrt hts
    have ht := he.2 t hts
    simpa [hrt] using ht

lemma swapRows_mul {m k l : ℕ} (N : Matrix (Fin m) (Fin k) ℚ)
    (P : Matrix (Fin k) (Fin l) ℚ) (r s : Fin m) :
    swapRows (N * P) r s = swapRows N r s * P := by
  ext i j
  by_cases hir : i = r
  · simp [swapRows, hir, Matrix.mul_apply]
  · by_cases his : i = s
    · simp [swapRows, his, Matrix.mul_apply]
    · simp [swapRows, hir, his, Matrix.mul_apply]

lemma swapRows_twice {m k : ℕ} (N : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) :
    swapRows (swapRows N r s) r s = N := by
  ext i j
  by_cases hir : i = r <;> by_cases his : i = s <;> simp_all [swapRows]

lemma pivotOperation_mul {m h k l : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (P : Matrix (Fin k) (Fin l) ℚ)
    (r s : Fin m) (c : Fin h) :
    pivotOperation M (N * P) r s c = pivotOperation M N r s c * P := by
  unfold pivotOperation
  rw [swapRows_mul]
  ext i j
  by_cases hir : i = r
  · simp [hir, Matrix.mul_apply, Finset.sum_div, div_mul_eq_mul_div]
  · simp [hir, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib,
      Finset.sum_div, Finset.mul_sum, div_mul_eq_mul_div, mul_assoc]

lemma pivotOperation_left {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) (c : Fin h) :
    pivotOperation M N r s c = pivotOperation M (1 : Matrix (Fin m) (Fin m) ℚ) r s c * N := by
  simpa using pivotOperation_mul M (1 : Matrix (Fin m) (Fin m) ℚ) N r s c

def undoPivot {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (Y : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) (c : Fin h) :
    Matrix (Fin m) (Fin k) ℚ :=
  let S := swapRows M r s
  swapRows (Matrix.of (fun i j => if i = r then S r c * Y r j
    else Y i j + S i c * Y r j)) r s

lemma undoPivot_mul {m h k l : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (P : Matrix (Fin k) (Fin l) ℚ)
    (r s : Fin m) (c : Fin h) :
    undoPivot M (N * P) r s c = undoPivot M N r s c * P := by
  unfold undoPivot
  rw [← swapRows_mul]
  apply congrArg (fun X => swapRows X r s)
  ext i j
  by_cases hir : i = r
  · simp [hir, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  · simp [hir, Matrix.mul_apply, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]

lemma undoPivot_operation {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) (c : Fin h) (hp : M s c ≠ 0) :
    undoPivot M (pivotOperation M N r s c) r s c = N := by
  have hd : swapRows M r s r c ≠ 0 := by simpa [swapRows] using hp
  have hh : (Matrix.of (fun i j => if i = r then
      swapRows M r s r c * pivotOperation M N r s c r j
      else pivotOperation M N r s c i j + swapRows M r s i c * pivotOperation M N r s c r j)) =
      swapRows N r s := by
    ext i j
    by_cases hir : i = r
    · subst i
      simp [pivotOperation]
      field_simp
    · simp [pivotOperation, hir]
  change swapRows _ r s = N
  rw [hh, swapRows_twice]

theorem pivot_operation_correct (m h : ℕ) (M : Matrix (Fin m) (Fin h) ℚ)
    (r s : Fin m) (c : Fin h) (hp : M s c ≠ 0) :
    IsUnit (pivotOperation M (1 : Matrix (Fin m) (Fin m) ℚ) r s c).det ∧
    (∀ (k : ℕ) (N : Matrix (Fin m) (Fin k) ℚ),
      pivotOperation M N r s c = pivotOperation M (1 : Matrix (Fin m) (Fin m) ℚ) r s c * N) ∧
    ∀ i : Fin m, pivotOperation M M r s c i c = if i = r then 1 else 0 := by
  refine ⟨?_, fun _ N => pivotOperation_left M N r s c, ?_⟩
  · apply Matrix.isUnit_det_of_left_inverse (B := undoPivot M 1 r s c)
    rw [← undoPivot_mul, Matrix.one_mul]
    exact undoPivot_operation M 1 r s c hp
  · intro i
    have hd : swapRows M r s r c ≠ 0 := by simpa [swapRows] using hp
    by_cases hir : i = r <;> simp [pivotOperation, hir, hd]

end ArithmeticThetaElimination
