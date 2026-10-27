import Mathlib

open scoped BigOperators

namespace ArithmeticThetaDet80

private def box (m : ℕ) : Set (ℤ × ℤ) :=
  Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) ×ˢ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1)

private lemma box_finite (m : ℕ) : (box m).Finite := by
  dsimp [box]
  exact (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)

private lemma sq_bound (x : ℤ) (m : ℕ) (h : x ^ 2 ≤ (m : ℤ)) :
    x ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hs : x ^ 2 ≤ ((m : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg x]
  have ha : |x| ≤ (m : ℤ) + 1 := (sq_le_sq).mp hs
  exact (abs_le.mp ha)

private lemma q1_bounds (x y : ℤ) (m : ℕ)
    (h : x ^ 2 + 20 * y ^ 2 = (m : ℤ)) :
    x ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) ∧
      y ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
  have hx : x ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg y]
  have hy : y ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg x]
  exact ⟨sq_bound x m hx, sq_bound y m hy⟩

private lemma q2_bounds (x y : ℤ) (m : ℕ)
    (h : 3 * x ^ 2 + 2 * x * y + 7 * y ^ 2 = (m : ℤ)) :
    x ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) ∧
      y ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
  have hid : 3 * x ^ 2 + 2 * x * y + 7 * y ^ 2 =
      (x + y) ^ 2 + 2 * x ^ 2 + 6 * y ^ 2 := by ring
  have hx : x ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg (x + y), sq_nonneg y]
  have hy : y ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg (x + y), sq_nonneg x]
  exact ⟨sq_bound x m hx, sq_bound y m hy⟩

private lemma q3_bounds (x y : ℤ) (m : ℕ)
    (h : 4 * x ^ 2 + 5 * y ^ 2 = (m : ℤ)) :
    x ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) ∧
      y ∈ Set.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
  have hx : x ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg y]
  have hy : y ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg x]
  exact ⟨sq_bound x m hx, sq_bound y m hy⟩

theorem representation_finiteness :
    ∀ (j : Fin 3) (m : ℕ), Set.Finite {v : ℤ × ℤ |
      (![v.1 ^ 2 + 20 * v.2 ^ 2,
        3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
        4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} := by
  intro j m
  have hb := box_finite m
  fin_cases j
  · apply hb.subset
    intro v hv
    exact q1_bounds v.1 v.2 m hv
  · apply hb.subset
    intro v hv
    exact q2_bounds v.1 v.2 m hv
  · apply hb.subset
    intro v hv
    exact q3_bounds v.1 v.2 m hv

private lemma card_q1_0 : Nat.card {v : ℤ × ℤ // v.1 ^ 2 + 20 * v.2 ^ 2 = (0 : ℤ)} = 1 := by
  change Nat.card (↑({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ))) = 1
  have hf : Set.Finite {v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (0 : ℤ)} := by
    simpa using representation_finiteness 0 0
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ)) = {(0, 0)} := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hx : v.1 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1, sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1, sq_nonneg v.2]
      apply Prod.ext <;> simp [sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      norm_num
  rw [h]
  simp

private lemma card_q1_1 : Nat.card {v : ℤ × ℤ // v.1 ^ 2 + 20 * v.2 ^ 2 = (1 : ℤ)} = 2 := by
  change Nat.card (↑({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ))) = 2
  have hf : Set.Finite {v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (1 : ℤ)} := by
    simpa using representation_finiteness 0 1
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ)) = {(1, 0), (-1, 0)} := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1]
      have hx : v.1 ^ 2 = 1 := by nlinarith [hv, sq_nonneg v.1]
      have hz : (v.1 - 1) * (v.1 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · have : v.1 = 1 := by omega
        left
        apply Prod.ext <;> simp [this, sq_eq_zero_iff.mp hy]
      · have : v.1 = -1 := by omega
        right
        apply Prod.ext <;> simp [this, sq_eq_zero_iff.mp hy]
    · intro hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl <;> norm_num
  rw [h]
  simp

private lemma card_q1_3 : Nat.card {v : ℤ × ℤ // v.1 ^ 2 + 20 * v.2 ^ 2 = (3 : ℤ)} = 0 := by
  change Nat.card (↑({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ))) = 0
  have hf : Set.Finite {v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (3 : ℤ)} := by
    simpa using representation_finiteness 0 3
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | v.1 ^ 2 + 20 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ)) = ∅ := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1]
      have hx : v.1 ^ 2 = 3 := by nlinarith
      have hb1 : -2 ≤ v.1 := by nlinarith [hv, sq_nonneg (v.1 + 2)]
      have hb2 : v.1 ≤ 2 := by nlinarith [hv, sq_nonneg (v.1 - 2)]
      interval_cases v.1 <;> norm_num at hx
    · simp
  rw [h]
  simp

private lemma card_q2_0 : Nat.card {v : ℤ × ℤ // 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (0 : ℤ)} = 1 := by
  change Nat.card (↑({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ))) = 1
  have hf : Set.Finite {v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (0 : ℤ)} := by
    simpa using representation_finiteness 1 0
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ)) = {(0, 0)} := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hx : v.1 ^ 2 = 0 := by nlinarith [hv, sq_nonneg (v.1 + v.2), sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg (v.1 + v.2), sq_nonneg v.1]
      apply Prod.ext <;> simp [sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      norm_num
  rw [h]
  simp

private lemma card_q2_1 : Nat.card {v : ℤ × ℤ // 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (1 : ℤ)} = 0 := by
  change Nat.card (↑({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ))) = 0
  have hf : Set.Finite {v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (1 : ℤ)} := by
    simpa using representation_finiteness 1 1
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ)) = ∅ := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hid : 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 =
          (v.1 + v.2) ^ 2 + 2 * v.1 ^ 2 + 6 * v.2 ^ 2 := by ring
      have hx : v.1 ^ 2 = 0 := by nlinarith [hv, sq_nonneg (v.1 + v.2), sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg (v.1 + v.2), sq_nonneg v.1]
      nlinarith [hv, sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
    · simp
  rw [h]
  simp

private lemma card_q2_3 : Nat.card {v : ℤ × ℤ // 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (3 : ℤ)} = 2 := by
  change Nat.card (↑({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ))) = 2
  have hf : Set.Finite {v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (3 : ℤ)} := by
    simpa using representation_finiteness 1 3
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ)) = {(1, 0), (-1, 0)} := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg (v.1 + v.2), sq_nonneg v.1]
      have hy0 : v.2 = 0 := sq_eq_zero_iff.mp hy
      have hx : v.1 ^ 2 = 1 := by simp only [hy0, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hv; omega
      have hz : (v.1 - 1) * (v.1 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · have : v.1 = 1 := by omega
        left
        apply Prod.ext <;> simp [this, sq_eq_zero_iff.mp hy]
      · have : v.1 = -1 := by omega
        right
        apply Prod.ext <;> simp [this, sq_eq_zero_iff.mp hy]
    · intro hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl <;> norm_num
  rw [h]
  simp

private lemma card_q3_0 : Nat.card {v : ℤ × ℤ // 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (0 : ℤ)} = 1 := by
  change Nat.card (↑({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ))) = 1
  have hf : Set.Finite {v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (0 : ℤ)} := by
    simpa using representation_finiteness 2 0
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (0 : ℤ)} : Set (ℤ × ℤ)) = {(0, 0)} := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hx : v.1 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1, sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [hv, sq_nonneg v.1, sq_nonneg v.2]
      apply Prod.ext <;> simp [sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      norm_num
  rw [h]
  simp

private lemma card_q3_1 : Nat.card {v : ℤ × ℤ // 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (1 : ℤ)} = 0 := by
  change Nat.card (↑({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ))) = 0
  have hf : Set.Finite {v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (1 : ℤ)} := by
    simpa using representation_finiteness 2 1
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (1 : ℤ)} : Set (ℤ × ℤ)) = ∅ := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hx : v.1 ^ 2 = 0 := by nlinarith [sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [sq_nonneg v.1]
      omega
    · simp
  rw [h]
  simp

private lemma card_q3_3 : Nat.card {v : ℤ × ℤ // 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (3 : ℤ)} = 0 := by
  change Nat.card (↑({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ))) = 0
  have hf : Set.Finite {v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (3 : ℤ)} := by
    simpa using representation_finiteness 2 3
  rw [Nat.card_eq_card_finite_toFinset hf,
    ← Set.ncard_eq_toFinset_card _ hf]
  have h : ({v : ℤ × ℤ | 4 * v.1 ^ 2 + 5 * v.2 ^ 2 = (3 : ℤ)} : Set (ℤ × ℤ)) = ∅ := by
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      have hx : v.1 ^ 2 = 0 := by nlinarith [sq_nonneg v.2]
      have hy : v.2 ^ 2 = 0 := by nlinarith [sq_nonneg v.1]
      omega
    · simp
  rw [h]
  simp

theorem actual_coefficient_matrix :
    ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ //
      (![v.1 ^ 2 + 20 * v.2 ^ 2,
        3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
        4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j =
          (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) =
      ![![1, 1, 1], ![2, 0, 0], ![0, 2, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j
  · norm_num [card_q1_0]
  · norm_num [card_q2_0]
  · norm_num [card_q3_0]
  · norm_num [card_q1_1]
  · norm_num [card_q2_1]
  · norm_num [card_q3_1]
  · norm_num [card_q1_3]
  · norm_num [card_q2_3]
  · norm_num [card_q3_3]

theorem actual_minor_determinant : Matrix.det
    ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ //
      (![v.1 ^ 2 + 20 * v.2 ^ 2,
        3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
        4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j =
          (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 4 := by
  rw [actual_coefficient_matrix]
  change (Matrix.of ![![1, 1, 1], ![2, 0, 0], ![0, 2, 0]] :
    Matrix (Fin 3) (Fin 3) ℤ).det = 4
  rw [Matrix.det_fin_three]
  decide

end ArithmeticThetaDet80
