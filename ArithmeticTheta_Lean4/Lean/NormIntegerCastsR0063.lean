import NormFiniteDefinitionsR0063

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormFiniteR0063

private theorem triangle_dvd (n : ℕ) :
    (2 : ℤ) ∣ (n : ℤ) * ((n : ℤ) - 1) := by
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  let q : ℤ := (n / 2 : ℕ)
  rcases hr with h | h
  · have hn : (n : ℤ) = 2 * q := by dsimp [q]; omega
    refine ⟨2 * q ^ 2 - q, ?_⟩
    rw [hn]
    ring
  · have hn : (n : ℤ) = 2 * q + 1 := by dsimp [q]; omega
    refine ⟨2 * q ^ 2 + q, ?_⟩
    rw [hn]
    ring

private theorem triangle_cast (n : ℕ) :
    (triangle n : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  unfold triangle
  rw [Int.cast_div_charZero (triangle_dvd n)]
  norm_cast

private theorem twelve_dvd_K (c : ℕ) (hc : Nat.Coprime c 6) :
    (12 : ℤ) ∣ K c := by
  have h2 : ¬ 2 ∣ c :=
    (Nat.prime_two.coprime_iff_not_dvd).mp
      ((hc.coprime_dvd_right (by norm_num : 2 ∣ 6)).symm)
  have h3 : ¬ 3 ∣ c :=
    ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mp
      ((hc.coprime_dvd_right (by norm_num : 3 ∣ 6)).symm)
  have hr : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
  let q : ℤ := (c / 12 : ℕ)
  unfold K
  rcases hr with h | h | h | h
  · have he : (c : ℤ) = 12 * q + 1 := by dsimp [q]; omega
    refine ⟨12 * q ^ 2 + 2 * q, ?_⟩
    rw [he]
    ring
  · have he : (c : ℤ) = 12 * q + 5 := by dsimp [q]; omega
    refine ⟨12 * q ^ 2 + 10 * q + 2, ?_⟩
    rw [he]
    ring
  · have he : (c : ℤ) = 12 * q + 7 := by dsimp [q]; omega
    refine ⟨12 * q ^ 2 + 14 * q + 4, ?_⟩
    rw [he]
    ring
  · have he : (c : ℤ) = 12 * q + 11 := by dsimp [q]; omega
    refine ⟨12 * q ^ 2 + 22 * q + 10, ?_⟩
    rw [he]
    ring

theorem integer_casts :
    ∀ (c d : ℕ), Nat.Coprime c 6 →
      ((p c : ℚ) = -(c : ℚ) * ((c : ℚ) - 1) / 2) ∧
      ((S c d : ℚ) = ArithmeticThetaNormQuotientsR0062.quotientSum c d) ∧
      ((E c d : ℚ) = ArithmeticThetaNormQuotientsR0062.weightedSum c d) ∧
      (((K c / 12 : ℤ) : ℚ) = ((c : ℚ) ^ 2 - 1) / 12) ∧
      ((triangle d : ℚ) = (d : ℚ) * ((d : ℚ) - 1) / 2) := by
  intro c d hc
  refine ⟨?_, ?_, ?_, ?_, triangle_cast d⟩
  · simp only [p, Int.cast_neg, triangle_cast]
    ring
  · simp [S, ArithmeticThetaNormQuotientsR0062.quotientSum]
  · simp only [E, Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ArithmeticThetaNormQuotientsR0062.weightedSum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ArithmeticThetaNormQuotientsR0062.weightedTerm, triangle_cast]
    ring
  · rw [Int.cast_div_charZero (twelve_dvd_K c hc)]
    simp [K]

end ArithmeticThetaNormFiniteR0063
