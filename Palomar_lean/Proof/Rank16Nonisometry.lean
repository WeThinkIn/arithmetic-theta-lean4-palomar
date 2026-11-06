module

public import Rank16Coordinates
public import Rank16Definitions
public import Rank16LatticeDefinitions
public import Rank16Similarity
public import Mathlib.Data.Int.Star

@[expose] public section

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16

lemma quadratic_congruence {n : ℕ} (G U : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    U.mulVec z ⬝ᵥ G.mulVec (U.mulVec z) = z ⬝ᵥ (U.transpose * G * U).mulVec z := by
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma doubled_basis_gram (n : ℕ) (hn : n = 8 ∨ n = 16) :
    (doubledBasis n).transpose * doubledBasis n = (4 : ℤ) • latticeGram n := by
  rcases hn with rfl | rfl <;> decide +kernel

lemma doubled_basis_norm (n : ℕ) (hn : n = 8 ∨ n = 16) (z : Fin n → ℤ) :
    normNumerator n ((doubledBasis n).mulVec z) = 4 * (z ⬝ᵥ (latticeGram n).mulVec z) := by
  calc
    normNumerator n ((doubledBasis n).mulVec z) =
        (doubledBasis n).mulVec z ⬝ᵥ
          (1 : Matrix (Fin n) (Fin n) ℤ).mulVec ((doubledBasis n).mulVec z) := by
            simp [normNumerator, dotProduct, pow_two]
    _ = z ⬝ᵥ ((doubledBasis n).transpose * 1 * doubledBasis n).mulVec z :=
      quadratic_congruence _ _ _
    _ = 4 * (z ⬝ᵥ (latticeGram n).mulVec z) := by
      simp only [Matrix.mul_one, doubled_basis_gram n hn, Matrix.smul_mulVec,
        dotProduct_smul, smul_eq_mul]

lemma d16_root_first_even (z : Fin 16 → ℤ)
    (hz : z ⬝ᵥ (latticeGram 16).mulVec z = 2) : 2 ∣ z 0 := by
  let y := (doubledBasis 16).mulVec z
  have hm : DPlusDoubled 16 y := doubled_basis_member 16 (Or.inr rfl) z
  have hy0 : y 0 = z 0 := by
    simp only [y, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    norm_num [doubledBasis, Fin.ext_iff]
  have hnorm : normNumerator 16 y = 8 := by
    dsimp [y]
    rw [doubled_basis_norm 16 (Or.inr rfl), hz]
    norm_num
  rcases hm.1 with he | ho
  · have h := he 0
    rw [hy0] at h
    exact ⟨z 0 / 2, by omega⟩
  · have hs : ∀ i, (1 : ℤ) ≤ y i ^ 2 := by
      intro i
      have hi : y i ≠ 0 := by have := ho i; omega
      have := sq_pos_of_ne_zero hi
      omega
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hs i)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hb
    change 16 ≤ normNumerator 16 y at hb
    omega

lemma sum_root_generates_parity (f : Fin 16 → ℤ)
    (hf : ∀ z : Fin 16 → ℤ, z ⬝ᵥ sumGram.mulVec z = 2 → 2 ∣ f ⬝ᵥ z) :
    ∀ i, 2 ∣ f i := by
  have he (i : Fin 16) (hi : i ≠ 7 ∧ i ≠ 15) :
      (Pi.single i 1 : Fin 16 → ℤ) ⬝ᵥ sumGram.mulVec (Pi.single i 1) = 2 := by
    simp only [single_dotProduct, Matrix.mulVec_single, one_mul]
    fin_cases i <;> simp_all [sumGram, latticeGram, Matrix.reindex_apply,
      Matrix.submatrix, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks, Fin.ext_iff]
  have hb (i : Fin 16) (hi : i ≠ 7 ∧ i ≠ 15) : 2 ∣ f i := by
    simpa using hf (Pi.single i 1) (he i hi)
  have h67 : (Pi.single 6 1 + Pi.single 7 1 : Fin 16 → ℤ) ⬝ᵥ
      sumGram.mulVec (Pi.single 6 1 + Pi.single 7 1) = 2 := by
    norm_num [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct,
      Matrix.mulVec_single, sumGram, latticeGram, Matrix.reindex_apply, Matrix.submatrix,
      finSumFinEquiv, Fin.addCases, Matrix.fromBlocks, Fin.ext_iff]
  have h1415 : (Pi.single 14 1 + Pi.single 15 1 : Fin 16 → ℤ) ⬝ᵥ
      sumGram.mulVec (Pi.single 14 1 + Pi.single 15 1) = 2 := by
    norm_num [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct,
      Matrix.mulVec_single, sumGram, latticeGram, Matrix.reindex_apply, Matrix.submatrix,
      finSumFinEquiv, Fin.addCases, Matrix.fromBlocks, Fin.ext_iff]
  have h7 : 2 ∣ f 7 := by
    have ha := hf _ h67
    simp only [dotProduct_add, dotProduct_single, mul_one] at ha
    simpa using ha.sub (hb 6 (by decide))
  have h15 : 2 ∣ f 15 := by
    have ha := hf _ h1415
    simp only [dotProduct_add, dotProduct_single, mul_one] at ha
    simpa using ha.sub (hb 14 (by decide))
  intro i
  by_cases h : i = 7
  · simpa [h] using h7
  by_cases h' : i = 15
  · simpa [h'] using h15
  exact hb i ⟨h, h'⟩

theorem no_isometry : ¬ ∃ U : Matrix (Fin 16) (Fin 16) ℤ,
    IsUnit U.det ∧ U.transpose * sumGram * U = latticeGram 16 := by
  rintro ⟨U, hU, hcong⟩
  let V := U⁻¹
  have hUV : U * V = 1 := Matrix.mul_nonsing_inv U hU
  have hV : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hUV
  have hback : V.transpose * latticeGram 16 * V = sumGram := by
    rw [← hcong]
    calc
      V.transpose * (U.transpose * sumGram * U) * V =
          (U*V).transpose * sumGram * (U*V) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = sumGram := by rw [hUV]; simp
  have heven : ∀ j, 2 ∣ V 0 j := by
    apply sum_root_generates_parity
    intro z hz
    have hvz : V.mulVec z ⬝ᵥ (latticeGram 16).mulVec (V.mulVec z) = 2 := by
      rw [quadratic_congruence, hback, hz]
    exact d16_root_first_even _ hvz
  have hdiv : 2 ∣ V.det := by
    rw [Matrix.det_eq_sum_mul_adjugate_row V 0]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (heven j) _)
  rcases Int.isUnit_iff.mp hV with hv | hv <;> rw [hv] at hdiv <;> norm_num at hdiv

theorem no_similarity : ¬ ∃ (s : ℚ) (U : Matrix (Fin 16) (Fin 16) ℤ),
    0 < s ∧ IsUnit U.det ∧
    (U.map (Int.castRingHom ℚ)).transpose * sumGram.map (Int.castRingHom ℚ) *
      U.map (Int.castRingHom ℚ) = s • (latticeGram 16).map (Int.castRingHom ℚ) := by
  rintro ⟨s, U, hs, hU, h⟩
  have hs1 := similarity_scale s hs U hU h
  rw [hs1, one_smul] at h
  apply no_isometry
  refine ⟨U, hU, ?_⟩
  apply Matrix.map_injective (f := Int.castRingHom ℚ) (by exact Int.cast_injective)
  change (U.transpose * sumGram * U).map (Int.castRingHom ℚ) = _
  rw [Matrix.map_mul, Matrix.map_mul]
  have htrans : U.transpose.map (Int.castRingHom ℚ) = (U.map (Int.castRingHom ℚ)).transpose := by rfl
  rw [htrans]
  exact h

end ArithmeticThetaRank16
