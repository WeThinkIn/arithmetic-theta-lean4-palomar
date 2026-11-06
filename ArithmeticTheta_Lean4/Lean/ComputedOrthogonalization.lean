import OrthogonalIteration

namespace ArithmeticThetaOrthogonalAlgorithm

lemma basis_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    (basisMatrix A).IsUpperTriangular := by
  have hi := prefix_invariant n A hs hp n (le_refl n)
  exact fun _ _ h => hi.2.1 _ _ h

lemma basis_diagonal_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    ∀ i, 0 < basisMatrix A i i :=
  (prefix_invariant n A hs hp n (le_refl n)).2.2.1

theorem computed_orthogonalization (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (he : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    0 < (basisMatrix A).det ∧ (∀ i, 0 < norms A i ∧ Even (norms A i)) ∧
      (basisMatrix A).transpose * A * basisMatrix A = Matrix.diagonal (norms A) := by
  have hd := basis_diagonal_positive A hs hp
  have hi := prefix_invariant n A hs hp n (le_refl n)
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_of_isUpperTriangular (basis_upper A hs hp)]
    exact Finset.prod_pos (fun i _ => hd i)
  · intro i
    have hn : (fun a => basisMatrix A a i) ≠ 0 := by
      intro hz
      have hzi := congrFun hz i
      have hdi := hd i
      simp only [Pi.zero_apply] at hzi
      omega
    exact ⟨pairing_positive A hp _ hn, (positive_even_pairing n A hs he hp).2 _⟩
  · ext i j
    rw [pairing_gram]
    by_cases hij : i = j
    · subst j
      simp [norms]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hi.2.2.2 i j i.isLt hij

theorem computed_natural_data (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (he : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    (∀ i, 0 < naturalNorms A i ∧ Even (naturalNorms A i) ∧
      (naturalNorms A i : ℤ) = norms A i) ∧
    indexValue A = ∏ i : Fin n, (basisMatrix A i i).toNat ∧ 0 < indexValue A := by
  have hc := computed_orthogonalization n A hs he hp
  have hd := basis_diagonal_positive A hs hp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi : (naturalNorms A i : ℤ) = norms A i :=
      Int.toNat_of_nonneg (hc.2.1 i).1.le
    refine ⟨by have := (hc.2.1 i).1; omega, ?_, hi⟩
    have hev : Even (naturalNorms A i : ℤ) := by rw [hi]; exact (hc.2.1 i).2
    exact_mod_cast hev
  · apply Int.ofNat_inj.mp
    simp only [indexValue, Int.natCast_natAbs, abs_of_pos hc.1, Nat.cast_prod]
    rw [Matrix.det_of_isUpperTriangular (basis_upper A hs hp)]
    apply Finset.prod_congr rfl
    intro i _
    exact (Int.toNat_of_nonneg (hd i).le).symm
  · change 0 < (basisMatrix A).det.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt hc.1)

end ArithmeticThetaOrthogonalAlgorithm
