module

public import Rank16Basis
public import Rank16Definitions
public import Rank16LatticeDefinitions
public import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16

lemma det_map_int (R : Type u) [CommRing R] {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) :
    (G.map (Int.castRingHom R)).det = (G.det : R) := (Int.cast_det G).symm

theorem lattice_gram_det (n : ℕ) (hn : n = 8 ∨ n = 16) :
    (latticeGram n).det = 1 := by
  have hd := congrArg Matrix.det (lattice_basis_gram n hn)
  rw [Matrix.det_mul, Matrix.det_transpose, lattice_basis_det n hn, det_map_int] at hd
  have hq : ((latticeGram n).det : ℚ) = 1 := by simpa using hd.symm
  exact_mod_cast hq

theorem orthogonal_realization :
    sumBasis.det = 1 ∧ sumBasis.transpose * sumBasis = sumGram.map (Int.castRingHom ℚ) ∧
      sumGram.det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sumBasis, Matrix.det_fromBlocks_zero₂₁,
      lattice_basis_det 8 (Or.inl rfl)]
  · simp [sumBasis, sumGram, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      lattice_basis_gram 8 (Or.inl rfl)]
    ext i j
    rcases hi : (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm i with i' | i' <;>
      rcases hj : (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm j with j' | j' <;>
      simp [Matrix.submatrix_apply, Matrix.map_apply, hi, hj, Matrix.fromBlocks]
  · simp [sumGram, Matrix.det_fromBlocks_zero₂₁,
      lattice_gram_det 8 (Or.inl rfl)]

theorem universal_smith (R : Type u) [CommRing R] :
    ∃ U V : Matrix (Fin 16) (Fin 16) R, IsUnit U.det ∧ IsUnit V.det ∧
      U * sumGram.map (Int.castRingHom R) * V = (latticeGram 16).map (Int.castRingHom R) := by
  let A := sumGram.map (Int.castRingHom R)
  let D := (latticeGram 16).map (Int.castRingHom R)
  have hA : A.det = 1 := by
    dsimp [A]
    rw [← Int.cast_det, orthogonal_realization.2.2]
    exact Int.cast_one
  have hD : D.det = 1 := by
    dsimp [D]
    rw [← Int.cast_det, lattice_gram_det 16 (Or.inr rfl)]
    exact Int.cast_one
  refine ⟨D, A.adjugate, ?_, ?_, ?_⟩
  · rw [hD]; exact isUnit_one
  · rw [Matrix.det_adjugate, hA, one_pow]; exact isUnit_one
  · change D * A * A.adjugate = D
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, hA, one_smul, Matrix.mul_one]

end ArithmeticThetaRank16
