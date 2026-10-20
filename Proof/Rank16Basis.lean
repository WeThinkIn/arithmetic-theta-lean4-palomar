module

public import Rank16Definitions
public import Rank16LatticeDefinitions

@[expose] public section

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16

lemma lattice_basis_lower (n : ℕ) : (latticeBasis n).IsLowerTriangular := by
  intro i j h
  change i < j at h
  have hij : i.val < j.val := h
  simp only [latticeBasis]
  split_ifs <;> simp_all; omega

theorem lattice_basis_det (n : ℕ) (hn : n = 8 ∨ n = 16) :
    (latticeBasis n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (lattice_basis_lower n)]
  rcases hn with rfl | rfl <;>
    norm_num [latticeBasis, Fin.prod_univ_succ]

theorem lattice_basis_gram (n : ℕ) (hn : n = 8 ∨ n = 16) :
    (latticeBasis n).transpose * latticeBasis n = (latticeGram n).map (Int.castRingHom ℚ) := by
  rcases hn with rfl | rfl <;> decide +kernel

end ArithmeticThetaRank16
