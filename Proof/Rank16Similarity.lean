module

public import Rank16Definitions
public import Rank16LatticeDefinitions
public import Rank16Unimodular

@[expose] public section

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16

theorem similarity_scale (s : ℚ) (hs : 0 < s)
    (U : Matrix (Fin 16) (Fin 16) ℤ) (hU : IsUnit U.det)
    (h : (U.map (Int.castRingHom ℚ)).transpose * sumGram.map (Int.castRingHom ℚ) *
      U.map (Int.castRingHom ℚ) = s • (latticeGram 16).map (Int.castRingHom ℚ)) : s = 1 := by
  have hd := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin,
    det_map_int, orthogonal_realization.2.2,
    lattice_gram_det 16 (Or.inr rfl), Int.cast_one, mul_one] at hd
  have hu : U.det = 1 ∨ U.det = -1 := Int.isUnit_iff.mp hU
  have hp : s^16 = (1 : ℚ)^16 := by
    rcases hu with hu | hu <;> rw [hu] at hd <;> norm_num at hd ⊢ <;> linarith
  exact (pow_left_inj₀ hs.le zero_le_one (by decide : 16 ≠ 0)).mp hp

end ArithmeticThetaRank16
