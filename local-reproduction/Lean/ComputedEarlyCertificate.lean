import ComputedCoefficientMatrix
import ComputedNullspaceBasis
import RationalMatrixScalarExtension

namespace ArithmeticThetaComputed

theorem computed_full_rank_certificate (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hv : ∀ i, validGram (A i))
    (hp : (ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.length = h) :
    LinearMap.ker (thetaMap A) = ⊥ := by
  have hr : (coefficientMatrix A B).rank = h := by
    rw [← (ArithmeticThetaElimination.run_kernel_rank (B+1) h (coefficientMatrix A B)).2]
    exact hp
  have hn := ArithmeticThetaLinearAlgebra.rational_matrix_nullity (B+1) h
    (coefficientMatrix A B)
  rw [hr, Nat.sub_self] at hn
  have hk : LinearMap.ker ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hn
  apply le_antisymm ?_ bot_le
  intro c hc
  have hz : thetaMap A c = 0 := hc
  have hm : c ∈ LinearMap.ker ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
    rw [← computed_prefix_map n h B A hv]
    change prefixMap B (thetaMap A c) = 0
    rw [hz, map_zero]
  rwa [hk] at hm

end ArithmeticThetaComputed
