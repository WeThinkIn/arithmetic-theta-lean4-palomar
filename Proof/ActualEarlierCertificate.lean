module

public import ComputedEarlyCertificate
public import TruncationCertificates

@[expose] public section

namespace ArithmeticThetaEarlyAssembly

/-- The earlier certificate for the executable coefficient matrix and actual counting series. -/
theorem actual_earlier_certificate :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ≤
        LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
          (algebraMap ℚ ℂ)).mulVecLin) ∧
      ((ArithmeticThetaComputed.coefficientMatrix A B).rank = h →
        LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = ⊥) ∧
      (∀ W : Submodule ℂ (Fin h → ℂ),
        (∀ c ∈ W, ArithmeticThetaComputed.thetaMap A c = 0) →
        Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank →
        W = LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ∧
        LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
          LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
            (algebraMap ℚ ℂ)).mulVecLin)) := by
  intro n h B A hv
  have hinc : LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ≤
      LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin) := by
    intro c hc
    rw [← ArithmeticThetaComputed.computed_prefix_map n h B A hv]
    change ArithmeticThetaComputed.prefixMap B (ArithmeticThetaComputed.thetaMap A c) = 0
    rw [show ArithmeticThetaComputed.thetaMap A c = 0 from hc, map_zero]
  refine ⟨hinc, ?_, ?_⟩
  · intro hr
    apply ArithmeticThetaComputed.computed_full_rank_certificate n h B A hv
    rw [(ArithmeticThetaElimination.run_kernel_rank (B+1) h
      (ArithmeticThetaComputed.coefficientMatrix A B)).2]
    exact hr
  · intro W hW hdim
    apply ArithmeticThetaElementary.dimension_sandwich_certificate h W
      (LinearMap.ker (ArithmeticThetaComputed.thetaMap A))
      (LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map
        (algebraMap ℚ ℂ)).mulVecLin))
    · intro c hc
      exact hW c hc
    · exact hinc
    · rw [ArithmeticThetaLinearAlgebra.rational_matrix_nullity]
      exact hdim

end ArithmeticThetaEarlyAssembly
