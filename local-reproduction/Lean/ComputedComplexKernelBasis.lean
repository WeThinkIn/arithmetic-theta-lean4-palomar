import ComputedNullspaceBasis
import RationalMatrixScalarExtension

namespace ArithmeticThetaComputed

theorem computed_complex_kernel_basis (m h : ℕ) (M : Matrix (Fin m) (Fin h) ℚ) :
    LinearIndependent ℂ (fun t => fun j => ((ArithmeticThetaElimination.nullBasis M t j : ℚ) : ℂ)) ∧
    Submodule.span ℂ (Set.range (fun t => fun j =>
      ((ArithmeticThetaElimination.nullBasis M t j : ℚ) : ℂ))) =
        LinearMap.ker (M.map (algebraMap ℚ ℂ)).mulVecLin ∧
    (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run M)).length = h - M.rank := by
  obtain ⟨hli,hspan,hcount⟩ := ArithmeticThetaElimination.computed_nullspace_basis m h M
  have hlic : LinearIndependent ℂ (fun t => fun j =>
      ((ArithmeticThetaElimination.nullBasis M t j : ℚ) : ℂ)) := by
    exact (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)).mpr hli
  refine ⟨hlic, ?_, hcount⟩
  have hle : Submodule.span ℂ (Set.range (fun t => fun j =>
      ((ArithmeticThetaElimination.nullBasis M t j : ℚ) : ℂ))) ≤
        LinearMap.ker (M.map (algebraMap ℚ ℂ)).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    have ht : ArithmeticThetaElimination.nullBasis M t ∈ LinearMap.ker M.mulVecLin := by
      rw [← hspan]
      exact Submodule.subset_span ⟨t,rfl⟩
    change M.mulVec (ArithmeticThetaElimination.nullBasis M t) = 0 at ht
    change (M.map (algebraMap ℚ ℂ)).mulVec (fun j =>
      ((ArithmeticThetaElimination.nullBasis M t j : ℚ) : ℂ)) = 0
    ext a
    have hh := congrArg (fun v : Fin m → ℚ => (v a : ℂ)) ht
    simpa [Matrix.mulVec, dotProduct] using hh
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [ArithmeticThetaLinearAlgebra.rational_matrix_nullity,
    finrank_span_eq_card hlic, Fintype.card_fin, hcount]


end ArithmeticThetaComputed
