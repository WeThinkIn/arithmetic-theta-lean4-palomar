module

public import Det80CompleteClassification
public import Det80Similarity
public import Det80LocalRealization
public import Det80LocalInvariants

@[expose] public section

/-! Existence and uniqueness for the actual all-prime local Smith order. -/

namespace ArithmeticThetaBinary

theorem same_order_classes (a b c : ℤ) (ha : 0 < a) (hd : 0 < 4*a*c-b^2)
    (hl : sameLocalSmith a b c) :
    ∃! j : Fin 3, ∃ U : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  obtain ⟨hdet,hcontent⟩ := local_smith_invariants a b c ha hd hl
  obtain ⟨j,U,hu,hU⟩ := all_positive_classes a b c ha hdet hcontent
  refine ⟨j, ⟨U,hu,hU⟩, ?_⟩
  rintro k ⟨V,hv,hV⟩
  by_contra hkj
  let T := U⁻¹ * V
  have htu : IsUnit T.det := by
    dsimp [T]
    rw [Matrix.det_mul]
    exact (U.isUnit_nonsing_inv_det hu).mul hv
  have ht : T.transpose * forms j * T = forms k := by
    rw [← hU]
    dsimp [T]
    rw [Matrix.transpose_mul]
    have hleft : (U⁻¹).transpose * U.transpose = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv U hu, Matrix.transpose_one]
    simp only [Matrix.mul_assoc] at *
    calc
      V.transpose * ((U⁻¹).transpose * (U.transpose * (gram a b c * (U * (U⁻¹ * V))))) =
          V.transpose * (gram a b c * V) := by
        rw [← Matrix.mul_assoc U U⁻¹ V, Matrix.mul_nonsing_inv U hu, one_mul]
        rw [← Matrix.mul_assoc (U⁻¹).transpose U.transpose, hleft, one_mul]
      _ = forms k := by simpa only [Matrix.mul_assoc] using hV
  apply similarity_distinct j k (Ne.symm hkj)
  refine ⟨1,T,by norm_num,htu,?_⟩
  rw [one_smul]
  simpa only [Matrix.map_mul, Matrix.transpose_map] using
    congrArg (fun M => M.map (Int.castRingHom ℚ)) ht

end ArithmeticThetaBinary
