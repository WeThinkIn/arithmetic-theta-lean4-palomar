import ScopedCuspDefinitionsR0102
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod

noncomputable section

namespace ArithmeticThetaIntegralCuspsR0102

theorem integral_primitive_lift :
    ∀ L : ℕ, 3 ≤ L → ∀ v : ArithmeticThetaLevelCount.PrimitivePair L,
      ∃ A : Marking, primitiveLabel L A = v := by
  intro L hL v
  haveI : NeZero L := ⟨by omega⟩
  obtain ⟨B, hB0, hB1⟩ := IsCoprime.exists_SL2_col v.property (0 : Fin 2)
  obtain ⟨A, hA⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod L B
  refine ⟨A, Subtype.ext ?_⟩
  apply Prod.ext
  · have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) (ZMod L) => C 0 0) hA
    simpa [primitiveLabel, Matrix.SpecialLinearGroup.map_apply_coe, hB0] using h
  · have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) (ZMod L) => C 1 0) hA
    simpa [primitiveLabel, Matrix.SpecialLinearGroup.map_apply_coe, hB1] using h

end ArithmeticThetaIntegralCuspsR0102
