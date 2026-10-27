import FieldSharpModularFamilyR0232
import RecoveredFieldConsumersR0232

/-! Simultaneous finite number-field descent of the constructed matrix family. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaArithmeticFieldR0231

/-- The same sharp family over the algebraic closure of the rationals has a
simultaneous finite model extending any prescribed finite coefficient field. -/
theorem arithmetic_matrix_finite_model :
    ∀ (n h : ℕ), 0 < n → 0 < h →
    ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h),
    (∀ i, ArithmeticThetaComputed.validGram (A i)) →
    ∀ K0 : ArithmeticThetaFiniteFieldModelsR0221.FieldStage,
    FiniteDimensional ℚ K0 →
    ∃ G : MatrixData (AlgebraicClosure ℚ) A,
      ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧
      ∃ hg : DescentGeometry G,
      ∃ K : ArithmeticThetaFiniteFieldModelsR0221.FieldStage,
        FiniteDimensional ℚ K ∧ K0 ≤ K ∧
        Nonempty (ArithmeticThetaFiniteFieldModelsR0221.RootModel (rootData G hg) K) := by
  intro n h hn hh A hA K0 hK0
  obtain ⟨G, hlevel⟩ := field_sharp_modular_family (AlgebraicClosure ℚ) n h hn hh A hA
  have hg : DescentGeometry G :=
    field_descent_geometry (AlgebraicClosure ℚ) n h hn hh A hA G
  refine ⟨G, hlevel, hg, ?_⟩
  exact ArithmeticThetaFiniteFieldModelsR0221.pointed_square_cover_finite_model
    h n _ (rootData G hg) K0 hK0

end ArithmeticThetaArithmeticFieldR0231

#print axioms ArithmeticThetaArithmeticFieldR0231.arithmetic_matrix_finite_model
