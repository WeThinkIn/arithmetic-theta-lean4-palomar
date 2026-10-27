import SplitMatrixModularFamilyR0239
import ArithmeticSectionImageR0239

/-! The compact theta family and its sharp image over the prescribed cyclotomic number field. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaCyclotomicModularityR0239
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent

/-- The positive-rank nonempty matrix family, with its original full Tate frame,
actual finite metaplectic level, and all sharp image assertions, over Q(ζ_L). -/
theorem cyclotomic_matrix_modularity :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro n h hn hh A hA
  have hN := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have hfinite : FiniteDimensional ℚ (CyclotomicField (level (commonN A)) ℚ) := by
    have hf := cyclotomic_finite ℚ (level (commonN A))
    unfold ArithmeticThetaLevelConstantsR0234.FiniteConstants at hf
    rw [toAlgebra_algebraMap] at hf
    exact hf
  obtain ⟨ζ, hζ⟩ := cyclotomic_primitiveRoot ℚ (level (commonN A)) hL
  obtain ⟨G, hG⟩ := split_matrix_modular_family
    (CyclotomicField (level (commonN A)) ℚ) n h hn hh A hA ζ hζ
  exact ⟨hfinite, G, hG, fun B hB => arithmetic_section_image
    (CyclotomicField (level (commonN A)) ℚ) n h hn hh A hA G B hB⟩

end ArithmeticThetaCyclotomicModularityR0239

#print axioms ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity
