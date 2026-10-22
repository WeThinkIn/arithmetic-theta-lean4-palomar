module
public import ArithmeticRecoveryBase
public import CompactActualMetaplecticLevelR0209
import Lean
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000
noncomputable section
namespace PalomarFactored882
open AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaCompactModularityR0209
def MatrixCore : Prop :=
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ 3 ≤ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ∧ Even (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections

def CompactLevel : Prop :=
∀ (k : Type) [Field k] [CharZero k] (L b : ℕ) (K : CompactRoot k L b),
  3 ≤ L → Even L → Etale K.cover.map → PalomarCyclotomic669.ActualLevel K

theorem matrix_core : MatrixCore := by
  intro n h hn hh A hA
  have hN := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [level]
    omega
  obtain ⟨hf, G, _, himage⟩ := PalomarCyclotomic669.cyclotomic_matrix_modularity n h hn hh A hA
  exact ⟨hf, hL, heven, G, himage⟩

theorem compact_level : CompactLevel := by
  intro k _ _ L b K hL heven hK
  exact (PalomarCyclotomic669.actualLevel_iff_original K).mpr
    (compact_actual_metaplectic_level k L b K hL heven hK)

theorem recover_from_components (hc : MatrixCore) (hl : CompactLevel) :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro n h hn hh A hA
  obtain ⟨hf, hL, heven, G, himage⟩ := hc n h hn hh A hA
  have hlevel := hl (CyclotomicField (level (commonN A)) ℚ)
    (level (commonN A)) _ G.root hL heven G.etale
  exact ⟨hf, G, (PalomarCyclotomic669.actualLevel_iff_original G.root).mp hlevel, himage⟩

theorem original_cyclotomic_matrix_modularity :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := recover_from_components matrix_core compact_level
end PalomarFactored882
