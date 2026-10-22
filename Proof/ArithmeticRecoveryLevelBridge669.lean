module
public import ArithmeticRecoveryBridge
public import CyclotomicMatrixModularityR0239
import Lean
@[expose] public section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaStackLevelR0199
open ArithmeticThetaCompactModularityR0209
open ArithmeticThetaActualLevelR0208
open ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaLocalWeierstrassR0203
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local instance] CategoryTheory.uliftCategory
noncomputable section
namespace PalomarCyclotomic669
variable {k : Type} [Field k] [CharZero k] {L b : ℕ}
def anchoredMap (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (ArithmeticThetaMetaplecticStackR0207.group L Y.left).Objects) : AnchoredMap C Y X where
  map := PalomarClassifier667.canonical C.functor Y X
  anchor := by
    erw [((PalomarClassifier667.canonicalClassifyingMap C.functor Y X).exists.choose_spec).1 (.mk (.op Y))]
    exact (Cat.Hom.toNatIso (C.unit (.op Y))).app X


theorem anchoredMap_mk_eq (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (ArithmeticThetaMetaplecticStackR0207.group L Y.left).Objects)
    (t u : Pseudofunctor.StrongTrans (representable Y) C.functor) (h : t = u)
    (happ : t.app (.mk (.op Y)) = u.app (.mk (.op Y)))
    (a : (u.app (.mk (.op Y))).toFunctor.obj (point (𝟙 Y)) ≅ X) :
    (⟨t, by rw [happ]; exact a⟩ : AnchoredMap C Y X) = ⟨u, a⟩ := by
  cases h
  rfl

theorem anchoredMap_eq_original (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (ArithmeticThetaMetaplecticStackR0207.group L Y.left).Objects) :
    anchoredMap C Y X = ArithmeticThetaActualLevelR0208.canonicalMap C Y X := by
  exact anchoredMap_mk_eq C Y X _ _ (PalomarClassifier667.canonical_eq_original C.functor Y X)
    (((PalomarClassifier667.canonicalClassifyingMap C.functor Y X).exists.choose_spec).1 (.mk (.op Y)))
    ((Cat.Hom.toNatIso (C.unit (.op Y))).app X)

def ActualLevel (K : CompactRoot k L b) : Prop :=
  InteriorGeometry K ∧ ∃ (h : Universal K)
    (C : ArithmeticThetaMetaplecticStackR0207.Coherence L
      (ArithmeticThetaLocalWeierstrassR0203.Base k)),
    Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L
      (ArithmeticThetaLocalWeierstrassR0203.Base k) C) ∧
    CategoryTheory.Pseudofunctor.IsStack C.functor
      (ArithmeticThetaRootStackR0198.rootTopology (ArithmeticThetaLocalWeierstrassR0203.Base k)) ∧
    Nonempty (ArithmeticThetaActualLevelR0208.PullbackComparison
      (anchoredMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))) ∧
    ArithmeticThetaActualLevelR0208.FiniteEtaleLevel (provider K h) (levelMap K h) (openSquare K)
      (anchoredMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))


theorem actualLevel_iff_original (K : CompactRoot k L b) :
    ActualLevel K ↔ ArithmeticThetaCompactModularityR0209.ActualLevel K := by
  simp only [ActualLevel, ArithmeticThetaCompactModularityR0209.ActualLevel,
    anchoredMap_eq_original]

/-- Full original cyclotomic matrix theorem, expressed using the characterized level map. -/
theorem cyclotomic_matrix_modularity :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, PalomarCyclotomic669.ActualLevel G.root ∧ ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro n h hn hh A hA
  obtain ⟨hf, G, hG, hImage⟩ :=
    ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity n h hn hh A hA
  exact ⟨hf, G, (actualLevel_iff_original G.root).mpr hG, hImage⟩

/-- Recover the complete original statement, with all hypotheses and all sharp image bounds. -/
theorem original_cyclotomic_matrix_modularity :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro n h hn hh A hA
  obtain ⟨hf, G, hG, hImage⟩ := cyclotomic_matrix_modularity n h hn hh A hA
  exact ⟨hf, G, (actualLevel_iff_original G.root).mp hG, hImage⟩

end PalomarCyclotomic669
