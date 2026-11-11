import ReviewRelationLinear
import FieldSectionImageR0233

/-!
# Transfer a full-series image to actual sheaf sections

The geometric input to this theorem is exactly the equivalence of full-series
and section relations. The subsequent image calculation is independent of how
the scheme, line bundle or modular level was constructed. Scalars on sections
still come from the displayed structure morphism to `Spec k`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaReview.Relations

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaFieldImageR0233

/-- Additivity of the existing combination with its actual structural scalars. -/
private def sectionCombination (k : Type) [Field k] {h : ℕ} {X : Scheme.{0}}
    (b : X ⟶ Spec (CommRingCat.of k)) {J : X.Modules}
    (s : Fin h → Sections J) : (Fin h → k) →+ Sections J where
  toFun := combination k b s
  map_zero' := by
    simp [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar]
  map_add' := by
    intro c d
    simp [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar,
      map_add, add_smul, Finset.sum_add_distrib]

/-- Transfer all six original image clauses without an atlas, root cover or
`MatrixData` in the hypotheses. The pivot indices and rational coordinates are
exactly the original elimination output, and the relation is for full series. -/
theorem section_image_of_series_image :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ)
      (A : Matrices n h) (B : ℕ) (X : Scheme.{0})
      (b : X ⟶ Spec (CommRingCat.of k)) (J : X.Modules)
      (s : Fin h → Sections J),
      (∀ c : Fin h → k, combination k b s c = 0 ↔ seriesCombination k A c = 0) →
      SeriesImage k A B → SectionImage k A B b s := by
  intro k _ _ n h A B X b J s hr hseries
  classical
  obtain ⟨hk, hi, hspan, hc, hu⟩ := hseries
  have heq (c d : Fin h → k) :
      combination k b s c = combination k b s d ↔
        seriesCombination k A c = seriesCombination k A d :=
    equality_of_same_relations _ _ _ (sectionCombination k b s)
      (FieldSeriesImageProof.linear k A).toAddMonoidHom hr c d
  have hp (c : Fin h → k) (d : Fin (pivotCount A B) → k) :
      combination k b s c = pivotCombination k A B b s d ↔
        seriesCombination k A c = seriesPivot k A B d := by
    change combination k b s c =
      ∑ t, baseScalar k b (d t) • s (ArithmeticThetaComputed.selectedIndex A B t) ↔ _
    rw [← FieldSectionImageProof.combination_insert, heq]
    exact congrArg (fun z => seriesCombination k A c = z)
      (FieldSeriesImageProof.inserted k A B d) |>.to_iff
  have hs (j : Fin h) (d : Fin (pivotCount A B) → k) :
      s j = pivotCombination k A B b s d ↔
        ArithmeticThetaArithmeticFieldR0231.theta k (A j) = seriesPivot k A B d := by
    have he := hp (Pi.single j 1) d
    rw [FieldSectionImageProof.combination_single] at he
    change _ ↔ FieldSeriesImageProof.linear k A (Pi.single j 1) = _ at he
    rw [FieldSeriesImageProof.single] at he
    exact he
  have hcoordinates :
      Function.Injective
        ((sectionCombination k b s) ∘
          FieldSeriesImageProof.insert k (ArithmeticThetaComputed.selectedIndex A B)) ∧
      ∀ c, ∃! d : Fin (pivotCount A B) → k,
        (sectionCombination k b s) c = (sectionCombination k b s)
          (FieldSeriesImageProof.insert k (ArithmeticThetaComputed.selectedIndex A B) d) := by
    apply (coordinates_of_same_relations _ _ _ _ (sectionCombination k b s)
      (FieldSeriesImageProof.linear k A).toAddMonoidHom hr _).mp
    constructor
    · intro d e hde
      change FieldSeriesImageProof.linear k A _ = FieldSeriesImageProof.linear k A _ at hde
      rw [FieldSeriesImageProof.inserted, FieldSeriesImageProof.inserted] at hde
      apply sub_eq_zero.mp
      apply hi
      rw [FieldSeriesImageProof.pivot_sub, hde, sub_self]
    · intro c
      change ∃! d : Fin (pivotCount A B) → k,
        seriesCombination k A c = FieldSeriesImageProof.linear k A
          (FieldSeriesImageProof.insert k (ArithmeticThetaComputed.selectedIndex A B) d)
      simpa only [FieldSeriesImageProof.inserted] using hspan c
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hr c).trans (hk c)
  · intro d hd
    apply hcoordinates.1
    change combination k b s _ = combination k b s _
    rw [FieldSectionImageProof.combination_insert, FieldSectionImageProof.combination_insert]
    change pivotCombination k A B b s d = pivotCombination k A B b s 0
    rw [hd]
    simp [pivotCombination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar]
  · intro c
    simpa only [sectionCombination, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      FieldSectionImageProof.combination_insert, pivotCombination] using hcoordinates.2 c
  · intro j
    exact (hs j _).mpr (hc j)
  · intro j d hd
    exact hu j d ((hs j _).mp hd)

end ArithmeticThetaReview.Relations
