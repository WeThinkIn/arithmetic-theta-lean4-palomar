module

public import FieldSeriesImageR0233
public import FieldSectionRelationsR0233

@[expose] public section

/-! Exact image of the actual compact sections, with scalars along their
specified structure morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFieldImageR0233
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTensorPower

namespace FieldSectionImageProof

variable (k : Type) [Field k] {h : ℕ} {X : Scheme.{0}}
  (b : X ⟶ Spec (CommRingCat.of k)) {J : X.Modules} (s : Fin h → Sections J)

lemma combination_sub (c d : Fin h → k) :
    combination k b s (c - d) = combination k b s c - combination k b s d := by
  simp [combination, Pi.sub_apply, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar,
    map_sub, sub_smul, Finset.sum_sub_distrib]

lemma combination_single (j : Fin h) :
    combination k b s (Pi.single j 1) = s j := by
  classical
  simp [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar, Pi.single_apply,
    apply_ite]

lemma combination_insert {p : ℕ} (f : Fin p → Fin h) (d : Fin p → k) :
    combination k b s (FieldSeriesImageProof.insert k f d) =
      ∑ t, baseScalar k b (d t) • s (f t) := by
  classical
  simp only [combination, FieldSeriesImageProof.insert, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [baseScalar, ArithmeticThetaOpenHodgeR0180.scalar, map_sum, map_mul,
    Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.smul_sum]
  congr 1
  simpa [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar] using
    combination_single k b s (f t)

lemma equality {n : ℕ} (A : Matrices n h)
    (hr : ∀ c, combination k b s c = 0 ↔ seriesCombination k A c = 0)
    (c d : Fin h → k) :
    combination k b s c = combination k b s d ↔
      seriesCombination k A c = seriesCombination k A d := by
  rw [← sub_eq_zero, ← combination_sub, hr]
  change FieldSeriesImageProof.linear k A (c - d) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  rfl

end FieldSectionImageProof

/-- All six exact image clauses for the same field-generic compact sections. -/
theorem field_section_image :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n h : ℕ),
      0 < n → 0 < h → ∀ (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ∀ B : ℕ,
      ArithmeticThetaSharpKernelR0195.cutoff A ≤ B →
      SectionImage k A B (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections := by
  intro k _ _ _ n h hn hh A hA G B hB
  classical
  let b := ArithmeticThetaArithmeticFieldR0231.structureMap G
  have hr := field_section_relations k n h hn hh A hA G
  obtain ⟨hk, hi, hspan, hc, hu⟩ := field_series_image k n h A hA B hB
  have hp (c : Fin h → k) (d : Fin (pivotCount A B) → k) :
      combination k b G.sections c = pivotCombination k A B b G.sections d ↔
        seriesCombination k A c = seriesPivot k A B d := by
    change combination k b G.sections c =
      ∑ t, baseScalar k b (d t) • G.sections (ArithmeticThetaComputed.selectedIndex A B t) ↔ _
    rw [← FieldSectionImageProof.combination_insert,
      FieldSectionImageProof.equality k b G.sections A hr]
    exact congrArg (fun z => seriesCombination k A c = z)
      (FieldSeriesImageProof.inserted k A B d) |>.to_iff
  have hs (j : Fin h) (d : Fin (pivotCount A B) → k) :
      G.sections j = pivotCombination k A B b G.sections d ↔
        ArithmeticThetaArithmeticFieldR0231.theta k (A j) = seriesPivot k A B d := by
    have he := hp (Pi.single j 1) d
    rw [FieldSectionImageProof.combination_single] at he
    change _ ↔ FieldSeriesImageProof.linear k A (Pi.single j 1) = _ at he
    rw [FieldSeriesImageProof.single] at he
    exact he
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hr c).trans (hk c)
  · intro d hd
    apply hi d
    have hz := (hr (FieldSeriesImageProof.insert k
      (ArithmeticThetaComputed.selectedIndex A B) d)).mp (by
        simpa only [FieldSectionImageProof.combination_insert, pivotCombination] using hd)
    change FieldSeriesImageProof.linear k A _ = 0 at hz
    rwa [FieldSeriesImageProof.inserted] at hz
  · intro c
    obtain ⟨d, hd, hud⟩ := hspan c
    exact ⟨d, (hp c d).mpr hd, fun e he => hud e ((hp c e).mp he)⟩
  · intro j
    exact (hs j _).mpr (hc j)
  · intro j d hd
    exact hu j d ((hs j _).mp hd)

#print axioms field_section_image
end ArithmeticThetaFieldImageR0233
