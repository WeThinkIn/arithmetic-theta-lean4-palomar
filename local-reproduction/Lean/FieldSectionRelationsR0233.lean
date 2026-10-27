import FieldImageDefinitionsR0233

/-! Full-series faithfulness for the prescribed field-generic compact sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFieldImageR0233
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSectionCompletion ArithmeticThetaSectionOrder
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower
open ArithmeticThetaSharpKernelR0195 ArithmeticThetaComputed

/-- The actual completed coordinate detects exactly the original full theta relations,
over the specified coefficient field and using the structural scalar action. -/
theorem field_section_relations :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A, ∀ c : Fin h → k, ArithmeticThetaFieldImageR0233.combination k (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections c = 0 ↔ ArithmeticThetaFieldImageR0233.seriesCombination k A c = 0 := by
  intro k _ _ _ n h hn hh A hA G c
  classical
  have hN := (indexed_full_unary_factorization n h hn hh A hA).1
  let L := ArithmeticThetaCompactUnaryR0183.level (commonN A)
  have hL24 : 24 ≤ L := by
    dsimp [L, ArithmeticThetaCompactUnaryR0183.level]
    have hp : 0 < (commonN A)^2 := pow_pos hN 2
    omega
  have hL : 0 < L := by omega
  have hLeven : Even L := even_iff_two_dvd.mpr
    (dvd_trans (by decide : 2 ∣ 24) (dvd_mul_right 24 _))
  letI := G.cover.integral
  letI := G.cover.proper
  obtain ⟨hY, _hcurve, hnormal, _hinv, ⟨ι, ⟨C⟩⟩, _hbound⟩ := G.degree
  letI := hY
  let M := tensorPower G.cover.space (ArithmeticThetaArithmeticFieldR0231.half G) n
  have hM : IsLineBundle G.cover.space M :=
    ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨hco, E, hE⟩ := ArithmeticThetaConservativeKernelR0189.lifted_cusp_completion
    k L (by omega) hLeven G.data G.compact G.test _ G.cover G.frame.disk
      G.frame.triangle G.frame.dominant
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers
    (show G.frame.disk (closedPoint k) ∈ (⊤ : G.cover.space.Opens) by trivial))
  obtain ⟨a, ha⟩ := ArithmeticThetaConservativeKernelR0189.disk_frame_completed_coordinate
    k G.cover.space (ArithmeticThetaArithmeticFieldR0231.half G) n ι C i G.frame.disk hxi E hE
      G.frame.frame G.frame.isFrame
  have hex : completedSection G.cover.space M C (combination k (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections c) i
      (G.frame.disk (closedPoint k)) hxi k E =
      (a : PowerSeries k) * scaledSeries L (seriesCombination k A c) := by
    rw [ha (combination k (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections c) (ArithmeticThetaArithmeticFieldR0231.expanded k A c) (G.expansion c)]
    congr 1
    ext m
    simpa [ArithmeticThetaArithmeticFieldR0231.expanded, seriesCombination, scaledSeries, L] using
      (PowerSeries.coeff_subst_X_pow (S := k) (ne_of_gt hL) (seriesCombination k A c) m)
  constructor
  · intro hs
    have hz : (a : PowerSeries k) * scaledSeries L (seriesCombination k A c) = 0 := by
      rw [← hex, hs]
      simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    have hz' := (mul_eq_zero.mp hz).resolve_left a.ne_zero
    ext m
    have hc := congrArg (PowerSeries.coeff (L * m)) hz'
    simpa [scaledSeries, Nat.mul_div_right m hL] using hc
  · intro ht
    apply completed_section_injective G.cover.space hnormal M hM ι C i
      (G.frame.disk (closedPoint k)) hxi k E hco
    dsimp only
    rw [hex, ht]
    simp [scaledSeries, completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    ext m
    simp


#print axioms field_section_relations
end ArithmeticThetaFieldImageR0233
