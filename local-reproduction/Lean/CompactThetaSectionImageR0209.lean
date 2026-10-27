import CompactModularityDefinitionsR0209

/-! The full-series image transferred to the given regular compact sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCompactModularityR0209
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSectionCompletion ArithmeticThetaSectionOrder
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower
open ArithmeticThetaSharpKernelR0195 ArithmeticThetaComputed

namespace SectionImageProof

variable {n h : ℕ} {A : Matrices n h}

/-- The actual completed coordinate detects exactly the original full theta relations. -/
theorem relations (hn : 0 < n) (hh : 0 < h)
    (hA : ∀ i, validGram (A i)) (G : MatrixData A) (c : Fin h → ℂ) :
    combination G c = 0 ↔ thetaMap A c = 0 := by
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
  let M := tensorPower G.cover.space (line G.root) n
  have hM : IsLineBundle G.cover.space M :=
    ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨hco, E, hE⟩ := ArithmeticThetaConservativeKernelR0189.lifted_cusp_completion
    ℂ L (by omega) hLeven G.data G.compact G.test _ G.cover G.frame.disk
      G.frame.triangle G.frame.dominant
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers
    (show G.frame.disk (closedPoint ℂ) ∈ (⊤ : G.cover.space.Opens) by trivial))
  obtain ⟨a, ha⟩ := ArithmeticThetaConservativeKernelR0189.disk_frame_completed_coordinate
    ℂ G.cover.space (line G.root) n ι C i G.frame.disk hxi E hE
      G.frame.frame G.frame.isFrame
  have hex : completedSection G.cover.space M C (combination G c) i
      (G.frame.disk (closedPoint ℂ)) hxi ℂ E =
      (a : PowerSeries ℂ) * scaledSeries L (thetaMap A c) := by
    rw [ha (combination G c) (expanded A c) (G.expansion c)]
    congr 1
    ext m
    simpa [expanded, scaledSeries, L] using
      (PowerSeries.coeff_subst_X_pow (S := ℂ) (ne_of_gt hL) (thetaMap A c) m)
  constructor
  · intro hs
    have hz : (a : PowerSeries ℂ) * scaledSeries L (thetaMap A c) = 0 := by
      rw [← hex, hs]
      simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    have hz' := (mul_eq_zero.mp hz).resolve_left a.ne_zero
    ext m
    have hc := congrArg (PowerSeries.coeff (L * m)) hz'
    simpa [scaledSeries, Nat.mul_div_right m hL] using hc
  · intro ht
    apply completed_section_injective G.cover.space hnormal M hM ι C i
      (G.frame.disk (closedPoint ℂ)) hxi ℂ E hco
    dsimp only
    rw [hex, ht]
    simp [scaledSeries, completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    ext m
    simp

/-- Coefficient insertion keeps repeated selected indices legitimate. -/
def insert {p : ℕ} (f : Fin p → Fin h) (c : Fin p → ℂ) : Fin h → ℂ :=
  ∑ t, c t • Pi.single (f t) 1

lemma combination_sub (G : MatrixData A) (c d : Fin h → ℂ) :
    combination G (c - d) = combination G c - combination G d := by
  simp [combination, Pi.sub_apply, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar,
    map_sub, sub_smul, Finset.sum_sub_distrib]

lemma combination_single (G : MatrixData A) (j : Fin h) :
    combination G (Pi.single j 1) = G.sections j := by
  classical
  simp [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar, Pi.single_apply,
    apply_ite]

lemma combination_insert (G : MatrixData A) {p : ℕ}
    (f : Fin p → Fin h) (c : Fin p → ℂ) :
    combination G (insert f c) = ∑ t, baseScalar ℂ (structureMap G) (c t) • G.sections (f t) := by
  classical
  simp only [combination, insert, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [baseScalar, ArithmeticThetaOpenHodgeR0180.scalar, map_sum, map_mul,
    Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.smul_sum]
  congr 1
  simpa [combination, baseScalar, ArithmeticThetaOpenHodgeR0180.scalar] using
    combination_single G (f t)

lemma theta_insert {p : ℕ} (f : Fin p → Fin h) (c : Fin p → ℂ) :
    thetaMap A (insert f c) = ∑ t, c t • theta (A (f t)) := by
  classical
  simp [insert, map_sum, map_smul, thetaMap]

lemma equality (G : MatrixData A)
    (hr : ∀ c, combination G c = 0 ↔ thetaMap A c = 0) (c d : Fin h → ℂ) :
    combination G c = combination G d ↔ thetaMap A c = thetaMap A d := by
  rw [← sub_eq_zero, ← combination_sub, hr, map_sub, sub_eq_zero]

end SectionImageProof

/-- The given compact sections have exactly the sharp computed full-series image. -/
theorem compact_theta_section_image :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (G : ArithmeticThetaCompactModularityR0209.MatrixData A) (B : ℕ), ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → ArithmeticThetaCompactModularityR0209.SectionImage G B := by
  intro n h hn hh A hA G B hB
  classical
  have hr := SectionImageProof.relations hn hh hA G
  obtain ⟨_hkernel, ⟨hli, hspan⟩, hcoords⟩ := sharp_exact_image_data n h hh A hA B hB
  have hp (c : Fin h → ℂ) (d : Fin (pivotCount (A := A) B) → ℂ) :
      combination G c = pivotCombination G B d ↔
        thetaMap A c = ∑ t, d t • theta (A (selectedIndex A B t)) := by
    change combination G c =
      ∑ t, baseScalar ℂ (structureMap G) (d t) • G.sections (selectedIndex A B t) ↔ _
    rw [← SectionImageProof.combination_insert, SectionImageProof.equality G hr,
      SectionImageProof.theta_insert]
  have hs (j : Fin h) (d : Fin (pivotCount (A := A) B) → ℂ) :
      G.sections j = pivotCombination G B d ↔
        theta (A j) = ∑ t, d t • theta (A (selectedIndex A B t)) := by
    simpa [SectionImageProof.combination_single, thetaMap] using hp (Pi.single j 1) d
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · intro d hd
    have hz : thetaMap A (SectionImageProof.insert (selectedIndex A B) d) = 0 :=
      (hr _).mp (by simpa [SectionImageProof.combination_insert, pivotCombination] using hd)
    rw [SectionImageProof.theta_insert] at hz
    exact funext (fun t => (Fintype.linearIndependent_iff.mp hli) d hz t)
  · intro c
    have hm : thetaMap A c ∈ Submodule.span ℂ
        (Set.range (fun t : Fin (pivotCount (A := A) B) => theta (A (selectedIndex A B t)))) := by
      rw [hspan]
      exact LinearMap.mem_range.mpr ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    refine ⟨d, (hp c d).mpr hd.symm, ?_⟩
    intro e he
    exact funext (hli.eq_coords_of_eq (((hp c e).mp he).symm.trans hd.symm))
  · intro j
    exact (hs j _).mpr (hcoords j).1
  · intro j c hc
    exact (hcoords j).2 c ((hs j _).mp hc)

#print axioms compact_theta_section_image
end ArithmeticThetaCompactModularityR0209
