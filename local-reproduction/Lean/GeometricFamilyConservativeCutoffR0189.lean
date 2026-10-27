import LiftedCuspCompletionR0189
import DiskFrameCompletedCoordinateR0189

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaConservativeKernelR0189
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSectionCompletion ArithmeticThetaSectionOrder
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaCurveDegree

namespace GeometricFamilyConservativeCutoff

private lemma degree_strict (P L : ℕ) (hL : 24 ≤ L) (d : ℤ)
    (hd : 48 * d ≤ 24 * (P : ℤ)) : d < (L * (P / 48 + 1) : ℕ) := by
  have hP : P < 48 * (P / 48 + 1) := by omega
  have hP' : (P : ℤ) < 48 * ((P / 48 : ℕ) + 1 : ℤ) := by exact_mod_cast hP
  have hmul : 24 * (P / 48 + 1) ≤ L * (P / 48 + 1) :=
    Nat.mul_le_mul_right _ hL
  have hmul' : (24 : ℤ) * ((P / 48 : ℕ) + 1) ≤ (L * (P / 48 + 1) : ℕ) := by
    exact_mod_cast hmul
  omega

end GeometricFamilyConservativeCutoff

/-- The actual common tensor-line realization gives the conservative finite jet cutoff. -/
theorem geometric_family_conservative_cutoff :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaConservativeKernelR0189.cutoff A U) → ArithmeticThetaComputed.thetaMap A c = 0 := by
  intro n h hn hh A hA U _ D X H V hfamily c hvan
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
  obtain ⟨J, hJ, R, hdegree, g, hg, hdom, β, η, e, hη, he, hsquare,
    t, σ, ht, hσ, hexpand⟩ := hfamily
  letI := R.integral
  letI := R.proper
  obtain ⟨hY, hcurve, hnormal, hinv, ⟨ι, ⟨C⟩⟩, hbound⟩ := hdegree
  letI := hY
  let M := tensorPower R.space (coverLine J R) n
  have hM : IsLineBundle R.space M := ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨hco, E, hE⟩ := lifted_cusp_completion ℂ L (by omega) hLeven D X V _ R g hg hdom
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers
    (show g (closedPoint ℂ) ∈ (⊤ : R.space.Opens) by trivial))
  obtain ⟨a, ha⟩ := disk_frame_completed_coordinate ℂ R.space (coverLine J R) n ι C i g hxi E hE e he
  let s := ∑ i : Fin h, baseScalar ℂ (R.map ≫ projection ℂ L D X
    (V.disk (closedPoint ℂ))) (c i) • σ i
  have hex : completedSection R.space M C s i (g (closedPoint ℂ)) hxi ℂ E =
      (a : PowerSeries ℂ) * scaledSeries L (ArithmeticThetaComputed.thetaMap A c) := by
    rw [ha s (expanded A c) (hexpand c)]
    congr 1
    ext m
    simpa [expanded, scaledSeries, L] using
      (PowerSeries.coeff_subst_X_pow (S := ℂ) (ne_of_gt hL)
        (ArithmeticThetaComputed.thetaMap A c) m)
  by_cases hs : s = 0
  · have hz : (a : PowerSeries ℂ) * scaledSeries L (ArithmeticThetaComputed.thetaMap A c) = 0 := by
      rw [← hex, hs]
      simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    have hz' := (mul_eq_zero.mp hz).resolve_left a.ne_zero
    ext m
    have hc := congrArg (PowerSeries.coeff (L * m)) hz'
    simpa [scaledSeries, Nat.mul_div_right m hL] using hc
  · obtain ⟨Q, hQ⟩ := exists_section_divisor R.space ℂ
      (R.map ≫ projection ℂ L D X (V.disk (closedPoint ℂ))) hcurve M ι C s hs
    have hd := (hbound ι C s Q hs hQ).2
    have hstrict : weightedDegree ℂ
        (R.map ≫ projection ℂ L D X (V.disk (closedPoint ℂ))) Q <
        (L * (cutoff A U + 1) : ℕ) := by
      apply GeometricFamilyConservativeCutoff.degree_strict _ L hL24
      push_cast at hd ⊢
      nlinarith [hd]
    exact (unit_frame_finite_jet_vanishing R.space ℂ
      (R.map ≫ projection ℂ L D X (V.disk (closedPoint ℂ))) hcurve hnormal M hM ι C s Q
      s i (g (closedPoint ℂ)) hxi ℂ E (ArithmeticThetaComputed.thetaMap A c) a L (cutoff A U)
      hs hQ hco hL hex hvan hstrict).2

#print axioms geometric_family_conservative_cutoff
end ArithmeticThetaConservativeKernelR0189
