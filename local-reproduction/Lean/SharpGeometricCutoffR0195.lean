import SharpKernelDefinitionsR0195

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaSharpKernelR0195
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaConservativeKernelR0189
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSectionCompletion ArithmeticThetaSectionOrder
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaCurveDegree

namespace SharpGeometricCutoff

/-- The exact floor guarantees strict inequality even when the numerator
is divisible by the denominator. No enlargement of the cutoff is used. -/
private lemma degree_strict (P L : ℕ) (hL : 0 < L) (d : ℤ)
    (hd : 48 * d ≤ (P : ℤ)) : d < (L * (P / (48 * L) + 1) : ℕ) := by
  have hP : P < (P / (48 * L) + 1) * (48 * L) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 48 * L)).mp (Nat.lt_succ_self _)
  have hP' : (P : ℤ) < ((P / (48 * L) : ℕ) + 1 : ℤ) * (48 * (L : ℤ)) := by
    exact_mod_cast hP
  push_cast
  nlinarith

end SharpGeometricCutoff

/-- The sharp square-line realization gives the exact floor finite-jet cutoff. -/
theorem sharp_geometric_cutoff :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaSharpKernelR0195.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaSharpKernelR0195.cutoff A) → ArithmeticThetaComputed.thetaMap A c = 0 := by
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
  obtain ⟨J, R, _hetale, _hiso, hdegree, F, t, σ, ht, hσ, hexpand⟩ := hfamily
  let g := F.disk
  letI := R.integral
  letI := R.proper
  obtain ⟨hY, hcurve, hnormal, hinv, ⟨ι, ⟨C⟩⟩, hbound⟩ := hdegree
  letI := hY
  let M := tensorPower R.space ((Scheme.Modules.pullback R.map).obj J.line) n
  have hM : IsLineBundle R.space M := ArithmeticThetaDegreeAssembly.isLineBundle_of_normalFrameCover _ _ C
  obtain ⟨hco, E, hE⟩ := lifted_cusp_completion ℂ L (by omega) hLeven D X V _ R g F.triangle F.dominant
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers
    (show g (closedPoint ℂ) ∈ (⊤ : R.space.Opens) by trivial))
  obtain ⟨a, ha⟩ := disk_frame_completed_coordinate ℂ R.space ((Scheme.Modules.pullback R.map).obj J.line) n ι C i g hxi E hE F.frame F.isFrame
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
        (L * (ArithmeticThetaSharpKernelR0195.cutoff A + 1) : ℕ) := by
      apply SharpGeometricCutoff.degree_strict _ L hL
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hd
    exact (unit_frame_finite_jet_vanishing R.space ℂ
      (R.map ≫ projection ℂ L D X (V.disk (closedPoint ℂ))) hcurve hnormal M hM ι C s Q
      s i (g (closedPoint ℂ)) hxi ℂ E (ArithmeticThetaComputed.thetaMap A c) a L (ArithmeticThetaSharpKernelR0195.cutoff A)
      hs hQ hco hL hex hvan hstrict).2

#print axioms sharp_geometric_cutoff
end ArithmeticThetaSharpKernelR0195
