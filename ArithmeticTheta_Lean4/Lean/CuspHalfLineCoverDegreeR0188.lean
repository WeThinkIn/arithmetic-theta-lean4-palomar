import LatticeGlobalSectionsDefinitionsR0188

/-! The actual half-cusp divisor line on a smooth proper finite cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaLatticeSectionsR0188
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaCurveDegree ArithmeticThetaSectionOrder ArithmeticThetaDegreeAssembly
open ArithmeticThetaTensorPower ArithmeticThetaPullback

namespace CuspHalfLineCoverDegreeR0188

/-- The residue-weighted degree of the actual half-cusp divisor. -/
lemma half_cusp_degree (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (hdiv : 24 ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (E : Component k L D X x →₀ ℤ)
    (hE : ∀ y, (y ∈ cuspSet k L D X x → E y = (L / 24 : ℕ)) ∧
      (y ∉ cuspSet k L D X x → E y = 0)) :
    24 * weightedDegree k (projection k L D X x) E =
      (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) := by
  have hquot : 24 * (L / 24) = L := Nat.mul_div_cancel' hdiv
  have hscale : (48 : ℤ) * (L / 24 : ℕ) = (2 * L : ℕ) := by
    exact_mod_cast (show 48 * (L / 24) = 2 * L by omega)
  have hscaled : ∀ y,
      (y ∈ cuspSet k L D X x → (48 • E) y = (2 * L : ℕ)) ∧
      (y ∉ cuspSet k L D X x → (48 • E) y = 0) := by
    intro y
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    constructor
    · intro hy
      rw [(hE y).1 hy]
      exact hscale
    · intro hy
      rw [(hE y).2 hy, mul_zero]
  have hd := ComponentHodgePowerDegreeR0184.cusp_divisor_degree
    k L hL heven D X x (48 • E) hscaled
  rw [weightedDegree_nsmul] at hd
  push_cast at hd
  nlinarith

end CuspHalfLineCoverDegreeR0188

/-- Finite pullback and tensor degree on O((L/24)C), retaining all actual
geometry, frames, residue scalar maps, and the pointwise cover degree bound. -/
theorem cusp_half_line_cover_degree :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L →
    ∀ (D : LevelData k L) (X : Compactification k L D) (x : X.space)
      (J : DivisorLine (Component k L D X x)), IsCuspHalfLine k L D X x J →
    ∀ (b n : ℕ) (R : RootCover k (Component k L D X x) (projection k L D X x) b),
      CoverDegree k L D X x J b n R := by
  intro k _ _ _ L hpos hdiv D X x J hJ b n R
  have hL : 3 ≤ L := le_trans (by decide : 3 ≤ 24) (Nat.le_of_dvd hpos hdiv)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) hdiv)
  have hg := component_curve_frames k L hL heven D X x
  letI := hg.1
  letI := R.integral
  letI := R.finite
  letI := R.flat
  letI := R.surjective
  letI := R.proper
  letI := R.smooth
  letI hY : IsLocallyNoetherian R.space :=
    LocallyOfFiniteType.isLocallyNoetherian (R.map ≫ projection k L D X x)
  have hcurve : OneDimensionalCharts R.space :=
    ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.smooth_oneDimensionalCharts
      (R.map ≫ projection k L D X x)
  have hnormal : NormalAffine R.space := fun U hU =>
    ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed
      R.space k (R.map ≫ projection k L D X x) U hU
  obtain ⟨F, hrep, hF⟩ := hJ
  obtain ⟨ι, ⟨C⟩⟩ := hrep.2.2.1
  have hline := isLineBundle_of_normalFrameCover _ _ C
  have hinv : Scheme.Modules.IsInvertible (coverLine J R) := hrep.1.pullback R.map
  obtain ⟨B⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    R.space hnormal (coverLine J R) hinv
  have hpLine := isLineBundle_of_normalFrameCover _ _ B
  have hs := pullbackGlobalSection_ne_zero R.map J.line hline J.section_ hrep.2.1
  obtain ⟨FY, hFY⟩ := exists_section_divisor R.space k
    (R.map ≫ projection k L D X x) hcurve (coverLine J R) R.space B
      (pullbackGlobalSection R.map J.line J.section_) hs
  have hpdeg := (finite_pullback_section_degree (Component k L D X x) R.space k
    (projection k L D X x) R.map hg.2.2.1 hcurve J.line hline ι R.space C B
    J.section_ F FY hrep.2.1 (hrep.2.2.2 ι C) hFY).2
  have hbase := CuspHalfLineCoverDegreeR0188.half_cusp_degree
    k L hL heven hdiv D X x F hF
  refine ⟨hY, hcurve, hnormal, hinv, ⟨R.space, ⟨powerCover _ _ B n⟩⟩, ?_⟩
  intro κ A t E ht hE
  have htdeg := tensor_power_fixed_degree R.space k
    (R.map ≫ projection k L D X x) hcurve (coverLine J R) hpLine R.space B n
    κ A (pullbackGlobalSection R.map J.line J.section_) t FY E hs ht hFY hE
  have hex : 24 * weightedDegree k (R.map ≫ projection k L D X x) E =
      (n : ℤ) * (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
        (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) := by
    calc
      _ = (n : ℤ) * (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
          (24 * weightedDegree k (projection k L D X x) F) := by
        rw [htdeg, hpdeg]
        ring
      _ = _ := by rw [hbase]; ring
  refine ⟨hex, ?_⟩
  have hb : (2 : ℤ) * (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
    exact_mod_cast (geometric_component_cusp_bound k L hL heven D X x).2.2.2
  have hr : (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) ≤ (b : ℤ) := by
    exact_mod_cast (R.degree (genericPoint (Component k L D X x))).2
  calc
    48 * weightedDegree k (R.map ≫ projection k L D X x) E =
        (n : ℤ) * (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
          (2 * (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ)) := by
      calc
        _ = 2 * (24 * weightedDegree k (R.map ≫ projection k L D X x) E) := by ring
        _ = _ := by rw [hex]; ring
    _ ≤ (n : ℤ) * (R.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity)

#print axioms cusp_half_line_cover_degree
end ArithmeticThetaLatticeSectionsR0188
