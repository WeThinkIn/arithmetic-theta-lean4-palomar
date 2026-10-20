module

public import SplitCuspDegreeR0239
public import SplitDiscriminantDivisorR0239
public import ComponentHodgePowerDegreeR0184

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaCyclotomicModularityR0239
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCurveDegree ArithmeticThetaDegreeAssembly
open ArithmeticThetaComponentDegreeR0184.ComponentHodgePowerDegreeR0184

namespace SplitHodgePowerDegree
/-- Only cusp residue degrees are replaced by one, using the actual projection. -/
lemma cusp_divisor_degree (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space)
    (F : (Component k L D X x) →₀ ℤ)
    (hF : ∀ y, (y ∈ cuspSet k L D X x → F y = (2*L : ℕ)) ∧
      (y ∉ cuspSet k L D X x → F y = 0)) :
    weightedDegree k (projection k L D X x) F =
      (2*L : ℕ) * (Nat.card (Cusps k L D X x) : ℤ) := by
  classical
  have hmem (y : Component k L D X x) : y ∈ F.support ↔ y ∈ cuspSet k L D X x := by
    rw [Finsupp.mem_support_iff]
    constructor
    · intro hy
      by_contra hc
      exact hy ((hF y).2 hc)
    · intro hy
      rw [(hF y).1 hy]
      exact_mod_cast (show 2 * L ≠ 0 by omega)
  have hcard := Nat.card_congr (Equiv.subtypeEquivRight hmem)
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  have hdeg (y : Component k L D X x) (hy : y ∈ F.support) :
      placeDegree k (projection k L D X x) y = 1 := by
    exact (split_cusp_residue k L ζ hζ hL heven D X x
      ⟨y, (hmem y).mp hy⟩).2
  unfold weightedDegree Finsupp.sum
  calc
    ∑ y ∈ F.support, (placeDegree k (projection k L D X x) y : ℤ) * F y =
        ∑ _y ∈ F.support, ((2*L : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hdeg y hy, (hF y).1 ((hmem y).mp hy)]
      simp
    _ = (2*L : ℕ) * (Nat.card (Cusps k L D X x) : ℤ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcard]
      ring

end SplitHodgePowerDegree

/-- Exact residue-weighted degree for every nonzero Hodge-power section,
including exponent zero, and its full-level upper bound. -/
theorem split_hodge_power_degree :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) ι) (t : (ArithmeticThetaComponentDegreeR0184.power k L D X x H n).presheaf.obj (Opposite.op ⊤)) (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ), t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) C t E → 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) = (n : ℤ) * (2*L : ℕ) * (Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) : ℤ) ∧ 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) ≤ (n : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
  intro k _ _ L ζ hζ hL heven D X x H hH n ι C t E ht hE
  have hg := ArithmeticThetaArithmeticHalfLinesR0237.field_component_geometry
    k L hL heven D X x
  letI := hg.1
  obtain ⟨A⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible
    (Component k L D X x) hg.2.2.2 (hodge k L D X x H)
    (H.invertible.pullback (inclusion k L D X x))
  let B := powerCover (Component k L D X x) (hodge k L D X x H) A 24
  obtain ⟨s, hs⟩ := split_compact_discriminant k L ζ hζ hL heven D X x H hH
  obtain ⟨hs0, hdiv⟩ := split_component_discriminant_divisor
    k L ζ hζ hL heven D X x H hH s hs
  obtain ⟨F, hF, hFc⟩ := hdiv (Component k L D X x) B
  have hd := cross_power_degree (Component k L D X x) k (projection k L D X x)
    hg.2.2.1 (hodge k L D X x H) n 24 ι (Component k L D X x) C B t
    (restrict k L D X x H 24 s) E F ht hs0 hE hF
  rw [SplitHodgePowerDegree.cusp_divisor_degree k L ζ hζ hL heven D X x F hFc] at hd
  norm_num only at hd
  constructor
  · simpa only [mul_assoc] using hd
  · rw [hd]
    have hb := (split_component_cusp_bound k L ζ hζ hL heven D X x).2.2
    have hb' : ((2*L : ℕ) : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
      exact_mod_cast hb
    exact mul_le_mul_of_nonneg_left hb' (Int.natCast_nonneg n)

#print axioms SplitHodgePowerDegree.cusp_divisor_degree
#print axioms split_hodge_power_degree
end ArithmeticThetaCyclotomicModularityR0239
