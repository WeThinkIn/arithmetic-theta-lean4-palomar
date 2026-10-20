module

public import SectionRatios

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree

universe u v w
noncomputable section
namespace ArithmeticThetaSectionCompletion

private theorem coefficient_nonzero
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (hH : IsLineBundle X H)
    {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i : ι)
    (hs : s ≠ 0) : sectionCoefficient X H (C.opens i) (C.frame i) s ≠ 0 := by
  intro hz
  apply hs
  apply sectionCoefficient_injective X H hH (C.opens i) (C.frame i)
  rw [hz]
  simp [sectionCoefficient, sectionCoordinate]

private theorem ratio_nonzero
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (hH : IsLineBundle X H)
    {ι : Type v} (C : NormalFrameCover X H ι) (s s₀ : Γ(H, ⊤)) (i : ι)
    (hs : s ≠ 0) (hs₀ : s₀ ≠ 0) : sectionRatio X H C i s s₀ ≠ 0 := by
  exact div_ne_zero (coefficient_nonzero X H hH C s i hs)
    (coefficient_nonzero X H hH C s₀ i hs₀)

/-- The actual ratio of two nonzero sections has their divisor difference as
its principal order, including points outside coheight one. -/
theorem section_ratio_principal_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules)
    (hH : IsLineBundle X H)
    (ι : Type v)
    (C : NormalFrameCover X H ι)
    (s s₀ : Γ(H, ⊤))
    (D D₀ : X →₀ ℤ)
    (i : ι) :
    s ≠ 0 → s₀ ≠ 0 →
    MatchesSectionOrder X H C s D →
    MatchesSectionOrder X H C s₀ D₀ →
    MatchesPrincipalOrder X (sectionRatio X H C i s s₀)
    (D - D₀) := by
  intro hs hs₀ hD hD₀ x
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp
    (C.covers (show x ∈ (⊤ : X.Opens) by trivial))
  change D x - D₀ x = Scheme.ord (sectionRatio X H C i s s₀) x
  rw [hD j x hxj, hD₀ j x hxj, section_ratio_frame_independent X H hH ι C s s₀ i j hs₀]
  have hden := coefficient_nonzero X H hH C s₀ j hs₀
  have hmul := Scheme.ord_mul (x := x) (ratio_nonzero X H hH C s s₀ j hs hs₀) hden
  have heq : sectionRatio X H C j s s₀ *
      sectionCoefficient X H (C.opens j) (C.frame j) s₀ =
      sectionCoefficient X H (C.opens j) (C.frame j) s := by
    exact div_mul_cancel₀ _ hden
  rw [heq] at hmul
  unfold localOrder
  omega

/-- Nonzero sections of the same actual line have equal residue-weighted
divisor degree under the displayed proper curve hypotheses. -/
theorem section_fixed_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X)
    (H : X.Modules)
    (hH : IsLineBundle X H)
    (ι : Type v)
    (C : NormalFrameCover X H ι)
    (s s₀ : Γ(H, ⊤))
    (D D₀ : X →₀ ℤ) :
    s ≠ 0 → s₀ ≠ 0 →
    MatchesSectionOrder X H C s D →
    MatchesSectionOrder X H C s₀ D₀ →
    weightedDegree k f D = weightedDegree k f D₀ := by
  intro hs hs₀ hD hD₀
  obtain ⟨i, _hi⟩ := Opens.mem_iSup.mp
    (C.covers (show genericPoint X ∈ (⊤ : X.Opens) by trivial))
  exact weightedDegree_eq_of_principal_difference X k f hcurve
    (sectionRatio X H C i s s₀) D D₀
    (ratio_nonzero X H hH C s s₀ i hs hs₀)
    (section_ratio_principal_divisor X H hH ι C s s₀ D D₀ i hs hs₀ hD hD₀)

/-- Construct the varying section divisor and bound its local order by the
degree of the single supplied reference divisor. -/
theorem section_fixed_degree_order_bound
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X)
    (H : X.Modules)
    (hH : IsLineBundle X H)
    (ι : Type v)
    (C : NormalFrameCover X H ι)
    (s s₀ : Γ(H, ⊤))
    (D₀ : X →₀ ℤ)
    (i : ι)
    (x : X) :
    s ≠ 0 → s₀ ≠ 0 →
    MatchesSectionOrder X H C s₀ D₀ →
    x ∈ C.opens i →
    localOrder X H C s i x ≤ weightedDegree k f D₀ := by
  intro hs hs₀ hD₀ hx
  obtain ⟨D, hD⟩ := exists_section_divisor X k f hcurve H ι C s hs
  have heff : ∀ y, 0 ≤ D y := by
    intro y
    obtain ⟨j, hy⟩ := Opens.mem_iSup.mp
      (C.covers (show y ∈ (⊤ : X.Opens) by trivial))
    rw [hD j y hy]
    exact local_order_nonnegative X H ι C s j y hy
  have hsupp := section_divisor_support_coheight_one X H ι C s D hD
  have hbound := section_order_point_le_degree X k f hcurve H ι C s D hD heff hsupp x
  rw [hD i x hx, section_fixed_degree X k f hcurve H hH ι C s s₀ D D₀
    hs hs₀ hD hD₀] at hbound
  exact hbound

end ArithmeticThetaSectionCompletion

#print axioms ArithmeticThetaSectionCompletion.section_ratio_principal_divisor
#print axioms ArithmeticThetaSectionCompletion.section_fixed_degree
#print axioms ArithmeticThetaSectionCompletion.section_fixed_degree_order_bound
