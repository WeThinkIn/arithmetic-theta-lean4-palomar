module

public import SectionDivisor
public import SectionOrderDefinitions
public import EffectiveDivisorBounds

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaCurveDegree

universe u v
noncomputable section

namespace ArithmeticThetaSectionOrder

/-- A section's effective order divisor satisfies the actual residue-weighted point bound. -/
theorem section_order_point_le_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (H : X.Modules) (ι : Type v)
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (D : X →₀ ℤ)
    (_hD : MatchesSectionOrder X H C s D)
    (heff : ∀ x, 0 ≤ D x)
    (hsupp : ∀ x ∈ D.support, Order.coheight x = 1) :
    ∀ x, D x ≤ weightedDegree k f D := by
  exact effective_divisor_point_le_degree X k f hcurve D heff hsupp

/-- A matched nonzero section cannot have local order greater than its divisor degree. -/
theorem nonzero_section_order_not_above_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (H : X.Modules) (ι : Type v)
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (D : X →₀ ℤ) (i : ι) (x : X)
    (hx : x ∈ C.opens i) (_hs : s ≠ 0)
    (hD : MatchesSectionOrder X H C s D)
    (heff : ∀ y, 0 ≤ D y)
    (hsupp : ∀ y ∈ D.support, Order.coheight y = 1) :
    ¬ (weightedDegree k f D < localOrder X H C s i x) := by
  have hbound := section_order_point_le_degree X k f hcurve H ι C s D hD heff hsupp x
  rw [hD i x hx] at hbound
  exact not_lt_of_ge hbound

end ArithmeticThetaSectionOrder

#print axioms ArithmeticThetaSectionOrder.section_order_point_le_degree
#print axioms ArithmeticThetaSectionOrder.nonzero_section_order_not_above_degree
