module

public import NormalizedSectionDefinitions
public import LineRootGluing
public import EffectiveDivisorBounds
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaCurveDegree

universe u v
noncomputable section

namespace ArithmeticThetaSectionOrder

/-- The order of a genuine global section in an actual local frame.  The frame
coefficient is a regular section on the chart; no divisor or completion is
assumed by this definition. -/
def localOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules)
    {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤))
    (i : ι) (x : X) : ℤ :=
  Scheme.ord (sectionCoefficient X H (C.opens i) (C.frame i) s) x

/-- The actual finite-support divisor relation to be proved for a section. -/
def MatchesSectionOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules)
    {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤))
    (D : X →₀ ℤ) : Prop :=
  ∀ (i : ι) (x : X), x ∈ C.opens i → D x = localOrder X H C s i x

/-- Vanishing of all coefficients through the displayed q-degree. -/
def VanishesThrough {R : Type u} [Semiring R] (F : PowerSeries R) (B : ℕ) : Prop :=
  ∀ n ≤ B, PowerSeries.coeff n F = 0

/-- Divisibility by a power of the local parameter, expressing a lower q-order. -/
def HasQOrderAtLeast {R : Type u} [Semiring R] (F : PowerSeries R) (m : ℕ) : Prop :=
  ∃ G : PowerSeries R, F = PowerSeries.X ^ m * G

/-- The formal pullback along the cusp coordinate q = t^L.  The positive-L
case is the one used by the source; the totalized definition keeps the API
well-formed at L = 0 without treating that degenerate case as a theorem. -/
def scaledSeries {R : Type u} [Semiring R] (L : ℕ) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => if h : L ∣ n then PowerSeries.coeff (n / L) F else 0)

end ArithmeticThetaSectionOrder
