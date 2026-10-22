module

public import CompletedAffineAlgebraization
public import CompletedCommonDenominator
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Ideal

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
universe u
noncomputable section

namespace ArithmeticThetaCompletedCharts

/-- A compatible localized completed family becomes algebraic after one common
power of the structural parameter.  The common denominator theorem produces
compatible unlocalized completions, and affine algebraization glues these to a
global regular function. -/
theorem localized_completed_algebraization :
    ∀ (k : Type u) [Field k]
      (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X
        (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f]
      (C : AlgebraicGeometry.Scheme.OrderedAffineCover X)
      (z : ArithmeticThetaCompletedCharts.LocalizedFamily
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C),
      ArithmeticThetaCompletedCharts.LocalizedCompatible
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C z →
      ∃ (b : ℕ)
        (a : ArithmeticThetaCompletedCharts.Sections
          (PowerSeries k) X f ⊤),
        ∀ i : C.ι,
          ArithmeticThetaCompletedCharts.toLocalized
              (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i)
              (ArithmeticThetaCompletedCharts.globalToCompleted
                (PowerSeries k) X f (PowerSeries.X : PowerSeries k) (C.U i) a) =
            (PowerSeries.X : PowerSeries k) ^ b • z i := by
  intro k _ X f _ _ C z hz
  obtain ⟨b, w, hw, hpow⟩ :=
    completed_common_denominator k X f C z hz
  obtain ⟨a, ha, _⟩ :=
    completed_affine_algebraization (PowerSeries k)
      (PowerSeries.X : PowerSeries k) X f C w hw
  refine ⟨b, a, ?_⟩
  intro i
  rw [ha i, hpow i]

end ArithmeticThetaCompletedCharts
