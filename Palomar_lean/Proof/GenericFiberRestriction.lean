module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

/-!
# Injectivity of restriction to the actual generic fiber

The fraction-field morphism is quasi-compact and scheme-theoretically dominant.
Flat base change preserves these properties, so its pullback is injective on
sections of every open, in particular on global regular functions.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ArithmeticThetaCompletedCharts

/-- Global regular functions on a flat scheme over `k[[t]]` are determined by
restriction along the categorical generic-fiber projection. -/
theorem generic_fiber_restriction_injective
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) [Flat f] :
    Function.Injective ((pullback.fst f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (PowerSeries k) (LaurentSeries k))))).appTop) := by
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (PowerSeries k) (LaurentSeries k)))
  have : QuasiCompact g := inferInstance
  have hinj : Function.Injective (algebraMap (PowerSeries k) (LaurentSeries k)) :=
    IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  have : IsDominant g := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap
      (algebraMap (PowerSeries k) (LaurentSeries k)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  have : IsSchemeTheoreticallyDominant g :=
    IsSchemeTheoreticallyDominant.of_isDominant g
  exact (pullback.fst f g).app_injective ⊤

end ArithmeticThetaCompletedCharts
