module

public import ProperNoPoleDefinitionsR0089

@[expose] public section

open AlgebraicGeometry CategoryTheory
universe u
noncomputable section
namespace ArithmeticThetaProperNoPoleR0089
open ArithmeticThetaFormalConstants

set_option autoImplicit false

/- The fraction-ring predicate is equivalent to the regular-chart predicate
   because each chart map into its fraction ring is injective. -/
theorem fraction_structural_scalar_equivalence :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      (C : X.OrderedAffineCover),
      ChartConditions k X f C →
      ∀ (z : RingFamily (PowerSeries k) X f PowerSeries.X C) (c : LaurentSeries k),
        FractionConstant k X f C (embedFamily k X f C z) c ↔
          IsRingLaurentConstant k X f C z c := by
  intro k _ X f C hC z c
  constructor
  · rintro ⟨n, r, hr, hfrac⟩
    refine ⟨n, r, hr, ?_⟩
    intro i
    letI : IsDomain (Completed k X f (C.U i)) := hC i |>.1
    letI : IsDomain (Generic k X f (C.U i)) :=
      IsLocalization.Away.isDomain _ (hC i |>.2.2.2)
    have hinj : Function.Injective
        (algebraMap (Generic k X f (C.U i)) (Fractions k X f (C.U i))) :=
      IsFractionRing.injective (Generic k X f (C.U i)) (Fractions k X f (C.U i))
    apply hinj
    simpa only [map_mul, map_pow, embedFamily, toFraction] using hfrac i
  · rintro ⟨n, r, hr, hreg⟩
    refine ⟨n, r, hr, ?_⟩
    intro i
    letI : IsDomain (Completed k X f (C.U i)) := hC i |>.1
    letI : IsDomain (Generic k X f (C.U i)) :=
      IsLocalization.Away.isDomain _ (hC i |>.2.2.2)
    simpa only [map_mul, map_pow, embedFamily, toFraction] using
      congrArg (algebraMap (Generic k X f (C.U i)) (Fractions k X f (C.U i))) (hreg i)

end ArithmeticThetaProperNoPoleR0089
