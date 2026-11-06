import RootCoverGenericRank
import GeometricRankConstancy

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaKummer ArithmeticThetaNormalization
  ArithmeticThetaNormalizationField ArithmeticThetaNormalizationFinite

namespace ArithmeticThetaGeometricDegree

universe u
noncomputable section

/-
The rank bound is obtained on the actual root-cover morphism.  The generic
rank theorem identifies its rank at the generic point with the function-field
degree of the actual normalization, while finite-flat rank constancy extends
that equality to every point of the integral base.
-/
theorem rootCover_geometric_degree_bound :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f]
      (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] (N s : ℕ),
      0 < N → ∀ (r : Fin s → Ω) (a : Fin s → X.functionField),
        (∀ j, r j ^ N = algebraMap X.functionField Ω (a j)) →
          ∀ x : X,
            AlgebraicGeometry.Scheme.Hom.finrank
                (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) x ≤ N ^ s := by
  intro X hX k hk hcz f hs hlf hrd Ω hΩ hAlg N s hN r a hr x
  let E : IntermediateField X.functionField Ω :=
    ArithmeticThetaKummerCover.generatedRootField X Ω s r
  have hdegree :=
    ArithmeticThetaKummerCover.generatedRootField_degree X Ω N s hN r a hr
  obtain ⟨hnoeth, hchar, hnormal⟩ :=
    ArithmeticThetaSmoothNormality.smooth_normalization_prerequisites X k f
  letI : IsLocallyNoetherian X := hnoeth
  letI : CharZero X.functionField := hchar
  letI : FiniteDimensional X.functionField E := hdegree.1
  letI : Algebra.IsAlgebraic X.functionField E := Algebra.IsAlgebraic.of_finite _ _
  letI : Algebra.IsIntegral X.functionField E := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable X.functionField E := inferInstance
  letI : IsFinite (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    extensionFromNormalization_finite X E hnormal
  letI : Flat (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    rootCover_finite_flat X k f Ω N s hN r a hr
  letI : LocallyOfFinitePresentation (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  letI : IsIntegral (ArithmeticThetaKummerCover.rootCover X Ω s r) := inferInstance
  letI : IsDominant (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) := inferInstance
  have hconst := finrank_eq_generic_on_integral_target
    (ArithmeticThetaKummerCover.rootCover X Ω s r) X
    (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) x
  have hgeneric := rootCover_generic_finrank_eq_functionField_finrank
    X k f Ω N s hN r a hr
  have hbound := (ArithmeticThetaKummerCover.rootCover_functionField_degree
    X Ω N s hN r a hr).2
  calc
    AlgebraicGeometry.Scheme.Hom.finrank
        (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) x =
        AlgebraicGeometry.Scheme.Hom.finrank
          (ArithmeticThetaKummerCover.rootCoverMap X Ω s r)
          (genericPoint X) := hconst
    _ = Module.finrank X.functionField
        (ArithmeticThetaKummerCover.rootCover X Ω s r).functionField := hgeneric
    _ ≤ N ^ s := hbound

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.rootCover_geometric_degree_bound
