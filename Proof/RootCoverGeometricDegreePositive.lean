module

public import RootCoverFlat
public import SmoothNormality
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaKummer ArithmeticThetaNormalization
  ArithmeticThetaNormalizationField ArithmeticThetaNormalizationFinite

namespace ArithmeticThetaGeometricDegree

universe u

noncomputable section

/-- The actual finite-flat common-root cover has positive geometric rank at every base point. -/
theorem rootCover_geometric_degree_positive :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f]
      (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] (N s : ℕ),
      0 < N → ∀ (r : Fin s → Ω) (a : Fin s → X.functionField),
        (∀ j, r j ^ N = algebraMap X.functionField Ω (a j)) →
          ∀ x : X, 1 ≤ AlgebraicGeometry.Scheme.Hom.finrank
            (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) x := by
  intro X hX k hk hcz f hsf hlf hrd Ω hΩ hAlg N s hN r a hr
  obtain ⟨hn, hc, hi⟩ := ArithmeticThetaSmoothNormality.smooth_normalization_prerequisites X k f
  letI := hn
  letI := hc
  have hgeom := ArithmeticThetaKummerCover.rootCover_geometry X Ω N s hN r a hr hi
  letI : AlgebraicGeometry.IsFinite (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) := hgeom.2.1
  letI : AlgebraicGeometry.Flat (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) :=
    rootCover_finite_flat X k f Ω N s hN r a hr
  intro x
  exact (AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective
    (ArithmeticThetaKummerCover.rootCoverMap X Ω s r)).mpr hgeom.2.2.2.1 x

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.rootCover_geometric_degree_positive
