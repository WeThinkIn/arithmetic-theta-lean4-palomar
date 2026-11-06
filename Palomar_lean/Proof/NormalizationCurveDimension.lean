module

public import SmoothCurveDimension
public import NormalizationField

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField

namespace ArithmeticThetaGeometricDegree

universe u

noncomputable section

/--
The actual affine chart of the normalization has dimension at most one.  The
normalization chart is identified with the integral closure of the base chart
in the specified finite extension field; integrality transfers the base
dimension bound, and the chart ring equivalence transports it back.
-/
theorem normalization_chart_dimensionLEOne :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f],
      ∀ (E : Type u) [Field E] [Algebra X.functionField E]
        [FiniteDimensional X.functionField E],
        ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ [Nonempty U],
          Ring.DimensionLEOne
            ((ArithmeticThetaNormalization.extensionNormalization X E).presheaf.obj
              (Opposite.op
                ((ArithmeticThetaNormalization.extensionFromNormalization X E ⁻¹ᵁ U)))) := by
  intro X hX k hk hcz f hs hlf hrd E hE hAlg hFin U hU hn
  letI := ((extensionFromNormalization X E).app U).hom.toAlgebra
  have hbase : Ring.DimensionLEOne Γ(X, U) :=
    smooth_relative_curve_dimension X k f U hU
  letI : Ring.DimensionLEOne (integralClosure Γ(X, U) E) :=
    Ring.DimensionLEOne.of_isIntegral Γ(X, U) (integralClosure Γ(X, U) E)
  exact Ring.DimensionLEOne.of_ringEquiv (normalizationChartRingEquiv X E U hU)

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.normalization_chart_dimensionLEOne
