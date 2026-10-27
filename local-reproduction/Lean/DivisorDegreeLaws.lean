import PrincipalDegreeZero

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

/-- Residue-degree-weighted degree is additive on finitely supported divisors. -/
theorem weightedDegree_add
    (X : Scheme.{u}) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (D E : X →₀ ℤ) :
    weightedDegree k f (D + E) = weightedDegree k f D + weightedDegree k f E := by
  classical
  unfold weightedDegree
  exact Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _)

/-- Changing a divisor by the actual principal divisor of a nonzero function
preserves its degree on an integral proper curve with one-dimensional charts. -/
theorem weightedDegree_eq_of_principal_difference
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (D E : X →₀ ℤ) :
    g ≠ 0 → MatchesPrincipalOrder X g (D - E) →
      weightedDegree k f D = weightedDegree k f E := by
  intro hg hDE
  have hz := principal_degree_zero X k f hcurve g (D - E) hg hDE
  have hadd := weightedDegree_add X k f (D - E) E
  simpa only [sub_add_cancel, hz, zero_add] using hadd

end ArithmeticThetaCurveDegree

#print axioms ArithmeticThetaCurveDegree.weightedDegree_add
#print axioms ArithmeticThetaCurveDegree.weightedDegree_eq_of_principal_difference
