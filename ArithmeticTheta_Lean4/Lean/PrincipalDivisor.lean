import FinitePrincipalSupport

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

/-- The finitely supported principal divisor records the order of a nonzero
rational function at every point. -/
theorem principal_divisor_exists
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) :
    g ≠ 0 → ∃ D : X →₀ ℤ, MatchesPrincipalOrder X g D := by
  intro hg
  classical
  have hfin : Set.Finite {x : X | principalOrder X g x ≠ 0} :=
    finite_principal_support X k f hcurve g hg
  let s : Finset X := hfin.toFinset
  let D : X →₀ ℤ := Finsupp.onFinset s (principalOrder X g)
    (by
      intro x hx
      exact hfin.mem_toFinset.mpr hx)
  refine ⟨D, ?_⟩
  intro x
  exact Finsupp.onFinset_apply

end ArithmeticThetaCurveDegree

#print axioms ArithmeticThetaCurveDegree.principal_divisor_exists
