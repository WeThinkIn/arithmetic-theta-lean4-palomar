module

public import Mathlib
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
public import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ArithmeticThetaGeometricDegree

universe u

noncomputable section

/-
The two imported geometric dimension results are proved in the deployed local
library.  The first bounds the topological Krull dimension of a smooth
relative-dimension-`n` scheme over a field by `n`; the second identifies that
dimension with the Krull dimension of each nonempty affine chart of an
integral, locally-finite-type scheme.  The final conversion uses the standard
domain characterization of Krull dimension at most one.
-/
theorem smooth_relative_curve_dimension :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f],
      ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ [Nonempty U],
        Ring.DimensionLEOne (X.presheaf.obj (Opposite.op U)) := by
  intro X hX k hk hcz f hs hlf hrd U hU hn
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    have htop :=
      AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f 1
    have heq :=
      AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
        f hU (⟨(Classical.choice hn : U), (Classical.choice hn : U).property⟩ :
          (U : Set X).Nonempty)
    rw [heq] at htop
    exact_mod_cast htop
  letI : Ring.KrullDimLE 1 Γ(X, U) := Ring.krullDimLE_iff.mpr hdim
  exact ⟨fun {p} hp hprime =>
    Ideal.IsPrime.isMaximal_of_ne_bot hprime hp⟩

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.smooth_relative_curve_dimension
