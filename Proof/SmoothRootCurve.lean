module

public import SmoothNormalizedCurve
public import KummerCover

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaKummerCover

namespace ArithmeticThetaNormalizedCurve

universe u
noncomputable section

/-- The actual common-root normalization is smooth over the constant field. -/
theorem rootCover_smooth :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f],
      (∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ [Nonempty U],
        Ring.DimensionLEOne (X.presheaf.obj (Opposite.op U))) →
      ∀ (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
        (N s : ℕ), 0 < N → ∀ (r : Fin s → Ω) (a : Fin s → X.functionField),
        (∀ j, r j ^ N = algebraMap X.functionField Ω (a j)) →
        AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.comp
          (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) f) := by
  intro X _ k _ _ f _ hdim Ω _ _ N s hN r a hr
  let E := ArithmeticThetaKummerCover.generatedRootField X Ω s r
  letI : FiniteDimensional X.functionField E :=
    (ArithmeticThetaKummerCover.generatedRootField_degree X Ω N s hN r a hr).1
  exact normalization_smooth X k f hdim E

end
end ArithmeticThetaNormalizedCurve

#print axioms ArithmeticThetaNormalizedCurve.rootCover_smooth
