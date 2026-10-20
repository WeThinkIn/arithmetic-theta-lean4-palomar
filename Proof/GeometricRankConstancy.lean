module

public import Mathlib

@[expose] public section

/-!
# Generic rank constancy on an integral target

The finite-flat rank of a finite locally finitely presented morphism is locally
constant.  An integral scheme is irreducible, hence preconnected, so this local
constancy identifies the rank at every target point with its value at the
canonical generic point.
-/

set_option autoImplicit false

universe u

namespace ArithmeticThetaGeometricDegree

open AlgebraicGeometry CategoryTheory TopologicalSpace

/--
Sharper-bound rank transport: a finite, flat, locally finitely presented and
explicitly dominant morphism over an integral target has the same geometric
rank at every target point as at the generic point.

The `IsDominant` instance is retained in the interface because the theorem is
used for the actual dominant root cover.  The equality itself follows from
finite-flat local constancy and the preconnectedness supplied by integrality.
-/
theorem finrank_eq_generic_on_integral_target
    (Y X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral Y] [AlgebraicGeometry.IsIntegral X]
    (p : Quiver.Hom Y X)
    [AlgebraicGeometry.IsFinite p]
    [AlgebraicGeometry.Flat p]
    [AlgebraicGeometry.IsDominant p]
    [AlgebraicGeometry.LocallyOfFinitePresentation p]
    (x : X) :
    AlgebraicGeometry.Scheme.Hom.finrank p x =
      AlgebraicGeometry.Scheme.Hom.finrank p (genericPoint X) := by
  have hloc : IsLocallyConstant (Scheme.Hom.finrank p) :=
    Scheme.Hom.isLocallyConstant_finrank p
  exact hloc.apply_eq_of_isPreconnected
    PreconnectedSpace.isPreconnected_univ trivial trivial

#print axioms finrank_eq_generic_on_integral_target

end ArithmeticThetaGeometricDegree
