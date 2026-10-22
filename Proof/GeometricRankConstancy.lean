module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial

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
