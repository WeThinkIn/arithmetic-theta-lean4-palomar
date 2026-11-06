module

public import RamifiedMarkedSectionsR0154
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
public import Mathlib.RingTheory.LaurentSeries
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
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial

@[expose] public section

/-! Correct scalar actions for the ramified-period recovery.
The r0154 definitions remain immutable. Its LaurentDegree predicate is not
used by the new degree obligation. Every rank below binds the actual module.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155

def LaurentDegree (k : Type u) [Field k] (d : ℕ)
    (ell : LaurentSeries k →+* LaurentSeries k) : Prop :=
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := ell.toAlgebra
  letI : Module (LaurentSeries k) (LaurentSeries k) :=
    @Algebra.toModule _ _ _ _ ell.toAlgebra
  FiniteDimensional (LaurentSeries k) (LaurentSeries k) ∧
    Module.finrank (LaurentSeries k) (LaurentSeries k) = d

def FiniteFieldMap {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (α : Y.functionField →+* X.functionField) : Prop :=
  letI : Algebra Y.functionField X.functionField := α.toAlgebra
  letI : Module Y.functionField X.functionField :=
    @Algebra.toModule _ _ _ _ α.toAlgebra
  FiniteDimensional Y.functionField X.functionField

def fieldDegree {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (α : Y.functionField →+* X.functionField) : ℕ :=
  letI : Algebra Y.functionField X.functionField := α.toAlgebra
  letI : Module Y.functionField X.functionField :=
    @Algebra.toModule _ _ _ _ α.toAlgebra
  Module.finrank Y.functionField X.functionField

end ArithmeticThetaRamifiedPeriodR0155
