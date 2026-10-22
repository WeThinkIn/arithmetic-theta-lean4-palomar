module

public import FixedLineFiniteJet
public import TensorLineDegrees
public import FinitePullbackSectionDegree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
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
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
universe u v w
noncomputable section
namespace ArithmeticThetaGeometricPrerequisites

/-- The actual affine N-th-root algebra, not a certificate for its properties. -/
abbrev unitRootAlgebra (R : Type u) [CommRing R] (N : ℕ) (a : Rˣ) :=
  AdjoinRoot (Polynomial.X ^ N - Polynomial.C (a : R))

/-- The base parameter as a global function via the specific structural map. -/
def baseParameter (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) (t : R) : Γ(X, ⊤) :=
  f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)

/-- The actual coherent principal ideal of the parameter on X. -/
def parameterIdeal (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) (t : R) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {baseParameter R X f t})

/-- A compatible section of O on every actual infinitesimal thickening.
The transition maps are the scheme maps induced by ideal inclusions. -/
def CompatibleFormalFunctions (X : Scheme.{u}) (I : X.IdealSheafData)
    (s : ∀ n : ℕ, Γ((I ^ n).subscheme, ⊤)) : Prop :=
  ∀ (m n : ℕ) (h : I ^ n ≤ I ^ m),
    (Scheme.IdealSheafData.inclusion h).appTop (s n) = s m

end ArithmeticThetaGeometricPrerequisites
