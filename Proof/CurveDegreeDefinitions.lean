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
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import FunctionOrders
public import SmoothPrerequisites

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

def baseToResidue (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : k →+* X.residueField x :=
  (Scheme.Γevaluation X x).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

def placeDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) := (baseToResidue k f x).toAlgebra
  Module.finrank k (X.residueField x)

def OneDimensionalCharts (X : Scheme.{u}) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U],
    Ring.DimensionLEOne Γ(X, U)

def principalOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) : X → ℤ :=
  fun x => Scheme.ord g x

def weightedDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (D : X →₀ ℤ) : ℤ :=
  D.sum (fun x n => (placeDegree k f x : ℤ) * n)

def MatchesPrincipalOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (D : X →₀ ℤ) : Prop :=
  ∀ x, D x = principalOrder X g x

end ArithmeticThetaCurveDegree
