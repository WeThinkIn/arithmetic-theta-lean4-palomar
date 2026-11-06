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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem.solution
