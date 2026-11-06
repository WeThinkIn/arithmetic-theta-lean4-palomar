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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Definitions.Def_EllipticCurve_FunctionFieldPullback
public import P2M.Util
public import P2M.Sol.S_WeierstrassCurve_Affine_valuation_transEquiv_le_self

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
theorem WeierstrassCurve.Affine.valuation_transEquiv_le_self {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {S : (W⁄K).Point} (hS : S ≠ 0) (h2S : S + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K (S + S) h2S).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K S hS).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le_self.solution
