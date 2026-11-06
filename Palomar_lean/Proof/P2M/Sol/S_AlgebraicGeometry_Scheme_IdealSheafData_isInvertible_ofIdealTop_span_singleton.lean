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
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Definitions.Def_AlgebraicCurve_RelCartier
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} [IsAffine X] (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).IsInvertible := by
  intro x
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hle : (X.affineBasicOpen (1 : Γ(X, T)) : X.Opens) ≤ (T : X.Opens) := X.basicOpen_le _
  refine ⟨T, 1, by rw [Scheme.basicOpen_one]; trivial, (X.presheaf.map (homOfLE hle).op).hom r, ?_, ?_⟩
  · letI := T.2.isLocalization_basicOpen (1 : Γ(X, T))
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers (1 : Γ(X, T)))
      (S := Γ(X, X.basicOpen (1 : Γ(X, T)))) hr
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
