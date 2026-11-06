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
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩
