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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {Y : Scheme.{u}} [CompactSpace Y] {n : ℕ} (X : Fin n → Scheme.{u}) (h : ∀ j, Y ⟶ X j)
    (𝒰 : ∀ j, (X j).OrderedAffineCover) :
    ∃ (𝒲 : Y.OrderedAffineCover) (lam : ∀ j, 𝒲.ι → (𝒰 j).ι),
      ∀ (j : Fin n) (w : 𝒲.ι), 𝒲.U w ≤ (h j) ⁻¹ᵁ (𝒰 j).U (lam j w) := by
  classical

  have hidx : ∀ (y : Y) (j : Fin n), ∃ i : (𝒰 j).ι, (h j).base y ∈ (𝒰 j).U i := by
    intro y j
    have hy : (h j).base y ∈ (⊤ : (X j).Opens) := trivial
    rw [← (𝒰 j).iSup_eq_top] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  choose a ha using hidx

  have hW : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧
      ∀ j : Fin n, (W : Set Y) ⊆ (h j).base ⁻¹' ((𝒰 j).U (a y j) : Set (X j)) := by
    intro y
    set O : Set Y := ⋂ j : Fin n, (h j).base ⁻¹' ((𝒰 j).U (a y j) : Set (X j)) with hO
    have hOopen : IsOpen O :=
      isOpen_iInter_of_finite fun j => ((𝒰 j).U (a y j)).isOpen.preimage (h j).base.hom.continuous
    have hyO : y ∈ O := Set.mem_iInter.mpr fun j => ha y j
    obtain ⟨_, ⟨W, hWaff, rfl⟩, hyW, hWO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyO hOopen
    exact ⟨W, hWaff, hyW, fun j => hWO.trans (Set.iInter_subset _ j)⟩
  choose W hWaff hyW hWsub using hW

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyW y⟩)

  letI : LinearOrder (↥t) := LinearOrder.lift' (Fintype.equivFin (↥t)) (Fintype.equivFin (↥t)).injective
  refine ⟨{ ι := ↥t
            U := fun w => W w.1
            isAffineOpen := fun w => hWaff w.1
            iSup_eq_top := ?_ }, fun j w => a w.1 j, fun j w => ?_⟩
  · refine top_le_iff.mp fun y _ => ?_
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hyw⟩
  · intro y hy
    exact hWsub w.1 j hy
