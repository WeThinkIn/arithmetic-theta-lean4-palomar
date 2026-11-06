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
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {X : Scheme.{u}} [IsNoetherian X] (𝓙₁ 𝓙₂ : X.IdealSheafData)
    (h : ∀ U : X.affineOpens, 𝓙₁.ideal U ≤ (𝓙₂.ideal U).radical) :
    ∃ t : ℕ, ∀ U : X.affineOpens, 𝓙₁.ideal U ^ t ≤ 𝓙₂.ideal U := by
  classical

  have hx : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  let V : s → X.affineOpens := fun y => ⟨U y.1, hU y.1⟩
  have hV : ⨆ y, (V y).1 = ⊤ := by
    refine top_le_iff.mp (fun x _ => ?_)
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ s, x ∈ (U y : Set X) := by
      simpa only [Set.mem_iUnion, exists_prop] using hs (Set.mem_univ x)
    exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

  have hn : ∀ y : s, ∃ n : ℕ, 𝓙₁.ideal (V y) ^ n ≤ 𝓙₂.ideal (V y) := fun y => by
    haveI : IsNoetherianRing Γ(X, (V y).1) := IsLocallyNoetherian.component_noetherian (V y)
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h (V y)) (IsNoetherian.noetherian _)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, fun W => ?_⟩
  have hle : 𝓙₁ ^ Finset.univ.sup n ≤ 𝓙₂ := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top V hV fun y => ?_
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    exact (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ y))).trans (hn y)
  have := Scheme.IdealSheafData.le_def.mp hle W
  rwa [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] at this
