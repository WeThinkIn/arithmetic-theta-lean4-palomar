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
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Definitions.Def_AlgebraicCurve_RelCartier
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] {I : Y.IdealSheafData} (hI : I.IsInvertible) (g : X ⟶ Y)
    (h : ((I.comap g).support : Set X) ≠ Set.univ) : (I.comap g).IsInvertible := by
  intro x
  obtain ⟨U, f, hxf, a, ha, hIa⟩ := hI (g.base x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (g ⁻¹ᵁ Y.basicOpen f : X.Opens) from hxf) (g ⁻¹ᵁ Y.basicOpen f).isOpen
  let V' : X.affineOpens := ⟨V, hV⟩
  have hx1 : x ∈ X.basicOpen (1 : Γ(X, V')) := by simpa using hxV
  refine ⟨V', 1, hx1, ?_⟩
  have hVle' : (V' : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hVle
  have hle : (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) :=
    (X.basicOpen_le (1 : Γ(X, V'))).trans hVle'
  have key := Scheme.IdealSheafData.ideal_comap_of_le I g (Y.affineBasicOpen f)
    (X.affineBasicOpen (1 : Γ(X, V'))) hle
  rw [hIa, Ideal.map_span, Set.image_singleton] at key
  set b : Γ(X, (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens)) := (g.appLE _ _ hle).hom a with hb
  refine ⟨b, ?_, key⟩

  haveI : Nonempty (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) := ⟨⟨x, hx1⟩⟩
  refine mem_nonZeroDivisors_of_ne_zero fun hb0 => h ?_

  have hsub : ((X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) : Set X) ⊆ (I.comap g).support := by
    intro y hy
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := X.affineBasicOpen (1 : Γ(X, V'))) hy, key,
      hb0, Scheme.mem_zeroLocus_iff]
    intro c hc
    rw [SetLike.mem_coe, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hc
    subst hc
    rw [Scheme.basicOpen_zero]
    exact fun h => h
  have hdense : Dense (((X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) : Set X)) :=
    (X.affineBasicOpen (1 : Γ(X, V'))).1.isOpen.dense ⟨x, hx1⟩
  refine Set.eq_univ_of_univ_subset ?_
  rw [← dense_iff_closure_eq.mp hdense]
  exact closure_minimal hsub (I.comap g).support.isClosed
