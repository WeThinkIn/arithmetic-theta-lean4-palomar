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
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ) := by
  refine ⟨AdicCompletion.map_injective I (LinearMap.ker ρ).injective_subtype, ?_⟩
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker ρ).subtype ρ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have h1 : Function.Exact (AdicCompletion.map I (LinearMap.ker ρ).subtype)
      (AdicCompletion.map I ρ.rangeRestrict) :=
    AdicCompletion.map_exact (LinearMap.ker ρ).injective_subtype hex hsurj
  have h2 : Function.Injective (AdicCompletion.map I (LinearMap.range ρ).subtype) :=
    AdicCompletion.map_injective I (LinearMap.range ρ).injective_subtype
  have hfac : (LinearMap.range ρ).subtype ∘ₗ ρ.rangeRestrict = ρ := by
    ext x; rfl
  have h3 : AdicCompletion.map I ρ =
      AdicCompletion.map I (LinearMap.range ρ).subtype ∘ₗ AdicCompletion.map I ρ.rangeRestrict := by
    first
      | (rw [AdicCompletion.map_comp, hfac])
      | (rw [← AdicCompletion.map_comp, hfac])
  rw [h3, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr h2)]
  exact (h1.linearMap_ker_eq).symm
