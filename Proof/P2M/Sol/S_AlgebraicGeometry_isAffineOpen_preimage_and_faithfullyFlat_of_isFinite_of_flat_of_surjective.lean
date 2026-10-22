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
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [Flat g] (hsurj : Function.Surjective g)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (g ⁻¹ᵁ U) ∧ Function.Injective (g.app U).hom ∧
      (letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra;
        Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) := by
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra

  have hflat : (g.app U).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @Flat g inferInstance ⟨U, hU⟩ ⟨g ⁻¹ᵁ U, hV⟩ le_rfl
  haveI : Module.Flat Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := hflat

  have hcomap : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U))) := by
    intro q
    obtain ⟨x, hx⟩ := hsurj (hU.fromSpec q)
    have hxV : x ∈ g ⁻¹ᵁ U := by
      show g x ∈ U
      rw [hx]
      have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
      rw [hU.range_fromSpec] at this
      exact this
    obtain ⟨p, hp⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    refine ⟨p, hU.fromSpec.isOpenEmbedding.injective ?_⟩
    have h := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    have h' := congrArg (fun φ => φ p) h
    simp only [Scheme.Hom.comp_apply] at h'
    rw [hp, hx] at h'
    exact h'
  haveI hff : Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.FaithfullyFlat.of_comap_surjective hcomap
  exact ⟨hV, FaithfulSMul.algebraMap_injective Γ(Y, U) Γ(X, g ⁻¹ᵁ U), hff⟩
