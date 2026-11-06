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
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_IsFinite_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g] [IsSeparated g] : IsFinite g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  haveI : IsProper g := IsProper.mk
  haveI : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    have hfin := (f ≫ g).finite_preimage_singleton z
    have hsub : g.base ⁻¹' {z} ⊆ f.base '' ((f ≫ g).base ⁻¹' {z}) := by
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
    exact (hfin.image _).subset hsub
  exact IsFinite.of_isProper_of_locallyQuasiFinite g
