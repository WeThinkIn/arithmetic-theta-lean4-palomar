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
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen

universe u v

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

theorem solution
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {W : Scheme.{u}} (a b : W ⟶ Proj 𝒜)
    (h : ∀ w : W, ∃ (n : ℕ) (r : A) (hn : 0 < n) (hr : r ∈ 𝒜 n)
      (e : a ⁻¹ᵁ Proj.basicOpen 𝒜 r = b ⁻¹ᵁ Proj.basicOpen 𝒜 r),
      w ∈ a ⁻¹ᵁ Proj.basicOpen 𝒜 r ∧
        ∀ x : Away 𝒜 r,
          a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl (Proj.awayToSection 𝒜 r x) =
            b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le (Proj.awayToSection 𝒜 r x)) :
    a = b := by
  refine Scheme.hom_ext_of_forall a b fun w => ?_
  obtain ⟨n, r, hn, hr, e, hw, happ⟩ := h w
  refine ⟨a ⁻¹ᵁ Proj.basicOpen 𝒜 r, hw, ?_⟩
  have hsurj : Function.Surjective (Proj.awayToSection 𝒜 r) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 r hr hn]
    exact (ConcreteCategory.bijective_of_isIso _).2
  have happLE : a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact happ y
  have key : a.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    haveI : IsAffine (Proj.basicOpen 𝒜 r).toScheme := Proj.isAffineOpen_basicOpen 𝒜 r hr hn
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happLE]
  have e₁ := Scheme.Hom.resLE_comp_ι a (U := Proj.basicOpen 𝒜 r) (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl
  have e₂ := Scheme.Hom.resLE_comp_ι b (U := Proj.basicOpen 𝒜 r) (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le
  rw [← e₁, ← e₂, key]
