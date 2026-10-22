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
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S S' A₁ X₁ A U : Scheme.{u}} (f₁ : A₁ ⟶ S) (g₁ : X₁ ⟶ S) (ι : S' ⟶ S)
    (f : A ⟶ S') (g : U ⟶ S') (a : A ⟶ A₁) (u : U ⟶ X₁)
    (ha : IsPullback a f f₁ ι) (hu : IsPullback u g g₁ ι) :
    IsPullback (pullback.map f g f₁ g₁ a u ι ha.w.symm hu.w.symm)
      (pullback.fst f g ≫ f) (pullback.fst f₁ g₁ ≫ f₁) ι := by

  have h1 : IsPullback (pullback.map f g f₁ g₁ a u ι ha.w.symm hu.w.symm) (pullback.snd f g) (pullback.snd f₁ g₁) u := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₁ g₁) (v₁₃ := f₁) (h₂₂ := g₁) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f₁ g₁)
    rw [pullback.lift_fst, hu.w]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback f g) ha

  have h2 := IsPullback.paste_vert h1 hu
  rw [pullback.condition (f := f) (g := g), pullback.condition (f := f₁) (g := g₁)]
  exact h2
