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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Definitions.Def_AlgebraicGeometry_AdicThickening
public import Definitions.Def_AlgebraicGeometry_ProjSpace
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_isPullback_adicThickening_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (prX : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hprX₁ : prX ≫ adicThickeningι f I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g)
    (hprX₂ : prX ≫ adicThickeningToBase f I n = adicThickeningToBase (pullback.fst f g ≫ f) I n)
    (prY : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening g I n)
    (hprY₁ : prY ≫ adicThickeningι g I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g)
    (hprY₂ : prY ≫ adicThickeningToBase g I n = adicThickeningToBase (pullback.fst f g ≫ f) I n) :
    IsPullback prX prY (adicThickeningToBase f I n) (adicThickeningToBase g I n) := by

  have sqX : IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
    IsPullback.of_hasPullback _ _
  have sqY : IsPullback (adicThickeningι g I n) (adicThickeningToBase g I n) g (adicThickeningBase I n) :=
    IsPullback.of_hasPullback _ _
  have sqP : IsPullback (adicThickeningι (pullback.fst f g ≫ f) I n) (adicThickeningToBase (pullback.fst f g ≫ f) I n)
      (pullback.fst f g ≫ f) (adicThickeningBase I n) := IsPullback.of_hasPullback _ _
  have sqXY : IsPullback (pullback.snd f g) (pullback.fst f g) g f := (IsPullback.of_hasPullback f g).flip

  have L2 : IsPullback prX (adicThickeningι (pullback.fst f g ≫ f) I n) (adicThickeningι f I n) (pullback.fst f g) := by
    refine IsPullback.of_right ?_ hprX₁ sqX.flip
    rw [hprX₂]
    exact sqP.flip

  have O3 : IsPullback (adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g) prX g (adicThickeningι f I n ≫ f) :=
    L2.flip.paste_horiz sqXY

  have comm : prY ≫ adicThickeningToBase g I n = prX ≫ adicThickeningToBase f I n := by rw [hprY₂, hprX₂]
  refine (IsPullback.of_right ?_ comm sqY).flip
  rw [hprY₁, ← adicThickeningι_comp]
  exact O3
