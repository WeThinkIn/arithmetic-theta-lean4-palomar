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
public import Definitions.Def_JacJ1Iface
public import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
public import Definitions.Def_AlgebraicGeometry_PolarisationRosati
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by
  have hg : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
  have s₁ : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ)) (pullback.fst (pullback.snd f σ) (pullback.snd f σ))
      (pullback.snd f σ) (pullback.snd f σ) := (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rw [hg.w]
    exact s₁.paste_horiz hg
  have s' : IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rwa [pullback.lift_snd]
  have step1 := IsPullback.of_right s' (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip
  exact step1.paste_vert hg
