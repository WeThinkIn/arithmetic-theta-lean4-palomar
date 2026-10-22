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
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace SheafGlueGC3

open TopCat TopCat.Presheaf

theorem stalkFunctor_map_surjective_of_isBasis {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F G : X.Presheaf CommRingCat.{u}} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective (α.app (op U))) (x : X) :
    Function.Surjective ((stalkFunctor _ x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s, rfl⟩ := hα U hU t
  exact ⟨F.germ U x hxU s, by rw [stalkFunctor_map_germ_apply]⟩

end SheafGlueGC3

theorem solution {X B : Scheme.{u}} (p : X ⟶ B)
    (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) (U : B.Opens) :
    Function.Bijective (p.app U) := by
  let F : TopCat.Sheaf CommRingCat.{u} B.carrier := B.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} B.carrier := (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf
  let f : F ⟶ G := ⟨p.c⟩
  have key := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ =>
    ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).1) x,
     SheafGlueGC3.stalkFunctor_map_surjective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).2) x⟩)
  exact key
