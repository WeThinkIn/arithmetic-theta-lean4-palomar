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
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.CategoryTheory.Monoidal.Mon
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace P4Aux

theorem bijective_app_congr {X B : Scheme.{u}} (p : X ⟶ B) {V W : B.Opens} (e : V = W)
    (h : Function.Bijective (p.app V)) : Function.Bijective (p.app W) := by
  subst e; exact h

end P4Aux

open P4Aux

set_option backward.isDefEq.respectTransparency false in

theorem solution {X B : Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by
  have e : U.ι ''ᵁ ⊤ = U := U.ι_image_top
  apply bijective_app_congr p e
  have key : p.app (U.ι ''ᵁ ⊤) =
      (p ∣_ U).appTop ≫ X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op := by
    simp only [morphismRestrict_appTop, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id]
    rw [show X.presheaf.map (𝟙 _) = 𝟙 _ from X.presheaf.map_id _, Category.comp_id]
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op)).comp h
