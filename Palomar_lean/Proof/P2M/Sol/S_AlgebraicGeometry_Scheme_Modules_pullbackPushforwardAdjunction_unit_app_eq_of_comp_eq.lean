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
public import Mathlib.CategoryTheory.Monoidal.Mon
public import P2M.Util

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι) (N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N =
      (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N
        ≫ (Scheme.Modules.pushforward ι').map
            ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N) := by
  subst h
  have key := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction ι').comp (Scheme.Modules.pullbackPushforwardAdjunction t))
    (Scheme.Modules.pullbackPushforwardAdjunction (t ≫ ι')) (Scheme.Modules.pullbackComp t ι').inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at key
  have h1 : (Scheme.Modules.pullbackCongr (rfl : t ≫ ι' = t ≫ ι')).hom.app N = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have h2 : (Scheme.Modules.pushforwardCongr (rfl : t ≫ ι' = t ≫ ι')).hom.app
      ((Scheme.Modules.pullback (t ≫ ι')).obj N) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    rw [Scheme.Modules.pushforwardCongr_hom_app_app]
    simp
  rw [h1, h2, CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  have key' := key =≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
  dsimp only [Functor.comp_obj] at key'
  simp only [Category.assoc] at key'
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id] at key'
  simp only [Category.assoc, Functor.comp_obj]
  exact key'.symm
