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
public import Theorems.Thm_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace EAlpha

theorem surjective_specMap_stalkMap {X U : Scheme.{u}} (c : X ⟶ U) [Flat c] (x : ↥X) :
    Surjective (Spec.map (c.stalkMap x)) := by
  letI : Algebra (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) := (c.stalkMap x).hom.toAlgebra
  haveI : Module.Flat (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) := Flat.stalkMap c x
  haveI : IsLocalHom (algebraMap (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (c.stalkMap x).hom)
  haveI : Module.FaithfullyFlat (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (surjective_iff (Spec.map (c.stalkMap x))).mpr PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem main {X U Y : Scheme.{u}} (c : X ⟶ U) [Flat c] [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] :
    Flat p := by
  refine Flat.of_stalkMap p fun u => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  have hcomp : ((c ≫ p).stalkMap x).hom.Flat := Flat.stalkMap (c ≫ p) x
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  haveI h1 : Flat (Spec.map (c.stalkMap x)) := Flat.SpecMap_iff.2 (Flat.stalkMap c x)
  haveI h2 : Surjective (Spec.map (c.stalkMap x)) := surjective_specMap_stalkMap c x
  haveI h3 : Flat (Spec.map (c.stalkMap x) ≫ Spec.map (p.stalkMap (c.base x))) := by
    rw [← Spec.map_comp]; exact Flat.SpecMap_iff.2 hcomp
  exact Flat.SpecMap_iff.1
    (AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective (Spec.map (c.stalkMap x))
      (Spec.map (p.stalkMap (c.base x))))

end EAlpha

theorem solution {X U Y : Scheme.{u}} (c : X ⟶ U) [Flat c]
    [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] : Flat p :=
  EAlpha.main c p
