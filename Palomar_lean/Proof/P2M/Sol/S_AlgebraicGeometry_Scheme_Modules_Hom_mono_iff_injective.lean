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
public import Mathlib.Algebra.Category.Grp.EpiMono
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem solution
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Mono φ ↔ ∀ U : X.Opens, Function.Injective (φ.app U) := by
  constructor
  · intro hφ U

    let ev : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} := (CategoryTheory.evaluation _ Ab.{u}).obj (op U)
    haveI : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
      preserves_mono_of_preservesLimit (Scheme.Modules.toPresheaf X) φ
    haveI : PreservesLimitsOfShape WalkingCospan ev := evaluation_preservesLimitsOfShape _
    haveI : Mono (ev.map ((Scheme.Modules.toPresheaf X).map φ)) := preserves_mono_of_preservesLimit _ _
    have h : Mono (φ.app U) := this
    exact (AddCommGrpCat.mono_iff_injective (φ.app U)).1 h
  · intro h
    refine ⟨fun g g' w => ?_⟩
    refine Scheme.Modules.hom_ext g g' fun U => ?_
    ext x
    apply h U
    have := congr(($w).app U x)
    simpa [Scheme.Modules.Hom.comp_app] using this
