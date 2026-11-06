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
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) :
    (OModulePresheaf.unit π).IsQuasicoherent := by
  intro U f
  haveI hloc : IsLocalization.Away f Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) (show Γ(V, V.basicOpen f) from x)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, y, ?_⟩
    show (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) * (show Γ(V, V.basicOpen f) from x)
    have e1 : (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y = algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) y := rfl
    have e2 : (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)
        = algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) (s : Γ(V, ↑U)) := by rw [← hn]; rfl
    rw [e1, e2, ← hs, mul_comm]
  · have hy' : algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) (show Γ(V, ↑U) from y) = 0 := hy
    obtain ⟨⟨m, hm⟩, hmy⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).mp hy'
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    exact ⟨n, hmy⟩
