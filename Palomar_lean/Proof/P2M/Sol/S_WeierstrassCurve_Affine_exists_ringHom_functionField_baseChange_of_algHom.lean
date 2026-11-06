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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import Definitions.Def_EllipticCurve_WeilPairingFun
public import P2M.Util

@[expose] public section
namespace P2MW.S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    (W : WeierstrassCurve F) (f : K →ₐ[F] K') :
    ∃ Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField,
      ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
        algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField
          (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))) := by
  classical

  have hcurve : (W⁄K).map (f : K →+* K') = W⁄K' := W.map_baseChange f
  let φ₀ : (W⁄K).CoordinateRing →+* ((W⁄K).map (f : K →+* K')).CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.map (W⁄K) (f : K →+* K')
  have hspan : (Ideal.span {((W⁄K).map (f : K →+* K')).polynomial} : Ideal K'[X][Y]) = Ideal.span {(W⁄K').polynomial} := by
    rw [hcurve]
  let ι : ((W⁄K).map (f : K →+* K')).CoordinateRing ≃+* (W⁄K').CoordinateRing := Ideal.quotEquivOfEq hspan
  let φ : (W⁄K).CoordinateRing →+* (W⁄K').CoordinateRing := ι.toRingHom.comp φ₀
  have hφmk : ∀ p : K[X][Y], φ (CoordinateRing.mk (W⁄K) p) = CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K'))) := by
    intro p
    simp only [φ, φ₀, ι, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      WeierstrassCurve.Affine.CoordinateRing.map_mk]
    exact Ideal.quotEquivOfEq_mk _ _
  have hφinj : Function.Injective φ :=
    ι.injective.comp (WeierstrassCurve.Affine.CoordinateRing.map_injective (W' := W⁄K) (f : K →+* K').injective)

  have hle : nonZeroDivisors (W⁄K).CoordinateRing ≤ (nonZeroDivisors (W⁄K').CoordinateRing).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    exact fun h => hx (hφinj (by rw [h, map_zero]))
  refine ⟨IsLocalization.map (M := nonZeroDivisors (W⁄K).CoordinateRing) (W⁄K').FunctionField φ hle, fun p => ?_⟩
  rw [IsLocalization.map_eq, hφmk]
