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
public import Mathlib.RingTheory.LaurentSeries
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped NNReal
open HahnSeries

namespace LaurentSeries.XAdic

variable (F : Type*) [Field F]

theorem valued_single_one_one :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
        (HahnSeries.single (1 : ℤ) (1 : F))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  simpa [WithZero.exp] using LaurentSeries.valuation_single_zpow (K := F) 1

theorem single_one_one_ne_zero : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ≠ 0 := by
  intro h
  have hv := valued_single_one_one F
  rw [h, map_zero] at hv
  exact WithZero.zero_ne_coe hv

scoped instance rankOne :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankOne := by
  haveI hnt : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨⟨HahnSeries.single (1 : ℤ) (1 : F),
      by rw [valued_single_one_one]; exact WithZero.coe_ne_zero,
      by
        rw [valued_single_one_one]
        intro h
        have h' := Multiplicative.ofAdd.injective (WithZero.coe_inj.mp (h.trans rfl : _ =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))))
        norm_num at h'⟩⟩
  haveI hle : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankLeOne :=
    Valuation.RankLeOne.mk
      ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding)
      (fun a b hab =>
        WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)
          (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hab))
  exact Valuation.RankOne.mk

scoped instance nontriviallyNormedField : NontriviallyNormedField (LaurentSeries F) :=
  Valued.toNontriviallyNormedField (LaurentSeries F) (WithZero (Multiplicative ℤ))

scoped instance isUltrametricDist : IsUltrametricDist (LaurentSeries F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (LaurentSeries F) (WithZero (Multiplicative ℤ)))

scoped instance (priority := low) decidableEq : DecidableEq (LaurentSeries F) := Classical.decEq _

theorem norm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_single_one_one]
  exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr (by norm_num))

theorem nnnorm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖₊ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact norm_X_lt_one F

theorem nnnorm_X_pow_lt_one {N : ℕ} (hN : N ≠ 0) :
    ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le (nnnorm_X_lt_one F) hN

theorem X_pow_ne_zero (N : ℕ) : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N ≠ 0 :=
  pow_ne_zero N (single_one_one_ne_zero F)

theorem charZero [CharZero F] : CharZero (LaurentSeries F) :=
  charZero_of_injective_ringHom (f := (HahnSeries.C : F →+* LaurentSeries F)) HahnSeries.C_injective

end LaurentSeries.XAdic

end
