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
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ArithmeticThetaElementary

/-- A relation of full series vanishes in each retained coefficient. -/
theorem truncation_inclusion :
    ∀ (h B : ℕ) (θ : Fin h → PowerSeries ℂ) (c : Fin h → ℂ),
      (∑ i : Fin h, c i • θ i) = 0 → ∀ a : Fin (B + 1),
        (∑ i : Fin h, c i * PowerSeries.coeff a.val (θ i)) = 0 := by
  intro h B θ c hc a
  have ha := congrArg (PowerSeries.coeff a.val) hc
  simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using ha

/-- Independent truncated columns certify independence of the full series. -/
theorem full_column_rank_early_stop :
    ∀ (h B : ℕ) (θ : Fin h → PowerSeries ℂ),
      LinearIndependent ℂ (fun i : Fin h => fun a : Fin (B + 1) =>
        PowerSeries.coeff a.val (θ i)) → LinearIndependent ℂ θ := by
  intro h B θ hcols
  rw [Fintype.linearIndependent_iff] at hcols ⊢
  intro c hc
  apply hcols c
  funext a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
    truncation_inclusion h B θ c hc a

/-- Nested relation spaces coincide when their outer dimensions agree. -/
theorem dimension_sandwich_certificate :
    ∀ (h : ℕ) (W K T : Submodule ℂ (Fin h → ℂ)),
      W ≤ K → K ≤ T → Module.finrank ℂ W = Module.finrank ℂ T →
        W = K ∧ K = T := by
  intro h W K T hWK hKT hdim
  have hWT : W = T := Submodule.eq_of_le_of_finrank_eq (hWK.trans hKT) hdim
  have hKW : K ≤ W := hWT.symm ▸ hKT
  exact ⟨le_antisymm hWK hKW, (le_antisymm hWK hKW).symm.trans hWT⟩

end ArithmeticThetaElementary
