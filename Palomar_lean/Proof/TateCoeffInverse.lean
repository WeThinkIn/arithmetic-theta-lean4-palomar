module

public import TateSeriesDefinitions
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.ENatToNat

@[expose] public section

namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

/-- The coefficient of the formal inverse of `1 - a t^m` is the geometric
    coefficient `a^(n/m)` on multiples of `m`, and zero otherwise. -/
theorem geometric_inverse_coeff {k : Type u} [Field k] (a : k) (m n : ℕ) (hm : 0 < m) :
    PowerSeries.coeff n ((1 - ArithmeticThetaTateSeries.monomial a m)⁻¹) =
      if m ∣ n then a ^ (n / m) else 0 := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ m) :=
    PowerSeries.HasSubst.X_pow (R := k) hm.ne'
  let g : PowerSeries k :=
    (PowerSeries.substAlgHom hs) (PowerSeries.rescale a (PowerSeries.mk 1))
  have hmul : g * (1 - ArithmeticThetaTateSeries.monomial a m) = 1 := by
    have h0 := PowerSeries.mk_one_mul_one_sub_eq_one k
    have h1 := congrArg (PowerSeries.rescale a) h0
    simp only [map_mul, map_sub] at h1
    have h2 := congrArg (PowerSeries.substAlgHom hs) h1
    simp only [map_mul, map_sub, map_one] at h2
    rw [PowerSeries.rescale_X] at h2
    simp [PowerSeries.substAlgHom_X] at h2
    have hC : (PowerSeries.substAlgHom hs) (PowerSeries.C a) = PowerSeries.C a := by
      rw [PowerSeries.C_eq_algebraMap]
      exact (PowerSeries.substAlgHom hs).commutes a
    rw [hC] at h2
    simpa [g, ArithmeticThetaTateSeries.monomial] using h2
  have hne : PowerSeries.constantCoeff (1 - ArithmeticThetaTateSeries.monomial a m) ≠ 0 := by
    simp [ArithmeticThetaTateSeries.monomial, hm.ne']
  have hinv : g = (1 - ArithmeticThetaTateSeries.monomial a m)⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hne).2 hmul
  rw [← hinv]
  change PowerSeries.coeff n g = _
  have hg : g = PowerSeries.subst (PowerSeries.X ^ m)
      (PowerSeries.rescale a (PowerSeries.mk 1)) := by
    simpa [g, PowerSeries.coe_substAlgHom]
  rw [hg, PowerSeries.coeff_subst_X_pow hm.ne']
  rw [PowerSeries.coeff_rescale]
  simp [PowerSeries.coeff_mk]

end ArithmeticThetaTateBridges
