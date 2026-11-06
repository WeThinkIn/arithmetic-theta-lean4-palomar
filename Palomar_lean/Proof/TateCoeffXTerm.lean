module

public import TateCoeffInverse

@[expose] public section

namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

 theorem x_term_coeff {k : Type u} [Field k] (a : k) (m n : ℕ) (hm : 0 < m) :
    PowerSeries.coeff n (ArithmeticThetaTateSeries.xTerm (ArithmeticThetaTateSeries.monomial a m)) =
      if m ∣ n then (((n / m : ℕ) : k) * a ^ (n / m)) else 0 := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ m) :=
    PowerSeries.HasSubst.X_pow (R := k) hm.ne'
  let A : PowerSeries k →ₐ[k] PowerSeries k := PowerSeries.substAlgHom hs
  let g0 : PowerSeries k := PowerSeries.rescale a (PowerSeries.mk 1)
  let g : PowerSeries k := A g0
  have hcoeffg : ∀ r : ℕ, PowerSeries.coeff r ((1 - ArithmeticThetaTateSeries.monomial a m)⁻¹) =
      PowerSeries.coeff r g := by
    intro r
    rw [geometric_inverse_coeff a m r hm]
    change (if m ∣ r then a ^ (r / m) else 0) =
      PowerSeries.coeff r (A g0)
    rw [show A g0 = PowerSeries.subst (PowerSeries.X ^ m) g0 by
      simpa [A, PowerSeries.coe_substAlgHom]]
    rw [PowerSeries.coeff_subst_X_pow hm.ne']
    simp [g0, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  have hinv : (1 - ArithmeticThetaTateSeries.monomial a m)⁻¹ = g := by
    ext r
    exact hcoeffg r
  have hsq : ∀ r : ℕ, PowerSeries.coeff r (g0 ^ 2) =
      (((r + 1 : ℕ) : k) * a ^ r) := by
    intro r
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i g0 * PowerSeries.coeff j g0) r]
    simp [g0, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
    calc
      (∑ j ∈ Finset.range (r + 1), a ^ j * a ^ (r - j)) =
          ∑ j ∈ Finset.range (r + 1), a ^ r := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            rw [← pow_add]
            simp [Nat.add_sub_of_le hjle]
      _ = (r + 1 : k) * a ^ r := by simp
  have hbase : ∀ q : ℕ, PowerSeries.coeff q
      (PowerSeries.C a * PowerSeries.X * g0 ^ 2) =
      if q = 0 then 0 else (((q : ℕ) : k) * a ^ q) := by
    intro q
    by_cases hq : q = 0
    · subst q
      simp [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      rw [show PowerSeries.C a * PowerSeries.X * g0 ^ 2 =
        (PowerSeries.C a * g0 ^ 2) * PowerSeries.X by ring]
      have hc := PowerSeries.coeff_mul_X_pow' (PowerSeries.C a * g0 ^ 2) 1 q
      rw [show PowerSeries.coeff q ((PowerSeries.C a * g0 ^ 2) * PowerSeries.X) =
          if 1 ≤ q then PowerSeries.coeff (q - 1) (PowerSeries.C a * g0 ^ 2) else 0 by
            simpa only [pow_one] using hc]
      rw [PowerSeries.coeff_C_mul, hsq]
      rw [if_pos (Nat.one_le_iff_ne_zero.mpr hq), if_neg hq]
      have hpow : a ^ q = a ^ (q - 1) * a := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
      rw [hpow]
      have hnat : (q - 1) + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)
      rw [hnat]
      ring
  change PowerSeries.coeff n
      (ArithmeticThetaTateSeries.monomial a m *
        ((1 - ArithmeticThetaTateSeries.monomial a m)⁻¹) ^ 2) = _
  rw [hinv]
  change PowerSeries.coeff n (ArithmeticThetaTateSeries.monomial a m * (A g0) ^ 2) = _
  have hsubst : ArithmeticThetaTateSeries.monomial a m * (A g0) ^ 2 =
      A (PowerSeries.C a * PowerSeries.X * g0 ^ 2) := by
    simp [A, g0, ArithmeticThetaTateSeries.monomial, PowerSeries.substAlgHom_X,
      PowerSeries.C_eq_algebraMap]
  rw [hsubst]
  rw [show A (PowerSeries.C a * PowerSeries.X * g0 ^ 2) =
      PowerSeries.subst (PowerSeries.X ^ m) (PowerSeries.C a * PowerSeries.X * g0 ^ 2) by
        simpa [A, PowerSeries.coe_substAlgHom]]
  rw [PowerSeries.coeff_subst_X_pow hm.ne']
  rw [hbase]
  by_cases hn0 : n = 0
  · subst n
    simp [hm.ne']
  by_cases hdiv : m ∣ n
  · have hle : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv
    have hqpos : 0 < n / m := Nat.div_pos hle hm
    simp [hdiv, hqpos.ne']
  · simp [hdiv]

end ArithmeticThetaTateBridges
