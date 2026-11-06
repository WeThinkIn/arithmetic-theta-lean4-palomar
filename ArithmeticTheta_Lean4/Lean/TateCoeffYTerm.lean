import TateSeriesDefinitions
open scoped BigOperators
namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries
open PowerSeries
variable {k : Type*} [Field k]

lemma choose_sq (n : ℕ) :
    ((Nat.choose (n+1) 2 : ℕ) : k) + (Nat.choose n 2 : k) = (n : k)^2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.choose_succ_succ, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one] at *
    ring_nf at *
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one] at *
    rw [← ih]
    ring

lemma inv_cube : ((1 - (PowerSeries.X : PowerSeries k))⁻¹)^3 =
    (PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k))) := by
  let u : (PowerSeries k)ˣ := Units.mkOfMulEqOne (1 - (PowerSeries.X : PowerSeries k)) (PowerSeries.mk 1) (by rw [mul_comm]; exact PowerSeries.mk_one_mul_one_sub_eq_one k)
  have hu : u.val = (1 - (PowerSeries.X : PowerSeries k)) := by exact Units.val_mkOfMulEqOne _
  have huv : (u⁻¹).val = (1 - (PowerSeries.X : PowerSeries k))⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
    have hmul := u.val_inv
    simpa [hu] using hmul
  have h := PowerSeries.invOneSubPow_eq_inv_one_sub_pow (S := k) 3
  have hv := congrArg (fun z : (PowerSeries k)ˣ => z.val) h
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at hv
  change (PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k))) = (u⁻¹).val ^ 3 at hv
  rw [huv] at hv
  exact hv.symm

lemma base :
    (PowerSeries.X : PowerSeries k) * (1 + PowerSeries.X) *
      ((1 - PowerSeries.X)⁻¹)^3 =
    PowerSeries.mk (fun n => ((n^2 : ℕ) : k)) := by
  have hinv : ((1 - (PowerSeries.X : PowerSeries k))⁻¹)^3 =
      (PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k))) := by
    let u : (PowerSeries k)ˣ := Units.mkOfMulEqOne (1 - (PowerSeries.X : PowerSeries k)) (PowerSeries.mk 1) (by rw [mul_comm]; exact PowerSeries.mk_one_mul_one_sub_eq_one k)
    have hu : u.val = (1 - (PowerSeries.X : PowerSeries k)) := by exact Units.val_mkOfMulEqOne _
    have huv : (u⁻¹).val = (1 - (PowerSeries.X : PowerSeries k))⁻¹ := by
      apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
      have hmul := u.val_inv
      simpa [hu] using hmul
    have h := PowerSeries.invOneSubPow_eq_inv_one_sub_pow (S := k) 3
    have hv := congrArg (fun z : (PowerSeries k)ˣ => z.val) h
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at hv
    change (PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k))) = (u⁻¹).val ^ 3 at hv
    rw [huv] at hv
    exact hv.symm
  rw [hinv]
  rw [show (PowerSeries.X : PowerSeries k) * (1 + PowerSeries.X) * (PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k))) =
      PowerSeries.X ^ 1 * PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k)) +
      PowerSeries.X ^ 2 * PowerSeries.mk (fun n => (Nat.choose (2+n) 2 : k)) by ring]
  ext n
  rcases n with _ | _ | n
  · simp [PowerSeries.coeff_X_pow_mul']
  · simp [PowerSeries.coeff_X_pow_mul']
  · simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, Nat.succ_eq_add_one]
    convert choose_sq (k := k) (n + 2) using 1 <;> norm_num [Nat.cast_add] <;> ring

lemma inv_map {a : k} {m : ℕ} (hm : 0 < m) :
    PowerSeries.subst (R := k) (τ := Unit) (S := k) ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
      (PowerSeries.rescale a ((1 - PowerSeries.X)⁻¹)) =
      (1 - ArithmeticThetaTateSeries.monomial a m)⁻¹ := by
  let hs : PowerSeries.HasSubst ((PowerSeries.X : MvPowerSeries Unit k) ^ m) := PowerSeries.HasSubst.X_pow (R := k) hm.ne'
  let φ := PowerSeries.substAlgHom (R := k) (τ := Unit) (S := k) hs
  have hrel := congrArg (PowerSeries.rescale a)
    (PowerSeries.inv_mul_cancel (1 - (PowerSeries.X : PowerSeries k)) (by simp))
  have hrel2 := congrArg φ hrel
  have hne : PowerSeries.constantCoeff (1 - ArithmeticThetaTateSeries.monomial a m) ≠ 0 := by
    simp [ArithmeticThetaTateSeries.monomial, hm.ne']
  apply (PowerSeries.eq_inv_iff_mul_eq_one hne).2
  have hrescale := congrArg (PowerSeries.rescale a)
    ((PowerSeries.inv_mul_cancel (1 - (PowerSeries.X : PowerSeries k)) (by simp)))
  have hrescale' : PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹ *
      (1 - (PowerSeries.X : PowerSeries k))) =
      PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹) *
      PowerSeries.rescale a (1 - (PowerSeries.X : PowerSeries k)) := by
    rw [map_mul]
  rw [hrescale'] at hrel2
  rw [map_mul] at hrel2
  change φ (PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹)) *
      φ (PowerSeries.rescale a (1 - (PowerSeries.X : PowerSeries k))) =
      φ (PowerSeries.rescale a 1) at hrel2
  have hsecond : φ (PowerSeries.rescale a (1 - (PowerSeries.X : PowerSeries k))) =
      1 - ArithmeticThetaTateSeries.monomial a m := by
    rw [show PowerSeries.rescale a (1 - (PowerSeries.X : PowerSeries k)) =
      1 - PowerSeries.rescale a (PowerSeries.X : PowerSeries k) by rw [map_sub, map_one]]
    rw [PowerSeries.rescale_X]
    rw [map_sub, map_one, map_mul, PowerSeries.substAlgHom_X]
    rw [PowerSeries.C_eq_algebraMap, φ.commutes]
    simp [ArithmeticThetaTateSeries.monomial]
  rw [hsecond] at hrel2
  have hone : φ (PowerSeries.rescale a 1) = 1 := by simp [φ]
  rw [hone] at hrel2
  simpa only [φ, PowerSeries.coe_substAlgHom] using hrel2

lemma y_formula {a : k} {m : ℕ} (hm : 0 < m) :
    ArithmeticThetaTateSeries.yTerm (ArithmeticThetaTateSeries.monomial a m) =
      PowerSeries.subst (R := k) (τ := Unit) (S := k) ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
        (PowerSeries.rescale a
          ((PowerSeries.X : PowerSeries k) * (1 + PowerSeries.X) *
            ((1 - PowerSeries.X)⁻¹)^3)) := by
  let hs : PowerSeries.HasSubst ((PowerSeries.X : MvPowerSeries Unit k) ^ m) := PowerSeries.HasSubst.X_pow (R := k) hm.ne'
  have hi := inv_map (k:=k) (a:=a) (m:=m) hm
  have hpow : PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
      (PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹)^3) =
      (1 - ArithmeticThetaTateSeries.monomial a m)⁻¹ ^ 3 := by
    rw [show PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
      (PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹)^3) =
      (PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
        (PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹)))^3 by
      have hmap := map_pow (PowerSeries.substAlgHom (R := k) (τ := Unit) (S := k) hs)
        (PowerSeries.rescale a ((1 - (PowerSeries.X : PowerSeries k))⁻¹)) 3
      simpa only [PowerSeries.coe_substAlgHom] using hmap]
    rw [hi]
  have hfactor : PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
      (PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X))) =
      ArithmeticThetaTateSeries.monomial a m *
        (1 + ArithmeticThetaTateSeries.monomial a m) := by
    let φ : PowerSeries k →ₐ[k] MvPowerSeries Unit k :=
      PowerSeries.substAlgHom (R := k) (τ := Unit) (S := k) hs
    have hfactor0 : φ (PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X))) =
        ArithmeticThetaTateSeries.monomial a m *
          (1 + ArithmeticThetaTateSeries.monomial a m) := by
      rw [show PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X)) =
          (PowerSeries.rescale a PowerSeries.X) *
            (PowerSeries.rescale a (1 + PowerSeries.X)) by rw [map_mul]]
      rw [map_mul, PowerSeries.rescale_X]
      rw [map_add, map_one, PowerSeries.rescale_X]
      simp only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X]
      rw [PowerSeries.C_eq_algebraMap, φ.commutes]
      have hx : φ (PowerSeries.X : PowerSeries k) =
          (PowerSeries.X : MvPowerSeries Unit k)^m := by
        exact PowerSeries.substAlgHom_X hs
      rw [hx]
      simp [ArithmeticThetaTateSeries.monomial, PowerSeries.C_eq_algebraMap]
    simpa [φ, PowerSeries.coe_substAlgHom] using hfactor0
  have hsplit : PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
      (PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X) *
        ((1 - PowerSeries.X)⁻¹)^3)) =
      PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
        (PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X))) *
      PowerSeries.subst ((PowerSeries.X : MvPowerSeries Unit k) ^ m)
        (PowerSeries.rescale a ((1 - PowerSeries.X)⁻¹)^3) := by
    have hr : PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X) *
        ((1 - PowerSeries.X)⁻¹)^3) =
        PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X)) *
        PowerSeries.rescale a ((1 - PowerSeries.X)⁻¹)^3 := by
      rw [map_mul, map_pow]
    rw [hr]
    have hmap := map_mul (PowerSeries.substAlgHom (R := k) (τ := Unit) (S := k) hs)
      (PowerSeries.rescale a (PowerSeries.X * (1 + PowerSeries.X)))
      (PowerSeries.rescale a ((1 - PowerSeries.X)⁻¹)^3)
    simpa only [PowerSeries.coe_substAlgHom] using hmap
  rw [hsplit, hfactor, hpow]
  rfl

theorem y_term_coeff {k : Type u} [Field k] (a : k) (m n : ℕ) (hm : 0 < m) :
    PowerSeries.coeff n (ArithmeticThetaTateSeries.yTerm (ArithmeticThetaTateSeries.monomial a m)) =
      if m ∣ n then (((((n / m : ℕ) ^ 2 : ℕ) : k) * a ^ (n / m))) else 0 := by
  rw [y_formula hm]
  rw [base]
  rw [PowerSeries.coeff_subst_X_pow hm.ne']
  rw [PowerSeries.coeff_rescale]
  simp [PowerSeries.coeff_mk, mul_comm]

end ArithmeticThetaTateBridges
