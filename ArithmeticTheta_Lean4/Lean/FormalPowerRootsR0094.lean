import Mathlib

namespace ArithmeticThetaRamifiedMapR0094

private theorem unit_nth_root_with_constant
    (k : Type u) [Field k] [CharZero k] (n : Nat) (hn : 0 < n)
    (u : PowerSeries k) (hu : IsUnit u) (a : k)
    (hconst : PowerSeries.constantCoeff u = a ^ n) :
    Exists fun v : PowerSeries k =>
      v ^ n = u /\ PowerSeries.constantCoeff v = a := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  let p : Polynomial (PowerSeries k) := Polynomial.X ^ n - Polynomial.C u
  obtain ⟨v, hvroot, hvnear⟩ := HenselianRing.is_henselian p
    (Polynomial.monic_X_pow_sub_C u hn.ne') (PowerSeries.C a) (by
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
      simp [p, hconst]) (by
      apply IsUnit.map (Ideal.Quotient.mk I)
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hcc : PowerSeries.constantCoeff u ≠ 0 :=
        (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero
      have ha : a ≠ 0 := by
        intro ha
        apply hcc
        rw [hconst, ha, zero_pow hn.ne']
      simp [p, Polynomial.derivative_X_pow, ha, Nat.cast_ne_zero.mpr hn.ne'])
  refine ⟨v, ?_, ?_⟩
  · simpa [p, Polynomial.IsRoot, sub_eq_zero] using hvroot
  · have hzero : PowerSeries.constantCoeff (v - PowerSeries.C a) = 0 := by
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hvnear
      exact hvnear
    apply sub_eq_zero.mp
    simpa only [map_sub, PowerSeries.constantCoeff_C] using hzero

private theorem order_toNat_of_pow_eq
    (k : Type u) [Field k] (n : Nat) (hn : 0 < n) (f g : PowerSeries k)
    (hf : f ≠ 0) (hg : g ^ n = f) :
    n * g.order.toNat = f.order.toNat := by
  have hg0 : g ≠ 0 := by
    intro hz
    apply hf
    calc
      f = g ^ n := hg.symm
      _ = 0 := by simp [hz, hn.ne']
  have horder : n • g.order = f.order := by
    rw [← hg, PowerSeries.order_pow]
  rw [← PowerSeries.coe_toNat_order hg0, ← PowerSeries.coe_toNat_order hf] at horder
  have horder' : (n * g.order.toNat : ENat) = (f.order.toNat : ENat) := by
    simpa [nsmul_eq_mul] using horder
  exact_mod_cast horder'

private theorem unit_nth_root_unique
    (k : Type u) [Field k] [CharZero k] (n : Nat) (hn : 0 < n)
    (u v w : PowerSeries k) (a : k) (ha : a ≠ 0)
    (hv : v ^ n = u) (hw : w ^ n = u)
    (hvc : PowerSeries.constantCoeff v = a)
    (hwc : PowerSeries.constantCoeff w = a) : v = w := by
  let p : Polynomial (PowerSeries k) := Polynomial.X ^ n - Polynomial.C u
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := p) ?_ ?_ ?_ ?_
  · simp [p, hv]
  · simp [p, hw]
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [hvc, hwc]
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [p, Polynomial.derivative_X_pow, hvc, ha,
      Nat.cast_ne_zero.mpr hn.ne']

private theorem exists_prescribed_root
    (k : Type u) [Field k] [CharZero k] (n : Nat) (hn : 0 < n)
    (f : PowerSeries k) (hf : f ≠ 0) (hdiv : n ∣ f.order.toNat)
    (a : k) (ha : a ^ n = PowerSeries.coeff f.order.toNat f) :
    Exists fun g : PowerSeries k =>
      g ^ n = f /\ PowerSeries.coeff (f.order.toNat / n) g = a := by
  let d := f.order.toNat / n
  let u := f.divXPowOrder
  have hu : IsUnit u := PowerSeries.isUnit_divided_by_X_pow_order hf
  have huca : PowerSeries.constantCoeff u = a ^ n := by
    rw [PowerSeries.constantCoeff_divXPowOrder, ← ha]
  obtain ⟨v, hv, hvc⟩ := unit_nth_root_with_constant k n hn u hu a huca
  have hd : n * d = f.order.toNat := Nat.mul_div_cancel' hdiv
  let g : PowerSeries k := PowerSeries.X ^ d * v
  have hg : g ^ n = f := by
    calc
      g ^ n = PowerSeries.X ^ (d * n) * v ^ n := by
        simp [g, mul_pow, ← pow_mul]
      _ = PowerSeries.X ^ f.order.toNat * u := by rw [hv, Nat.mul_comm, hd]
      _ = f := PowerSeries.X_pow_order_mul_divXPowOrder
  have hgc : PowerSeries.coeff d g = a := by
    dsimp only [g]
    rw [PowerSeries.coeff_X_pow_mul']
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hvc
  exact ⟨g, hg, by simpa [d] using hgc⟩

/-- A formal power series over a characteristic-zero field has an `n`th root
exactly when its order and leading coefficient have the stated `n`th-root data. -/
theorem formal_power_root_criterion
    (k : Type u) [Field k] [CharZero k] (n : Nat) (hn : 0 < n)
    (f : PowerSeries k) :
    (Exists fun g : PowerSeries k => g ^ n = f) ↔
      f = 0 ∨ (n ∣ f.order.toNat ∧
        Exists fun a : k => a ^ n = PowerSeries.coeff f.order.toNat f) := by
  constructor
  · rintro ⟨g, hg⟩
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    have horder : n * g.order.toNat = f.order.toNat :=
      order_toNat_of_pow_eq k n hn f g hf hg
    refine ⟨⟨g.order.toNat, horder.symm⟩, g.divXPowOrder.constantCoeff, ?_⟩
    calc
      g.divXPowOrder.constantCoeff ^ n = (g.divXPowOrder ^ n).constantCoeff := by
        simp
      _ = (f.divXPowOrder).constantCoeff := by
        rw [← PowerSeries.divXPowOrder_pow, hg]
      _ = PowerSeries.coeff f.order.toNat f :=
        PowerSeries.constantCoeff_divXPowOrder
  · intro h
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf, hn.ne']⟩
    rcases h with hzero | ⟨hdiv, a, ha⟩
    · exact False.elim (hf hzero)
    · obtain ⟨g, hg, _⟩ := exists_prescribed_root k n hn f hf hdiv a ha
      exact ⟨g, hg⟩

/-- Specifying the root of the leading coefficient specifies a unique formal
branch of an `n`th root. -/
theorem prescribed_formal_root
    (k : Type u) [Field k] [CharZero k] (n : Nat) (hn : 0 < n)
    (f : PowerSeries k) (hf : f ≠ 0) (hdiv : n ∣ f.order.toNat)
    (a : k) (ha : a ^ n = PowerSeries.coeff f.order.toNat f) :
    ExistsUnique fun g : PowerSeries k =>
      g ^ n = f /\ PowerSeries.coeff (f.order.toNat / n) g = a := by
  obtain ⟨g, hg, hgc⟩ := exists_prescribed_root k n hn f hf hdiv a ha
  refine ⟨g, ⟨hg, hgc⟩, ?_⟩
  intro w hw
  rcases hw with ⟨hw, hwc⟩
  let d := f.order.toNat / n
  let u := f.divXPowOrder
  have ha0 : a ≠ 0 := by
    intro ha0
    have hlead := PowerSeries.coeff_order hf
    rw [← ha, ha0, zero_pow hn.ne'] at hlead
    exact hlead rfl
  have hd : n * d = f.order.toNat := Nat.mul_div_cancel' hdiv
  have horderg : n * g.order.toNat = f.order.toNat :=
    order_toNat_of_pow_eq k n hn f g hf hg
  have hgd : g.order.toNat = d := by
    apply Nat.mul_left_cancel hn
    rw [horderg, hd]
  have horder : n * w.order.toNat = f.order.toNat :=
    order_toNat_of_pow_eq k n hn f w hf hw
  have hwd : w.order.toNat = d := by
    apply Nat.mul_left_cancel hn
    rw [horder, hd]
  have hgu : g.divXPowOrder ^ n = u := by
    rw [← PowerSeries.divXPowOrder_pow, hg]
  have hwu : w.divXPowOrder ^ n = u := by
    rw [← PowerSeries.divXPowOrder_pow, hw]
  have hguc : PowerSeries.constantCoeff g.divXPowOrder = a := by
    rw [PowerSeries.constantCoeff_divXPowOrder, hgd]
    simpa [d] using hgc
  have hwuc : PowerSeries.constantCoeff w.divXPowOrder = a := by
    rw [PowerSeries.constantCoeff_divXPowOrder, hwd]
    simpa [d] using hwc
  have hgw : g.divXPowOrder = w.divXPowOrder :=
    unit_nth_root_unique k n hn u g.divXPowOrder w.divXPowOrder a ha0 hgu hwu hguc hwuc
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := g), hgd,
    ← PowerSeries.X_pow_order_mul_divXPowOrder (f := w), hwd, hgw]

end ArithmeticThetaRamifiedMapR0094
