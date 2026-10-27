import OriginInitialDefinitionsR0161

/-! Transport of the accepted rational initial term along Q ↦ t^r.
The outer variable is unchanged throughout. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
namespace RamifiedInitialTransport

variable (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)

def powerMap : PowerSeries ℚ →+* PowerSeries k :=
  (PowerSeries.expand r (Nat.ne_of_gt hr)).toRingHom.comp
    (PowerSeries.map (algebraMap ℚ k))

lemma powerMap_apply (f : PowerSeries ℚ) : powerMap k r hr f =
    PowerSeries.subst (PowerSeries.X^r) (PowerSeries.map (algebraMap ℚ k) f) := by
  exact PowerSeries.expand_apply r (Nat.ne_of_gt hr) _

lemma powerMap_injective : Function.Injective (powerMap k r hr) := by
  intro f g h
  apply PowerSeries.ext
  intro n
  have hn := congrArg (PowerSeries.coeff (r * n)) h
  simp only [powerMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, PowerSeries.coeff_expand_mul, PowerSeries.coeff_map] at hn
  exact (algebraMap ℚ k).injective hn

def powerToLaurent : PowerSeries ℚ →+* LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k).comp (powerMap k r hr)

lemma powerToLaurent_injective : Function.Injective (powerToLaurent k r hr) := by
  intro f g h
  apply powerMap_injective k r hr
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  exact h

def coefficientMap : LaurentSeries ℚ →+* LaurentSeries k :=
  IsFractionRing.lift (g := powerToLaurent k r hr) (powerToLaurent_injective k r hr)

lemma coefficientMap_power (f : PowerSeries ℚ) :
    coefficientMap k r hr (HahnSeries.ofPowerSeries ℤ ℚ f) =
      HahnSeries.ofPowerSeries ℤ k (powerMap k r hr f) := by
  exact IsFractionRing.lift_algebraMap (g := powerToLaurent k r hr)
    (powerToLaurent_injective k r hr) f

def seriesMap {K L : Type} [Field K] [Field L] (φ : K →+* L) :
    LaurentSeries K →+* LaurentSeries L where
  toFun f := f.map φ
  map_zero' := HahnSeries.map_zero φ.toZeroHom
  map_one' := HahnSeries.map_one φ.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add φ.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul φ.toNonUnitalRingHom

lemma seriesMap_coeff {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (f : LaurentSeries K) (i : ℤ) : (seriesMap φ f).coeff i = φ (f.coeff i) := rfl

lemma seriesMap_power {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (f : PowerSeries K) :
    seriesMap φ (HahnSeries.ofPowerSeries ℤ K f) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map φ f) := by
  ext i
  change φ ((f : LaurentSeries K).coeff i) =
    ((PowerSeries.map φ f : PowerSeries L) : LaurentSeries L).coeff i
  simp only [PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

lemma seriesMap_C {K L : Type} [Field K] [Field L] (φ : K →+* L) (a : K) :
    seriesMap φ (HahnSeries.C a) = HahnSeries.C (φ a) :=
  HahnSeries.map_single φ.toZeroHom

lemma seriesMap_order {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (f : LaurentSeries K) : (seriesMap φ f).order = f.order := by
  by_cases hf : f = 0
  · simp [hf]
  have hm : seriesMap φ f ≠ 0 := by simpa using (seriesMap φ).injective.ne hf
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [seriesMap_coeff]
    simpa only [map_zero, HahnSeries.leadingCoeff_eq] using
      φ.injective.ne (HahnSeries.leadingCoeff_ne_zero.mpr hf)
  · apply (HahnSeries.le_order_iff_forall hm).mpr
    intro i hi
    rw [seriesMap_coeff, HahnSeries.coeff_eq_zero_of_lt_order hi, map_zero]

lemma coefficientMap_q : coefficientMap k r hr ArithmeticThetaDiscriminant.q =
    ArithmeticThetaLaurentNormR0064.t k ^ r := by
  rw [ArithmeticThetaDiscriminant.q, ArithmeticThetaDiscriminant.qEmbed,
    coefficientMap_power]
  simp [powerMap, ArithmeticThetaLaurentNormR0064.t, HahnSeries.ofPowerSeries_X]

lemma discriminant_eq : ArithmeticThetaUnaryKatoPowerR0160.discriminant k r =
    coefficientMap k r hr
      (ArithmeticThetaDiscriminant.q ^ 2 * ArithmeticThetaDiscriminant.p ^ 48) := by
  unfold ArithmeticThetaDiscriminant.q ArithmeticThetaDiscriminant.p
    ArithmeticThetaDiscriminant.qEmbed
  rw [← map_pow, ← map_pow, ← map_mul, coefficientMap_power]
  rw [powerMap_apply]
  rfl

lemma gamma_eq (c : ℕ) : gammaTaylor k r c =
    seriesMap (coefficientMap k r hr)
      (ArithmeticThetaDiscriminant.tEmbed (ArithmeticThetaDiscriminant.gamma c)) := by
  rw [ArithmeticThetaDiscriminant.tEmbed, RingHom.comp_apply, seriesMap_power]
  apply congrArg (HahnSeries.ofPowerSeries ℤ (LaurentSeries k))
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map]
  rw [ArithmeticThetaDiscriminant.qEmbed, coefficientMap_power]
  rw [powerMap_apply]

lemma f5_eq : f5Taylor k r =
    seriesMap (coefficientMap k r hr) ArithmeticThetaDiscriminant.f5 := by
  have hz : seriesMap (coefficientMap k r hr) ArithmeticThetaDiscriminant.tZ =
      HahnSeries.ofPowerSeries ℤ (LaurentSeries k) (1 + PowerSeries.X) := by
    rw [ArithmeticThetaDiscriminant.tZ, seriesMap_power]
    simp only [map_add, map_one, PowerSeries.map_X]
  simp only [f5Taylor, ArithmeticThetaDiscriminant.f5, map_div₀, map_mul, map_inv₀,
    map_pow, map_neg, hz]
  have hs : seriesMap (coefficientMap k r hr)
      (HahnSeries.single 0 (ArithmeticThetaDiscriminant.q^2)) =
      HahnSeries.C (coefficientMap k r hr (ArithmeticThetaDiscriminant.q^2)) :=
    seriesMap_C _ _
  rw [hs]
  rw [map_pow, coefficientMap_q, ← gamma_eq, ← gamma_eq]
  simp only [map_pow]

end RamifiedInitialTransport

theorem ramified_initial_transport :
    ∀ (k : Type) [Field k] [CharZero k] (r : ℕ), 0 < r →
      (f5Taylor k r).order = 24 ∧
      (f5Taylor k r).coeff 24 = (1/5 : LaurentSeries k) *
        ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ∧
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ≠ 0 := by
  intro k _ _ r hr
  rw [RamifiedInitialTransport.f5_eq k r hr]
  refine ⟨?_, ?_, ?_⟩
  · rw [RamifiedInitialTransport.seriesMap_order, ArithmeticThetaDiscriminant.f5_order]
  · rw [RamifiedInitialTransport.seriesMap_coeff, ArithmeticThetaDiscriminant.f5_coefficient,
      RamifiedInitialTransport.discriminant_eq k r hr]
    simp only [map_mul, map_div₀, map_one, map_ofNat]
    ring
  · rw [RamifiedInitialTransport.discriminant_eq k r hr]
    simpa only [map_zero] using (RamifiedInitialTransport.coefficientMap k r hr).injective.ne
      (mul_ne_zero (pow_ne_zero _ ArithmeticThetaDiscriminant.q_ne_zero)
        (pow_ne_zero _ ArithmeticThetaDiscriminant.p_ne_zero))

end ArithmeticThetaOriginInitialR0161

#print axioms ArithmeticThetaOriginInitialR0161.ramified_initial_transport
