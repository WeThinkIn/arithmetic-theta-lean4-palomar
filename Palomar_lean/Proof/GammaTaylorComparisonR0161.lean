module

public import FaithfulTaylorFieldR0161
public import DiscriminantInitial
public import LocalGammaProviderBridgeR0065
public import OriginInitialDefinitionsR0161
public import CompletedChartFieldMapsR0152
public import Mathlib.RingTheory.PowerSeries.Expand

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
namespace GammaTaylorComparisonR0161
open ArithmeticThetaAnnularTorsionPrereqR0053 hiding Chart
open ArithmeticThetaDiscriminant hiding swap

private def swap (R : Type) [CommRing R] : PowerSeries (PowerSeries R) →+* PowerSeries (PowerSeries R) where
  toFun F := PowerSeries.mk (fun i => PowerSeries.mk (fun j =>
    PowerSeries.coeff i (PowerSeries.coeff j F)))
  map_zero' := by ext i j; simp
  map_one' := by
    ext i j
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs <;> simp_all
  map_add' F G := by ext i j; simp
  map_mul' F G := by
    ext i j
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum]
    exact Finset.sum_comm

private lemma swap_coeff {R : Type} [CommRing R] (F : PowerSeries (PowerSeries R)) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (swap R F)) =
      PowerSeries.coeff i (PowerSeries.coeff j F) := by simp [swap]
private lemma swap_swap {R : Type} [CommRing R] (F : PowerSeries (PowerSeries R)) :
    swap R (swap R F) = F := by ext i j; simp only [swap_coeff]
private lemma swap_C {R : Type} [CommRing R] (F : PowerSeries R) :
    swap R (PowerSeries.C F) = PowerSeries.map PowerSeries.C F := by
  ext i j
  simp only [swap_coeff, PowerSeries.coeff_C, PowerSeries.coeff_map]
  split_ifs <;> simp_all
private lemma swap_X {R : Type} [CommRing R] :
    swap R PowerSeries.X = PowerSeries.C PowerSeries.X := by
  ext i j
  simp only [swap_coeff, PowerSeries.coeff_X, PowerSeries.coeff_C]
  split_ifs <;> simp_all [PowerSeries.coeff_X]

private def finiteGamma {R : Type} [CommRing R] (a b : R) (N : ℕ) : PowerSeries R :=
  (∏ l ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ l)) * partialEuler b N

private lemma finiteGamma_succ {R : Type} [CommRing R] (a b : R) (N : ℕ) :
    finiteGamma a b (N+1) =
      PowerSeries.C (1-a) * partialEuler a N * partialEuler b N *
        (1 - PowerSeries.C b * PowerSeries.X ^ (N+1)) := by
  rw [finiteGamma, Finset.prod_range_succ', partialEuler, Finset.prod_range_succ]
  simp only [pow_zero, mul_one, map_sub, map_one]
  simp only [partialEuler]
  ring

private lemma coeff_mul_congr {R : Type} [CommRing R] (f f' g g' : PowerSeries R)
    (d : ℕ) (hf : ∀ i, i ≤ d → PowerSeries.coeff i f = PowerSeries.coeff i f')
    (hg : ∀ i, i ≤ d → PowerSeries.coeff i g = PowerSeries.coeff i g') :
    PowerSeries.coeff d (f*g) = PowerSeries.coeff d (f'*g') := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]

/-- Stabilization of the entire product, including its horizontal factor. -/
private lemma finiteGamma_stable {R : Type} [CommRing R] (a b : R)
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d (finiteGamma a b N) =
      PowerSeries.coeff d (PowerSeries.C (1-a) * euler a * euler b) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [finiteGamma_succ]
  simp only [mul_sub, mul_one, ← mul_assoc, map_sub,
    PowerSeries.coeff_mul_X_pow', show ¬ M+1 ≤ d by omega, if_false, sub_zero]
  apply coeff_mul_congr
  · intro i hi
    rw [← map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, partial_stable R a i M (by omega)]
  · intro i hi
    exact partial_stable R b i M (by omega)

variable (k : Type) [Field k] [CharZero k]
private def zi : PowerSeries k := PowerSeries.invOfUnit (1 + PowerSeries.X) 1
omit [CharZero k] in
private lemma zi_mul : (1 + PowerSeries.X) * zi k = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)
private lemma map_zi : PowerSeries.map (algebraMap ℚ k) (zUnit⁻¹ : (PowerSeries ℚ)ˣ) = zi k := by
  apply mul_left_cancel₀ (show (1 + PowerSeries.X : PowerSeries k) ≠ 0 by
    intro h; have := congrArg PowerSeries.constantCoeff h; simp at this)
  rw [zi_mul]
  have h := congrArg (PowerSeries.map (algebraMap ℚ k)) (show (zUnit : PowerSeries ℚ) * ((zUnit⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) = 1 from zUnit.val_inv)
  simpa only [map_mul, map_one, show (zUnit : PowerSeries ℚ) = 1 + PowerSeries.X from rfl,
    map_add, PowerSeries.map_X] using h
private lemma swap_zi : swap k (zInverse k) = PowerSeries.C (zi k) := by
  have hz : (1 + PowerSeries.X) * zInverse k = 1 := PowerSeries.mul_invOfUnit _ _ (by simp)
  have ha := congrArg (swap k) hz
  rw [map_mul, map_add, map_one, swap_X] at ha
  have hb : (1 + PowerSeries.C PowerSeries.X) * PowerSeries.C (zi k) = 1 := by
    simpa only [map_mul, map_add, map_one, map_one] using
      congrArg (PowerSeries.C : PowerSeries k →+* Bivariate k) (zi_mul k)
  calc
    swap k (zInverse k) = swap k (zInverse k) *
        ((1 + PowerSeries.C PowerSeries.X) * PowerSeries.C (zi k)) := by rw [hb, mul_one]
    _ = PowerSeries.C (zi k) := by rw [← mul_assoc, mul_comm _ (1 + PowerSeries.C PowerSeries.X), ha, one_mul]

private def expandHom {R : Type} [CommRing R] (r : ℕ) (hr : 0 < r) :
    PowerSeries R →+* PowerSeries R where
  toFun := PowerSeries.expand r (by omega)
  map_zero' := map_zero (PowerSeries.expand r (by omega))
  map_one' := map_one (PowerSeries.expand r (by omega))
  map_add' := map_add (PowerSeries.expand r (by omega))
  map_mul' := map_mul (PowerSeries.expand r (by omega))

private lemma expandHom_apply {R : Type} [CommRing R] (r : ℕ) (hr : 0 < r) (f : PowerSeries R) :
    expandHom r hr f = PowerSeries.subst (PowerSeries.X ^ r) f :=
  PowerSeries.expand_apply r (by omega) f

private def ramify (r : ℕ) (hr : 0 < r) :
    PowerSeries (PowerSeries ℚ) →+* Bivariate k :=
  (expandHom r hr).comp
    (PowerSeries.map (PowerSeries.map (algebraMap ℚ k)))

private def target (r c : ℕ) (hr : 0 < r) : Bivariate k :=
  ramify k r hr (gammaQ (zUnit ^ c))

private lemma target_iterated (r c : ℕ) (hr : 0 < r) :
    toIterated k (swap k (target k r c hr)) = gammaTaylor k r c := by
  apply congrArg (HahnSeries.ofPowerSeries ℤ (LaurentSeries k))
  apply PowerSeries.ext
  intro i
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  apply congrArg (HahnSeries.ofPowerSeries ℤ k)
  apply PowerSeries.ext
  intro j
  simp only [swap_coeff, target, ramify, RingHom.comp_apply, expandHom_apply,
    PowerSeries.coeff_map,
    PowerSeries.coeff_subst_X_pow (by omega : r ≠ 0), gamma,
    ArithmeticThetaDiscriminant.swap_coeff]
  split_ifs <;> simp

private lemma target_stable (r c d N : ℕ) (hr : 0 < r) (h : d < N) :
    PowerSeries.coeff d (ramify k r hr
      (finiteGamma ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ)
        (((zUnit ^ c)⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) N)) =
      PowerSeries.coeff d (target k r c hr) := by
  simp only [ramify, target, RingHom.comp_apply, expandHom_apply,
    PowerSeries.coeff_subst_X_pow (by omega : r ≠ 0)]
  split_ifs
  · simp only [PowerSeries.coeff_map]
    exact congrArg (PowerSeries.map (algebraMap ℚ k))
      (finiteGamma_stable (R := PowerSeries ℚ) _ _ _ _ (lt_of_le_of_lt (Nat.div_le_self d r) h))
  · rfl

private def chartPartial (r c N : ℕ) : Chart k :=
  ∏ l ∈ Finset.range N,
    (1 - tau k ^ (r*l) * cx k ^ c) *
      (1 - tau k ^ (r*(l+1)-c) * cy k ^ c)

omit [CharZero k] in
private lemma tau_base : tau k = base k PowerSeries.X := rfl

private lemma chartPartial_image (r c N : ℕ) (hr : 0 < r) (hc : c ≤ r)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    swap k (σ (chartPartial k r c N)) = ramify k r hr
      (finiteGamma ((zUnit ^ c : (PowerSeries ℚ)ˣ) : PowerSeries ℚ)
        (((zUnit ^ c)⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) N) := by
  have ht : swap k (σ (tau k)) = PowerSeries.X := by
    rw [tau_base, hσ.1, swap_C, PowerSeries.map_X]
  have hx : swap k (σ (cx k)) = PowerSeries.C (1 + PowerSeries.X) := by
    rw [hσ.2.1, map_add, map_one, swap_X, map_add, map_one]
  have hy : swap k (σ (cy k)) = PowerSeries.X * PowerSeries.C (zi k) := by
    rw [hσ.2.2.1, map_mul, swap_C, PowerSeries.map_X, swap_zi]
  have hC (a : PowerSeries ℚ) : ramify k r hr (PowerSeries.C a) =
      PowerSeries.C (PowerSeries.map (algebraMap ℚ k) a) := by
    change PowerSeries.expand r (by omega : r ≠ 0) (PowerSeries.map _ (PowerSeries.C a)) = _
    rw [PowerSeries.map_C, PowerSeries.expand_C]
  have hX : ramify k r hr PowerSeries.X = PowerSeries.X ^ r := by
    change PowerSeries.expand r (by omega : r ≠ 0) (PowerSeries.map _ PowerSeries.X) = _
    rw [PowerSeries.map_X, PowerSeries.expand_X]
  simp only [chartPartial, finiteGamma, partialEuler, map_prod, map_mul, map_sub,
    map_one, map_pow, ht, hx, hy, hC, hX, Units.val_pow_eq_pow_val,
    ← inv_pow, map_zi, show (zUnit : PowerSeries ℚ) = 1 + PowerSeries.X from rfl,
    map_add, PowerSeries.map_X]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  have hle : c ≤ r * (l+1) := hc.trans (Nat.le_mul_of_pos_right r (by omega))
  have hpow : (PowerSeries.X : Bivariate k) ^ (r*(l+1)-c) *
      (PowerSeries.X * PowerSeries.C (zi k)) ^ c =
      PowerSeries.C (zi k) ^ c * (PowerSeries.X ^ r) ^ (l+1) := by
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle, pow_mul]
    ring
  rw [hpow]
  simp only [pow_mul]
  ring

omit [CharZero k] in
private lemma tpower_nat (n : ℕ) : tpower k (n : ℤ) = toGeneric k (tau k) ^ n := by
  simp only [tpower, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [show (parameterUnit k : GenericChart k) = toGeneric k (tau k) from
    (IsLocalization.Away.algebraMap_isUnit (tau k)).unit_spec]

private lemma exponent_nonneg (r c l : ℕ) (hc : c ≤ r) :
    0 ≤ rightExponent r c 0 l := by
  have h := hc.trans (Nat.le_mul_of_pos_right r (by omega : 0 < l+1))
  have hz : (c : ℤ) ≤ (r : ℤ) * (l+1) := by exact_mod_cast h
  simp only [rightExponent, Nat.cast_zero, zero_add, mul_one]
  omega

private lemma literal_chart (r c N : ℕ) (hc : c ≤ r) :
    literalPartial k r c 0 N = toGeneric k (chartPartial k r c N) := by
  simp only [literalPartial, chartPartial, map_prod, map_mul, map_sub, map_one, map_pow]
  apply Finset.prod_congr rfl
  intro l hl
  have hle := hc.trans (Nat.le_mul_of_pos_right r (by omega : 0 < l+1))
  have he : rightExponent r c 0 l = ((r*(l+1)-c : ℕ) : ℤ) := by
    simp only [rightExponent, Nat.cast_zero, zero_add, mul_one, Nat.cast_sub hle,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [he, tpower_nat]
  simp only [leftExponent, mul_zero, add_zero, tpower_nat]

omit [CharZero k] in
private lemma clearing_one (r c N : ℕ) (hc : c ≤ r) : clearingPartial k r c 0 N = 1 := by
  simp [clearingPartial, not_lt.mpr (exponent_nonneg r c _ hc)]

omit [CharZero k] in
private lemma full_chart (r N : ℕ) :
    ArithmeticThetaCorrectedGammaR0061.fullPartial k r 0 N = chartPartial k r 1 N := by
  simp only [ArithmeticThetaCorrectedGammaR0061.fullPartial,
    ArithmeticThetaCorrectedGammaR0061.leftPartial,
    ArithmeticThetaCorrectedGammaR0061.rightPartial,
    ArithmeticThetaCorrectedGammaR0061.leftFactor,
    ArithmeticThetaCorrectedGammaR0061.rightFactor,
    ArithmeticThetaCorrectedGammaR0061.leftExponent,
    ArithmeticThetaCorrectedGammaR0061.rightExponent, chartPartial,
    pow_one, add_zero, Nat.sub_zero, Finset.prod_mul_distrib]
  rfl

/-- Continuity at every outer coefficient determines the whole Taylor image. -/
private lemma compare_limit (r c : ℕ) (hr : 0 < r) (hc : c ≤ r)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) (g : Chart k)
    (hg : ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      g - chartPartial k r c N ∈ filtration k n) :
    σ g = swap k (target k r c hr) := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  obtain ⟨N₀, hN₀⟩ := hg (j+1)
  let N := max N₀ (j+1)
  have hmem := hσ.2.2.2 (j+1) _ (hN₀ N (Nat.le_max_left _ _)) i
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have hz := PowerSeries.X_pow_dvd_iff.mp hmem j (Nat.lt_succ_self j)
  have heq : PowerSeries.coeff j (PowerSeries.coeff i (σ g)) =
      PowerSeries.coeff j (PowerSeries.coeff i (σ (chartPartial k r c N))) := by
    simpa only [map_sub, sub_eq_zero] using hz
  rw [heq, swap_coeff]
  have hf := congrArg (fun F : Bivariate k => PowerSeries.coeff i (PowerSeries.coeff j F))
    (chartPartial_image k r c N hr hc σ hσ)
  rw [swap_coeff] at hf
  rw [hf, target_stable k r c j N hr (by dsimp [N]; omega)]

private lemma gamma_image (r : ℕ) (hr : 0 < r)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.gammaLocal k r 0 hr hr)) = gammaTaylor k r 1 := by
  rw [ArithmeticThetaGenericOverlapR0065.local_gamma_provider_bridge]
  have hg := (Classical.choose_spec (Classical.choose_spec
    (ArithmeticThetaCorrectedGammaR0061.gamma_data_exists k r 0 hr hr))).2.2.1
  have hlim : ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ArithmeticThetaGenericOverlapR0065.correctedGamma k r 0 hr hr -
        chartPartial k r 1 N ∈ filtration k n := by
    simpa only [ArithmeticThetaCorrectedGammaR0061.Converges, full_chart,
      ArithmeticThetaGenericOverlapR0065.correctedGamma] using hg
  have hh := compare_limit k r 1 hr (by omega) σ hσ _ hlim
  change Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k
    (ArithmeticThetaGenericOverlapR0065.correctedGamma k r 0 hr hr)) = _
  have hE (a : Chart k) : Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k a) =
      toIterated k (σ a) := RingHom.congr_fun hΨ a
  rw [hE, hh, target_iterated]

private lemma powered_image (r c : ℕ) (hr : 0 < r) (hc : 1 < c)
    (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.poweredLocal k r c 0 ζ hr hc hdiv hcop hζ hr)) =
      gammaTaylor k r c := by
  let γ := ArithmeticThetaLocalNormR0054.poweredLocal k r c 0 ζ hr hc hdiv hcop hζ hr
  have hcr : c ≤ r := Nat.le_of_dvd hr hdiv
  have happ := (Classical.choose_spec
    (powered_gamma_local_divisor k r c 0 ζ hr hc hdiv hcop hζ hr)).1.1
  obtain ⟨f, hf, hdiff⟩ := happ 0 (cutoff c 0 0) le_rfl
  have hγ : γ = toGeneric k (chartPartial k r c (cutoff c 0 0) + f) := by
    change γ - literalPartial k r c 0 (cutoff c 0 0) = _ at hdiff
    rw [clearing_one k r c _ hcr, one_mul, literal_chart k r c _ hcr] at hdiff
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp hdiff).trans (add_comm _ _)
  let g := chartPartial k r c (cutoff c 0 0) + f
  have hinj : Function.Injective (toGeneric k) := by
    intro a b hab
    apply ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps.chartToField_injective k
    exact congrArg (ArithmeticThetaLocalOrdersR0066.toFunctionField k) hab
  have hlim : ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      g - chartPartial k r c N ∈ filtration k n := by
    intro n
    refine ⟨cutoff c 0 n, ?_⟩
    intro N hN
    obtain ⟨a, ha, hea⟩ := happ n N hN
    change γ - literalPartial k r c 0 N = _ at hea
    rw [hγ, clearing_one k r c _ hcr, one_mul, literal_chart k r c _ hcr, ← map_sub] at hea
    exact hinj hea ▸ ha
  have hh := compare_limit k r c hr hcr σ hσ g hlim
  change Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k γ) = _
  rw [hγ]
  change Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k g) = _
  have hE (a : Chart k) : Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k a) =
      toIterated k (σ a) := RingHom.congr_fun hΨ a
  rw [hE, hh, target_iterated]

end GammaTaylorComparisonR0161
/-- The actual completed gamma factors agree with the full rational bivariate
product after coefficient extension and positive period ramification. -/
theorem gamma_taylor_comparison :
    ∀ (k : Type) [Field k] [CharZero k] (r c : ℕ) (hr : 0 < r) (hc : 1 < c)
      (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
      (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
      (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ),
      Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k
        (ArithmeticThetaLocalNormR0054.gammaLocal k r 0 hr hr)) = gammaTaylor k r 1 ∧
      Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k
        (ArithmeticThetaLocalNormR0054.poweredLocal k r c 0 ζ hr hc hdiv hcop hζ hr)) =
        gammaTaylor k r c := by
  intro k _ _ r c hr hc hdiv hcop ζ hζ σ hσ Ψ hΨ
  exact ⟨GammaTaylorComparisonR0161.gamma_image k r hr σ hσ Ψ hΨ,
    GammaTaylorComparisonR0161.powered_image k r c hr hc hdiv hcop ζ hζ σ hσ Ψ hΨ⟩
end ArithmeticThetaOriginInitialR0161

#print axioms ArithmeticThetaOriginInitialR0161.gamma_taylor_comparison
