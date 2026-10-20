module

public import AnnularNormBridgeDefinitionsR0156

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156
namespace RamifiedLiteralQuotientR0156
open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaRamifiedPeriodR0154
open ArithmeticThetaLocalNormR0054 (gammaLocal gammaUnit gammaHorizontal poweredLocal localZ)
variable (k : Type) [Field k] [CharZero k]

private lemma tau_map (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    ρ (tau k) = tau k ^ d := by
  have h := hρ.1 PowerSeries.X
  simpa only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    PowerSeries.expand_X, map_pow, base, tau, ArithmeticThetaScaledAnnularR0050.tau] using h

private lemma filtration_eq (n : ℕ) :
    filtration k n = (Ideal.span {tau k}) ^ n := by
  congr 2
  simp [filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
    tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter]

private lemma filtered (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)
    (n : ℕ) (a : Chart k) (ha : a ∈ filtration k n) :
    ρ a ∈ filtration k n := by
  rw [filtration_eq] at ha ⊢
  have hle : (Ideal.span {tau k}).map ρ ≤ Ideal.span {tau k} := by
    rw [Ideal.map_span, Set.image_singleton, tau_map k d hd q ρ hρ]
    apply Ideal.span_le.mpr
    rintro a (rfl : a = tau k ^ d)
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self _ (Nat.ne_of_gt hd))
  have h := Ideal.mem_map_of_mem ρ ha
  rw [Ideal.map_pow] at h
  exact (pow_le_pow_left' hle n) h

private lemma chart_domain (k : Type) [Field k] [CharZero k] :
    IsDomain (Chart k) :=
  (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1

private lemma chart_tau_ne_zero (k : Type) [Field k] [CharZero k] :
    tau k ≠ 0 := by
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

private lemma generic_domain (k : Type) [Field k] [CharZero k] :
    IsDomain (GenericChart k) := by
  letI : IsDomain (Chart k) := chart_domain k
  exact IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))

private lemma generic_injective (k : Type) [Field k] [CharZero k] :
    Function.Injective (toGeneric k) := by
  letI : IsDomain (Chart k) := chart_domain k
  exact IsLocalization.injective (GenericChart k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))


private lemma generic_filtration_separated (k : Type) [Field k] [CharZero k]
    (z : GenericChart k) (hz : ∀ n : ℕ, ∃ f : Chart k,
      f ∈ filtration k n ∧ z = toGeneric k f) : z = 0 := by
  letI : IsAdicComplete
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k)).mpr inferInstance
  letI : IsHausdorff
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := hcomp.1
  have hpow (n : ℕ) : filtration k n =
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) ^ n := by
    simp [filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
  obtain ⟨a, _, ha⟩ := hz 0
  have hamem (n : ℕ) : a ∈ filtration k n := by
    obtain ⟨f, hf, hz_eq⟩ := hz n
    have heq : a = f := generic_injective k (ha.symm.trans hz_eq)
    exact heq ▸ hf
  have ha0 : a = 0 := by
    apply (IsHausdorff.eq_iff_smodEq
      (I := (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (M := Chart k)).mpr
    intro n
    rw [SModEq.sub_mem]
    simpa [hpow, smul_eq_mul, Ideal.mul_top] using hamem n
  simpa [ha0] using ha


private lemma chart_separated (a : Chart k)
    (ha : ∀ n, a ∈ filtration k n) : a = 0 := by
  apply generic_injective k
  rw [map_zero]
  exact generic_filtration_separated k (toGeneric k a) (fun n => ⟨a, ha n, rfl⟩)

private lemma bounded_unique (a b C D : GenericChart k)
    (h : ∀ n, ∃ f g : Chart k,
      f ∈ filtration k n ∧ g ∈ filtration k n ∧
      a - b = C * toGeneric k f - D * toGeneric k g) : a = b := by
  obtain ⟨A, B, s, ha, hb⟩ :=
    IsLocalization.surj₂ (Submonoid.powers (tau k)) (GenericChart k) C D
  obtain ⟨m, hm⟩ := s.property
  have hA : toGeneric k (tau k) ^ m * C = toGeneric k A := by
    simpa only [← hm, map_pow, mul_comm, toGeneric] using ha
  have hB : toGeneric k (tau k) ^ m * D = toGeneric k B := by
    simpa only [← hm, map_pow, mul_comm, toGeneric] using hb
  have hz : toGeneric k (tau k) ^ m * (a-b) = 0 := by
    apply generic_filtration_separated k
    intro n
    obtain ⟨f,g,hf,hg,he⟩ := h n
    refine ⟨A*f-B*g, (filtration k n).sub_mem
      ((filtration k n).mul_mem_left A hf) ((filtration k n).mul_mem_left B hg), ?_⟩
    rw [he, mul_sub, ← mul_assoc, hA, ← mul_assoc, hB]
    simp only [map_sub, map_mul]
  have hu : IsUnit (toGeneric k (tau k) ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit (tau k)).pow m
  letI : IsDomain (GenericChart k) := generic_domain k
  exact sub_eq_zero.mp (hu.mul_left_cancel (hz.trans (mul_zero _).symm))

private def genericMap (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    GenericChart k →+* GenericChart k :=
  IsLocalization.Away.lift (tau k) (show IsUnit ((toGeneric k).comp ρ (tau k)) by
    simp only [RingHom.comp_apply, tau_map k d hd q ρ hρ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (tau k)).pow d)

private lemma genericMap_chart (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) (a : Chart k) :
    genericMap k d hd q ρ hρ (toGeneric k a) = toGeneric k (ρ a) :=
  IsLocalization.Away.lift_eq _ _ _

private lemma tp_nat (n : ℕ) : tpower k (n : ℤ) = toGeneric k (tau k) ^ n := by
  simp only [tpower, zpow_natCast, Units.val_pow_eq_pow_val]
  congr 1

private lemma tp_map (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) (e : ℤ) :
    genericMap k d hd q ρ hρ (tpower k e) = tpower k ((d : ℤ)*e) := by
  have hu : Units.map (genericMap k d hd q ρ hρ).toMonoidHom (parameterUnit k) =
      parameterUnit k ^ d := by
    apply Units.ext
    change genericMap k d hd q ρ hρ (toGeneric k (tau k)) =
      toGeneric k (tau k) ^ d
    rw [genericMap_chart, tau_map k d hd q ρ hρ, map_pow]
  change (Units.map (genericMap k d hd q ρ hρ).toMonoidHom (parameterUnit k ^ e)).val = _
  rw [map_zpow, hu]
  simp [tpower, ← zpow_natCast, ← zpow_mul]

private lemma gammaPartial_map (r i d : ℕ) (hr : 0 < r) (hi : i < r)
    (hd : 0 < d) (q : Fin d) (ρ : Chart k →+* Chart k)
    (hρ : IsChartRamification k d hd q ρ) (N : ℕ) :
    ρ (ArithmeticThetaScaledAnnularR0050.gammaPartial k 1 r i N) =
      ArithmeticThetaScaledAnnularR0050.gammaPartial k 1 (r*d) (d*i+q.val) N := by
  unfold ArithmeticThetaScaledAnnularR0050.gammaPartial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro l hl
  have hleft : d*(r*l+i)+q.val = (r*d)*l+(d*i+q.val) := by ring
  have hbound : i+1 ≤ r*(l+1) := by nlinarith
  have hright : d*(r*(l+1)-i-1)+(d-q.val-1) =
      (r*d)*(l+1)-(d*i+q.val)-1 := by
    have hsub : r*(l+1)-i-1+i+1 = r*(l+1) := by omega
    have hq : d-q.val-1+q.val+1 = d := by omega
    have hh : d*(r*(l+1)-i-1)+(d-q.val-1)+(d*i+q.val)+1 =
        (r*d)*(l+1) := by nlinarith
    omega
  change ρ ((1-tau k ^ (r*l+i)*cx k)*(1-tau k ^ (r*(l+1)-i-1)*cy k)) =
    (1-tau k ^ ((r*d)*l+(d*i+q.val))*cx k)*
      (1-tau k ^ ((r*d)*(l+1)-(d*i+q.val)-1)*cy k)
  simp only [map_mul, map_sub, map_one, map_pow, tau_map k d hd q ρ hρ,
    hρ.2.1, hρ.2.2, ← mul_assoc, ← pow_mul, ← pow_add, hleft, hright]

private lemma gamma_map (r i d : ℕ) (hr : 0 < r) (hi : i < r)
    (hd : 0 < d) (q : Fin d) (ρ : Chart k →+* Chart k)
    (hρ : IsChartRamification k d hd q ρ)
    (hrd : 0 < r*d) (hj : d*i+q.val < r*d) :
    genericMap k d hd q ρ hρ (gammaLocal k r i hr hi) =
      gammaLocal k (r*d) (d*i+q.val) hrd hj := by
  unfold gammaLocal
  rw [genericMap_chart]
  apply congrArg (toGeneric k)
  apply sub_eq_zero.mp
  apply chart_separated k
  intro n
  obtain ⟨A,hA⟩ := (Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 r i (by omega) (by omega))).1.2.2 n
  obtain ⟨B,hB⟩ := (Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 (r*d) (d*i+q.val)
      (by omega) (by omega))).1.2.2 n
  have ha := filtered k d hd q ρ hρ n _ (hA (max A B) (Nat.le_max_left _ _))
  have hb := hB (max A B) (Nat.le_max_right _ _)
  rw [map_sub, gammaPartial_map k r i d hr hi hd q ρ hρ] at ha
  change gammaHorizontal k (r*d) (d*i+q.val) *
    gammaUnit k (r*d) (d*i+q.val) hrd hj - _ ∈ filtration k n at hb
  change ρ (gammaHorizontal k r i * gammaUnit k r i hr hi) - _ ∈ filtration k n at ha
  convert (filtration k n).sub_mem ha hb using 1 <;> ring

private lemma tp_add (a b : ℤ) : tpower k (a+b) = tpower k a * tpower k b := by
  simp [tpower, zpow_add]

private lemma tp_pow (a : ℤ) (n : ℕ) : tpower k a ^ n = tpower k (a*n) := by
  unfold tpower
  rw [← Units.val_pow_eq_pow_val, zpow_mul, zpow_natCast]

private lemma literalPartial_map (r c i d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) (N : ℕ) :
    genericMap k d hd q ρ hρ (literalPartial k r c i N) =
      literalPartial k (r*d) c (d*i+q.val) N := by
  unfold literalPartial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro l hl
  have hL : (d : ℤ)*(leftExponent r c i l : ℤ)+(q.val : ℤ)*c =
      (leftExponent (r*d) c (d*i+q.val) l : ℤ) := by
    simp only [leftExponent, Nat.cast_add, Nat.cast_mul]; ring
  have hR : (d : ℤ)*rightExponent r c i l+((d-q.val-1 : ℕ) : ℤ)*c =
      rightExponent (r*d) c (d*i+q.val) l := by
    have hq : ((d-q.val-1 : ℕ) : ℤ) = (d : ℤ)-q.val-1 := by omega
    simp only [rightExponent, Nat.cast_add, Nat.cast_mul, hq]; ring
  simp only [map_mul, map_sub, map_one, map_pow, tp_map,
    genericMap_chart, hρ.2.1, hρ.2.2, map_mul, map_pow, mul_pow]
  rw [← tp_nat k q.val, ← tp_nat k (d-q.val-1), tp_pow, tp_pow]
  rw [← mul_assoc, ← tp_add, hL, ← mul_assoc, ← tp_add, hR]

private lemma powered_map (r c i d : ℕ) (hr : 0 < r) (hc : 1 < c)
    (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (hi : i < r) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)
    (hrd : 0 < r*d) (hdiv' : c ∣ r*d) (hj : d*i+q.val < r*d) :
    genericMap k d hd q ρ hρ (poweredLocal k r c i ζ hr hc hdiv hcop hζ hi) =
      poweredLocal k (r*d) c (d*i+q.val) ζ hrd hc hdiv' hcop hζ hj := by
  let G := genericMap k d hd q ρ hρ
  let C := clearingPartial k r c i (cutoff c i 0)
  let D := clearingPartial k (r*d) c (d*i+q.val) (cutoff c (d*i+q.val) 0)
  apply bounded_unique k _ _ (G C) D
  intro n
  let N := max (cutoff c i n) (cutoff c (d*i+q.val) n)
  have hN : cutoff c i n ≤ N := Nat.le_max_left _ _
  have hN' : cutoff c (d*i+q.val) n ≤ N := Nat.le_max_right _ _
  obtain ⟨f,hf,he⟩ := (Classical.choose_spec
    (powered_gamma_local_divisor k r c i ζ hr hc hdiv hcop hζ hi)).1.1 n N hN
  obtain ⟨g,hg,he'⟩ := (Classical.choose_spec
    (powered_gamma_local_divisor k (r*d) c (d*i+q.val) ζ hrd hc hdiv' hcop hζ hj)).1.1 n N hN'
  have hC : clearingPartial k r c i N = C := by
    apply (powered_gamma_clearing k r c i hr hc hdiv hcop hi).2.2
    · dsimp [cutoff] at hN ⊢; omega
    · rfl
  have hD : clearingPartial k (r*d) c (d*i+q.val) N = D := by
    apply (powered_gamma_clearing k (r*d) c (d*i+q.val) hrd hc hdiv' hcop hj).2.2
    · dsimp [cutoff] at hN' ⊢; omega
    · rfl
  rw [hC] at he
  rw [hD] at he'
  have heG := congrArg G he
  simp only [map_sub, map_mul] at heG
  change G (poweredLocal k r c i ζ hr hc hdiv hcop hζ hi) - G (literalPartial k r c i N) =
    G C * G (toGeneric k f) at heG
  rw [literalPartial_map, genericMap_chart] at heG
  change poweredLocal k (r*d) c (d*i+q.val) ζ hrd hc hdiv' hcop hζ hj -
    literalPartial k (r*d) c (d*i+q.val) N = D * toGeneric k g at he'
  refine ⟨ρ f, g, filtered k d hd q ρ hρ n f hf, hg, ?_⟩
  linear_combination heG - he'

private lemma fieldMap_generic (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)
    (E : ChartField k →+* ChartField k) (hE : ExtendsChart k ρ E)
    (a : GenericChart k) :
    E (ArithmeticThetaLocalOrdersR0066.toFunctionField k a) =
      ArithmeticThetaLocalOrdersR0066.toFunctionField k (genericMap k d hd q ρ hρ a) := by
  have he : E.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k) =
      (ArithmeticThetaLocalOrdersR0066.toFunctionField k).comp (genericMap k d hd q ρ hρ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (tau k))
    apply RingHom.ext
    intro b
    change E (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      ArithmeticThetaLocalOrdersR0066.toFunctionField k
        (genericMap k d hd q ρ hρ (toGeneric k b))
    rw [hE, genericMap_chart]
    rfl
  exact RingHom.congr_fun he a

private lemma localZ_map (i d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    genericMap k d hd q ρ hρ (localZ k i) = localZ k (d*i+q.val) := by
  unfold localZ chartCoordinate
  rw [genericMap_chart, map_mul, map_pow, tau_map k d hd q ρ hρ, hρ.2.1]
  rw [← mul_assoc, ← pow_mul, ← pow_add]

end RamifiedLiteralQuotientR0156

open RamifiedLiteralQuotientR0156
open ArithmeticThetaRamifiedPeriodR0154

/-- The full literal quotient commutes with every specified ramified chart pullback. -/
theorem ramified_literal_quotient :
    ∀ (k : Type) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c) (d : ℕ) (hd : 0 < d) (hrd : 0 < (2*c)*d) (hdiv : c ∣ (2*c)*d) (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k)) (hρ : ∀ q, ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q (ρ q)) (E : Fin d → (ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hE : ∀ q, ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k (ρ q) (E q)), ∀ j : Fin ((2*c)*d), E (ArithmeticThetaRamifiedPeriodR0154.residueIndex (2*c) d hd j) (ArithmeticThetaRatioRegularityR0067.LocalTheta k c ζ hc hcop hζ (ArithmeticThetaRamifiedPeriodR0154.coarseIndex (2*c) d hd j)) = ArithmeticThetaAnnularNormBridgeR0156.literalTheta k ((2*c)*d) c hrd hc hdiv hcop ζ hζ j := by
  intro k _ _ c hc hcop ζ hζ d hd hrd hdiv ρ hρ E hE j
  let i := coarseIndex (2*c) d hd j
  let q := residueIndex (2*c) d hd j
  have hj : d*i.val+q.val = j.val := by
    dsimp [i,q,coarseIndex,residueIndex]
    exact Nat.div_add_mod j.val d
  have hjlt : d*i.val+q.val < (2*c)*d := by rw [hj]; exact j.isLt
  have hnorm : d * ((2*c)*(c^2-1)/12) = ((2*c)*d)*(c^2-1)/12 := by
    rw [← Nat.mul_div_assoc _ (ArithmeticThetaLocalNormR0054.norm_exponent_integral c hc hcop).1]
    congr 1
    ring
  have hnormZ : (d : ℤ) * (((2*c)*(c^2-1)/12 : ℕ) : ℤ) =
      ((((2*c)*d)*(c^2-1)/12 : ℕ) : ℤ) := by
    exact_mod_cast hnorm
  change E q (ArithmeticThetaRatioRegularityR0067.LocalTheta k c ζ hc hcop hζ i) = _
  unfold ArithmeticThetaRatioRegularityR0067.LocalTheta ArithmeticThetaLocalOrdersR0066.localFunction
    ArithmeticThetaGenericOverlapR0065.numerator ArithmeticThetaGenericOverlapR0065.denominator
    ArithmeticThetaLocalNormR0054.localNumerator ArithmeticThetaLocalNormR0054.localDenominator
  rw [map_div₀]
  simp only [fieldMap_generic k d hd q (ρ q) (hρ q) (E q) (hE q), map_mul, map_pow, map_neg]
  rw [tp_map k d hd q (ρ q) (hρ q), hnormZ,
    gamma_map k (2*c) i.val d (by omega) i.isLt hd q (ρ q) (hρ q) hrd hjlt,
    localZ_map k i.val d hd q (ρ q) (hρ q),
    powered_map k (2*c) c i.val d (by omega) hc (by simp) hcop ζ hζ i.isLt hd q
      (ρ q) (hρ q) hrd hdiv hjlt]
  simp only [literalTheta, hj, map_mul, map_pow, map_neg]

end ArithmeticThetaAnnularNormBridgeR0156

#print axioms ArithmeticThetaAnnularNormBridgeR0156.ramified_literal_quotient
