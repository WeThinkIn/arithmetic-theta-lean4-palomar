module

public import CoefficientCompletedMapsR0157
public import CoefficientNormDescentDefinitionsR0157
public import AnnularNormBridgeDefinitionsR0156

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace LiteralCoefficientTransportR0157
open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaLocalNormR0054 (gammaLocal gammaUnit gammaHorizontal poweredLocal localZ)
variable (k : Type) [Field k] [CharZero k]

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


variable (l : Type) [Field l] [CharZero l] (ι : k →+* l)
variable (ρ : Chart k →+* Chart l) (hρ : IsChartMap k l ι ρ)

include hρ

private lemma tau_map : ρ (tau k) = tau l := by
  have h := hρ.1 PowerSeries.X
  simpa only [baseMap, PowerSeries.map_X, base, tau,
    ArithmeticThetaScaledAnnularR0050.tau] using h

private def genericMap : GenericChart k →+* GenericChart l :=
  IsLocalization.Away.lift (tau k) (show IsUnit ((toGeneric l).comp ρ (tau k)) by
    rw [RingHom.comp_apply, tau_map k l ι ρ hρ]
    exact IsLocalization.Away.algebraMap_isUnit (tau l))

private lemma genericMap_chart (a : Chart k) :
    genericMap k l ι ρ hρ (toGeneric k a) = toGeneric l (ρ a) :=
  IsLocalization.Away.lift_eq _ _ _

private lemma tp_map (e : ℤ) :
    genericMap k l ι ρ hρ (tpower k e) = tpower l e := by
  have hu : Units.map (genericMap k l ι ρ hρ).toMonoidHom (parameterUnit k) =
      parameterUnit l := by
    apply Units.ext
    change genericMap k l ι ρ hρ (toGeneric k (tau k)) = toGeneric l (tau l)
    rw [genericMap_chart, tau_map k l ι ρ hρ]
  change (Units.map (genericMap k l ι ρ hρ).toMonoidHom (parameterUnit k ^ e)).val = _
  rw [map_zpow, hu]
  rfl

private lemma gammaPartial_map (r i N : ℕ) :
    ρ (ArithmeticThetaScaledAnnularR0050.gammaPartial k 1 r i N) =
      ArithmeticThetaScaledAnnularR0050.gammaPartial l 1 r i N := by
  unfold ArithmeticThetaScaledAnnularR0050.gammaPartial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro m hm
  change ρ ((1-tau k ^ (r*m+i)*cx k)*(1-tau k ^ (r*(m+1)-i-1)*cy k)) =
    (1-tau l ^ (r*m+i)*cx l)*(1-tau l ^ (r*(m+1)-i-1)*cy l)
  simp only [map_mul, map_sub, map_one, map_pow, tau_map k l ι ρ hρ,
    hρ.2.1, hρ.2.2.1]

private lemma gamma_map (r i : ℕ) (hr : 0 < r) (hi : i < r) :
    genericMap k l ι ρ hρ (gammaLocal k r i hr hi) = gammaLocal l r i hr hi := by
  unfold gammaLocal
  rw [genericMap_chart]
  apply congrArg (toGeneric l)
  apply sub_eq_zero.mp
  apply chart_separated l
  intro n
  obtain ⟨A,hA⟩ := (Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 r i (by omega) (by omega))).1.2.2 n
  obtain ⟨B,hB⟩ := (Classical.choose_spec
    (ArithmeticThetaScaledAnnularR0050.gamma_unit_product l 1 r i (by omega) (by omega))).1.2.2 n
  have ha := hρ.2.2.2 n _ (hA (max A B) (Nat.le_max_left _ _))
  have hb := hB (max A B) (Nat.le_max_right _ _)
  rw [map_sub, gammaPartial_map k l ι ρ hρ] at ha
  change gammaHorizontal l r i * gammaUnit l r i hr hi - _ ∈ filtration l n at hb
  change ρ (gammaHorizontal k r i * gammaUnit k r i hr hi) - _ ∈ filtration l n at ha
  convert (filtration l n).sub_mem ha hb using 1 <;> ring

private lemma literalPartial_map (r c i N : ℕ) :
    genericMap k l ι ρ hρ (literalPartial k r c i N) = literalPartial l r c i N := by
  unfold literalPartial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro m hm
  simp only [map_mul, map_sub, map_one, map_pow, tp_map,
    genericMap_chart, hρ.2.1, hρ.2.2.1]

private lemma powered_map (r c i : ℕ) (hr : 0 < r) (hc : 1 < c)
    (hdiv : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c)
    (hζl : IsPrimitiveRoot (ι ζ) c) (hi : i < r) :
    genericMap k l ι ρ hρ (poweredLocal k r c i ζ hr hc hdiv hcop hζ hi) =
      poweredLocal l r c i (ι ζ) hr hc hdiv hcop hζl hi := by
  let G := genericMap k l ι ρ hρ
  let C := clearingPartial k r c i (cutoff c i 0)
  let D := clearingPartial l r c i (cutoff c i 0)
  apply bounded_unique l _ _ (G C) D
  intro n
  let N := cutoff c i n
  obtain ⟨f,hf,he⟩ := (Classical.choose_spec
    (powered_gamma_local_divisor k r c i ζ hr hc hdiv hcop hζ hi)).1.1 n N le_rfl
  obtain ⟨g,hg,he'⟩ := (Classical.choose_spec
    (powered_gamma_local_divisor l r c i (ι ζ) hr hc hdiv hcop hζl hi)).1.1 n N le_rfl
  have hC : clearingPartial k r c i N = C := by
    apply (powered_gamma_clearing k r c i hr hc hdiv hcop hi).2.2
    · dsimp [N, cutoff]; omega
    · rfl
  have hD : clearingPartial l r c i N = D := by
    apply (powered_gamma_clearing l r c i hr hc hdiv hcop hi).2.2
    · dsimp [N, cutoff]; omega
    · rfl
  rw [hC] at he
  rw [hD] at he'
  have heG := congrArg G he
  simp only [map_sub, map_mul] at heG
  change G (poweredLocal k r c i ζ hr hc hdiv hcop hζ hi) - G (literalPartial k r c i N) =
    G C * G (toGeneric k f) at heG
  rw [literalPartial_map, genericMap_chart] at heG
  change poweredLocal l r c i (ι ζ) hr hc hdiv hcop hζl hi -
    literalPartial l r c i N = D * toGeneric l g at he'
  refine ⟨ρ f, g, hρ.2.2.2 n f hf, hg, ?_⟩
  linear_combination heG - he'

private lemma fieldMap_generic
    (E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField l)
    (hE : ExtendsChart k l ρ E) (a : GenericChart k) :
    E (ArithmeticThetaLocalOrdersR0066.toFunctionField k a) =
      ArithmeticThetaLocalOrdersR0066.toFunctionField l (genericMap k l ι ρ hρ a) := by
  have he : E.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k) =
      (ArithmeticThetaLocalOrdersR0066.toFunctionField l).comp (genericMap k l ι ρ hρ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (tau k))
    apply RingHom.ext
    intro b
    change E (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      ArithmeticThetaLocalOrdersR0066.toFunctionField l
        (genericMap k l ι ρ hρ (toGeneric k b))
    rw [hE, genericMap_chart]
    rfl
  exact RingHom.congr_fun he a

private lemma localZ_map (i : ℕ) :
    genericMap k l ι ρ hρ (localZ k i) = localZ l i := by
  unfold localZ chartCoordinate
  rw [genericMap_chart, map_mul, map_pow, tau_map k l ι ρ hρ, hρ.2.1]

end LiteralCoefficientTransportR0157
open LiteralCoefficientTransportR0157

/-- Transport of the full normalized annular quotient under coefficient change. -/
theorem literal_coefficient_transport :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l) (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ) (E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField l) (hE : ArithmeticThetaCoefficientNormDescentR0157.ExtendsChart k l ρ E) (r c : ℕ) (hr : 0 < r) (hc : 1 < c) (hcr : c ∣ r) (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c) (hζl : IsPrimitiveRoot (ι ζ) c), ∀ j : Fin r, E (ArithmeticThetaAnnularNormBridgeR0156.literalTheta k r c hr hc hcr hcop ζ hζ j) = ArithmeticThetaAnnularNormBridgeR0156.literalTheta l r c hr hc hcr hcop (ι ζ) hζl j := by
  intro k l _ _ _ _ ι ρ hρ E hE r c hr hc hcr hcop ζ hζ hζl j
  unfold ArithmeticThetaAnnularNormBridgeR0156.literalTheta
  simp only [map_div₀, map_mul, map_pow, map_neg,
    fieldMap_generic k l ι ρ hρ E hE, tp_map k l ι ρ hρ,
    gamma_map k l ι ρ hρ, localZ_map k l ι ρ hρ,
    powered_map k l ι ρ hρ r c j.val hr hc hcr hcop ζ hζ hζl j.isLt]

end ArithmeticThetaCoefficientNormDescentR0157

#print axioms ArithmeticThetaCoefficientNormDescentR0157.literal_coefficient_transport
