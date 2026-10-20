module

public import HorizontalSplitReducedR0053
public import PoweredGammaClearingR0053
public import PoweredGammaUnitLimitR0053
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

/-! The local divisor of the literal powered-gamma product. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

private lemma chart_domain (k : Type u) [Field k] [CharZero k] :
    IsDomain (Chart k) :=
  (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1

private lemma chart_tau_ne_zero (k : Type u) [Field k] [CharZero k] :
    tau k ≠ 0 := by
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

private lemma generic_domain (k : Type u) [Field k] [CharZero k] :
    IsDomain (GenericChart k) := by
  letI : IsDomain (Chart k) := chart_domain k
  exact IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))

private lemma generic_injective (k : Type u) [Field k] [CharZero k] :
    Function.Injective (toGeneric k) := by
  letI : IsDomain (Chart k) := chart_domain k
  exact IsLocalization.injective (GenericChart k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))

private lemma chart_xy (k : Type u) [Field k] [CharZero k] :
    cx k * cy k = tau k := by
  change ArithmeticThetaScaledAnnularR0050.cx k 1 *
    ArithmeticThetaScaledAnnularR0050.cy k 1 =
      ArithmeticThetaScaledAnnularR0050.tau k 1
  change ArithmeticThetaScaledTateBridgeR0046.toCompleted k 1
      (ArithmeticThetaScaledTateBridgeR0046.x k 1) *
    ArithmeticThetaScaledTateBridgeR0046.toCompleted k 1
      (ArithmeticThetaScaledTateBridgeR0046.y k 1) = _
  rw [← map_mul]
  have hrel : ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxy : ArithmeticThetaScaledTateBridgeR0046.x k 1 *
      ArithmeticThetaScaledTateBridgeR0046.y k 1 =
        ArithmeticThetaScaledTateBridgeR0046.t k 1 := by
    apply sub_eq_zero.mp
    change ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0) *
      ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1) -
      algebraMap (Base k) (Node k)
        (ArithmeticThetaScaledTateBridgeR0046.parameter k 1) = 0
    change ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0) *
      ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1) -
      ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
        (MvPolynomial.C (ArithmeticThetaScaledTateBridgeR0046.parameter k 1)) = 0
    simpa [ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.quotientMap] using hrel
  rw [hxy]
  simp [ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter]

private lemma chart_tau_jacobson (k : Type u) [Field k] [CharZero k] :
    tau k ∈ (⊥ : Ideal (Chart k)).jacobson := by
  letI : IsAdicComplete
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k)).mpr inferInstance
  have hle : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (Node k) (Chart k)) ≤
      (⊥ : Ideal (Chart k)).jacobson := IsAdicComplete.le_jacobson_bot _
  have hmem : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 ∈
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k)) :=
    Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using hle hmem

private lemma horizontal_x_y_coprime (k : Type u) [Field k] [CharZero k]
    (c : ℕ) (hc : 0 < c) :
    horizontalIdeal k true c ⊔ horizontalIdeal k false c = ⊤ := by
  let J := horizontalIdeal k true c ⊔ horizontalIdeal k false c
  have hx : horizontalEquation k true c ∈ J :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hy : horizontalEquation k false c ∈ J :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hpow : (cx k * cy k) ^ c = tau k ^ c := congrArg (· ^ c) (chart_xy k)
  have hmem : 1 - tau k ^ c ∈ J := by
    have h := J.add_mem hx (J.mul_mem_left (cx k ^ c) hy)
    convert h using 1
    · simp [horizontalEquation, coord]
      rw [← hpow, mul_pow]
      ring
  have hjac : tau k ^ c ∈ (⊥ : Ideal (Chart k)).jacobson :=
    (⊥ : Ideal (Chart k)).jacobson.pow_mem_of_mem (chart_tau_jacobson k) c hc
  have hu : IsUnit (1 - tau k ^ c) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa [sub_eq_add_neg] using
      ((⊥ : Ideal (Chart k)).jacobson.neg_mem hjac)
  exact J.eq_top_of_isUnit_mem hmem hu

private lemma horizontal_ideal_radical (k : Type u) [Field k] [CharZero k]
    (r c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) :
    (Ideal.span {horizontal k r c j} : Ideal (Chart k)).IsRadical := by
  have hx := (horizontal_split_reduced k true c ζ hc hcop hζ).2.2.1
  have hy := (horizontal_split_reduced k false c ζ hc hcop hζ).2.2.1
  by_cases hX : r ∣ c * j <;> by_cases hY : r ∣ c * (j + 1)
  · have heq : (Ideal.span {horizontal k r c j} : Ideal (Chart k)) =
        horizontalIdeal k true c * horizontalIdeal k false c := by
      simp [horizontal, hX, hY, horizontalIdeal,
        Ideal.span_singleton_mul_span_singleton]
    rw [heq, Ideal.mul_eq_inf_of_coprime
      (horizontal_x_y_coprime k c (by omega))]
    exact hx.inf hy
  · simpa [horizontal, hX, hY, horizontalIdeal] using hx
  · simpa [horizontal, hX, hY, horizontalIdeal] using hy
  · simp [horizontal, hX, hY]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top (Chart k))

private lemma generic_filtration_separated (k : Type u) [Field k] [CharZero k]
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

private lemma horizontal_nzd (k : Type u) [Field k] [CharZero k]
    (r c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) :
    horizontal k r c j ∈ nonZeroDivisors (Chart k) := by
  have hx := (horizontal_split_reduced k true c ζ hc hcop hζ).2.2.2.1
  have hy := (horizontal_split_reduced k false c ζ hc hcop hζ).2.2.2.1
  by_cases hX : r ∣ c * j <;> by_cases hY : r ∣ c * (j + 1)
  · simpa [horizontal, hX, hY] using mul_mem_nonZeroDivisors.mpr ⟨hx, hy⟩
  · simpa [horizontal, hX, hY] using hx
  · simpa [horizontal, hX, hY] using hy
  · simp [horizontal, hX, hY]

theorem powered_gamma_local_divisor :
    ∀ (k : Type u) [Field k] [CharZero k] (r c j : ℕ) (ζ : k),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 → IsPrimitiveRoot ζ c → j < r →
      ∃! γ : GenericChart k,
        (∀ n N : ℕ, cutoff c j n ≤ N →
          ∃ f : Chart k, f ∈ filtration k n ∧
            γ - literalPartial k r c j N =
              clearingPartial k r c j N * toGeneric k f) ∧
        Associated γ (toGeneric k (horizontal k r c j)) ∧
        (Ideal.span {γ} : Ideal (GenericChart k)).IsRadical ∧
        γ ∈ nonZeroDivisors (GenericChart k) := by
  intro k _ _ r c j ζ hr hc hcr hcop hζ hj
  obtain ⟨v, ⟨hvunit, hvlim⟩, _⟩ :=
    powered_gamma_unit_limit k r c j hr hc hcr hcop hj
  have hclear := powered_gamma_clearing k r c j hr hc hcr hcop hj
  let C := clearingPartial k r c j (cutoff c j 0)
  have hCunit : IsUnit C := (hclear.2.1 (cutoff c j 0)).2
  have hstable (n N : ℕ) (hN : cutoff c j n ≤ N) :
      clearingPartial k r c j N = C := by
    apply (hclear.2.2 (cutoff c j 0) N (le_refl _) ?_).symm
    simp only [cutoff] at hN ⊢
    omega
  let H := horizontal k r c j
  let γ := C * toGeneric k (H * v)
  have happrox (n N : ℕ) (hN : cutoff c j n ≤ N) :
      ∃ f : Chart k, f ∈ filtration k n ∧
        γ - literalPartial k r c j N =
          clearingPartial k r c j N * toGeneric k f := by
    refine ⟨H * v - normalizedPartial k r c j N, (hvlim n N hN).2, ?_⟩
    rw [(hclear.2.1 N).1, hstable n N hN]
    dsimp [γ]
    simp only [map_sub, map_mul]
    ring
  have hHnzd : H ∈ nonZeroDivisors (Chart k) :=
    horizontal_nzd k r c j ζ hc hcop hζ
  have hHne : H ≠ 0 := by
    letI : IsDomain (Chart k) := chart_domain k
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hHnzd)
  have hHgeneric : toGeneric k H ≠ 0 := by
    simpa using (generic_injective k).ne hHne
  have hγassoc : Associated γ (toGeneric k H) := by
    have hu : IsUnit (C * toGeneric k v) :=
      hCunit.mul (hvunit.map (toGeneric k))
    have heq : γ = (C * toGeneric k v) * toGeneric k H := by
      dsimp [γ]
      rw [map_mul]
      ring
    rw [heq]
    exact associated_unit_mul_left _ _ hu
  have hγrad : (Ideal.span {γ} : Ideal (GenericChart k)).IsRadical := by
    have hrad := horizontal_ideal_radical k r c j ζ hc hcop hζ
    have hmap : (Ideal.span {toGeneric k H} : Ideal (GenericChart k)).IsRadical := by
      apply Ideal.radical_eq_iff.mp
      have heq : (Ideal.span {H} : Ideal (Chart k)).map (toGeneric k) =
          (Ideal.span {toGeneric k H} : Ideal (GenericChart k)) := by
        simp [Ideal.map_span]
      calc
        (Ideal.span {toGeneric k H} : Ideal (GenericChart k)).radical =
            ((Ideal.span {H} : Ideal (Chart k)).map (toGeneric k)).radical := by rw [heq]
        _ = ((Ideal.span {H} : Ideal (Chart k)).radical).map (toGeneric k) := by
          simpa only [toGeneric] using
            (IsLocalization.map_radical
              (M := Submonoid.powers (tau k)) (S := GenericChart k)
              (Ideal.span {H} : Ideal (Chart k))).symm
        _ = (Ideal.span {H} : Ideal (Chart k)).map (toGeneric k) := by
          rw [hrad.radical]
        _ = _ := heq
    have heq : (Ideal.span {γ} : Ideal (GenericChart k)) =
        Ideal.span {toGeneric k H} := by
      rw [show γ = (C * toGeneric k v) * toGeneric k H by
        dsimp [γ]; rw [map_mul]; ring]
      exact Ideal.span_singleton_mul_left_unit
        (hCunit.mul (hvunit.map (toGeneric k))) _
    rwa [heq]
  have hγnzd : γ ∈ nonZeroDivisors (GenericChart k) := by
    letI : IsDomain (GenericChart k) := generic_domain k
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (hγassoc.ne_zero_iff.mpr hHgeneric)
  refine ⟨γ, ⟨happrox, hγassoc, hγrad, hγnzd⟩, ?_⟩
  intro γ' ⟨hγ'approx, _, _, _⟩
  obtain ⟨D, hCD⟩ := hCunit.exists_right_inv
  have hsep : D * (γ' - γ) = 0 := by
    apply generic_filtration_separated k
    intro n
    let N := cutoff c j n
    obtain ⟨f, hf, hγ'f⟩ := hγ'approx n N (le_refl _)
    obtain ⟨g, hg, hγg⟩ := happrox n N (le_refl _)
    refine ⟨f - g, (filtration k n).sub_mem hf hg, ?_⟩
    rw [hstable n N (le_refl _)] at hγ'f hγg
    rw [map_sub]
    calc
      D * (γ' - γ) = D * (C * (toGeneric k f - toGeneric k g)) := by
        congr 1
        linear_combination hγ'f - hγg
      _ = toGeneric k f - toGeneric k g := by
        rw [← mul_assoc, mul_comm D C, hCD, one_mul]
  have hdiff : γ' - γ = 0 := by
    calc
      γ' - γ = (C * D) * (γ' - γ) := by rw [hCD, one_mul]
      _ = 0 := by rw [mul_assoc, hsep, mul_zero]
  exact sub_eq_zero.mp hdiff

end ArithmeticThetaAnnularTorsionPrereqR0053
