module

public import CompletedChartTaylorR0161
public import CompletedSectionKernelsR0053

@[expose] public section

/-! Faithfulness at the actual identity section, and the uniquely determined
extension to the fraction field of the generic completed chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
namespace FaithfulTaylorFieldR0161
open ArithmeticThetaAnnularTorsionPrereqR0053 hiding Chart
variable (k : Type) [Field k] [CharZero k]
variable (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)

private def evaluation : Chart k →+* PowerSeries k :=
  PowerSeries.constantCoeff.comp σ

include hσ in
private lemma evaluation_spec : SectionAt k true 1 (evaluation k σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro b
    change PowerSeries.constantCoeff (σ (base k b)) = b
    rw [hσ.1 b, PowerSeries.constantCoeff_C]
  · change PowerSeries.constantCoeff (σ (cx k)) = PowerSeries.C 1
    rw [hσ.2.1]
    simp
  · change PowerSeries.constantCoeff (σ (cy k)) = PowerSeries.C (1 : k)⁻¹ * PowerSeries.X
    rw [hσ.2.2.1]
    simp [zInverse, PowerSeries.constantCoeff_invOfUnit]
  · intro n b hb
    simpa only [evaluation, RingHom.comp_apply, PowerSeries.coeff_zero_eq_constantCoeff]
      using hσ.2.2.2 n b hb 0

include hσ in
private lemma equation_image : σ (sectionEquation k true 1) = PowerSeries.X := by
  simp only [sectionEquation, coord, if_true, map_sub, hσ.2.1, hσ.1,
    map_one, add_sub_cancel_left]

include hσ in
private lemma faithful : Function.Injective σ := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  letI : IsNoetherianRing (Chart k) :=
    (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1
  have hs := (completed_section_kernels k true 1 (one_ne_zero)).2
    (evaluation k σ) (evaluation_spec k σ hσ)
  have hdiv (b : Chart k) (hb : σ b = 0) : sectionEquation k true 1 ∣ b := by
    apply Ideal.mem_span_singleton.mp
    change b ∈ sectionIdeal k true 1
    rw [← hs.2.1]
    change PowerSeries.constantCoeff (σ b) = 0
    rw [hb, map_zero]
  have hall (n : ℕ) : ∀ b : Chart k, σ b = 0 →
      sectionEquation k true 1 ^ n ∣ b := by
    induction n with
    | zero => intro b _; simp
    | succ n ih =>
      intro b hb
      obtain ⟨a, ha⟩ := hdiv b hb
      have hsa : σ a = 0 := by
        rw [ha, map_mul, equation_image k σ hσ] at hb
        exact (mul_eq_zero.mp hb).resolve_left PowerSeries.X_ne_zero
      obtain ⟨c, hc⟩ := ih a hsa
      refine ⟨c, ?_⟩
      rw [ha, hc, pow_succ']
      exact (mul_assoc _ _ _).symm
  apply (injective_iff_map_eq_zero σ).mpr
  intro b hb
  have hm : b ∈ ⨅ n : ℕ, sectionIdeal k true 1 ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [sectionIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hall n b hb
  rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hs.2.2.1.ne_top] at hm
  exact hm

private lemma iterated_injective : Function.Injective (toIterated k) :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k)).comp
    (PowerSeries.map_injective (HahnSeries.ofPowerSeries ℤ k)
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)))

private lemma parameter_ne_zero : tau k ≠ 0 := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

private lemma extension (hinj : Function.Injective σ) :
    ∃! Ψ : ChartField k →+* Iterated k, ExtendsTaylor k σ Ψ := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  let f : Chart k →+* Iterated k := (toIterated k).comp σ
  have hf : Function.Injective f := (iterated_injective k).comp hinj
  have hloc : Function.Injective (algebraMap (Chart k) (GenericChart k)) :=
    IsLocalization.injective (GenericChart k)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (parameter_ne_zero k))
  have hunit : IsUnit (f (tau k)) := isUnit_iff_ne_zero.mpr (by
    intro h
    exact parameter_ne_zero k (hf (h.trans (map_zero f).symm)))
  let g : GenericChart k →+* Iterated k := IsLocalization.Away.lift (tau k) hunit
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (tau k)) g).mpr
    intro a b
    simp only [g, IsLocalization.Away.lift_eq]
    exact hloc.eq_iff.trans hf.eq_iff.symm
  let E : ChartField k →+* Iterated k := IsFractionRing.lift hg
  have hE : ExtendsTaylor k σ E := by
    apply RingHom.ext
    intro a
    change E (algebraMap (GenericChart k) _ (algebraMap (Chart k) _ a)) = f a
    rw [IsFractionRing.lift_algebraMap]
    exact IsLocalization.Away.lift_eq (tau k) hunit a
  refine ⟨E, hE, ?_⟩
  intro F hF
  apply IsFractionRing.ringHom_ext (A := GenericChart k)
  suffices h : F.comp (algebraMap (GenericChart k) _) = E.comp (algebraMap _ _) from
    fun a => RingHom.congr_fun h a
  apply IsLocalization.ringHom_ext (Submonoid.powers (tau k))
  apply RingHom.ext
  intro a
  exact (RingHom.congr_fun hF a).trans (RingHom.congr_fun hE a).symm
end FaithfulTaylorFieldR0161

/-- The prescribed actual Taylor map is faithful and admits exactly one extension
from the actual generic chart fraction field to k((t))((u)). -/
theorem faithful_taylor_field :
    ∀ (k : Type) [Field k] [CharZero k]
      (σ : Chart k →+* Bivariate k), IsChartTaylor k σ →
      Function.Injective σ ∧ ∃! Ψ : ChartField k →+* Iterated k,
        ExtendsTaylor k σ Ψ := by
  intro k _ _ σ hσ
  have h := FaithfulTaylorFieldR0161.faithful k σ hσ
  exact ⟨h, FaithfulTaylorFieldR0161.extension k σ h⟩
end ArithmeticThetaOriginInitialR0161

#print axioms ArithmeticThetaOriginInitialR0161.faithful_taylor_field
