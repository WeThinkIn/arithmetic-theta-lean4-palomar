module

public import FaithfulAnnularEvaluationR0156

@[expose] public section

/-! Naturality of faithful evaluation under residue-zero parameter ramification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158
namespace RamifiedEvaluationNaturality
open ArithmeticThetaAnnularNormBridgeR0156
open ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation
open ArithmeticThetaAnnularTorsionPrereqR0053 (base cx cy tau filtration GenericChart)
open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaKatoAnnularR0152 (chartToField)
open ArithmeticThetaRamifiedPeriodR0154
variable (k : Type) [Field k] [CharZero k]

private lemma evaluation_chart (ev : ChartField k →+* Series k)
    (hev : IsEvaluation k 1 1 ev) (b : Chart k) :
    ev (chartToField k b) = HahnSeries.ofPowerSeries ℤ (Coeff k)
      (chartEvaluation k 1 1 b) := by
  have hnode (p : Node k 1) : ev (chartToField k (toCompleted k 1 p)) =
      HahnSeries.ofPowerSeries ℤ (Coeff k) (chartEvaluation k 1 1 (toCompleted k 1 p)) := by
    suffices h : (ev.comp (chartToField k)).comp (toCompleted k 1) =
        ((HahnSeries.ofPowerSeries ℤ (Coeff k)).comp (chartEvaluation k 1 1)).comp
          (toCompleted k 1) from RingHom.congr_fun h p
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (hev.1 c).trans (congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k))
        (chartEvaluation_base k 1 1 c)).symm
    · intro i
      fin_cases i
      · change ev (chartToField k (cx k)) =
          HahnSeries.ofPowerSeries ℤ (Coeff k) (chartEvaluation k 1 1 (cx k))
        simpa only [chartEvaluation_x, HahnSeries.ofPowerSeries_C] using hev.2.1
      · change ev (chartToField k (cy k)) =
          HahnSeries.ofPowerSeries ℤ (Coeff k) (chartEvaluation k 1 1 (cy k))
        simpa [chartEvaluation_y, ArithmeticThetaLaurentNormR0064.t,
          HahnSeries.ofPowerSeries_X] using hev.2.2.1
  apply HahnSeries.ext
  funext e
  let N := (e + 1).toNat
  have he : e < (N : ℤ) := by dsimp [N]; omega
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 N b
  have h1 := hev.2.2.2 N _ hp e he
  have h2 : (HahnSeries.ofPowerSeries ℤ (Coeff k)
      (chartEvaluation k 1 1 (b - toCompleted k 1 (quotientMap k 1 p)))).coeff e = 0 := by
    have h := chartEvaluation_filtered k 1 1 N _ hp
    change chartEvaluation k 1 1 _ ∈ (Ideal.span {PowerSeries.X}) ^ N at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h
    by_cases hn : e < 0
    · simp [PowerSeries.coeff_coe, hn]
    · simpa [PowerSeries.coeff_coe, hn] using h e.natAbs (by omega)
  simp only [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, hnode]

omit [CharZero k] in
private lemma filtration_eq (N : ℕ) :
    filtration k N = (Ideal.span {tau k}) ^ N := by
  simp [filtration, completedPower, tau, ArithmeticThetaScaledAnnularR0050.tau,
    completedParameter, completedBaseMap, t, parameter]

private lemma ps_ext (f g : Chart k →+* PowerSeries (Coeff k))
    (hf : PowerSeries.X ∣ f (tau k)) (hg : PowerSeries.X ∣ g (tau k))
    (hb : ∀ b, f (base k b) = g (base k b))
    (hx : f (cx k) = g (cx k)) (hy : f (cy k) = g (cy k)) : f = g := by
  have hnode : f.comp (toCompleted k 1) = g.comp (toCompleted k 1) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hb
    · intro i; fin_cases i
      · exact hx
      · exact hy
  have hfiltered (f : Chart k →+* PowerSeries (Coeff k))
      (hf : PowerSeries.X ∣ f (tau k)) (N : ℕ) (b : Chart k)
      (hb : b ∈ filtration k N) : PowerSeries.X ^ N ∣ f b := by
    rw [filtration_eq] at hb
    have hle : (Ideal.span {tau k}).map f ≤ Ideal.span {PowerSeries.X} := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton]
      exact hf
    have h := Ideal.mem_map_of_mem f hb
    rw [Ideal.map_pow] at h
    have h' := (pow_le_pow_left' hle N) h
    simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using h'
  apply RingHom.ext
  intro b
  ext n
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 (n+1) b
  have h1 := PowerSeries.X_pow_dvd_iff.mp (hfiltered f hf (n+1) _ hp) n (by omega)
  have h2 := PowerSeries.X_pow_dvd_iff.mp (hfiltered g hg (n+1) _ hp) n (by omega)
  simp only [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]
  exact congrArg (PowerSeries.coeff n) (RingHom.congr_fun hnode p)

private lemma chart_square (d : ℕ) (hd : 0 < d) (q : Fin d) (hq : q.val = 0)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    (chartEvaluation k 1 1).comp ρ =
      (baseMap (Coeff k) d hd).comp (chartEvaluation k 1 1) := by
  have ht : ρ (tau k) = tau k ^ d := by
    have h := hρ.1 PowerSeries.X
    simpa only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_X, map_pow, base, tau, ArithmeticThetaScaledAnnularR0050.tau] using h
  have heval : chartEvaluation k 1 1 (tau k) = PowerSeries.X := by
    simpa [tau, ArithmeticThetaScaledAnnularR0050.tau, completedParameter,
      completedBaseMap, t, parameter] using chartEvaluation_parameter k 1 1
  apply ps_ext k
  · simp only [RingHom.comp_apply, ht, map_pow, heval]
    exact dvd_pow_self _ (Nat.ne_of_gt hd)
  · simp only [RingHom.comp_apply, heval, baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      PowerSeries.expand_X]
    exact dvd_pow_self _ (Nat.ne_of_gt hd)
  · intro b
    simp only [RingHom.comp_apply, hρ.1, chartEvaluation_base, baseMap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.map_expand]
  · simp only [RingHom.comp_apply, hρ.2.1, hq, pow_zero, one_mul,
      chartEvaluation_x, baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_C]
  · simp only [RingHom.comp_apply, hρ.2.2, hq, Nat.sub_zero, map_mul, map_pow,
      heval, chartEvaluation_y, baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_C,
      PowerSeries.expand_X]
    conv_rhs => rw [show d = (d-1)+1 by omega, pow_succ]
    ring

end RamifiedEvaluationNaturality

/-- The complete evaluation square for residue-zero ramification, including degree one. -/
theorem ramified_evaluation_naturality :
    ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d) (q : Fin d) (hq : q.val = 0) (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k), ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρ → ∀ (E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField k), ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρ E → ∀ (ell : ArithmeticThetaLaurentNormR0064.Series k →+* ArithmeticThetaLaurentNormR0064.Series k), ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (ArithmeticThetaLaurentNormR0064.Coeff k) d hd ell → ∀ (ev : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaLaurentNormR0064.Series k), ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 ev → ev.comp E = ell.comp ev := by
  intro k _ _ d hd q hq ρ hρ E hE ell hell ev hev
  have hchart (b : ArithmeticThetaKatoAnnularR0152.Chart k) :
      ev (E (ArithmeticThetaKatoAnnularR0152.chartToField k b)) =
        ell (ev (ArithmeticThetaKatoAnnularR0152.chartToField k b)) := by
    rw [hE, RamifiedEvaluationNaturality.evaluation_chart k ev hev,
      RamifiedEvaluationNaturality.evaluation_chart k ev hev]
    exact (congrArg (HahnSeries.ofPowerSeries ℤ (ArithmeticThetaLaurentNormR0064.Coeff k))
      (RingHom.congr_fun (RamifiedEvaluationNaturality.chart_square k d hd q hq ρ hρ) b)).trans
        (hell _).symm
  apply IsFractionRing.ringHom_ext (A := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
  suffices h : (ev.comp E).comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) =
      (ell.comp ev).comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) from
    fun b => RingHom.congr_fun h b
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  apply RingHom.ext
  exact hchart

end ArithmeticThetaUnsplitExpansionR0158
#print axioms ArithmeticThetaUnsplitExpansionR0158.ramified_evaluation_naturality
