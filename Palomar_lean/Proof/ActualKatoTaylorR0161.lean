module

public import GammaTaylorComparisonR0161
public import FaithfulTaylorFieldR0161
public import CompletedChartTaylorR0161
public import SplitPeriodKatoFormulaR0158
public import GammaBaseChangeNaturalityR0158

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
namespace ActualKatoTaylorR0161
open ArithmeticThetaAnnularTorsionPrereqR0053 hiding Chart
open ArithmeticThetaUnsplitExpansionR0158.GammaBaseChangeNaturalityR0158

/-- Uniqueness for a coefficient-changing Taylor map on the completed chart.
Continuity follows from the principal base filtration. -/
private lemma chart_ext (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (B : PowerSeries k →+* PowerSeries l) (hB : PowerSeries.X ∣ B PowerSeries.X)
    (f g : Chart k →+* Bivariate l)
    (hf : ∀ b, f (base k b) = PowerSeries.C (B b))
    (hg : ∀ b, g (base k b) = PowerSeries.C (B b))
    (hx : f (cx k) = g (cx k)) (hy : f (cy k) = g (cy k)) : f = g := by
  have hfg : f.comp (complete k) = g.comp (complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b; exact (hf b).trans (hg b).symm
    · intro i; fin_cases i
      · exact hx
      · exact hy
  have filtered (q : Chart k →+* Bivariate l)
      (hq : ∀ b, q (base k b) = PowerSeries.C (B b))
      (n : ℕ) (b : Chart k) (hb : b ∈ filtration k n) (i : ℕ) :
      PowerSeries.X ^ n ∣ PowerSeries.coeff i (q b) := by
    change b ∈ (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1}) ^ n at hb
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
    obtain ⟨a, rfl⟩ := hb
    have ht : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 = base k PowerSeries.X := by
      simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
        ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
        base, ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
    rw [map_mul, map_pow, ht, hq, ← map_pow, PowerSeries.coeff_C_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hB n) _
  ext z i j
  obtain ⟨a, ha⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by decide)).2.2.2.2.2.2 (j+1) z
  let a' := ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 a
  have hap : z - complete k a' ∈ filtration k (j+1) := ha
  have hc (q : Chart k →+* Bivariate l)
      (hq : ∀ b, q (base k b) = PowerSeries.C (B b)) :
      PowerSeries.coeff j (PowerSeries.coeff i (q z)) =
        PowerSeries.coeff j (PowerSeries.coeff i (q (complete k a'))) := by
    have hh := PowerSeries.X_pow_dvd_iff.mp (filtered q hq (j+1) _ hap i) j (Nat.lt_succ_self j)
    simpa only [map_sub, sub_eq_zero] using hh
  rw [hc f hf, hc g hg]
  exact congrArg (fun b : Bivariate l => PowerSeries.coeff j (PowerSeries.coeff i b))
    (RingHom.congr_fun hfg a')

private lemma field_ext (k : Type) [Field k] [CharZero k] {F : Type} [Field F]
    (f g : ChartField k →+* F)
    (h : ∀ a : Chart k, f (ArithmeticThetaKatoAnnularR0152.chartToField k a) =
      g (ArithmeticThetaKatoAnnularR0152.chartToField k a)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := GenericChart k)
  suffices hh : f.comp (algebraMap (GenericChart k) _) = g.comp (algebraMap _ _) from
    fun a => RingHom.congr_fun hh a
  apply IsLocalization.ringHom_ext (Submonoid.powers (tau k))
  exact RingHom.ext h

private lemma toIterated_map (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (B : PowerSeries k →+* PowerSeries l) (L : LaurentSeries k →+* LaurentSeries l)
    (hL : ∀ b : PowerSeries k, L ((HahnSeries.ofPowerSeries ℤ k) b) =
      (HahnSeries.ofPowerSeries ℤ l) (B b)) (a : Bivariate k) :
    coefficientHom _ _ L (toIterated k a) = toIterated l (PowerSeries.map B a) := by
  rw [toIterated, RingHom.comp_apply]
  change coefficientHom _ _ L (algebraMap (PowerSeries (LaurentSeries k)) _ _) = _
  rw [coefficientHom_base]
  apply congrArg (HahnSeries.ofPowerSeries ℤ (LaurentSeries l))
  apply PowerSeries.ext
  intro i
  simp only [PowerSeries.coeff_map]
  exact hL _

private lemma zInverse_map (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (B : PowerSeries k →+* PowerSeries l) :
    PowerSeries.map B (zInverse k) = zInverse l := by
  apply mul_left_cancel₀ (show (1 + PowerSeries.X : Bivariate l) ≠ 0 by
    intro h; have := congrArg PowerSeries.constantCoeff h; simp at this)
  have h := congrArg (PowerSeries.map B)
    (show (1 + PowerSeries.X) * zInverse k = 1 from PowerSeries.mul_invOfUnit _ _ (by simp))
  rw [show (1 + PowerSeries.X) * zInverse l = 1 from PowerSeries.mul_invOfUnit _ _ (by simp)]
  simpa only [map_mul, map_add, map_one, PowerSeries.map_X] using h

private lemma coefficient_square (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (ρ : Chart k →+* Chart l)
    (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)
    (E : ChartField k →+* ChartField l)
    (hE : ArithmeticThetaCoefficientNormDescentR0157.ExtendsChart k l ρ E)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (σl : Chart l →+* Bivariate l) (hσl : IsChartTaylor l σl)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ)
    (Ψl : ChartField l →+* Iterated l) (hΨl : ExtendsTaylor l σl Ψl) :
    Ψl.comp E = (coefficientHom _ _ (coefficientHom k l ι)).comp Ψ := by
  let B := PowerSeries.map ι
  have H : σl.comp ρ = (PowerSeries.map B).comp σ := by
    apply chart_ext k l B (by simp [B])
    · intro b; simp only [RingHom.comp_apply, hρ.1, hσl.1]; rfl
    · intro b; simp only [RingHom.comp_apply, hσ.1, PowerSeries.map_C]
    · simp only [RingHom.comp_apply, hρ.2.1, hσl.2.1, hσ.2.1, map_add, map_one, PowerSeries.map_X]
    · simp only [RingHom.comp_apply, hρ.2.2.1, hσl.2.2.1, hσ.2.2.1,
        map_mul, PowerSeries.map_C, zInverse_map, B, PowerSeries.map_X]
  apply field_ext k
  intro a
  change Ψl (E (ArithmeticThetaKatoAnnularR0152.chartToField k a)) = _
  rw [hE a]
  simp only [RingHom.comp_apply]
  have Hl (b : Chart l) : Ψl (ArithmeticThetaKatoAnnularR0152.chartToField l b) =
      toIterated l (σl b) := RingHom.congr_fun hΨl b
  have Hk (b : Chart k) : Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      toIterated k (σ b) := RingHom.congr_fun hΨ b
  rw [Hl, Hk, toIterated_map k l B (coefficientHom k l ι) (coefficientHom_base k l ι)]
  exact congrArg (toIterated l) (RingHom.congr_fun H a)

private lemma ramified_square (k : Type) [Field k] [CharZero k]
    (d : ℕ) (hd : 0 < d) (q : Fin d) (hq : q.val = 0)
    (ρ : Chart k →+* Chart k)
    (hρ : ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρ)
    (E : ChartField k →+* ChartField k)
    (hE : ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρ E)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Ψ.comp E = (coefficientHom _ _ (ramificationHom k d hd)).comp Ψ := by
  let B := ArithmeticThetaRamifiedPeriodR0154.baseMap k d hd
  have HX : B PowerSeries.X = PowerSeries.X ^ d := PowerSeries.expand_X _ _
  have H : σ.comp ρ = (PowerSeries.map B).comp σ := by
    apply chart_ext k k B (by rw [HX]; exact dvd_pow_self _ (by omega))
    · intro b; simp only [RingHom.comp_apply, hρ.1, hσ.1]; rfl
    · intro b; simp only [RingHom.comp_apply, hσ.1, PowerSeries.map_C]
    · simp only [RingHom.comp_apply, hρ.2.1, hq, pow_zero, one_mul,
        hσ.2.1, map_add, map_one, PowerSeries.map_X]
    · simp only [RingHom.comp_apply, hρ.2.2, hq, Nat.sub_zero, map_mul, map_pow,
        show tau k = base k PowerSeries.X from rfl, hσ.1, hσ.2.2.1,
        PowerSeries.map_C, zInverse_map, HX]
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hd, ← map_pow]
  apply field_ext k
  intro a
  change Ψ (E (ArithmeticThetaKatoAnnularR0152.chartToField k a)) = _
  rw [hE a]
  simp only [RingHom.comp_apply]
  have Hk (b : Chart k) : Ψ (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      toIterated k (σ b) := RingHom.congr_fun hΨ b
  rw [Hk, Hk, toIterated_map k k B (ramificationHom k d hd) (ramificationHom_base k d hd)]
  exact congrArg (toIterated k) (RingHom.congr_fun H a)

private lemma coefficient_gamma (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (r c : ℕ) (hr : 0 < r) :
    coefficientHom _ _ (coefficientHom k l ι) (gammaTaylor k r c) = gammaTaylor l r c := by
  unfold gammaTaylor
  change coefficientHom _ _ _ (algebraMap (PowerSeries (LaurentSeries k)) _ _) = _
  rw [coefficientHom_base]
  apply congrArg (HahnSeries.ofPowerSeries ℤ (LaurentSeries l))
  apply PowerSeries.ext
  intro i
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change coefficientHom k l ι (algebraMap (PowerSeries k) _ _) = _
  rw [coefficientHom_base]
  apply congrArg (HahnSeries.ofPowerSeries ℤ l)
  rw [← PowerSeries.expand_apply r (by omega), PowerSeries.map_expand,
    ← PowerSeries.expand_apply r (by omega)]
  congr 1
  ext j
  simp only [PowerSeries.coeff_map]
  simp

private lemma ramified_gamma (k : Type) [Field k] [CharZero k]
    (d : ℕ) (hd : 0 < d) (r c : ℕ) (hr : 0 < r) :
    coefficientHom _ _ (ramificationHom k d hd) (gammaTaylor k r c) = gammaTaylor k (r*d) c := by
  unfold gammaTaylor
  change coefficientHom _ _ _ (algebraMap (PowerSeries (LaurentSeries k)) _ _) = _
  rw [coefficientHom_base]
  apply congrArg (HahnSeries.ofPowerSeries ℤ (LaurentSeries k))
  apply PowerSeries.ext
  intro i
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change ramificationHom k d hd (algebraMap (PowerSeries k) _ _) = _
  rw [ramificationHom_base]
  apply congrArg (HahnSeries.ofPowerSeries ℤ k)
  rw [← PowerSeries.expand_apply r (by omega), ← PowerSeries.expand_mul,
    PowerSeries.expand_apply]
  rw [Nat.mul_comm d r]

private lemma coefficient_f5 (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (r : ℕ) (hr : 0 < r) :
    coefficientHom _ _ (coefficientHom k l ι) (f5Taylor k r) = f5Taylor l r := by
  have hz : coefficientHom _ _ (coefficientHom k l ι)
      ((HahnSeries.ofPowerSeries ℤ (LaurentSeries k)) (1 + PowerSeries.X)) =
      (HahnSeries.ofPowerSeries ℤ (LaurentSeries l)) (1 + PowerSeries.X) := by
    change coefficientHom _ _ _ (algebraMap (PowerSeries (LaurentSeries k)) _ _) = _
    rw [coefficientHom_base]; simp
  simp only [f5Taylor, map_div₀, map_mul, map_inv₀, map_pow, map_neg,
    coefficient_gamma k l ι r _ hr, hz, HahnSeries.C_apply,
    coefficientHom_single, ArithmeticThetaLaurentNormR0064.t, map_one]

private lemma ramified_f5 (k : Type) [Field k] [CharZero k]
    (d : ℕ) (hd : 0 < d) (r : ℕ) (hr : 0 < r) :
    coefficientHom _ _ (ramificationHom k d hd) (f5Taylor k r) = f5Taylor k (r*d) := by
  have hz : coefficientHom _ _ (ramificationHom k d hd)
      ((HahnSeries.ofPowerSeries ℤ (LaurentSeries k)) (1 + PowerSeries.X)) =
      (HahnSeries.ofPowerSeries ℤ (LaurentSeries k)) (1 + PowerSeries.X) := by
    change coefficientHom _ _ _ (algebraMap (PowerSeries (LaurentSeries k)) _ _) = _
    rw [coefficientHom_base]; simp
  have ht : ramificationHom k d hd (ArithmeticThetaLaurentNormR0064.t k) =
      ArithmeticThetaLaurentNormR0064.t k ^ d := by
    simp [ArithmeticThetaLaurentNormR0064.t, ramificationHom_single, HahnSeries.single_pow]
  simp only [f5Taylor, map_div₀, map_mul, map_inv₀, map_pow, map_neg,
    ramified_gamma k d hd r _ hr, hz, HahnSeries.C_apply,
    coefficientHom_single, ht]
  simp only [← HahnSeries.C_apply, ← map_pow]
  simp only [← pow_mul, Nat.mul_assoc, Nat.mul_comm]

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151

private lemma literal_five (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (hdiv : 5 ∣ r) (ζ : k) (hζ : IsPrimitiveRoot ζ 5)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Ψ (ArithmeticThetaAnnularNormBridgeR0156.literalTheta k r 5 hr (by decide)
      hdiv (by decide) ζ hζ (zeroIndex r hr)) = f5Taylor k r := by
  have H := gamma_taylor_comparison k r 5 hr (by decide) hdiv (by decide) ζ hζ σ hσ Ψ hΨ
  have hE (b : Chart k) : Ψ (chartToField k b) = toIterated k (σ b) := RingHom.congr_fun hΨ b
  have hx : Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.localZ k 0)) =
      (HahnSeries.ofPowerSeries ℤ (LaurentSeries k)) (1 + PowerSeries.X) := by
    simp only [ArithmeticThetaLocalNormR0054.localZ, chartCoordinate, pow_zero, one_mul]
    change Ψ (chartToField k (cx k)) = _
    rw [hE, hσ.2.1]
    simp [toIterated]
  have ht : Ψ (chartToField k (tau k)) =
      HahnSeries.C (ArithmeticThetaLaurentNormR0064.t k) := by
    rw [hE, show tau k = base k PowerSeries.X from rfl, hσ.1]
    simp [toIterated, ArithmeticThetaLaurentNormR0064.t, HahnSeries.ofPowerSeries_X]
  have hp (n : ℕ) : Ψ (ArithmeticThetaLocalOrdersR0066.toFunctionField k (tpower k (n : ℤ))) =
      HahnSeries.C (ArithmeticThetaLaurentNormR0064.t k) ^ n := by
    simp only [tpower, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    congr 1
  have he : r * (5^2-1) / 12 = r*2 := by omega
  simp only [ArithmeticThetaAnnularNormBridgeR0156.literalTheta, zeroIndex,
    show (5:ℕ)^2 = 25 from rfl, show 5*(5-1)/2 = (10:ℕ) from rfl,
    map_div₀, map_mul, map_pow, map_neg, hp, hx, H.1, H.2, f5Taylor]
  norm_num only at he ⊢
  rw [he, pow_mul, ← map_pow, ← map_pow]
  ring

private theorem split_taylor :
    ∀ (k : Type)
    [Field k]
    [CharZero k]
    (r : ℕ)
    (hr : 0 < r)
    (h3 : 3 ≤ r)
    (he : Even r)
    (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
    (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X)
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j))
    (σ : ArithmeticThetaOriginInitialR0161.Chart k →+* ArithmeticThetaOriginInitialR0161.Bivariate k)
    (hσ : ArithmeticThetaOriginInitialR0161.IsChartTaylor k σ)
    (Ψ : ArithmeticThetaOriginInitialR0161.ChartField k →+* ArithmeticThetaOriginInitialR0161.Iterated k)
    (hΨ : ArithmeticThetaOriginInitialR0161.ExtendsTaylor k σ Ψ)
    (hdiv : 5 ∣ r)
    (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) 5)
    (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g → Ψ (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) g) = ArithmeticThetaOriginInitialR0161.f5Taylor k r := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ χ hχ φ hφ σ hσ Ψ hΨ hdiv ζ hζ g hg
  obtain ⟨f, hf, _⟩ := ArithmeticThetaUnsplitExpansionR0158.split_period_kato_formula
    k r 5 (by decide) (by decide) hr h3 he T M hM s hs G hG ζ hζ χ hχ φ hφ hdiv
  obtain ⟨g₀, hg₀, hu⟩ := actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG 5 (by decide) (by decide)
  have hgf : g = f := (hu g hg).trans (hu f hf.1).symm
  rw [hgf, hf.2]
  exact literal_five k r hr hdiv (ζ : k) hζ σ hσ Ψ hΨ

private lemma exists_model (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    ∃ (T : Tower k r hr) (M : Model k T), IsModel k T M := by
  obtain ⟨T, _⟩ := ArithmeticThetaInfinitesimalPolygonR0129.proper_flat_polygon_tower k r hr h3
  obtain ⟨b, hb, hbr, _⟩ :=
    ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis k r hr h3 T (fun _ => 1) 3 (by omega)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩


private theorem split_field_taylor :
    ∀ (k : Type)
    [Field k]
    [CharZero k]
    (r : ℕ)
    (hr : 0 < r)
    (h3 : 3 ≤ r)
    (he : Even r)
    (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
    (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X)
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j))
    (σ : ArithmeticThetaOriginInitialR0161.Chart k →+* ArithmeticThetaOriginInitialR0161.Bivariate k)
    (hσ : ArithmeticThetaOriginInitialR0161.IsChartTaylor k σ)
    (Ψ : ArithmeticThetaOriginInitialR0161.ChartField k →+* ArithmeticThetaOriginInitialR0161.Iterated k)
    (hΨ : ArithmeticThetaOriginInitialR0161.ExtendsTaylor k σ Ψ)
    (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) 5)
    (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g → Ψ (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) g) = ArithmeticThetaOriginInitialR0161.f5Taylor k r := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ χ hχ φ hφ σ hσ Ψ hΨ ζ hζ g hg
  classical
  let c : ℕ := 5
  have hc : 1 < c := by decide
  have hcop : Nat.Coprime c 6 := by decide
  let d := 2*c
  have hd : 0 < d := by dsimp [d]; omega
  have hrd : 0 < r*d := Nat.mul_pos hr hd
  have h3d : 3 ≤ r*d := h3.trans (Nat.le_mul_of_pos_right r hd)
  have hed : Even (r*d) := he.mul_right d
  have hcr : c ∣ r*d := by dsimp [d]; exact dvd_mul_of_dvd_right (dvd_mul_left c 2) r
  obtain ⟨Tb, Mb, hMb⟩ := exists_model k (r*d) hrd h3d
  letI : AlgebraicGeometry.IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3d Mb hMb
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k Mb hMb
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme k Mb) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Mb)
  obtain ⟨sb, hsb, _⟩ := marked_section_algebraization k (r*d) hrd h3d Tb Mb hMb
    (zeroIndex (r*d) hrd) 1
  obtain ⟨Gb, hGb, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb
  have Hχ : ∀ j : Fin (r*d), ∃ χj, IsChartMap k Mb j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k (r*d) hrd h3d Tb Mb hMb j
    exact ⟨χj, hj⟩
  choose χb hχb using Hχ
  have Hφ : ∀ j : Fin (r*d), ∃ φj, IsChartFieldMap k Mb (χb j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k (r*d) hrd h3d Tb Mb hMb j (χb j) (hχb j)
    exact ⟨φj, hj.1⟩
  choose φb hφb using Hφ
  have Hρ : ∀ q : Fin d, ∃ (ρq : Chart k →+* Chart k) (Eq : ChartField k →+* ChartField k),
      ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρq ∧
      ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρq Eq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := ArithmeticThetaRamifiedPeriodR0154.completed_chart_ramification k d hd q
    obtain ⟨Eq, hEq, _⟩ := hρq.2.2
    exact ⟨ρq, Eq, hρq.1, hEq⟩
  choose ρ E hρ hE using Hρ
  obtain ⟨F, hF, _⟩ := ArithmeticThetaRamifiedPeriodR0154.ramified_model_morphism k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k d hd
  obtain ⟨b, hb, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_generic_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1
  obtain ⟨α, hα, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_function_field_expansion k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    φ hφ φb hφb E hE
  have hbase := ArithmeticThetaRamifiedPeriodR0155.ramified_kato_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    he hed s hs sb hsb G hG Gb hGb
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb Gb hGb ell b hbase α hα.1 c hc hcop).2 g hg
  let jb := ArithmeticThetaRamifiedPeriodR0154.markedIndex r d hd (zeroIndex r hr)
  have hjc : ArithmeticThetaRamifiedPeriodR0154.coarseIndex r d hd jb = zeroIndex r hr := by
    apply Fin.ext
    simp [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex,
      ArithmeticThetaRamifiedPeriodR0154.coarseIndex, Nat.ne_of_gt hd]
  have hjq : (ArithmeticThetaRamifiedPeriodR0154.residueIndex r d hd jb).val = 0 := by
    simp [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex,
      ArithmeticThetaRamifiedPeriodR0154.residueIndex, zeroIndex]
  have hjb : jb = zeroIndex (r*d) hrd := by
    apply Fin.ext
    simp [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex, zeroIndex]
  have H := split_taylor k (r*d) hrd h3d hed Tb Mb hMb sb hsb Gb hGb
    χb hχb φb hφb σ hσ Ψ hΨ hcr ζ hζ (α g) hK
  rw [← hjb, hα.2.2.2.1, hjc] at H
  have hsquare := ramified_square k d hd
    (ArithmeticThetaRamifiedPeriodR0154.residueIndex r d hd jb) hjq
    (ρ _) (hρ _) (E _) (hE _) σ hσ Ψ hΨ
  have hval : Ψ (E _ (φ (zeroIndex r hr) g)) =
      coefficientHom _ _ (ramificationHom k d hd) (Ψ (φ (zeroIndex r hr) g)) :=
    RingHom.congr_fun hsquare _
  rw [hval, ← ramified_f5 k d hd r hr] at H
  exact (coefficientHom _ _ (ramificationHom k d hd)).injective H

end ActualKatoTaylorR0161
open ActualKatoTaylorR0161
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaUnsplitExpansionR0158.GammaBaseChangeNaturalityR0158

/-- The full normalized five-Kato identity in the actual identity Taylor field,
with auxiliary torsion splitting and period ramification eliminated. -/
theorem actual_kato_taylor :
    ∀ (k : Type)
    [Field k]
    [CharZero k]
    (r : ℕ)
    (hr : 0 < r)
    (h3 : 3 ≤ r)
    (he : Even r)
    (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
    (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X)
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j))
    (σ : ArithmeticThetaOriginInitialR0161.Chart k →+* ArithmeticThetaOriginInitialR0161.Bivariate k)
    (hσ : ArithmeticThetaOriginInitialR0161.IsChartTaylor k σ)
    (Ψ : ArithmeticThetaOriginInitialR0161.ChartField k →+* ArithmeticThetaOriginInitialR0161.Iterated k)
    (hΨ : ArithmeticThetaOriginInitialR0161.ExtendsTaylor k σ Ψ)
    (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g → Ψ (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) g) = ArithmeticThetaOriginInitialR0161.f5Taylor k r := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ χ hχ φ hφ σ hσ Ψ hΨ g hg
  classical
  let c : ℕ := 5
  have hc : 1 < c := by decide
  have hcop : Nat.Coprime c 6 := by decide
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  letI : NeZero c := ⟨by omega⟩
  letI : NeZero (c : k) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot l c
  let ζ : lˣ := Units.mk0 z (hz.ne_zero (by omega))
  have hζ : IsPrimitiveRoot (ζ : l) c := hz
  obtain ⟨Tl, Ml, hMl⟩ := exists_model l r hr h3
  letI : AlgebraicGeometry.IsIntegral (genericScheme l Ml) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral l h3 Ml hMl
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation l Ml hMl
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme l Ml) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure l Ml)
  obtain ⟨sl, hsl, _⟩ := marked_section_algebraization l r hr h3 Tl Ml hMl (zeroIndex r hr) 1
  obtain ⟨Gl, hGl, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    l r hr h3 Tl he Ml hMl sl hsl
  have Hχ : ∀ j : Fin r, ∃ χj, IsChartMap l Ml j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps l r hr h3 Tl Ml hMl j
    exact ⟨χj, hj⟩
  choose χl hχl using Hχ
  have Hφ : ∀ j : Fin r, ∃ φj, IsChartFieldMap l Ml (χl j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps l r hr h3 Tl Ml hMl j (χl j) (hχl j)
    exact ⟨φj, hj.1⟩
  choose φl hφl using Hφ
  obtain ⟨Hell, Hρ, HE⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι
  obtain ⟨ell, hell, _⟩ := Hell
  obtain ⟨ρ, hρ, _⟩ := Hρ
  obtain ⟨E, hE, _⟩ := HE ρ hρ.1
  obtain ⟨F, hF, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_model_base_change
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl
  obtain ⟨b, hb, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_generic_kato_square
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl F hF ell hell
    he s hs sl hsl G hG Gl hGl
  obtain ⟨α, hα, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_function_field_expansion
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 E hE χ hχ χl hχl F hF ell hell b hb.1 φ hφ φl hφl
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    l r hr h3 Tl he Ml hMl sl hsl Gl hGl ell b hb.2 α hα.1 c hc hcop).2 g hg
  obtain ⟨σl, hσl, _⟩ := completed_chart_taylor l
  obtain ⟨Ψl, hΨl, _⟩ := (faithful_taylor_field l σl hσl).2
  have H := split_field_taylor l r hr h3 he Tl Ml hMl sl hsl Gl hGl
    χl hχl φl hφl σl hσl Ψl hΨl ζ hζ (α g) hK
  rw [hα.2.2] at H
  have hsquare := coefficient_square k l ι ρ hρ.1 E hE σ hσ σl hσl Ψ hΨ Ψl hΨl
  have hval : Ψl (E (φ (zeroIndex r hr) g)) =
      coefficientHom _ _ (coefficientHom k l ι) (Ψ (φ (zeroIndex r hr) g)) :=
    RingHom.congr_fun hsquare _
  rw [hval, ← coefficient_f5 k l ι r hr] at H
  exact (coefficientHom _ _ (coefficientHom k l ι)).injective H

end ArithmeticThetaOriginInitialR0161
#print axioms ArithmeticThetaOriginInitialR0161.actual_kato_taylor
