module

public import PeriodOneNormDefinitionsR0248
public import PeriodOneCoefficientDescentR0246
public import FaithfulAnnularEvaluationR0156

@[expose] public section

/-! Literal coordinate descent and the faithful period-one affine evaluation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaPeriodOneNormR0248
namespace ChartEvaluationProof
open ArithmeticThetaTateSeries
open ArithmeticThetaPeriodOneR0246

lemma map_inv {K L : Type} [Field K] [Field L] (f : K →+* L)
    (p : PowerSeries K) : PowerSeries.map f p⁻¹ = (PowerSeries.map f p)⁻¹ := by
  have hc : PowerSeries.constantCoeff (PowerSeries.map f p) =
      f (PowerSeries.constantCoeff p) := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using PowerSeries.coeff_map f 0 p
  by_cases hp : PowerSeries.constantCoeff p = 0
  · rw [PowerSeries.inv_eq_zero.mpr hp, map_zero,
      PowerSeries.inv_eq_zero.mpr (by rw [hc, hp, map_zero])]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by rwa [hc, ne_eq, map_eq_zero])).2
    rw [← map_mul, PowerSeries.inv_mul_cancel p hp, map_one]

lemma map_partialX {K L : Type} [Field K] [Field L] (f : K →+* L)
    (d i : ℕ) (a : K) (N : ℕ) :
    PowerSeries.map f (partialX d i a N) = partialX d i (f a) N := by
  simp [partialX, xTerm, monomial, map_inv, map_ofNat]

lemma map_tateX {K L : Type} [Field K] [Field L] (f : K →+* L)
    (d i : ℕ) (a : K) : PowerSeries.map f (tateX d i a) = tateX d i (f a) := by
  ext n
  simpa only [PowerSeries.coeff_map, tateX, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff n) (map_partialX f d i a (n+1))

lemma map_coefficient {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L]
    (f : K →+* L) (j : Fin 3) :
    PowerSeries.map f (coefficient K j) = coefficient L j := by
  have h : PowerSeries.map f (ramifiedCoefficient K j) = ramifiedCoefficient L j := by
    fin_cases j <;> simp [ramifiedCoefficient,
      ArithmeticThetaCubicModelR0144.rootSeries, map_tateX]
  ext n
  simpa only [PowerSeries.coeff_map, coefficient, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff (4*n)) h

lemma expand_injective {K : Type} [CommRing K] :
    Function.Injective (PowerSeries.expand 4 (by decide) (R := K)) := by
  intro a b h
  ext n
  simpa using congrArg (PowerSeries.coeff (4*n)) h

lemma period_cubic (K : Type) [Field K] [CharZero K] (a : K)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    (tateY 1 0 a)^2 = (tateX 1 0 a)^3 +
      coefficient K 0 * (tateX 1 0 a)^2 +
      coefficient K 1 * tateX 1 0 a + coefficient K 2 := by
  apply expand_injective
  have hs := ArithmeticThetaTateBridges.ramified_substitution 4 1 0 a
    (by decide) ⟨by decide, by decide, ha0, fun _ => ha1⟩
  norm_num only [Nat.reduceMul] at hs
  simp only [map_pow, map_add, map_mul, period_one_coefficient_descent,
    ← hs.1, ← hs.2]
  have hc := ArithmeticThetaTateIdentities.general_annular_split_cubic
    2 0 a ⟨by decide, by decide, ha0, fun _ => ha1⟩
  norm_num only [Nat.reduceMul] at hc
  rw [hc]
  simp [ramifiedCoefficient, ArithmeticThetaCubicModelR0144.rootSeries]
  ring

variable (k : Type) [Field k] [CharZero k]

lemma w_ne_zero : ArithmeticThetaLaurentNormR0064.w k ≠ 0 := by
  simpa [ArithmeticThetaLaurentNormR0064.w] using
    (IsFractionRing.injective (LaurentPolynomial k) (Coeff k)).ne
      (LaurentPolynomial.isUnit_T (1 : ℤ) (R := k)).ne_zero

lemma w_transcendental : Transcendental k (ArithmeticThetaLaurentNormR0064.w k) := by
  simpa [ArithmeticThetaAnnularNormBridgeR0156.coordinate] using
    ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.coordinate_transcendental
      k 1 1 (by decide)

lemma w_ne_one : ArithmeticThetaLaurentNormR0064.w k ≠ 1 := by
  intro h
  have ht := w_transcendental k
  rw [h] at ht
  exact ht (isAlgebraic_one (R := k))

lemma baseMap_powerSeries (p : PowerSeries k) :
    baseMap k (HahnSeries.ofPowerSeries ℤ k p) =
      HahnSeries.ofPowerSeries ℤ (Coeff k)
        (PowerSeries.map (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k) p) := by
  ext n
  simp [baseMap, ArithmeticThetaRationalTateR0247.seriesMap,
    HahnSeries.map, PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

lemma literal_cubic :
    (ySeries k 1)^2 = (xSeries k 1)^3 +
      baseMap k ((periodCurve k).a₂) * (xSeries k 1)^2 +
      baseMap k ((periodCurve k).a₄) * xSeries k 1 +
      baseMap k ((periodCurve k).a₆) := by
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  have hb (p : PowerSeries k) : baseMap k (algebraMap (PowerSeries k) (LaurentSeries k) p) =
      HahnSeries.ofPowerSeries ℤ (Coeff k) (PowerSeries.map
        (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k) p) := baseMap_powerSeries k p
  have h := congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k))
    (period_cubic (Coeff k) (ArithmeticThetaLaurentNormR0064.w k)
      (w_ne_zero k) (w_ne_one k))
  simpa only [map_add, map_mul, map_pow, periodCurve, periodOneCurve,
    hb, map_coefficient, xSeries, ySeries] using h

lemma x_residue_transcendental : Transcendental k
    (PowerSeries.constantCoeff (tateX 1 0 (ArithmeticThetaLaurentNormR0064.w k))) := by
  have he := ArithmeticThetaTateIdentities.tateX_boundary_constant
    (k := Coeff k) 1 (by decide) (ArithmeticThetaLaurentNormR0064.w k)
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at he
  rw [he]
  intro hx
  let w := ArithmeticThetaLaurentNormR0064.w k
  let b : integralClosure k (Coeff k) := ⟨w * ((1-w)⁻¹)^2, hx.isIntegral⟩
  have ht := (w_transcendental k).integralClosure
  let p : Polynomial (integralClosure k (Coeff k)) :=
    Polynomial.C b * Polynomial.X^2 - Polynomial.C (2*b+1) * Polynomial.X + Polynomial.C b
  have hp : Polynomial.aeval w p = 0 := by
    simp only [p, Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
    change w * ((1-w)⁻¹)^2 * w^2 - (2*(w * ((1-w)⁻¹)^2)+1)*w +
      w * ((1-w)⁻¹)^2 = 0
    have hw : 1-w ≠ 0 := sub_ne_zero.mpr (Ne.symm (w_ne_one k))
    field_simp [hw]
    ring
  have hz : p = 0 := (transcendental_iff.mp ht) p hp
  have hb : b = 0 := by
    simpa [p, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one] using
      congrArg (fun q => Polynomial.coeff q 2) hz
  have h1 := congrArg (fun q => Polynomial.coeff q 1) hz
  simp [p, hb] at h1

lemma powerSeries_eval_injective {K L : Type} [Field K] [Field L] [Algebra K L]
    (x : PowerSeries L) (hx : Transcendental K (PowerSeries.constantCoeff x)) :
    Function.Injective (Polynomial.eval₂RingHom (PowerSeries.map (algebraMap K L)) x) := by
  let F := Polynomial.eval₂RingHom (PowerSeries.map (algebraMap K L)) x
  let t : Polynomial (PowerSeries K) := Polynomial.C PowerSeries.X
  have ht : F t = PowerSeries.X := by simp [F, t]
  have hdvd (p : Polynomial (PowerSeries K)) (hp : F p = 0) : t ∣ p := by
    have he : Polynomial.aeval (PowerSeries.constantCoeff x)
        (p.map PowerSeries.constantCoeff) = 0 := by
      have hh := congrArg PowerSeries.constantCoeff hp
      have hc : PowerSeries.constantCoeff.comp (PowerSeries.map (algebraMap K L)) =
          (algebraMap K L).comp PowerSeries.constantCoeff := by
        apply RingHom.ext
        intro a
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff, RingHom.comp_apply] using
          PowerSeries.coeff_map (algebraMap K L) 0 a
      change Polynomial.eval₂ (algebraMap K L) (PowerSeries.constantCoeff x)
        (p.map PowerSeries.constantCoeff) = 0
      rw [Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂]
      exact hh
    have hz := (transcendental_iff.mp hx) _ he
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    apply PowerSeries.X_dvd_iff.mpr
    simpa using congrArg (fun q => Polynomial.coeff q n) hz
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hpow : ∀ N : ℕ, ∀ p, F p = 0 → t^N ∣ p := by
    intro N
    induction N with
    | zero => intro p hp; simp
    | succ N ih =>
      intro p hp
      obtain ⟨q, rfl⟩ := hdvd p hp
      have hq : F q = 0 := by
        rw [map_mul, ht] at hp
        exact (mul_eq_zero.mp hp).resolve_left PowerSeries.X_ne_zero
      obtain ⟨r, hr⟩ := ih q hq
      refine ⟨r, ?_⟩
      rw [hr, pow_succ]
      ring
  apply Polynomial.ext
  intro n
  apply PowerSeries.ext
  intro m
  obtain ⟨q, hq⟩ := hpow (m+1) p hp
  rw [hq]
  rw [show t^(m+1) = Polynomial.C (PowerSeries.X^(m+1)) by simp [t],
    Polynomial.coeff_C_mul]
  simp [PowerSeries.coeff_X_pow_mul']

lemma x_polynomial_injective :
    Function.Injective (Polynomial.eval₂RingHom (baseMap k) (xSeries k 1)) := by
  let x : PowerSeries (Coeff k) := tateX 1 0 (ArithmeticThetaLaurentNormR0064.w k)
  let F := Polynomial.eval₂RingHom
    (PowerSeries.map (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k)) x
  have hF : Function.Injective F := powerSeries_eval_injective x (x_residue_transcendental k)
  let M := nonZeroDivisors (PowerSeries k)
  have he : (HahnSeries.ofPowerSeries ℤ (Coeff k)).comp F =
      Polynomial.eval₂RingHom ((baseMap k).comp
        (algebraMap (PowerSeries k) (LaurentSeries k))) (xSeries k 1) := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa [F] using (baseMap_powerSeries k c).symm
    · simp [F, x, xSeries]
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  let q := IsLocalization.integerNormalization M p
  have hq := IsLocalization.integerNormalization_eval₂_eq_zero M (baseMap k) p hp
  have hz : F q = 0 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [map_zero]
    exact (RingHom.congr_fun he q).trans hq
  have hq0 : q = 0 := hF (hz.trans (map_zero F).symm)
  exact (IsLocalization.integerNormalization_eq_zero_iff (M := M) le_rfl p).mp hq0

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

lemma chart_equiv (R : Type) [CommRing R] (W : WeierstrassCurve R) :
    ∃ e : ArithmeticThetaLegendreComparisonR0177.ChartRing R W ≃+*
        W.toAffine.CoordinateRing,
      (∀ b, e (ArithmeticThetaLegendreComparisonR0177.chartScalar R W b) =
        algebraMap R W.toAffine.CoordinateRing b) ∧
      e (xOverZ W.toProjective) = AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) ∧
      e (yOverZ W.toProjective) = AdjoinRoot.mk W.toAffine.polynomial Polynomial.X := by
  obtain ⟨f, hf, hc, hm⟩ := exists_zChartAway_equiv_coordinateRing W.toProjective
  refine ⟨RingEquiv.ofBijective f hf, ?_, ?_, ?_⟩
  · intro b
    rw [ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.chartScalar_apply]
    exact RingHom.congr_fun hc b
  · have h := hm 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (by simpa using MvPolynomial.isHomogeneous_X R (0 : Fin 3)))
    change f (xOverZ W.toProjective) = _ at h
    simpa only [MvPolynomial.aeval_X, Matrix.cons_val_zero] using! h
  · have h := hm 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (by simpa using MvPolynomial.isHomogeneous_X R (1 : Fin 3)))
    change f (yOverZ W.toProjective) = _ at h
    simpa only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero] using! h

lemma chart_unique (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    (a b : ChartRing k W →+* Series k)
    (ha : IsChartEvaluation k W r a) (hb : IsChartEvaluation k W r b) : a = b := by
  apply P2MW.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration.WMLocal.zChart_ringHom_ext W
  · apply RingHom.ext
    intro c
    have hs := ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.chartScalar_apply W c
    exact (congrArg a hs.symm).trans ((ha.1 c).trans
      ((hb.1 c).symm.trans (congrArg b hs)))
  · exact ha.2.1.trans hb.2.1.symm
  · exact ha.2.2.trans hb.2.2.symm

lemma evaluation_exists :
    ∃ a : ChartRing k (periodCurve k) →+* Series k,
      IsChartEvaluation k (periodCurve k) 1 a := by
  let W := periodCurve k
  let F : Polynomial (Polynomial (LaurentSeries k)) →+* Series k :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (baseMap k) (xSeries k 1)) (ySeries k 1)
  have hF : F W.toAffine.polynomial = 0 := by
    have hc := literal_cubic k
    simpa [F, W, WeierstrassCurve.Affine.polynomial, periodCurve, periodOneCurve,
      sub_eq_zero, Polynomial.eval₂_pow] using hc
  let g : W.toAffine.CoordinateRing →+* Series k :=
    Ideal.Quotient.lift (Ideal.span {W.toAffine.polynomial}) F (by
      change Ideal.span {W.toAffine.polynomial} ≤ RingHom.ker F
      apply Ideal.span_le.mpr
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact hF)
  obtain ⟨e, he, hx, hy⟩ := chart_equiv (LaurentSeries k) W
  refine ⟨g.comp e.toRingHom, ?_, ?_, ?_⟩
  · intro b
    change g (e _) = _
    rw [he]
    change F (Polynomial.C (Polynomial.C b)) = _
    simp [F]
  · change g (e _) = _
    rw [hx]
    change F (Polynomial.C Polynomial.X) = _
    simp [F]
  · change g (e _) = _
    rw [hy]
    change F Polynomial.X = _
    simp [F]

lemma chart_injective (a : ChartRing k (periodCurve k) →+* Series k)
    (ha : IsChartEvaluation k (periodCurve k) 1 a) : Function.Injective a := by
  let W := periodCurve k
  let B := W.toAffine.CoordinateRing
  letI : Module.Finite (Polynomial (LaurentSeries k)) B :=
    (WeierstrassCurve.Affine.monic_polynomial (W := W.toAffine)).finite_adjoinRoot
  obtain ⟨e, he, hx, hy⟩ := chart_equiv (LaurentSeries k) W
  let f : B →+* Series k := a.comp e.symm.toRingHom
  have hs (b : LaurentSeries k) :
      e.symm (algebraMap (LaurentSeries k) B b) =
        ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W b := by
    apply e.injective
    simpa using (he b).symm
  have hxx : e.symm (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X)) =
      xOverZ W.toProjective := by
    apply e.injective
    simpa using hx.symm
  have hfC : f.comp (algebraMap (Polynomial (LaurentSeries k)) B) =
      Polynomial.eval₂RingHom (baseMap k) (xSeries k 1) := by
    apply Polynomial.ringHom_ext
    · intro b
      change a (e.symm (algebraMap (LaurentSeries k) B b)) = _
      rw [hs]
      simpa [W] using ha.1 b
    · change a (e.symm (AdjoinRoot.mk W.toAffine.polynomial
        (Polynomial.C Polynomial.X))) = _
      rw [hxx]
      simpa [W] using ha.2.1
  have hf : Function.Injective f := by
    apply (RingHom.injective_iff_ker_eq_bot f).mpr
    apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial (LaurentSeries k))
    change RingHom.ker (f.comp (algebraMap (Polynomial (LaurentSeries k)) B)) = ⊥
    rw [hfC]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (x_polynomial_injective k)
  intro b c hbc
  have h := hf (show f (e b) = f (e c) by
    change a (e.symm (e b)) = a (e.symm (e c))
    simpa only [RingEquiv.symm_apply_apply] using hbc)
  exact e.injective h

end ChartEvaluationProof
/-- The full literal period-one Tate coordinates define the unique faithful
map on the concrete affine chart, with the frozen coefficient embedding. -/
theorem period_one_chart_evaluation :
    ∀ (k : Type) [Field k] [CharZero k],
      ∃! a : ChartRing k (periodCurve k) →+* Series k,
        IsChartEvaluation k (periodCurve k) 1 a ∧ Function.Injective a := by
  intro k _ _
  obtain ⟨a, ha⟩ := ChartEvaluationProof.evaluation_exists k
  refine ⟨a, ⟨ha, ChartEvaluationProof.chart_injective k a ha⟩, ?_⟩
  intro b hb
  exact ChartEvaluationProof.chart_unique k (periodCurve k) 1 b a hb.1 ha

#print axioms period_one_chart_evaluation
end ArithmeticThetaPeriodOneNormR0248
