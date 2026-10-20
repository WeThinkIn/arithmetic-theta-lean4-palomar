module

public import MarkedKatoValueDefinitionsR0159

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Actual completed marked specialization and its unique generic extension. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ArithmeticThetaMarkedKatoValuesR0159
namespace CompletedMarkedSpecializationR0159
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaKatoAnnularR0152.CompletedMarkedChartIdealR0152
open ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137
variable (k : Type) [Field k] [CharZero k]

private lemma specialization_base (a : kˣ) (b : PowerSeries k) :
    ArithmeticThetaAnnularThetaR0128.specialize k a
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = b :=
  ArithmeticThetaScaledAnnularR0050.specialization_base k 1 0 (by decide) (by decide)
    (a : k) a.ne_zero b

private lemma specialization_coordinates (a : kˣ) :
    ArithmeticThetaAnnularThetaR0128.specialize k a
      (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = PowerSeries.C (a : k) ∧
    ArithmeticThetaAnnularThetaR0128.specialize k a
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = PowerSeries.C ((a : k)⁻¹) * PowerSeries.X := by
  simpa only [ArithmeticThetaAnnularThetaR0128.specialize,
    ArithmeticThetaAnnularTorsionPrereqR0053.cx, ArithmeticThetaAnnularTorsionPrereqR0053.cy,
    pow_zero, mul_one, Nat.sub_zero, pow_one] using
    (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) (a : k) a.ne_zero).2

private lemma specialization_reduction (a : kˣ) (n : ℕ) :
    (trunc (PowerSeries k) PowerSeries.X n).comp
        (ArithmeticThetaAnnularThetaR0128.specialize k a) =
      (markedPoint k n a).comp (reduction k n) := by
  let f := (trunc (PowerSeries k) PowerSeries.X n).comp
    (ArithmeticThetaAnnularThetaR0128.specialize k a)
  let g := (markedPoint k n a).comp (reduction k n)
  have hb (b : PowerSeries k) : f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) := by
    simp only [f, g, RingHom.comp_apply, specialization_base, reduction_base, point_base_apply]
  have hx : f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) := by
    simp only [f, g, RingHom.comp_apply, (specialization_coordinates k a).1,
      reduction_x, point_x]
    rfl
  have hy : f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) := by
    simp only [f, g, RingHom.comp_apply, (specialization_coordinates k a).2,
      reduction_y, point_y, map_mul]
    change trunc _ PowerSeries.X n (PowerSeries.C ((a : k)⁻¹)) *
      trunc _ PowerSeries.X n PowerSeries.X =
      trunc _ PowerSeries.X n PowerSeries.X * trunc _ PowerSeries.X n (PowerSeries.C ((a⁻¹ : kˣ) : k))
    rw [Units.val_inv_eq_inv_val, mul_comm]
  have hfg : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hb
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  have ht : f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0 := by
    change (trunc _ PowerSeries.X n
      (ArithmeticThetaAnnularThetaR0128.specialize k a
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X))) ^ (n+1) = 0
    rw [specialization_base, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
  have hparam : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  have hkill (q : Chart k →+* R k n)
      (hq : q (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0)
      (z : Chart k) (hz : z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 (n+1)) :
      q z = 0 := by
    have hm := Ideal.mem_map_of_mem q hz
    rw [ArithmeticThetaScaledTateBridgeR0046.completedPower, hparam,
      Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm
    simpa only [Ideal.span_singleton_pow, hq, Ideal.span_singleton_zero, Ideal.mem_bot] using hm
  apply RingHom.ext
  intro z
  obtain ⟨b, hb'⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by decide)).2.2.2.2.2.2 (n+1) z
  have hf := hkill f ht _ hb'
  have hg := hkill g (by
    change g (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) ^ (n+1) = 0
    rw [← hb]
    exact ht) _ hb'
  rw [map_sub, sub_eq_zero] at hf hg
  exact hf.trans ((RingHom.congr_fun hfg _).trans hg.symm)

private lemma generic_extension (a : kˣ) :
    ∃! σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries k,
      IsSpecialization k a σ := by
  let f := (algebraMap (PowerSeries k) (LaurentSeries k)).comp
    (ArithmeticThetaAnnularThetaR0128.specialize k a)
  have hu : IsUnit (f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) := by
    change IsUnit (algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaAnnularThetaR0128.specialize k a
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X)))
    rw [specialization_base]
    exact IsLocalization.Away.algebraMap_isUnit (S := LaurentSeries k) PowerSeries.X
  refine ⟨IsLocalization.Away.lift (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) hu,
    IsLocalization.Away.lift_comp _ hu, ?_⟩
  intro σ hσ
  apply IsLocalization.ringHom_ext (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  exact hσ.trans (IsLocalization.Away.lift_comp _ hu).symm

end CompletedMarkedSpecializationR0159
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaKatoAnnularR0152

/-- Completed specialization is the actual marked morphism, and extends uniquely
on the chart ring after inverting the base parameter. -/
theorem completed_marked_specialization :
    ∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r)
    (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M) (j : Fin r) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j a p)
    (χ : chartScheme k ⟶ M.X), IsChartMap k M j χ →
      (Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularThetaR0128.specialize k a)) ≫ χ = p) ∧
      (∃! σ : ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k →+* LaurentSeries k,
        IsSpecialization k a σ) := by
  intro k _ _ r hr h3 he T M hM j a p hp χ hχ
  refine ⟨?_, CompletedMarkedSpecializationR0159.generic_extension k a⟩
  apply MarkedSectionAlgebraizationR0136.hom_ext k
  intro n
  rw [← Category.assoc, baseInclusion, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((trunc (PowerSeries k) PowerSeries.X n).comp
      (ArithmeticThetaAnnularThetaR0128.specialize k a))) ≫ χ = _
  rw [CompletedMarkedSpecializationR0159.specialization_reduction]
  change Spec.map (CommRingCat.ofHom (reduction k n) ≫
    CommRingCat.ofHom (ArithmeticThetaPolygonCohomologyR0131.markedPoint k n a)) ≫ χ = _
  rw [Spec.map_comp, Category.assoc, hχ.2 n, ← Category.assoc]
  exact (hp.2 n).symm

end ArithmeticThetaMarkedKatoValuesR0159
#print axioms ArithmeticThetaMarkedKatoValuesR0159.completed_marked_specialization
