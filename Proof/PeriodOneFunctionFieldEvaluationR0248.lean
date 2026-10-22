module

public import PeriodOneChartEvaluationR0248

@[expose] public section

-- Preserve original field inference without overriding specialized local-ring instances.
attribute [local instance 999] HenselianLocalRing.toIsLocalRing

/-! Extension of the literal affine evaluation to the projective function field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaPeriodOneNormR0248
namespace FunctionFieldEvaluationProof
open CategoryTheory AlgebraicGeometry

variable (k : Type) [Field k] [CharZero k]

/-- An injective affine evaluation reaches the actual projective generic point. -/
lemma generic_image (W : WeierstrassCurve (LaurentSeries k)) [IsIntegral (Curve k W)]
    (a : ChartRing k W →+* Series k) (ha : Function.Injective a) :
    (Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W)
      (IsLocalRing.closedPoint (Series k)) = genericPoint (Curve k W) := by
  letI : IsDomain (ChartRing k W) := Function.Injective.isDomain a ha
  letI : IsOpenImmersion (chartInclusion k W) := by
    unfold chartInclusion ArithmeticThetaLegendreComparisonR0177.chartInclusion
    infer_instance
  letI : IsDominant (Spec.map (CommRingCat.ofHom a)) := by
    constructor
    change DenseRange (PrimeSpectrum.comap a)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot a).mp ha]
    exact bot_le
  have hg : Spec.map (CommRingCat.ofHom a)
      (genericPoint (Spec (CommRingCat.of (Series k)))) =
      genericPoint (Spec (CommRingCat.of (ChartRing k W))) := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    have h := (genericPoint_spec (Spec (CommRingCat.of (Series k)))).image
      (Spec.map (CommRingCat.ofHom a)).continuous
    simpa only [Set.image_univ,
      (Spec.map (CommRingCat.ofHom a)).denseRange.closure_range] using h
  have hp : IsLocalRing.closedPoint (Series k) =
      genericPoint (Spec (CommRingCat.of (Series k))) := Subsingleton.elim _ _
  change (chartInclusion k W)
    ((Spec.map (CommRingCat.ofHom a)) (IsLocalRing.closedPoint (Series k))) = _
  rw [hp, hg]
  exact genericPoint_eq_of_isOpenImmersion (chartInclusion k W)

/-- The stalk universal property gives the field map and its geometric square. -/
lemma extend (W : WeierstrassCurve (LaurentSeries k)) [IsIntegral (Curve k W)]
    (a : ChartRing k W →+* Series k) (ha : Function.Injective a) :
    ∃ ev : (Curve k W).functionField →+* Series k,
      Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W =
        Spec.map (CommRingCat.ofHom ev) ≫
          (Curve k W).fromSpecStalk (genericPoint (Curve k W)) := by
  have hgeneral {X : Scheme} (F : Type) [Field F]
      (f : Spec (CommRingCat.of F) ⟶ X) (x : X)
      (hx : f (IsLocalRing.closedPoint F) = x) :
      ∃ ev : X.presheaf.stalk x →+* F,
        Spec.map (CommRingCat.ofHom ev) ≫ X.fromSpecStalk x = f := by
    subst x
    exact ⟨(Scheme.stalkClosedPointTo f).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩
  obtain ⟨ev, hev⟩ := hgeneral (Series k)
    (Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W) _
    (generic_image k W a ha)
  exact ⟨ev, hev.symm⟩

/-- The prescribed scalar and coordinate images determine the field map. -/
lemma unique (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    [IsIntegral (Curve k W)]
    (ev ev' : (Curve k W).functionField →+* Series k)
    (h : IsEvaluation k W r ev) (h' : IsEvaluation k W r ev') : ev = ev' := by
  obtain ⟨a, ha, hs⟩ := h
  obtain ⟨a', ha', hs'⟩ := h'
  have he : a = a' := ChartEvaluationProof.chart_unique k W r a a' ha ha'
  suffices hh : CommRingCat.ofHom ev = CommRingCat.ofHom ev' from
    congrArg CommRingCat.Hom.hom hh
  apply Spec.map_injective
  apply (cancel_mono ((Curve k W).fromSpecStalk (genericPoint (Curve k W)))).mp
  rw [← hs, ← hs', he]

end FunctionFieldEvaluationProof

/-- The unique faithful extension preserves the actual generic-point square. -/
theorem period_one_function_field_evaluation :
    ∀ (k : Type) [Field k] [CharZero k]
      [AlgebraicGeometry.IsIntegral (Curve k (periodCurve k))],
      ∃! ev : (Curve k (periodCurve k)).functionField →+* Series k,
        IsEvaluation k (periodCurve k) 1 ev ∧ Function.Injective ev := by
  intro k _ _ _
  obtain ⟨a, ⟨ha, hi⟩, _⟩ := period_one_chart_evaluation k
  obtain ⟨ev, hev⟩ := FunctionFieldEvaluationProof.extend k (periodCurve k) a hi
  refine ⟨ev, ⟨⟨a, ha, hev⟩, ev.injective⟩, ?_⟩
  intro ev' h'
  exact FunctionFieldEvaluationProof.unique k (periodCurve k) 1 ev' ev h'.1 ⟨a, ha, hev⟩

#print axioms period_one_function_field_evaluation
end ArithmeticThetaPeriodOneNormR0248
