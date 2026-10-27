import CompletedScalingExtensionR0153
import MarkedFieldActionR0153

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153.CompletedActionEquivariance
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaKatoAnnularR0152
variable (k : Type u) [Field k] [CharZero k]

private abbrev chartIdeal : Ideal (Chart k) :=
  Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}

omit [CharZero k] in
private lemma parameter_eq :
    ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
  simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]


private lemma reduction_complete (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
        (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec
    (Classical.choose_spec (finite_stage_completion_comparison k n))).1 a

private lemma approx (n : ℕ) (z : Chart k) :
    ∃ a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k,
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈ chartIdeal k ^ (n+1) := by
  obtain ⟨a, ha⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by omega)).2.2.2.2.2.2 (n+1) z
  refine ⟨ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 a, ?_⟩
  change z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k _ ∈
    (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1}) ^ (n+1) at ha
  rw [parameter_eq] at ha
  exact ha


private lemma reduction_base (n : ℕ) :
    (ArithmeticThetaKatoAnnularR0152.reduction k n).comp (ArithmeticThetaAnnularTorsionPrereqR0053.base k) =
      (base k n).comp (trunc (PowerSeries k) PowerSeries.X n) := by
  apply RingHom.ext
  intro a
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) a)) = _
  rw [reduction_complete]
  rfl

private lemma reduction_base_apply (n : ℕ) (b : PowerSeries k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      base k n (trunc (PowerSeries k) PowerSeries.X n b) :=
  RingHom.congr_fun (reduction_base k n) b


private lemma reduction_x (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_complete]
  rfl

private lemma reduction_y (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [reduction_complete]
  rfl


lemma scaling_reduction (a : kˣ) (e : Chart k ≃+* Chart k)
    (he : IsScaling k a e) (n : ℕ) :
    (ArithmeticThetaKatoAnnularR0152.reduction k n).comp e.toRingHom =
      (TowerScalarTranslation.ringMap k n a).comp
        (ArithmeticThetaKatoAnnularR0152.reduction k n) := by
  let ρ := ArithmeticThetaKatoAnnularR0152.reduction k n
  let f := ρ.comp e.toRingHom
  let g := (TowerScalarTranslation.ringMap k n a).comp ρ
  have hn : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      change ρ (e (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) =
        TowerScalarTranslation.ringMap k n a
          (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b))
      rw [he.1]
      simp only [ρ, reduction_base_apply, TowerScalarTranslation.ringMap_base]
    · intro i
      fin_cases i
      · change ρ (e (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) =
          TowerScalarTranslation.ringMap k n a (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k))
        rw [he.2.1]
        simp only [ρ, map_mul, reduction_base_apply, reduction_x, TowerScalarTranslation.ringMap_x]
        rfl
      · change ρ (e (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) =
          TowerScalarTranslation.ringMap k n a (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k))
        rw [he.2.2]
        simp only [ρ, map_mul, reduction_base_apply, reduction_y, TowerScalarTranslation.ringMap_y]
        rfl
  have hm : (chartIdeal k).map e.toRingHom = chartIdeal k := by
    change (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X}).map e.toRingHom = _
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {e (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X)} = _
    rw [he.1]
    rfl
  apply RingHom.ext
  intro z
  obtain ⟨b, hb⟩ := approx k n z
  have hbρ : ρ z = ρ (ArithmeticThetaAnnularTorsionPrereqR0053.complete k b) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (CompletedChartFieldMaps.reduction_kernel k n ▸ hb :
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k b ∈ RingHom.ker ρ)
  have hbe : ρ (e z) = ρ (e (ArithmeticThetaAnnularTorsionPrereqR0053.complete k b)) := by
    have hh := Ideal.mem_map_of_mem e.toRingHom hb
    rw [Ideal.map_pow, hm] at hh
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (show e z - e (ArithmeticThetaAnnularTorsionPrereqR0053.complete k b) ∈
      RingHom.ker ρ from ?_)
    rw [CompletedChartFieldMaps.reduction_kernel]
    simpa only [map_sub, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using hh
  change ρ (e z) = TowerScalarTranslation.ringMap k n a (ρ z)
  rw [hbe, hbρ]
  exact RingHom.congr_fun hn b

lemma scaling_inverse (a : kˣ) (e : Chart k ≃+* Chart k) (he : IsScaling k a e) :
    IsScaling k a⁻¹ e.symm := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    apply e.injective
    rw [e.apply_symm_apply, he.1]
  · apply e.injective
    rw [e.apply_symm_apply, map_mul, he.1, he.2.1, ← mul_assoc, ← map_mul, ← map_mul]
    simp
  · apply e.injective
    rw [e.apply_symm_apply, map_mul, he.1, he.2.2, ← mul_assoc, ← map_mul, ← map_mul]
    simp

lemma scaling_base (a : kˣ) (e : Chart k ≃+* Chart k) (he : IsScaling k a e) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartBase k = chartBase k := by
  rw [chartBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext he.1

lemma scaling_reduction_square (a : kˣ) (e : Chart k ≃+* Chart k)
    (he : IsScaling k a e) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (ArithmeticThetaKatoAnnularR0152.reduction k n)) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) =
      TowerScalarTranslation.chartMap k n a ≫
        Spec.map (CommRingCat.ofHom (ArithmeticThetaKatoAnnularR0152.reduction k n)) := by
  rw [TowerScalarTranslation.chartMap, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (scaling_reduction k a e he n)

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma chart_equivariance (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv)
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (i j : Fin r) (a : kˣ) (e : Chart k ≃+* Chart k) (he : IsScaling k a e) :
    χ j ≫ MarkedFieldAction.modelTranslation k M rot scal i a =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ χ (shift (hr := hr) j i) := by
  let ψ := Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    χ j ≫ MarkedFieldAction.modelTranslation k M rot scal i a
  have hψ : IsChartMap k M (shift (hr := hr) j i) ψ := by
    refine ⟨?_, fun n => ?_⟩
    · simp only [ψ, Category.assoc, MarkedFieldAction.model_over k M rot scal inv ha,
        (hχ j).1]
      exact scaling_base k a⁻¹ e.symm (scaling_inverse k a e he)
    · simp only [ψ, ← Category.assoc]
      rw [scaling_reduction_square k a⁻¹ e.symm (scaling_inverse k a e he)]
      simp only [Category.assoc, (hχ j).2 n]
      change TowerScalarTranslation.chartMap k n a⁻¹ ≫
        AlgebraizedActionLawsR0137.modelChart M n j ≫
        (iterateHom rot.hom i.val ≫ (scal a).hom) = _
      rw [← Category.assoc (AlgebraizedActionLawsR0137.modelChart M n j),
        AlgebraizedActionLawsR0137.chart_iterate_rotation M ha.1,
        AlgebraizedActionLawsR0137.chart_scalar M (ha.2.1 a),
        ← Category.assoc, AlgebraizedActionLawsR0137.chartMap_mul]
      simp only [inv_mul_cancel, AlgebraizedActionLawsR0137.chartMap_one, Category.id_comp]
      congr 2
      apply Fin.ext
      exact AlgebraizedActionLawsR0137.next_iterate_val i.val j
  have hh : ψ = χ (shift (hr := hr) j i) :=
    (completed_model_chart_maps k r hr h3 T M hM _).unique hψ (hχ _)
  have hcancel : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) = 𝟙 (chartScheme k) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.toRingHom.comp e.symm.toRingHom)) = _
    simp [chartScheme]
  rw [← hh]
  simp only [ψ, ← Category.assoc, hcancel]
  change _ = (𝟙 (chartScheme k) ≫ χ j) ≫ _
  rw [Category.id_comp]

end ArithmeticThetaSplitNormR0153.CompletedActionEquivariance

namespace ArithmeticThetaSplitNormR0153
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152 CompletedActionEquivariance

/-- Pullback by the specified actual translation agrees with completed scaling
on the cyclically shifted chart, for every rational function including zero. -/
theorem completed_action_equivariance :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv) (σ : Fin r → kˣ → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) ≃+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)))) (hσ : ArithmeticThetaSplitNormR0153.IsFieldAction k M rot scal inv ha σ) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∀ (i : Fin r) (a : kˣ) (e : ArithmeticThetaKatoAnnularR0152.Chart k ≃+* ArithmeticThetaKatoAnnularR0152.Chart k) (E : ArithmeticThetaKatoAnnularR0152.ChartField k ≃+* ArithmeticThetaKatoAnnularR0152.ChartField k), ArithmeticThetaSplitNormR0153.IsScaling k a e → ArithmeticThetaSplitNormR0153.ExtendsScaling k e E → ∀ (j : Fin r) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), φ j (σ i a g) = E (φ (ArithmeticThetaSplitNormR0153.shift (hr := hr) j i) g) := by
  intro k _ _ r hr h3 T heven M hM _ rot scal inv ha σ hσ χ hχ φ hφ i a e E he hE j g
  have hinc : translation k M rot scal inv ha i a ≫ genericInclusion k M =
      genericInclusion k M ≫ MarkedFieldAction.modelTranslation k M rot scal i a := by
    rw [MarkedFieldAction.translation_generic]
    exact pullback.lift_fst _ _ _
  have hEsq : Spec.map (CommRingCat.ofHom E.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (chartToField k)) =
      Spec.map (CommRingCat.ofHom (chartToField k)) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext hE
  have heq : (φ j).comp (σ i a).toRingHom =
      E.toRingHom.comp (φ (shift (hr := hr) j i)) := by
    suffices hh : CommRingCat.ofHom ((φ j).comp (σ i a).toRingHom) =
        CommRingCat.ofHom (E.toRingHom.comp (φ (shift (hr := hr) j i))) from
      congrArg CommRingCat.Hom.hom hh
    apply Spec.map_injective
    letI : IsOpenImmersion (genericInclusion k M) :=
      AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
    apply (cancel_mono ((genericScheme k M).fromSpecStalk
      (_root_.genericPoint (genericScheme k M)))).mp
    apply (cancel_mono (genericInclusion k M)).mp
    change (Spec.map (CommRingCat.ofHom (σ i a).toRingHom ≫ CommRingCat.ofHom (φ j)) ≫ _) ≫ _ =
      (Spec.map (CommRingCat.ofHom (φ (shift (hr := hr) j i)) ≫ CommRingCat.ofHom E.toRingHom) ≫ _) ≫ _
    rw [Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% (hσ i a), hinc]
    rw [reassoc_of% (hφ j)]
    rw [chart_equivariance k h3 M hM rot scal inv ha χ hχ i j a e he]
    rw [← Category.assoc, ← hEsq, Category.assoc]
    rw [hφ (shift (hr := hr) j i)]
  exact RingHom.congr_fun heq g

#print axioms completed_action_equivariance
end ArithmeticThetaSplitNormR0153
