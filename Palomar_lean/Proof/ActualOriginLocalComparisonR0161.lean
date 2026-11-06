module

public import FaithfulTaylorFieldR0161
public import CompletedMarkedSpecializationR0159
public import KatoAnnularDivisorR0152
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import OriginInitialDefinitionsR0161

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The local comparison uses the actual Taylor arc and the pulled-back
identity ideal. Helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161.ActualOriginLocalComparisonR0161
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133.MarkedIdealTowerBaseChangeR0133

private lemma local_arc {R : Type} [CommRing R] [IsLocalRing R]
    {X : Scheme} (f : Spec (.of R) ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint R) = x) :
    ∃ κ : X.presheaf.stalk x →+* R, IsLocalHom κ ∧
      Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk x = f := by
  subst x
  exact ⟨(Scheme.stalkClosedPointTo f).hom, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

private lemma arc_field_square {R L : Type} [CommRing R] [Field L]
    {X : Scheme} [IsIntegral X] (x : X)
    (f : Spec (.of R) ⟶ X) (ι : R →+* L) (E : X.functionField →+* L)
    (hE : Spec.map (CommRingCat.ofHom E) ≫ X.fromSpecStalk (_root_.genericPoint X) =
      Spec.map (CommRingCat.ofHom ι) ≫ f)
    (κ : X.presheaf.stalk x →+* R)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk x = f) :
    ι.comp κ = E.comp (algebraMap (X.presheaf.stalk x) X.functionField) := by
  suffices h : CommRingCat.ofHom (ι.comp κ) =
      CommRingCat.ofHom (E.comp (algebraMap (X.presheaf.stalk x) X.functionField)) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk x)).mp
  change Spec.map (CommRingCat.ofHom κ ≫ CommRingCat.ofHom ι) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) ≫
      CommRingCat.ofHom E) ≫ _
  simp only [Spec.map_comp, Category.assoc]
  have hi : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (_root_.genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((_root_.genericPoint_spec X).specializes trivial)
  rw [hκ, hi]
  exact hE.symm

private lemma arc_value_square (F : Type) [Field F]
    {X : Scheme} (e : Spec (.of F) ⟶ X)
    (f : Spec (.of (PowerSeries F)) ⟶ X)
    (hf : Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := F))) ≫ f = e)
    (κ : X.presheaf.stalk (e (IsLocalRing.closedPoint F)) →+* PowerSeries F)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫
      X.fromSpecStalk (e (IsLocalRing.closedPoint F)) = f) :
    PowerSeries.constantCoeff.comp κ = (Scheme.stalkClosedPointTo e).hom := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (e (IsLocalRing.closedPoint F)))).mp
  change Spec.map (CommRingCat.ofHom κ ≫ CommRingCat.ofHom PowerSeries.constantCoeff) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, hκ, hf]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk e).symm

private lemma arc_ideal_square (F : Type) [Field F]
    {X : Scheme} (e : Spec (.of F) ⟶ X) [IsClosedImmersion e]
    (f : Spec (.of (PowerSeries F)) ⟶ X)
    (κ : X.presheaf.stalk (e (IsLocalRing.closedPoint F)) →+* PowerSeries F)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫
      X.fromSpecStalk (e (IsLocalRing.closedPoint F)) = f) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (e (IsLocalRing.closedPoint F)))).map κ =
      specIdeal (e.ker.comap f) := by
  rw [← hκ, Scheme.IdealSheafData.comap_comp]
  change _ = specIdeal ((e.ker.comap (X.fromSpecStalk _)).comap
    (Spec.map (CommRingCat.ofHom κ)))
  rw [specIdeal_comap, ArithmeticThetaKatoAnnularR0152.AnnularDivisor.point_stalk_ideal]

private lemma reflects_powers {A F : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field F]
    (κ : A →+* PowerSeries F) [IsLocalHom κ] (hi : Function.Injective κ)
    (hm : (IsLocalRing.maximalIdeal A).map κ = Ideal.span {PowerSeries.X})
    (b : A) (n : ℕ) :
    b ∈ (IsLocalRing.maximalIdeal A)^n ↔
      ∀ i : ℕ, i < n → PowerSeries.coeff i (κ b) = 0 := by
  letI := κ.toAlgebra
  letI : Module.IsTorsionFree A (PowerSeries F) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  letI : Module.Flat A (PowerSeries F) := inferInstance
  letI : Module.FaithfullyFlat A (PowerSeries F) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hc := Ideal.comap_map_eq_self_of_faithfullyFlat (B := PowerSeries F)
    ((IsLocalRing.maximalIdeal A)^n)
  change Ideal.comap κ (Ideal.map κ ((IsLocalRing.maximalIdeal A)^n)) = _ at hc
  rw [Ideal.map_pow, hm, Ideal.span_singleton_pow] at hc
  rw [← hc]
  change κ b ∈ Ideal.span {PowerSeries.X ^ n} ↔ _
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]


open ArithmeticThetaAnnularTorsionPrereqR0053 hiding Chart
variable (k : Type) [Field k] [CharZero k]

private lemma constant_specialization (σ : Chart k →+* Bivariate k)
    (hσ : IsChartTaylor k σ) :
    PowerSeries.constantCoeff.comp σ = ArithmeticThetaAnnularThetaR0128.specialize k 1 := by
  have he : SectionAt k true 1 (PowerSeries.constantCoeff.comp σ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply RingHom.ext
      intro b
      change PowerSeries.constantCoeff (σ (base k b)) = b
      rw [hσ.1, PowerSeries.constantCoeff_C]
    · change PowerSeries.constantCoeff (σ (cx k)) = PowerSeries.C 1
      rw [hσ.2.1]
      simp
    · change PowerSeries.constantCoeff (σ (cy k)) = PowerSeries.C (1 : k)⁻¹ * PowerSeries.X
      rw [hσ.2.2.1]
      simp [zInverse, PowerSeries.constantCoeff_invOfUnit]
    · intro n b hb
      simpa only [RingHom.comp_apply, PowerSeries.coeff_zero_eq_constantCoeff]
        using hσ.2.2.2 n b hb 0
  have hs : SectionAt k true 1 (ArithmeticThetaAnnularThetaR0128.specialize k 1) := by
    have hc := ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) 1 (one_ne_zero)
    have hf := (Classical.choose_spec
      (ArithmeticThetaScaledTateCompletionExtensionR0048.completion_specialization_exists_and_filtered
        k 1 0 (by decide) (by decide) 1 (one_ne_zero))).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply RingHom.ext
      intro b
      exact ArithmeticThetaScaledAnnularR0050.specialization_base k 1 0
        (by decide) (by decide) 1 (one_ne_zero) b
    · simpa [ArithmeticThetaAnnularThetaR0128.specialize, coord, cx] using hc.2.1
    · simpa [ArithmeticThetaAnnularThetaR0128.specialize, coord, cy] using hc.2.2
    · intro n b hb
      simpa only [ArithmeticThetaAnnularThetaR0128.specialize, Units.val_one,
        ArithmeticThetaScaledAnnularR0050.specialization,
        ArithmeticThetaScaledTateCompletionExtensionR0048.targetIdeal, one_mul] using hf n b hb
  exact (completed_section_kernels k true 1 one_ne_zero).1.unique he hs

private def chartArc (σ : Chart k →+* Bivariate k) :
    Chart k →+* PowerSeries (LaurentSeries k) :=
  (PowerSeries.map (HahnSeries.ofPowerSeries ℤ k)).comp σ

omit [CharZero k] in
private lemma chartArc_base (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (b : PowerSeries k) :
    chartArc k σ (base k b) = PowerSeries.C (algebraMap (PowerSeries k) (LaurentSeries k) b) := by
  simp only [chartArc, RingHom.comp_apply, hσ.1, PowerSeries.map_C]
  rfl

private lemma chartArc_constant (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    PowerSeries.constantCoeff.comp (chartArc k σ) =
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp
        (ArithmeticThetaAnnularThetaR0128.specialize k 1) := by
  apply RingHom.ext
  intro b
  change PowerSeries.constantCoeff (PowerSeries.map (HahnSeries.ofPowerSeries ℤ k) (σ b)) = _
  change (HahnSeries.ofPowerSeries ℤ k) (PowerSeries.constantCoeff (σ b)) = _
  exact congrArg (HahnSeries.ofPowerSeries ℤ k)
    (RingHom.congr_fun (constant_specialization k σ hσ) b)

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

private def arc (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    Spec (.of (PowerSeries (LaurentSeries k))) ⟶ genericScheme k M :=
  pullback.lift (Spec.map (CommRingCat.ofHom (chartArc k σ)) ≫ χ)
    (Spec.map (CommRingCat.ofHom PowerSeries.C)) (by
      rw [Category.assoc, hχ]
      change Spec.map (CommRingCat.ofHom (chartArc k σ)) ≫
        Spec.map (CommRingCat.ofHom (base k)) =
        Spec.map (CommRingCat.ofHom PowerSeries.C) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      exact chartArc_base k σ hσ)

private lemma arc_inclusion (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    arc k M χ hχ σ hσ ≫ genericInclusion k M =
      Spec.map (CommRingCat.ofHom (chartArc k σ)) ≫ χ := pullback.lift_fst _ _ _


private lemma arc_identity (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := LaurentSeries k))) ≫
      arc k M χ hχ.1 σ hσ = Origin k M s hs.1 := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, arc_inclusion, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff.comp (chartArc k σ))) ≫ χ = _
  rw [chartArc_constant k σ hσ]
  change Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularThetaR0128.specialize k 1) ≫
    CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫ χ = _
  rw [Spec.map_comp, Category.assoc,
    (ArithmeticThetaMarkedKatoValuesR0159.completed_marked_specialization
      k r hr h3 he T M hM (zeroIndex r hr) 1 s hs χ hχ).1]
  exact (genericPoint_inclusion k M s hs.1).symm

private lemma arc_point (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    arc k M χ hχ.1 σ hσ (IsLocalRing.closedPoint (PowerSeries (LaurentSeries k))) =
      Origin k M s hs.1 (IsLocalRing.closedPoint (LaurentSeries k)) := by
  have hp : (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := LaurentSeries k))))
        (IsLocalRing.closedPoint (LaurentSeries k)) =
      IsLocalRing.closedPoint (PowerSeries (LaurentSeries k)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap PowerSeries.constantCoeff (IsLocalRing.maximalIdeal (LaurentSeries k)) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact PowerSeries.ker_coeff_eq_max_ideal
  have h := congrArg (fun f : Spec (.of (LaurentSeries k)) ⟶ genericScheme k M =>
    f (IsLocalRing.closedPoint (LaurentSeries k))) (arc_identity k h3 he M hM s hs χ hχ σ hσ)
  simpa only [Scheme.Hom.comp_apply, hp] using h

private lemma arc_identity_ideal (h3 : 3 ≤ r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    specIdeal ((Origin k M s hs.1).ker.comap (arc k M χ hχ.1 σ hσ)) =
      Ideal.span {PowerSeries.X} := by
  rw [← genericPoint_ker k M hM s hs.1, ← Scheme.IdealSheafData.comap_comp,
    arc_inclusion, Scheme.IdealSheafData.comap_comp]
  change specIdeal ((s.ker.comap χ).comap (Spec.map (CommRingCat.ofHom (chartArc k σ)))) = _
  rw [specIdeal_comap]
  change (markedChartIdeal k M s χ).map (chartArc k σ) = _
  rw [(completed_marked_chart_ideal k r hr h3 T M hM
    (zeroIndex r hr) (zeroIndex r hr) 1 s hs χ hχ).1, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  simp only [markedEquation, ite_true,
    if_neg (CompletedMarkedChartIdealR0152.next_ne hr h3 (zeroIndex r hr)),
    mul_one, chartArc, RingHom.comp_apply, map_sub, hσ.2.1, map_one,
    map_add, PowerSeries.map_X, Units.val_one, map_one, add_sub_cancel_left]

private lemma arc_field (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ArithmeticThetaKatoAnnularR0152.ChartField k)
    (hφ : IsChartFieldMap k M χ φ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Spec.map (CommRingCat.ofHom (Ψ.comp φ)) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) =
    Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ (LaurentSeries k))) ≫
      arc k M χ hχ σ hσ := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, Category.assoc, arc_inclusion]
  change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom Ψ) ≫ _ ≫ _ = _
  rw [Spec.map_comp, Category.assoc, hφ, ← Category.assoc,
    ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (Ψ.comp (chartToField k))) ≫ χ =
    Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ (LaurentSeries k)).comp
      (chartArc k σ))) ≫ χ
  rw [hΨ]
  rfl

end ArithmeticThetaOriginInitialR0161.ActualOriginLocalComparisonR0161

namespace ArithmeticThetaOriginInitialR0161
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ActualOriginLocalComparisonR0161

/-- The actual identity-stalk Taylor map preserves the specified field expansion,
residue evaluation, and every power of the maximal ideal. -/
theorem actual_origin_local_comparison :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (σ : ArithmeticThetaOriginInitialR0161.Chart k →+* ArithmeticThetaOriginInitialR0161.Bivariate k) (hσ : ArithmeticThetaOriginInitialR0161.IsChartTaylor k σ) (Ψ : ArithmeticThetaOriginInitialR0161.ChartField k →+* ArithmeticThetaOriginInitialR0161.Iterated k) (hΨ : ArithmeticThetaOriginInitialR0161.ExtendsTaylor k σ Ψ), ∃! κ : ArithmeticThetaOriginInitialR0161.OriginStalk k M s hs.1 →+* PowerSeries (LaurentSeries k), ArithmeticThetaOriginInitialR0161.IsOriginTaylor k M s hs.1 (Ψ.comp (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr))) κ := by
  intro k _ _ r hr h3 he T M hM s hs _ _ χ hχ φ hφ σ hσ Ψ hΨ
  let f := arc k M (χ (zeroIndex r hr)) (hχ _).1 σ hσ
  let E := Ψ.comp (φ (zeroIndex r hr))
  let e := Origin k M s hs.1
  let x := e (IsLocalRing.closedPoint (LaurentSeries k))
  let ι := HahnSeries.ofPowerSeries ℤ (LaurentSeries k)
  have hf : Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ f = e :=
    arc_identity k h3 he M hM s hs _ (hχ _) σ hσ
  have hx : f (IsLocalRing.closedPoint (PowerSeries (LaurentSeries k))) = x :=
    arc_point k h3 he M hM s hs _ (hχ _) σ hσ
  obtain ⟨κ, hlocal, hκ⟩ := local_arc f x hx
  letI : IsLocalHom κ := hlocal
  have hfield : ι.comp κ = E.comp (algebraMap (OriginStalk k M s hs.1)
      (genericScheme k M).functionField) :=
    arc_field_square x f ι E (arc_field k M _ (hχ _).1 _ (hφ _) σ hσ Ψ hΨ) κ hκ
  have hi : Function.Injective κ := by
    intro a b hab
    apply IsFractionRing.injective (OriginStalk k M s hs.1) (genericScheme k M).functionField
    apply E.injective
    exact (RingHom.congr_fun hfield a).symm.trans
      ((congrArg ι hab).trans (RingHom.congr_fun hfield b))
  letI : IsClosedImmersion e := genericPoint_closed k M hM s hs.1
  have hm : (IsLocalRing.maximalIdeal (OriginStalk k M s hs.1)).map κ =
      Ideal.span {PowerSeries.X} :=
    (arc_ideal_square (LaurentSeries k) e f κ hκ).trans
      (arc_identity_ideal k h3 M hM s hs _ (hχ _) σ hσ)
  have hclosed : IsClosed ({x} : Set (genericScheme k M)) := by
    have heq : Set.range e = {x} := Set.range_eq_singleton fun a =>
      congrArg e (Subsingleton.elim a (IsLocalRing.closedPoint (LaurentSeries k)))
    rw [← heq]
    exact e.isClosedEmbedding.isClosed_range
  letI : SmoothOfRelativeDimension 1 (genericStructure k M) := generic_relative_one k h3 M hM s hs
  letI : IsIntegral (CategoryTheory.Limits.pullback M.p (genericBase k)) :=
    inferInstanceAs (IsIntegral (genericScheme k M))
  letI : IsDiscreteValuationRing (OriginStalk k M s hs.1) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      (genericStructure k M) x hclosed
  refine ⟨κ, ⟨fun b => RingHom.congr_fun hfield b, ?_, ?_⟩, ?_⟩
  · intro b
    exact RingHom.congr_fun (arc_value_square (LaurentSeries k) e f hf κ hκ) b
  · intro b n
    exact reflects_powers κ hi hm b n
  · intro κ' hκ'
    apply RingHom.ext
    intro b
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k)
    exact (hκ'.1 b).trans (RingHom.congr_fun hfield b).symm

end ArithmeticThetaOriginInitialR0161
#print axioms ArithmeticThetaOriginInitialR0161.actual_origin_local_comparison
