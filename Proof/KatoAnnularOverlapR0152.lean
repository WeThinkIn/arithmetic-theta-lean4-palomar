module

public import CompletedModelChartMapsR0152
public import CompletedChartFieldMapsR0152

@[expose] public section

/-! Geometric compatibility on the completed cyclic annular overlaps. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152.KatoAnnularOverlap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem complete_hom_ext
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {B Y : Scheme.{u}} (b : Spec (.of R) ⟶ B) (p : Y ⟶ B) [IsSeparated p]
    (f g : Spec (.of R) ⟶ Y) (hf : f ≫ p = b) (hg : g ≫ p = b)
    (h : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1)))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1)))) ≫ g) : f = g := by
  let F : Spec (.of R) ⟶ pullback p b := pullback.lift f (𝟙 _) (by simpa using hf)
  let G : Spec (.of R) ⟶ pullback p b := pullback.lift g (𝟙 _) (by simpa using hg)
  have he : F = G := by
    apply eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
      R I (𝟙 _) (pullback.snd p b)
      (fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1)))))
      (fun _ => rfl) F G (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    intro n
    apply pullback.hom_ext
    · simp only [Category.assoc, F, G, pullback.lift_fst]
      rw [show pullback.fst (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1))))) =
        pullback.snd (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1))))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1)))) by
            simpa using (pullback.condition (f := 𝟙 (Spec (.of R)))
              (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n+1))))))]
      rw [Category.assoc, Category.assoc, h]
    · simp only [Category.assoc, F, G, pullback.lift_snd]
  have := congrArg (fun a => a ≫ pullback.fst p b) he
  simpa only [F, G, pullback.lift_fst] using this

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
variable (k : Type u) [Field k] [CharZero k]

private def openComparison (n : ℕ) (side : Bool) : HatB k n side ≃+* B k n side :=
  Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) side

private lemma comparison_spec (n : ℕ) : CompletionComparison k n
    (Classical.choose (finite_stage_completion_comparison k n)) (openComparison k n) :=
  Classical.choose_spec (Classical.choose_spec (finite_stage_completion_comparison k n))

private def openReduction (n : ℕ) (side : Bool) : HatOpen k side →+* B k n side :=
  (openComparison k n side).toRingHom.comp
    (trunc (HatOpen k side)
      (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n)

private lemma openReduction_of (n : ℕ) (side : Bool) (a : RawOpen k side) :
    openReduction k n side (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side a) =
      trunc (RawOpen k side) (openParameter k side) n a :=
  RingHom.congr_fun ((comparison_spec k n).2.1 side) a

open ArithmeticThetaIndexedOverlapsR0058

omit [CharZero k] in
private lemma parameter_eq (side : Bool) : ot k 0 side =
    ArithmeticThetaInfinitesimalPolygonR0129.openParameter k side := by
  change algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side)
    (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
  have he : nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X) =
      ArithmeticThetaNodeCharts.t k := by
    simp only [nodeEquiv]
    rfl
  rw [he]
  rfl

private lemma restriction_reduction (n j : ℕ) (side : Bool) :
    (openReduction k n side).comp (ArithmeticThetaCorrectedGammaR0061.restrict k j side) =
      (restriction k n side).comp (reduction k n) := by
  have he : ArithmeticThetaCorrectedGammaR0061.restrict k j side =
      Classical.choose (completed_coordinate_restrictions k 0 side) := by
    apply (Classical.choose_spec (completed_coordinate_restrictions k 0 side)).2
    exact Classical.choose_spec (completed_coordinate_restrictions k j side).exists
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply, he]
  exact (comparison_spec k n).2.2 side a

private lemma completion_approx {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I.FG) (m : ℕ) (z : AdicCompletion I S) :
    ∃ a : S, z - algebraMap S _ a ∈ (I.map (algebraMap S (AdicCompletion I S))) ^ m := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I m z)
  refine ⟨a, ?_⟩
  rw [← ArithmeticThetaNodeCharts.completion_eval_kernel I hI m]
  change AdicCompletion.evalₐ I m (z - algebraMap S _ a) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simpa using sub_eq_zero.mpr ha.symm

set_option backward.isDefEq.respectTransparency true in
omit [CharZero k] in
private lemma open_approx (n : ℕ) (side : Bool) (z : HatOpen k side) :
    ∃ a : RawOpen k side, z - completeOpen k 0 side a ∈ hatPower k 0 side (n+1) := by
  have hfg : (openIdeal k 0 side).FG := Submodule.fg_span (Set.finite_singleton _)
  obtain ⟨a, ha⟩ := completion_approx (openIdeal k 0 side) hfg (n+1) z
  refine ⟨a, ?_⟩
  have he : (openIdeal k 0 side).map (completeOpen k 0 side) =
      Ideal.span {completeOpen k 0 side (ot k 0 side)} := by
    change (Ideal.span {ot k 0 side}).map (completeOpen k 0 side) = _
    rw [Ideal.map_span, Set.image_singleton]
  change z - completeOpen k 0 side a ∈
    ((openIdeal k 0 side).map (completeOpen k 0 side)) ^ (n+1) at ha
  rw [he] at ha
  exact ha

private lemma openReduction_zero (n : ℕ) (side : Bool) (z : HatOpen k side)
    (hz : z ∈ hatPower k 0 side (n+1)) : openReduction k n side z = 0 := by
  have hzero : trunc (HatOpen k side) (completeOpen k 0 side
      (ArithmeticThetaInfinitesimalPolygonR0129.openParameter k side)) n z = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [hatPower, parameter_eq] using hz
  change openComparison k n side (trunc _ _ n z) = 0
  rw [hzero, map_zero]

private lemma adjacent_reduction {r : ℕ} (hr : 0 < r) (j : Fin r)
    (T : Tower k r hr) (n : ℕ) :
    (openReduction k n true).comp
        (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom =
      (T.overlap n).toRingHom.comp (openReduction k n false) := by
  let E : HatOpen k false ≃+* HatOpen k true := ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
  have hE : IsCompletedAdjacent k r j.val E :=
    Classical.choose_spec (completed_indexed_adjacent k r j.val hr j.isLt).exists
  apply RingHom.ext
  intro z
  let z₀ : HatOpen k false := z
  change openReduction k n true (E z₀) = T.overlap n (openReduction k n false z₀)
  obtain ⟨a, ha⟩ := open_approx k n false z₀
  have hleft := openReduction_zero k n true (E (z₀ - completeOpen k 0 false a))
    (hE.2.1 (n+1) _ ha)
  have hright := openReduction_zero k n false (z₀ - completeOpen k 0 false a) ha
  rw [map_sub, map_sub] at hleft
  rw [map_sub] at hright
  change openReduction k n true (E z) = T.overlap n (openReduction k n false z)
  rw [sub_eq_zero.mp hleft, sub_eq_zero.mp hright]
  rw [show E (completeOpen k 0 false a) = completeOpen k 0 true
      (rawAdjacent k a) from RingHom.congr_fun hE.1 a]
  rw [openReduction_of, openReduction_of]
  exact (RingHom.congr_fun (T.overlap_spec n) a).symm

private instance open_noetherian (side : Bool) : IsNoetherianRing (RawOpen k side) := by
  letI : IsNoetherianRing (ArithmeticThetaNodeCharts.Node k) :=
    (ArithmeticThetaNodeCharts.node_noetherian_finite_type k).1
  exact IsLocalization.isNoetherianRing (Submonoid.powers (nodeCoord k side)) (RawOpen k side) inferInstance

private instance hatOpen_noetherian (side : Bool) : IsNoetherianRing (HatOpen k side) :=
  ArithmeticThetaFractionalCharts.noetherian_adic_completion _ (openIdeal k 0 side)

set_option backward.isDefEq.respectTransparency true in
private instance hatOpen_complete (side : Bool) : IsAdicComplete
    (Ideal.span {(completeOpen k 0 side
      (ArithmeticThetaInfinitesimalPolygonR0129.openParameter k side))}) (HatOpen k side) := by
  have hfg : (openIdeal k 0 side).FG := Submodule.fg_span (Set.finite_singleton _)
  have h := AdicCompletion.isAdicComplete_map_algebraMap_of_fg
    (openIdeal k 0 side) hfg
  have he : (openIdeal k 0 side).map (algebraMap (RawOpen k side) (HatOpen k side)) =
      Ideal.span {(completeOpen k 0 side
        (ArithmeticThetaInfinitesimalPolygonR0129.openParameter k side))} := by
    change (Ideal.span {ot k 0 side}).map (completeOpen k 0 side) = _
    rw [Ideal.map_span, Set.image_singleton, parameter_eq]
  rw [he] at h
  exact h

private lemma restriction_base (j : ℕ) (side : Bool) (a : PowerSeries k) :
    ArithmeticThetaCorrectedGammaR0061.restrict k j side
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k a) =
        completeOpen k 0 side (openBase k 0 side a) :=
  RingHom.congr_fun (Classical.choose_spec
    (completed_coordinate_restrictions k j side).exists).1
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k a)

private lemma overlap_base {r : ℕ} (hr : 0 < r) (j : Fin r) :
    (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom.comp
        ((ArithmeticThetaCorrectedGammaR0061.restrict k j.val false).comp
          (ArithmeticThetaAnnularTorsionPrereqR0053.base k)) =
      (ArithmeticThetaCorrectedGammaR0061.restrict k
        (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j).val true).comp
          (ArithmeticThetaAnnularTorsionPrereqR0053.base k) := by
  apply RingHom.ext
  intro a
  change ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
    (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k a)) =
    ArithmeticThetaCorrectedGammaR0061.restrict k _ true
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k a)
  rw [restriction_base, restriction_base]
  have hE := (Classical.choose_spec (completed_indexed_adjacent k r j.val hr j.isLt).exists).1
  exact (RingHom.congr_fun hE (openBase k 0 false a)).trans
    (congrArg (completeOpen k 0 true)
      (RingHom.congr_fun (indexed_adjacent_coordinates k r j.val hr j.isLt).1 a))

private lemma completed_overlap {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M)
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (j : Fin r) :
    Spec.map (CommRingCat.ofHom
      ((ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom.comp
        (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false))) ≫ χ j =
    Spec.map (CommRingCat.ofHom (ArithmeticThetaCorrectedGammaR0061.restrict k
      (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j).val true)) ≫
        χ (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j) := by
  let RY := ArithmeticThetaCorrectedGammaR0061.restrict k j.val false
  let RX := ArithmeticThetaCorrectedGammaR0061.restrict k
    (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j).val true
  let E : HatOpen k false ≃+* HatOpen k true := ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
  let b := Spec.map (CommRingCat.ofHom RX) ≫ chartBase k
  letI : IsSeparated M.p := hM.1.toIsSeparated
  apply complete_hom_ext (R := HatOpen k true) (Ideal.span {(completeOpen k 0 true
    (ArithmeticThetaInfinitesimalPolygonR0129.openParameter k true))}) b M.p
  · rw [Category.assoc, (hχ j).1]
    change Spec.map (CommRingCat.ofHom (E.toRingHom.comp RY)) ≫
      Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.base k)) =
      Spec.map (CommRingCat.ofHom RX) ≫
      Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.base k))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (overlap_base k hr j)
  · rw [Category.assoc, (hχ _).1]
  · intro n
    let e := Scheme.Spec.mapIso (openComparison k n true).toCommRingCatIso.op
    apply (cancel_epi e.hom).mp
    have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.span {(completeOpen k 0 true
          (ArithmeticThetaInfinitesimalPolygonR0129.openParameter k true))}) ^ (n+1)))) =
        Spec.map (CommRingCat.ofHom (openReduction k n true)) := by
      change Spec.map (CommRingCat.ofHom (openComparison k n true).toRingHom) ≫ _ = _
      rw [← Spec.map_comp]
      rfl
    simp only [← Category.assoc, he]
    have hl : (openReduction k n true).comp (E.toRingHom.comp RY) =
        ((T.overlap n).toRingHom.comp (restriction k n false)).comp (reduction k n) := by
      rw [← RingHom.comp_assoc, adjacent_reduction, RingHom.comp_assoc,
        restriction_reduction, RingHom.comp_assoc]
    have hl' : Spec.map (CommRingCat.ofHom (openReduction k n true)) ≫
        Spec.map (CommRingCat.ofHom (E.toRingHom.comp RY)) =
        leftLeg k n (T.overlap n) ≫ Spec.map (CommRingCat.ofHom (reduction k n)) := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((openReduction k n true).comp
        (E.toRingHom.comp RY))) = _
      rw [hl]
      exact Spec.map_comp (CommRingCat.ofHom (reduction k n))
        (CommRingCat.ofHom ((T.overlap n).toRingHom.comp (restriction k n false)))
    have hr' : Spec.map (CommRingCat.ofHom (openReduction k n true)) ≫
        Spec.map (CommRingCat.ofHom RX) =
        rightLeg k n ≫ Spec.map (CommRingCat.ofHom (reduction k n)) := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((openReduction k n true).comp RX)) = _
      rw [restriction_reduction]
      exact Spec.map_comp (CommRingCat.ofHom (reduction k n))
        (CommRingCat.ofHom (restriction k n true))
    rw [hl', hr', Category.assoc, Category.assoc, (hχ j).2 n, (hχ _).2 n,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun f => f ≫ M.inclusion n) ((T.atlas n).adjacent j).w

private lemma spec_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) :=
  Spec.map_comp _ _

open ArithmeticThetaRatioRegularityR0067
open ArithmeticThetaGenericEvaluationR0140

private lemma fraction_restriction_square (j : ℕ) (side : Bool)
    (F : ChartField k →+* OpenField k j side) (hF : IsFractionRestriction k j side F) :
    F.comp (chartToField k) =
      ((openToField k j side).comp (ArithmeticThetaGenericOverlapR0065.includeOpen k j side)).comp
        (ArithmeticThetaCorrectedGammaR0061.restrict k j side) := by
  rw [chartToField, ← RingHom.comp_assoc, hF, RingHom.comp_assoc,
    ArithmeticThetaGenericOverlapR0065.genericRestriction_spec, RingHom.comp_assoc]

private theorem rational_overlap {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) [IsIntegral (genericScheme k M)]
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (φ : Fin r → ((genericScheme k M).functionField →+* ChartField k))
    (hφ : ∀ j, IsChartFieldMap k M (χ j) (φ j)) (g : (genericScheme k M).functionField) :
    RationalCompatible k r hr (fun j => φ j g) := by
  intro j FY FX E hFY hFX hE
  let i := nextIndex r hr j
  let L := (openToField k i.val true).comp
    (ArithmeticThetaGenericOverlapR0065.includeOpen k i.val true)
  let O := ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
  let RY := ArithmeticThetaCorrectedGammaR0061.restrict k j.val false
  let RX := ArithmeticThetaCorrectedGammaR0061.restrict k i.val true
  have hy : (E.toRingHom.comp FY).comp (chartToField k) = L.comp (O.toRingHom.comp RY) := by
    apply RingHom.ext
    intro a
    have hfy := RingHom.congr_fun (fraction_restriction_square k _ _ FY hFY) a
    have he := RingHom.congr_fun hE
      (ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false (RY a))
    have ho := RingHom.congr_fun (Classical.choose_spec
      (ArithmeticThetaGenericOverlapR0065.generic_adjacent_providers k r j.val hr j.isLt)).1 (RY a)
    change E (FY (chartToField k a)) = L (O (RY a))
    rw [show FY (chartToField k a) = openToField k j.val false
      (ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false (RY a)) from hfy]
    exact he.trans (congrArg (openToField k i.val true) ho)
  have hx : FX.comp (chartToField k) = L.comp RX :=
    fraction_restriction_square k _ _ FX hFX
  have heq : (E.toRingHom.comp FY).comp (φ j) = FX.comp (φ i) := by
    letI : IsOpenImmersion (genericInclusion k M) :=
      AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
    suffices hh : CommRingCat.ofHom ((E.toRingHom.comp FY).comp (φ j)) =
        CommRingCat.ofHom (FX.comp (φ i)) from congrArg CommRingCat.Hom.hom hh
    apply Spec.map_injective
    apply (cancel_mono ((genericScheme k M).fromSpecStalk
      (_root_.genericPoint (genericScheme k M)))).mp
    apply (cancel_mono (genericInclusion k M)).mp
    rw [spec_comp (φ j) (E.toRingHom.comp FY), spec_comp (φ i) FX]
    simp only [Category.assoc]
    rw [hφ j, hφ i]
    rw [← Category.assoc, ← spec_comp (chartToField k) (E.toRingHom.comp FY),
      ← Category.assoc, ← spec_comp (chartToField k) FX, hy, hx]
    rw [spec_comp (O.toRingHom.comp RY) L, spec_comp RX L]
    simp only [Category.assoc]
    exact congrArg (fun a => Spec.map (CommRingCat.ofHom L) ≫ a)
      (completed_overlap k M hM χ hχ j)
  exact RingHom.congr_fun heq g

end ArithmeticThetaKatoAnnularR0152.KatoAnnularOverlap

namespace ArithmeticThetaKatoAnnularR0152

/-- Rational pullbacks agree on every completed cyclic overlap. -/
theorem kato_annular_overlap :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∀ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaRatioRegularityR0067.RationalCompatible k r hr (fun j => φ j g) := by
  intro k _ _ r hr _h3 T M hM _ χ hχ φ hφ g
  exact KatoAnnularOverlap.rational_overlap k M hM χ hχ φ hφ g

end ArithmeticThetaKatoAnnularR0152

#print axioms ArithmeticThetaKatoAnnularR0152.kato_annular_overlap
