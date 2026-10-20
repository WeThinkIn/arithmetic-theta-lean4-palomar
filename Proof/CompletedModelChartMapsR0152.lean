module

public import KatoAnnularDefinitionsR0152

@[expose] public section

/-! Effectivity of the prescribed completed annular charts. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152.CompletedModelChartMapsR0152
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem proper_point_effectivity
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) [IsProper g]
    (x : ∀ n, Spec (.of (R ⧸ I ^ (n+1))) ⟶ Y)
    (hx : ∀ n, x n ≫ g = adicThickeningBase I n)
    (hxt : ∀ n, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n+1))) ≫
      x (n+1) = x n) :
    ∃! y : Spec (.of R) ⟶ Y, y ≫ g = 𝟙 _ ∧
      ∀ n, adicThickeningBase I n ≫ y = x n := by
  let f : Spec (.of R) ⟶ Spec (.of R) := 𝟙 _
  let q n := adicThickeningToBase f I n
  let φ (n : ℕ) : adicThickening f I n ⟶ adicThickening g I n :=
    pullback.lift (q n ≫ x n) (q n) (by simp only [Category.assoc, hx])
  have hφ₁ (n : ℕ) : φ n ≫ adicThickeningι g I n = q n ≫ x n :=
    pullback.lift_fst _ _ _
  have hφ₂ (n : ℕ) : φ n ≫ adicThickeningToBase g I n = q n :=
    pullback.lift_snd _ _ _
  have ht (n : ℕ) : adicThickeningTransition f I n ≫ φ (n+1) =
      φ n ≫ adicThickeningTransition g I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι g I (n+1) = _ ≫ adicThickeningι g I (n+1)
      rw [Category.assoc, hφ₁, ← Category.assoc,
        show adicThickeningTransition f I n ≫ q (n+1) = q n ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n+1))) from
          adicThickeningTransition_toBase f I n,
        Category.assoc, hxt, Category.assoc, adicThickeningTransition_ι, hφ₁]
    · change _ ≫ adicThickeningToBase g I (n+1) = _ ≫ adicThickeningToBase g I (n+1)
      simp only [Category.assoc, adicThickeningTransition_toBase,
        Category.assoc, hφ₂, reassoc_of% hφ₂]
      exact adicThickeningTransition_toBase f I n
  obtain ⟨y, hy, hu⟩ :=
    ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
      I f g φ hφ₂ ht
  have he (n : ℕ) : adicThickeningι f I n = q n ≫ adicThickeningBase I n := by
    simpa only [f, Category.comp_id] using adicThickeningι_comp f I n
  haveI (n : ℕ) : IsIso (q n) := by
    dsimp [q, adicThickeningToBase, f]
    infer_instance
  refine ⟨y, ⟨hy.1, fun n => ?_⟩, ?_⟩
  · apply (cancel_epi (q n)).mp
    rw [← Category.assoc, ← he, hy.2, hφ₁]
  · intro y' hy'
    apply hu y'
    refine ⟨hy'.1, fun n => ?_⟩
    rw [he, Category.assoc, hy'.2, hφ₁]

private theorem proper_point_over_effectivity
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {B Y : Scheme.{u}} (b : Spec (.of R) ⟶ B) (g : Y ⟶ B) [IsProper g]
    (x : ∀ n, Spec (.of (R ⧸ I ^ (n+1))) ⟶ Y)
    (hx : ∀ n, x n ≫ g = adicThickeningBase I n ≫ b)
    (hxt : ∀ n, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n+1))) ≫
      x (n+1) = x n) :
    ∃! y : Spec (.of R) ⟶ Y, y ≫ g = b ∧
      ∀ n, adicThickeningBase I n ≫ y = x n := by
  let x' n : Spec (.of (R ⧸ I ^ (n+1))) ⟶ pullback g b :=
    pullback.lift (x n) (adicThickeningBase I n) (hx n)
  have hx' n : x' n ≫ pullback.snd g b = adicThickeningBase I n :=
    pullback.lift_snd _ _ _
  have hxt' n : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n+1))) ≫
      x' (n+1) = x' n := by
    apply pullback.hom_ext
    · simp only [Category.assoc, x', pullback.lift_fst, hxt]
    · simp only [Category.assoc, hx']
      exact adicThickeningBase_succ_comp I n
  obtain ⟨y, hy, hu⟩ := proper_point_effectivity I (pullback.snd g b) x' hx' hxt'
  refine ⟨y ≫ pullback.fst g b, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hy.1, Category.id_comp]
  · intro n
    rw [← Category.assoc, hy.2]
    exact pullback.lift_fst _ _ _
  · intro z hz
    let z' : Spec (.of R) ⟶ pullback g b :=
      pullback.lift z (𝟙 _) (by simpa using hz.1)
    have hz' : z' = y := by
      apply hu
      refine ⟨pullback.lift_snd _ _ _, fun n => ?_⟩
      apply pullback.hom_ext
      · simp only [Category.assoc, z', x', pullback.lift_fst, hz.2]
      · simp only [Category.assoc, z', x', pullback.lift_snd, Category.comp_id]
    rw [← hz']
    exact (pullback.lift_fst _ _ _).symm

open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]
private abbrev chartIdeal : Ideal (Chart k) :=
  Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}

private lemma parameter_eq :
    ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
  simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private instance chart_noetherian : IsNoetherianRing (Chart k) :=
  (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1

private instance chart_complete : IsAdicComplete (chartIdeal k) (Chart k) := by
  have h := AdicCompletion.isAdicComplete_map_algebraMap_of_fg
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (Submodule.fg_span (Set.finite_singleton _))
  have he : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k)) = chartIdeal k := by
    simp only [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : Chart k => Ideal.span {z}) (parameter_eq k)
  rw [he] at h
  exact h

private abbrev comparison (n : ℕ) : HatA k n ≃+* A k n :=
  Classical.choose (finite_stage_completion_comparison k n)

private lemma reduction_complete (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
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

private lemma reduction_transition (n N : ℕ) (h : n ≤ N) :
    (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h).comp
      (reduction k N) = reduction k n := by
  apply RingHom.ext
  intro z
  obtain ⟨a, ha⟩ := approx k N z
  have hN : trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) N z =
      trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) N
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) := Ideal.Quotient.eq.mpr ha
  have hn : trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z =
      trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) :=
    Ideal.Quotient.eq.mpr ((Ideal.pow_le_pow_right (by omega : n+1 ≤ N+1)) ha)
  change truncReduce _ _ n N h (comparison k N (trunc _ _ N z)) =
    comparison k n (trunc _ _ n z)
  rw [hN, hn]
  change truncReduce _ _ n N h (reduction k N _) = reduction k n _
  rw [reduction_complete, reduction_complete]
  rfl

private lemma reduction_base (n : ℕ) :
    (reduction k n).comp (ArithmeticThetaAnnularTorsionPrereqR0053.base k) =
      (base k n).comp (trunc (PowerSeries k) PowerSeries.X n) := by
  apply RingHom.ext
  intro a
  change reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) a)) = _
  rw [reduction_complete]
  rfl

private lemma comparison_transition (n : ℕ) :
    (comparison k n).toRingHom.comp
        (Ideal.Quotient.factorPowSucc (chartIdeal k) (n+1)) =
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n (n+1) (Nat.le_succ n)).comp (comparison k (n+1)).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (RingHom.congr_fun (reduction_transition k n (n+1) (Nat.le_succ n)) a).symm

private def comparisonIso (n : ℕ) : Spec (.of (A k n)) ≅ Spec (.of (HatA k n)) :=
  (Scheme.Spec.mapIso (comparison k n).toCommRingCatIso.op)

private lemma comparisonIso_base (n : ℕ) :
    (comparisonIso k n).hom ≫ adicThickeningBase (chartIdeal k) n =
      Spec.map (CommRingCat.ofHom (reduction k n)) := by
  change Spec.map (CommRingCat.ofHom (comparison k n).toRingHom) ≫ _ = _
  rw [adicThickeningBase, ← Spec.map_comp]
  rfl

private lemma comparisonIso_transition (n : ℕ) :
    (comparisonIso k n).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (chartIdeal k) (n+1))) =
      chartReduction k n (n+1) (Nat.le_succ n) ≫ (comparisonIso k (n+1)).hom := by
  change Spec.map (CommRingCat.ofHom (comparison k n).toRingHom) ≫ _ =
    _ ≫ Spec.map (CommRingCat.ofHom (comparison k (n+1)).toRingHom)
  rw [← Spec.map_comp, chartReduction, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (comparison_transition k n)

open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136

private theorem chart_effectivity {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (j : Fin r) :
    ∃! χ : chartScheme k ⟶ M.X, IsChartMap k M j χ := by
  let x (n : ℕ) : Spec (.of (HatA k n)) ⟶ M.X :=
    (comparisonIso k n).inv ≫ (T.atlas n).chart j ≫ M.inclusion n
  have hx (n : ℕ) : x n ≫ M.p = adicThickeningBase (chartIdeal k) n ≫ chartBase k := by
    apply (cancel_epi (comparisonIso k n).hom).mp
    simp only [x, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, (T.atlas n).chart_over,
      comparisonIso_base]
    change Spec.map (CommRingCat.ofHom (base k n)) ≫
      Spec.map (CommRingCat.ofHom (trunc (PowerSeries k) PowerSeries.X n)) =
      Spec.map (CommRingCat.ofHom (reduction k n)) ≫
        Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.base k))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (reduction_base k n).symm
  have hxt (n : ℕ) :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (chartIdeal k) (n+1))) ≫
        x (n+1) = x n := by
    apply (cancel_epi (comparisonIso k n).hom).mp
    rw [← Category.assoc, comparisonIso_transition]
    simp only [x, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← (T.transition_spec n (n+1) (Nat.le_succ n)).2 j,
      Category.assoc, hM.2.2.2]
  letI : IsProper M.p := hM.1
  obtain ⟨χ, hχ, hu⟩ := proper_point_over_effectivity (chartIdeal k) (chartBase k) M.p x hx hxt
  refine ⟨χ, ⟨hχ.1, fun n => ?_⟩, ?_⟩
  · rw [← comparisonIso_base, Category.assoc, hχ.2]
    simp only [x, Iso.hom_inv_id_assoc]
  · intro χ' hχ'
    apply hu χ'
    refine ⟨hχ'.1, fun n => ?_⟩
    apply (cancel_epi (comparisonIso k n).hom).mp
    rw [← Category.assoc, comparisonIso_base, hχ'.2]
    simp only [x, Iso.hom_inv_id_assoc]

end ArithmeticThetaKatoAnnularR0152.CompletedModelChartMapsR0152


namespace ArithmeticThetaKatoAnnularR0152
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135

/-- The actual completed chart map, with all prescribed finite-stage equations. -/
theorem completed_model_chart_maps :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M),
      ∀ j : Fin r, ∃! χ : Quiver.Hom (chartScheme k) M.X, IsChartMap k M j χ := by
  intro k _ _ r hr _ T M hM j
  exact CompletedModelChartMapsR0152.chart_effectivity k M hM j

end ArithmeticThetaKatoAnnularR0152

#print axioms ArithmeticThetaKatoAnnularR0152.completed_model_chart_maps
