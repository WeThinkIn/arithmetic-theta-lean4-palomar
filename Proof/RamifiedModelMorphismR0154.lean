module

public import RamifiedPolygonTowerR0154

@[expose] public section

/-! Algebraization of the ramified polygon contraction. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0154
namespace RamifiedModelMorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaKatoAnnularR0152 ArithmeticThetaAlgebraizedMarkedLineR0136

/-- Apply the accepted proper-morphism effectivity theorem to maps into the
whole target; the required maps into its thickenings are pullback lifts. -/
private theorem effectivity
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    [IsProper f] [IsProper g]
    (x : ∀ n, adicThickening f I n ⟶ Y)
    (hx : ∀ n, x n ≫ g = adicThickeningToBase f I n ≫ adicThickeningBase I n)
    (ht : ∀ n, adicThickeningTransition f I n ≫ x (n+1) = x n) :
    ∃! F : X ⟶ Y, F ≫ g = f ∧ ∀ n, adicThickeningι f I n ≫ F = x n := by
  let φ n : adicThickening f I n ⟶ adicThickening g I n :=
    pullback.lift (x n) (adicThickeningToBase f I n) (hx n)
  have hφ₁ n : φ n ≫ adicThickeningι g I n = x n := pullback.lift_fst ..
  have hφ₂ n : φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n :=
    pullback.lift_snd ..
  have hφt n : adicThickeningTransition f I n ≫ φ (n+1) =
      φ n ≫ adicThickeningTransition g I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι g I (n+1) = _ ≫ adicThickeningι g I (n+1)
      rw [Category.assoc, hφ₁, ht, Category.assoc, adicThickeningTransition_ι, hφ₁]
    · change _ ≫ adicThickeningToBase g I (n+1) = _ ≫ adicThickeningToBase g I (n+1)
      simp only [Category.assoc, hφ₂, adicThickeningTransition_toBase,
        reassoc_of% hφ₂]
  obtain ⟨F, hF, hu⟩ :=
    ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
      I f g φ hφ₂ hφt
  exact ⟨F, ⟨hF.1, fun n => (hF.2 n).trans (hφ₁ n)⟩,
    fun F' hF' => hu F' ⟨hF'.1, fun n => (hF'.2 n).trans (hφ₁ n).symm⟩⟩

/-- Formal faithfulness over a specified map of bases. -/
private theorem over_ext
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {X Y B : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (g : Y ⟶ B) [IsSeparated g] (b : Spec (.of R) ⟶ B)
    (F F' : X ⟶ Y) (hF : F ≫ g = f ≫ b) (hF' : F' ≫ g = f ≫ b)
    (h : ∀ n, adicThickeningι f I n ≫ F = adicThickeningι f I n ≫ F') : F = F' := by
  let G : X ⟶ pullback g b := pullback.lift F f hF
  let G' : X ⟶ pullback g b := pullback.lift F' f hF'
  have he : G = G' := by
    apply AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
      R I f (pullback.snd g b) (adicThickeningBase I) (fun _ => rfl)
      G G' (pullback.lift_snd ..) (pullback.lift_snd ..)
    intro n
    apply pullback.hom_ext
    · simpa only [Category.assoc, G, G', pullback.lift_fst, adicThickening, adicThickeningι] using h n
    · simp only [Category.assoc, G, G', pullback.lift_snd]
  have := congrArg (fun z => z ≫ pullback.fst g b) he
  simpa only [G, G', pullback.lift_fst] using this

variable (k : Type u) [Field k] [CharZero k]

lemma base_finite (d : ℕ) (hd : 0 < d) : IsFinite (baseMorphism k d hd) := by
  let φ := PowerSeries.expand (R := k) d (Nat.ne_of_gt hd)
  have ho : (φ PowerSeries.X).order = (d : ℕ∞) := by
    simp only [φ, PowerSeries.expand_X, PowerSeries.order_X_pow]
  obtain ⟨b, hb⟩ := ArithmeticThetaArithmeticRamificationR0096.ramified_monomial_basis k d hd φ ho
  letI := φ.toRingHom.toAlgebra
  letI : Module (PowerSeries k) (PowerSeries k) :=
    @Algebra.toModule _ _ _ _ φ.toRingHom.toAlgebra
  apply (IsFinite.SpecMap_iff _).mpr
  change @Module.Finite (PowerSeries k) (PowerSeries k) _ _
    (@Algebra.toModule _ _ _ _ φ.toRingHom.toAlgebra)
  exact Module.Finite.of_basis b

variable {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
variable (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
variable (M : Model k T) (hM : IsModel k T M) (Mb : Model k Tb) (hMb : IsModel k Tb Mb)
variable (ρ : Fin d → (Chart k →+* Chart k))
    (hρ : ∀ q, IsChartRamification k d hd q (ρ q))

lemma stage_base (n : ℕ) :
    Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n)) ≫ baseInclusion k n =
      baseInclusion k n ≫ baseMorphism k d hd := by
  simp only [baseInclusion, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom z))
    (RamifiedPolygonTower.coefficientMap_trunc k d hd n)

include hM hMb in
/-- Algebraize after changing the target base. The source thickenings remain
those of the actual refined model over the new parameter. -/
lemma model_effectivity :
    ∃ F : Mb.X ⟶ M.X, F ≫ M.p = Mb.p ≫ baseMorphism k d hd ∧
      ∀ n, Mb.inclusion n ≫ F = RamifiedPolygonTower.towerHom k T Tb ρ hρ n ≫ M.inclusion n := by
  letI : IsProper M.p := hM.1
  letI : IsProper Mb.p := hMb.1
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  let b := baseMorphism k d hd
  let Y := pullback M.p b
  let g : Y ⟶ baseScheme k := pullback.snd M.p b
  let e (n : ℕ) : (Tb.atlas n).X ≅ adicThickening Mb.p I n := (hMb.2.2.1 n).isoPullback
  have he₁ n : (e n).hom ≫ adicThickeningι Mb.p I n = Mb.inclusion n :=
    (hMb.2.2.1 n).isoPullback_hom_fst
  have he₂ n : (e n).hom ≫ adicThickeningToBase Mb.p I n = (Tb.atlas n).p :=
    (hMb.2.2.1 n).isoPullback_hom_snd
  have hei₂ n : (e n).inv ≫ (Tb.atlas n).p = adicThickeningToBase Mb.p I n :=
    (hMb.2.2.1 n).isoPullback_inv_snd
  have het n : Tb.transition n (n+1) (Nat.le_succ n) ≫ (e (n+1)).hom =
      (e n).hom ≫ adicThickeningTransition Mb.p I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι Mb.p I (n+1) = _ ≫ adicThickeningι Mb.p I (n+1)
      rw [Category.assoc, he₁, hMb.2.2.2, Category.assoc, adicThickeningTransition_ι, he₁]
    · change _ ≫ adicThickeningToBase Mb.p I (n+1) = _ ≫ adicThickeningToBase Mb.p I (n+1)
      rw [Category.assoc, he₂, (Tb.transition_spec n (n+1) (Nat.le_succ n)).1,
        Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, he₂]
      rfl
  let f := RamifiedPolygonTower.towerHom k T Tb ρ hρ
  have hf n : f n ≫ (T.atlas n).p = (Tb.atlas n).p ≫
      Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n)) :=
    RamifiedPolygonTower.stageHom_over k ρ hρ (T.atlas n) (Tb.atlas n)
      (T.overlap_spec n) (Tb.overlap_spec n)
  have hw n : (f n ≫ M.inclusion n) ≫ M.p =
      ((Tb.atlas n).p ≫ baseInclusion k n) ≫ b := by
    rw [Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, hf, Category.assoc, stage_base]
    rfl
  let x₀ n : (Tb.atlas n).X ⟶ Y :=
    pullback.lift (f n ≫ M.inclusion n) ((Tb.atlas n).p ≫ baseInclusion k n) (hw n)
  have hx₀t n : Tb.transition n (n+1) (Nat.le_succ n) ≫ x₀ (n+1) = x₀ n := by
    apply pullback.hom_ext
    · simp only [Category.assoc, x₀, pullback.lift_fst]
      rw [← Category.assoc, RamifiedPolygonTower.towerHom_transition,
        Category.assoc, hM.2.2.2]
    · simp only [Category.assoc, x₀, pullback.lift_snd]
      rw [← (hMb.2.2.1 (n+1)).w, ← Category.assoc, hMb.2.2.2, (hMb.2.2.1 n).w]
  let x n : adicThickening Mb.p I n ⟶ Y := (e n).inv ≫ x₀ n
  have hx n : x n ≫ g = adicThickeningToBase Mb.p I n ≫ adicThickeningBase I n := by
    dsimp only [x, x₀, g]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hei₂]
    rfl
  have hxt n : adicThickeningTransition Mb.p I n ≫ x (n+1) = x n := by
    apply (cancel_epi (e n).hom).mp
    rw [← Category.assoc, ← het]
    simp only [x, Category.assoc, Iso.hom_inv_id_assoc, hx₀t]
  obtain ⟨G, hG, _⟩ := effectivity I Mb.p g x hx hxt
  refine ⟨G ≫ pullback.fst M.p b, ?_, fun n => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hG.1]
  · rw [← he₁, Category.assoc, ← Category.assoc (adicThickeningι Mb.p I n), hG.2]
    simp only [x, x₀, Category.assoc, pullback.lift_fst, Iso.hom_inv_id_assoc]
    rfl


private abbrev chartIdeal : Ideal (Chart k) :=
  Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}

private instance chart_noetherian : IsNoetherianRing (Chart k) :=
  (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by decide)).2.1

private instance chart_complete : IsAdicComplete (chartIdeal k) (Chart k) := by
  have h := AdicCompletion.isAdicComplete_map_algebraMap_of_fg
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (Submodule.fg_span (Set.finite_singleton _))
  have he : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k)) = chartIdeal k := by
    simp only [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton]
    apply congrArg (fun z : Chart k => Ideal.span {z})
    change ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 = _
    simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  rw [he] at h
  exact h

/-- Reduction along the genuine completed-chart quotient maps is faithful. -/
private lemma chart_ext {Y B : Scheme.{u}} (g : Y ⟶ B) [IsSeparated g]
    (b : chartScheme k ⟶ B) (F F' : chartScheme k ⟶ Y)
    (hF : F ≫ g = b) (hF' : F' ≫ g = b)
    (h : ∀ n, Spec.map (CommRingCat.ofHom (reduction k n)) ≫ F =
      Spec.map (CommRingCat.ofHom (reduction k n)) ≫ F') : F = F' := by
  apply over_ext (chartIdeal k) (𝟙 (chartScheme k)) g b F F'
    (by simpa using hF) (by simpa using hF')
  intro n
  have hn : adicThickeningBase (chartIdeal k) n ≫ F =
      adicThickeningBase (chartIdeal k) n ≫ F' := by
    let e := (Classical.choose (finite_stage_completion_comparison k n)).toCommRingCatIso
    apply (cancel_epi (Scheme.Spec.mapIso e.op).hom).mp
    change (Spec.map (CommRingCat.ofHom (Classical.choose (finite_stage_completion_comparison k n)).toRingHom) ≫
      adicThickeningBase (chartIdeal k) n) ≫ F =
      (Spec.map (CommRingCat.ofHom (Classical.choose (finite_stage_completion_comparison k n)).toRingHom) ≫
      adicThickeningBase (chartIdeal k) n) ≫ F'
    rw [adicThickeningBase, ← Spec.map_comp]
    exact h n
  have hp : adicThickeningι (𝟙 (chartScheme k)) (chartIdeal k) n =
      adicThickeningToBase (𝟙 (chartScheme k)) (chartIdeal k) n ≫
        adicThickeningBase (chartIdeal k) n := by
    simpa using adicThickeningι_comp (𝟙 (chartScheme k)) (chartIdeal k) n
  rw [hp, Category.assoc, hn, ← Category.assoc]

include hρ in
lemma chart_base (q : Fin d) :
    Spec.map (CommRingCat.ofHom (ρ q)) ≫ chartBase k =
      chartBase k ≫ baseMorphism k d hd := by
  simp only [chartBase, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (hρ q).1

variable (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
variable (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))

include hM hχ hχb in
lemma model_charts (F : Mb.X ⟶ M.X)
    (hF : F ≫ M.p = Mb.p ≫ baseMorphism k d hd)
    (hn : ∀ n, Mb.inclusion n ≫ F = RamifiedPolygonTower.towerHom k T Tb ρ hρ n ≫ M.inclusion n) :
    IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F := by
  letI : IsProper M.p := hM.1
  refine ⟨hF, fun i => ?_⟩
  apply chart_ext k M.p (chartBase k ≫ baseMorphism k d hd)
  · rw [Category.assoc, hF, ← Category.assoc, (hχb i).1]
  · rw [Category.assoc, (hχ _).1, chart_base k ρ hρ]
  · intro n
    rw [← Category.assoc, (hχb i).2, Category.assoc, hn, ← Category.assoc]
    dsimp only [RamifiedPolygonTower.towerHom]
    rw [RamifiedPolygonTower.stageHom_chart]
    dsimp only [RamifiedPolygonTower.localMap]
    rw [Category.assoc, ← (hχ _).2]
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom z) ≫ χ (coarseIndex r d hd i))
      (RamifiedPolygonTower.nodeMap_reduction k _ (hρ _) n)

include hM hMb hχb in
lemma model_unique (F F' : Mb.X ⟶ M.X)
    (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (hF' : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F') : F = F' := by
  letI : IsProper M.p := hM.1
  letI : IsProper Mb.p := hMb.1
  apply over_ext (Ideal.span {PowerSeries.X}) Mb.p M.p (baseMorphism k d hd) F F' hF.1 hF'.1
  intro n
  have hn : Mb.inclusion n ≫ F = Mb.inclusion n ≫ F' := by
    apply (Tb.atlas n).hom_ext
    intro i
    have hi : χb i ≫ F = χb i ≫ F' := (hF.2 i).trans (hF'.2 i).symm
    simpa only [← Category.assoc, (hχb i).2] using
      congrArg (fun z => Spec.map (CommRingCat.ofHom (reduction k n)) ≫ z) hi
  change pullback.fst Mb.p (baseInclusion k n) ≫ F = pullback.fst Mb.p (baseInclusion k n) ≫ F'
  rw [← (hMb.2.2.1 n).isoPullback_inv_fst]
  simp only [Category.assoc, hn]

end RamifiedModelMorphism
open CategoryTheory

/-- The unique proper contraction of the refined model over t ↦ s^d,
with every specified completed-chart equation. -/
theorem ramified_model_morphism :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
      (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (hrd : 0 < r*d)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model k Tb)
      (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel k Tb Mb)
      (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k))
      (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
      (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X)
      (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
      (χb : Fin (r*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) Mb.X)
      (hχb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j (χb j)),
      ∃! F : Quiver.Hom Mb.X M.X,
        IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F ∧ AlgebraicGeometry.IsProper F := by
  intro k _ _ d hd r hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨F, hFp, hFn⟩ := RamifiedModelMorphism.model_effectivity k T Tb M hM Mb hMb ρ hρ
  have hF := RamifiedModelMorphism.model_charts k T Tb M hM Mb ρ hρ χ hχ χb hχb F hFp hFn
  letI : AlgebraicGeometry.IsProper M.p := hM.1
  letI : AlgebraicGeometry.IsProper Mb.p := hMb.1
  letI : AlgebraicGeometry.IsFinite (baseMorphism k d hd) := RamifiedModelMorphism.base_finite k d hd
  haveI : AlgebraicGeometry.IsProper (F ≫ M.p) := by rw [hFp]; infer_instance
  refine ⟨F, ⟨hF, AlgebraicGeometry.IsProper.of_comp F M.p⟩, fun F' hF' => ?_⟩
  exact RamifiedModelMorphism.model_unique k T Tb M hM Mb hMb ρ χ χb hχb F' F hF'.1 hF

end ArithmeticThetaRamifiedPeriodR0154

#print axioms ArithmeticThetaRamifiedPeriodR0154.ramified_model_morphism
