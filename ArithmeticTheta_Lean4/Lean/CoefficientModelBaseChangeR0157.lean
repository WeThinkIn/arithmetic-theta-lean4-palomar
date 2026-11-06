import CoefficientPolygonTowerR0157

/-! Algebraization of coefficient extension on the polygon tower. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace CoefficientModelBaseChangeR0157
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

section ChartFaithfulness
variable (k : Type u) [Field k] [CharZero k]
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

end ChartFaithfulness

variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable (ι : k →+* l)
variable {r : ℕ} {hr : 0 < r}
variable (T : Tower k r hr) (Tl : Tower l r hr)
variable (M : Model k T) (hM : IsModel k T M) (Ml : Model l Tl) (hMl : IsModel l Tl Ml)
variable (ρ : Chart k →+* Chart l) (hρ : IsChartMap k l ι ρ)

lemma stage_base (n : ℕ) :
    Spec.map (CommRingCat.ofHom (CoefficientPolygonTowerR0157.coefficientMap k l ι n)) ≫ baseInclusion k n =
      baseInclusion l n ≫ baseMorphism k l ι := by
  simp only [baseInclusion, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom z))
    (CoefficientPolygonTowerR0157.coefficientMap_trunc k l ι n)

include hM hMl in
/-- Algebraize after changing the target base. The source thickenings remain
those of the specified model over the extended coefficient field. -/
lemma model_effectivity :
    ∃ F : Ml.X ⟶ M.X, F ≫ M.p = Ml.p ≫ baseMorphism k l ι ∧
      ∀ n, Ml.inclusion n ≫ F = CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl n ≫ M.inclusion n := by
  letI : IsProper M.p := hM.1
  letI : IsProper Ml.p := hMl.1
  let I : Ideal (PowerSeries l) := Ideal.span {PowerSeries.X}
  let b := baseMorphism k l ι
  let Y := pullback M.p b
  let g : Y ⟶ baseScheme l := pullback.snd M.p b
  let e (n : ℕ) : (Tl.atlas n).X ≅ adicThickening Ml.p I n := (hMl.2.2.1 n).isoPullback
  have he₁ n : (e n).hom ≫ adicThickeningι Ml.p I n = Ml.inclusion n :=
    (hMl.2.2.1 n).isoPullback_hom_fst
  have he₂ n : (e n).hom ≫ adicThickeningToBase Ml.p I n = (Tl.atlas n).p :=
    (hMl.2.2.1 n).isoPullback_hom_snd
  have hei₂ n : (e n).inv ≫ (Tl.atlas n).p = adicThickeningToBase Ml.p I n :=
    (hMl.2.2.1 n).isoPullback_inv_snd
  have het n : Tl.transition n (n+1) (Nat.le_succ n) ≫ (e (n+1)).hom =
      (e n).hom ≫ adicThickeningTransition Ml.p I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι Ml.p I (n+1) = _ ≫ adicThickeningι Ml.p I (n+1)
      rw [Category.assoc, he₁, hMl.2.2.2, Category.assoc, adicThickeningTransition_ι, he₁]
    · change _ ≫ adicThickeningToBase Ml.p I (n+1) = _ ≫ adicThickeningToBase Ml.p I (n+1)
      rw [Category.assoc, he₂, (Tl.transition_spec n (n+1) (Nat.le_succ n)).1,
        Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, he₂]
      rfl
  let f := CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl
  have hf n : f n ≫ (T.atlas n).p = (Tl.atlas n).p ≫
      Spec.map (CommRingCat.ofHom (CoefficientPolygonTowerR0157.coefficientMap k l ι n)) :=
    CoefficientPolygonTowerR0157.stageHom_over k l ι ρ hρ (T.atlas n) (Tl.atlas n)
      (T.overlap_spec n) (Tl.overlap_spec n)
  have hw n : (f n ≫ M.inclusion n) ≫ M.p =
      ((Tl.atlas n).p ≫ baseInclusion l n) ≫ b := by
    rw [Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, hf, Category.assoc, stage_base]
    rfl
  let x₀ n : (Tl.atlas n).X ⟶ Y :=
    pullback.lift (f n ≫ M.inclusion n) ((Tl.atlas n).p ≫ baseInclusion l n) (hw n)
  have hx₀t n : Tl.transition n (n+1) (Nat.le_succ n) ≫ x₀ (n+1) = x₀ n := by
    apply pullback.hom_ext
    · simp only [Category.assoc, x₀, pullback.lift_fst]
      rw [← Category.assoc, CoefficientPolygonTowerR0157.towerHom_transition,
        Category.assoc, hM.2.2.2]
    · simp only [Category.assoc, x₀, pullback.lift_snd]
      rw [← (hMl.2.2.1 (n+1)).w, ← Category.assoc, hMl.2.2.2, (hMl.2.2.1 n).w]
  let x n : adicThickening Ml.p I n ⟶ Y := (e n).inv ≫ x₀ n
  have hx n : x n ≫ g = adicThickeningToBase Ml.p I n ≫ adicThickeningBase I n := by
    dsimp only [x, x₀, g]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hei₂]
    rfl
  have hxt n : adicThickeningTransition Ml.p I n ≫ x (n+1) = x n := by
    apply (cancel_epi (e n).hom).mp
    rw [← Category.assoc, ← het]
    simp only [x, Category.assoc, Iso.hom_inv_id_assoc, hx₀t]
  obtain ⟨G, hG, _⟩ := effectivity I Ml.p g x hx hxt
  refine ⟨G ≫ pullback.fst M.p b, ?_, fun n => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hG.1]
  · rw [← he₁, Category.assoc, ← Category.assoc (adicThickeningι Ml.p I n), hG.2]
    simp only [x, x₀, Category.assoc, pullback.lift_fst, Iso.hom_inv_id_assoc]
    rfl

include hM hMl in
/-- The algebraized comparison is an isomorphism onto the actual base change,
as detected by its cartesian restrictions at every thickness. -/
lemma model_cartesian (F : Ml.X ⟶ M.X)
    (hF : F ≫ M.p = Ml.p ≫ baseMorphism k l ι)
    (hn : ∀ n, Ml.inclusion n ≫ F =
      CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl n ≫ M.inclusion n) :
    IsPullback F Ml.p M.p (baseMorphism k l ι) := by
  letI : IsProper M.p := hM.1
  letI : IsProper Ml.p := hMl.1
  let b := baseMorphism k l ι
  let g := pullback.snd M.p b
  let G := pullback.lift F Ml.p hF
  have hG₁ : G ≫ pullback.fst M.p b = F := pullback.lift_fst ..
  have hG₂ : G ≫ g = Ml.p := pullback.lift_snd ..
  haveI : IsProper (G ≫ g) := by rw [hG₂]; infer_instance
  haveI : IsProper G := IsProper.of_comp G g
  haveI : IsIso G := by
    apply AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
      (PowerSeries l) (Ideal.span {PowerSeries.X}) g G (baseInclusion l) (fun _ => rfl)
    intro n
    let f := CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl n
    have hf : IsPullback f (Tl.atlas n).p (T.atlas n).p
        (Spec.map (CommRingCat.ofHom (CoefficientPolygonTowerR0157.coefficientMap k l ι n))) :=
      CoefficientPolygonTowerR0157.stageHom_pullback k l ι ρ hρ (T.atlas n) (Tl.atlas n)
        (T.overlap_spec n) (Tl.overlap_spec n)
    have hw : (f ≫ M.inclusion n) ≫ M.p =
        ((Tl.atlas n).p ≫ baseInclusion l n) ≫ b := by
      rw [Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, hf.w,
        Category.assoc, stage_base]
      rfl
    let x := pullback.lift (f ≫ M.inclusion n)
      ((Tl.atlas n).p ≫ baseInclusion l n) hw
    have hx₁ : x ≫ pullback.fst M.p b = f ≫ M.inclusion n := pullback.lift_fst ..
    have hx₂ : x ≫ g = (Tl.atlas n).p ≫ baseInclusion l n := pullback.lift_snd ..
    have hx : IsPullback x (Tl.atlas n).p g (baseInclusion l n) := by
      have hh := hf.paste_horiz (hM.2.2.1 n)
      rw [stage_base] at hh
      apply IsPullback.of_right (h₁₂ := pullback.fst M.p b) ?_ hx₂
        (IsPullback.of_hasPullback M.p b)
      rw [hx₁]
      exact hh
    have hi : Ml.inclusion n ≫ G = x := by
      apply pullback.hom_ext
      · rw [Category.assoc, hG₁, hx₁]
        exact hn n
      · rw [Category.assoc, hG₂, hx₂]
        exact (hMl.2.2.1 n).w
    have hp : IsPullback (Ml.inclusion n) hx.isoPullback.hom G
        (pullback.fst g (baseInclusion l n)) := by
      apply IsPullback.of_bot (v₂₁ := pullback.snd g (baseInclusion l n))
        (v₂₂ := g) ?_ ?_ (IsPullback.of_hasPullback g (baseInclusion l n))
      · rw [hx.isoPullback_hom_snd, hG₂]
        exact hMl.2.2.1 n
      · rw [hi, hx.isoPullback_hom_fst]
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨hF⟩ (asIso G) hG₁ hG₂

include hρ in
lemma chart_base :
    Spec.map (CommRingCat.ofHom ρ) ≫ chartBase k =
      chartBase l ≫ baseMorphism k l ι := by
  simp only [chartBase, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext hρ.1

variable (χ : Fin r → (chartScheme k ⟶ M.X))
  (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
variable (χl : Fin r → (chartScheme l ⟶ Ml.X))
  (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j))

include hM hχ hχl in
lemma model_charts (F : Ml.X ⟶ M.X)
    (hF : F ≫ M.p = Ml.p ≫ baseMorphism k l ι)
    (hn : ∀ n, Ml.inclusion n ≫ F =
      CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl n ≫ M.inclusion n) :
    ∀ j, χl j ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ j := by
  letI : IsProper M.p := hM.1
  intro j
  apply chart_ext l M.p (chartBase l ≫ baseMorphism k l ι)
  · rw [Category.assoc, hF, ← Category.assoc, (hχl j).1]
  · rw [Category.assoc, (hχ j).1, chart_base k l ι ρ hρ]
  · intro n
    rw [← Category.assoc, (hχl j).2, Category.assoc, hn, ← Category.assoc]
    dsimp only [CoefficientPolygonTowerR0157.towerHom]
    rw [CoefficientPolygonTowerR0157.stageHom_chart]
    dsimp only [CoefficientPolygonTowerR0157.localMap]
    rw [Category.assoc, ← (hχ j).2]
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom z) ≫ χ j)
      (CoefficientPolygonTowerR0157.nodeMap_reduction k l ι ρ hρ n)

include hM hMl hχl in
lemma model_unique (F F' : Ml.X ⟶ M.X)
    (hF : IsModelMap k l ι T Tl M Ml ρ χ χl F)
    (hF' : IsModelMap k l ι T Tl M Ml ρ χ χl F') : F = F' := by
  letI : IsProper M.p := hM.1
  letI : IsProper Ml.p := hMl.1
  apply over_ext (Ideal.span {PowerSeries.X}) Ml.p M.p (baseMorphism k l ι)
    F F' hF.1.w hF'.1.w
  intro n
  have hn : Ml.inclusion n ≫ F = Ml.inclusion n ≫ F' := by
    apply (Tl.atlas n).hom_ext
    intro j
    have hi : χl j ≫ F = χl j ≫ F' := (hF.2 j).trans (hF'.2 j).symm
    simpa only [← Category.assoc, (hχl j).2] using
      congrArg (fun z => Spec.map (CommRingCat.ofHom (reduction l n)) ≫ z) hi
  change pullback.fst Ml.p (baseInclusion l n) ≫ F =
    pullback.fst Ml.p (baseInclusion l n) ≫ F'
  rw [← (hMl.2.2.1 n).isoPullback_inv_fst]
  simp only [Category.assoc, hn]

end CoefficientModelBaseChangeR0157

/-- Unique coefficient base change of the specified proper models, retaining
the full cartesian square and all prescribed completed-chart equations. -/
theorem coefficient_model_base_change :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l)
      (r : ℕ)
      (hr : 0 < r)
      (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (Tl : ArithmeticThetaInfinitesimalPolygonR0129.Tower l r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (Ml : ArithmeticThetaProjectiveEffectivityR0135.Model l Tl)
      (hMl : ArithmeticThetaProjectiveEffectivityR0135.IsModel l Tl Ml)
      (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l)
      (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)
      (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X)
      (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
      (χl : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme l) Ml.X)
      (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j)),
      ∃! F : Quiver.Hom Ml.X M.X,
        ArithmeticThetaCoefficientNormDescentR0157.IsModelMap k l ι T Tl M Ml ρ χ χl F := by
  intro k l _ _ _ _ ι r hr _ T Tl M hM Ml hMl ρ hρ χ hχ χl hχl
  obtain ⟨F, hFp, hFn⟩ :=
    CoefficientModelBaseChangeR0157.model_effectivity k l ι T Tl M hM Ml hMl ρ hρ
  have hFc := CoefficientModelBaseChangeR0157.model_cartesian
    k l ι T Tl M hM Ml hMl ρ hρ F hFp hFn
  have hFχ := CoefficientModelBaseChangeR0157.model_charts
    k l ι T Tl M hM Ml ρ hρ χ hχ χl hχl F hFp hFn
  exact ⟨F, ⟨hFc, hFχ⟩, fun F' hF' =>
    CoefficientModelBaseChangeR0157.model_unique
      k l ι T Tl M hM Ml hMl ρ χ χl hχl F' F hF' ⟨hFc, hFχ⟩⟩

end ArithmeticThetaCoefficientNormDescentR0157

#print axioms ArithmeticThetaCoefficientNormDescentR0157.coefficient_model_base_change
