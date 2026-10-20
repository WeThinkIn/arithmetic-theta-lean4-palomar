module

public import KatoAnnularDefinitionsR0152

@[expose] public section

/-! Geometric function-field maps for completed annular charts. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def laurentInclusion : LaurentSeries k →+* ChartField k :=
  Classical.choose (ArithmeticThetaCyclicConstantsR0088.laurent_scalar_graph k)

lemma laurentInclusion_base (a : PowerSeries k) :
    laurentInclusion k (algebraMap (PowerSeries k) (LaurentSeries k) a) =
      chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k a) :=
  (Classical.choose_spec
    (ArithmeticThetaCyclicConstantsR0088.laurent_scalar_graph k)).1.1 a

lemma field_base_square :
    Spec.map (CommRingCat.ofHom (chartToField k)) ≫ chartBase k =
      Spec.map (CommRingCat.ofHom (laurentInclusion k)) ≫ genericBase k := by
  rw [chartBase, genericBase, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (laurentInclusion_base k a).symm

/-- The geometric map to the generic fiber is fixed by the structural square. -/
def genericChart (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) :
    Spec (CommRingCat.of (ChartField k)) ⟶ genericScheme k M :=
  pullback.lift (Spec.map (CommRingCat.ofHom (chartToField k)) ≫ χ)
    (Spec.map (CommRingCat.ofHom (laurentInclusion k))) (by
      rw [Category.assoc, hχ, field_base_square])

@[reassoc (attr := simp)]
lemma genericChart_inclusion (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) :
    genericChart k M χ hχ ≫ genericInclusion k M =
      Spec.map (CommRingCat.ofHom (chartToField k)) ≫ χ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericChart_structure (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) :
    genericChart k M χ hχ ≫ genericStructure k M =
      Spec.map (CommRingCat.ofHom (laurentInclusion k)) :=
  pullback.lift_snd _ _ _

lemma fieldMap_unique (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X)
    (φ ψ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ) (hψ : IsChartFieldMap k M χ ψ) : ψ = φ := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  suffices h : CommRingCat.ofHom ψ = CommRingCat.ofHom φ from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono ((genericScheme k M).fromSpecStalk
    (_root_.genericPoint (genericScheme k M)))).mp
  apply (cancel_mono (genericInclusion k M)).mp
  exact hψ.trans hφ.symm

lemma scalarHom_square {X : Scheme.{u}} [IsIntegral X]
    (F : Type u) [Field F] (p : X ⟶ Spec (CommRingCat.of F)) :
    Spec.map (CommRingCat.ofHom (scalarHom F p)) =
      X.fromSpecStalk (_root_.genericPoint X) ≫ p := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨_root_.genericPoint X, trivial⟩⟩
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
    p.appTop ≫ X.germToFunctionField ⊤) = _
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ,
    Category.assoc]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Every geometric field map automatically has the prescribed scalar action,
including at zero. -/
lemma fieldMap_scalar (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ) (a : LaurentSeries k) :
    φ (baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) a) =
      laurentInclusion k a := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  have hsquare : Spec.map (CommRingCat.ofHom φ) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) =
      genericChart k M χ hχ := by
    apply (cancel_mono (genericInclusion k M)).mp
    simpa only [IsChartFieldMap, Category.assoc, genericChart_inclusion] using hφ
  have h : φ.comp (scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)) =
      laurentInclusion k := by
    suffices h : CommRingCat.ofHom (φ.comp (scalarHom (X := genericScheme k M) (LaurentSeries k)
        (genericStructure k M))) = CommRingCat.ofHom (laurentInclusion k) from
      congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (scalarHom (X := genericScheme k M) (LaurentSeries k)
      (genericStructure k M)) ≫ CommRingCat.ofHom φ) = _
    rw [Spec.map_comp, scalarHom_square, ← Category.assoc, hsquare,
      genericChart_structure]
  exact RingHom.congr_fun h a

lemma exists_fieldMap_of_generic (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (hη : genericChart k M χ hχ (IsLocalRing.closedPoint (ChartField k)) =
      _root_.genericPoint (genericScheme k M)) :
    ∃ φ : (genericScheme k M).functionField →+* ChartField k,
      IsChartFieldMap k M χ φ := by
  have hgeneral {X : Scheme.{u}} (F : Type u) [Field F]
      (f : Spec (CommRingCat.of F) ⟶ X) (x : X)
      (hx : f (IsLocalRing.closedPoint F) = x) :
      ∃ φ : X.presheaf.stalk x →+* F,
        Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x = f := by
    subst x
    exact ⟨(Scheme.stalkClosedPointTo f).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩
  obtain ⟨φ, hφ⟩ := hgeneral (ChartField k) (genericChart k M χ hχ) _ hη
  refine ⟨φ, ?_⟩
  change Spec.map (CommRingCat.ofHom φ) ≫ _ ≫ _ = _
  rw [← Category.assoc, hφ, genericChart_inclusion]

open AlgebraizedGenericSmoothnessR0135

lemma model_integral (M : Model k T) (hM : IsModel k T M)
    [IsIntegral (genericScheme k M)] : IsIntegral M.X := by
  letI : Flat M.p := hM.2.1
  letI : IsSchemeTheoreticallyDominant (genericBase k) :=
    GenericDualLocalizationR0140.genericBase_schematic k
  letI : IsSchemeTheoreticallyDominant (genericInclusion k M) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst M.p (genericBase k)))
  letI : QuasiCompact (genericInclusion k M) :=
    inferInstanceAs (QuasiCompact (pullback.fst M.p (genericBase k)))
  letI : IsReduced M.X :=
    IsSchemeTheoreticallyDominant.isReduced (genericInclusion k M)
  have hi : IsIrreducible (Set.range (genericInclusion k M)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (genericScheme k M)).image
        (genericInclusion k M) (genericInclusion k M).continuous.continuousOn
  letI : IrreducibleSpace M.X := (irreducibleSpace_def M.X).mpr (by
    simpa only [(genericInclusion k M).denseRange.closure_range, Set.top_eq_univ] using hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced M.X

lemma dominant_of_stalk_injective {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (x : X) (hi : Function.Injective (f.stalkMap x).hom) :
    IsDominant f := by
  letI : IsDominant (Spec.map (f.stalkMap x)) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (f.stalkMap x).hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp hi]
    exact bot_le
  letI : IsDominant (Y.fromSpecStalk (f x)) := by
    constructor
    change Dense (Set.range (Y.fromSpecStalk (f x)))
    apply Dense.mono (s₁ := {_root_.genericPoint Y})
    · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
      exact (genericPoint_spec Y).specializes trivial
    · rw [dense_iff_closure_eq]
      exact genericPoint_spec Y
  haveI : IsDominant (X.fromSpecStalk x ≫ f) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
    infer_instance
  exact IsDominant.of_comp (X.fromSpecStalk x) f

lemma reduction_surjective (n : ℕ) : Function.Surjective (reduction k n) :=
  (Classical.choose (finite_stage_completion_comparison k n)).surjective.comp
    Ideal.Quotient.mk_surjective

lemma reduction_kernel (n : ℕ) : RingHom.ker (reduction k n) =
    (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}) ^ (n+1) := by
  rw [reduction, RingHom.ker_comp_of_injective _
    (Classical.choose (finite_stage_completion_comparison k n)).injective]
  exact Ideal.mk_ker

lemma reduction_range (x : chartScheme k)
    (hx : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∈ x.asIdeal) (n : ℕ) :
    ∃ z : specA k n, Spec.map (CommRingCat.ofHom (reduction k n)) z = x := by
  change x ∈ Set.range (PrimeSpectrum.comap (reduction k n))
  rw [range_comap_of_surjective _ _ (reduction_surjective k n),
    reduction_kernel]
  exact (Ideal.pow_le_self (by omega)).trans (Ideal.span_le.mpr (by simpa using hx))

lemma exists_special_point : ∃ x : chartScheme k,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∈ x.asIdeal := by
  let σ := ArithmeticThetaScaledAnnularR0050.specialization k 1 0
    (by omega) (by omega) (1 : k) (by simp)
  refine ⟨PrimeSpectrum.comap σ (IsLocalRing.closedPoint (PowerSeries k)), ?_⟩
  change σ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ∈
    IsLocalRing.maximalIdeal (PowerSeries k)
  rw [show σ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X from
    (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by omega) (by omega) (1 : k) (by simp)).1]
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- At a special-fiber point, every finite-stage kernel bounds the kernel of
 the completed-chart stalk map. No flatness of the completed-chart map is used. -/
lemma stalk_kernel_le_power (M : Model k T) (hM : IsModel k T M)
    (j : Fin r) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (x : chartScheme k) (hx : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∈ x.asIdeal)
    (n : ℕ) :
    RingHom.ker (χ.stalkMap x).hom ≤
      Ideal.span {(modelStalkParameter k M (χ x)) ^ (n+1)} := by
  obtain ⟨z, rfl⟩ := reduction_range k x hx n
  let ρ := Spec.map (CommRingCat.ofHom (reduction k n))
  have he : ρ ≫ χ = modelChart k M n j := hχ.2 n
  have hk : RingHom.ker ((ρ ≫ χ).stalkMap z).hom =
      Ideal.span {(modelStalkParameter k M ((ρ ≫ χ) z)) ^ (n+1)} := by
    rw [he]
    exact (modelChart_stalk_quotient k M hM n j z).2
  change RingHom.ker (χ.stalkMap (ρ z)).hom ≤
    Ideal.span {(modelStalkParameter k M ((ρ ≫ χ) z)) ^ (n+1)}
  rw [← hk, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  intro a ha
  change (ρ.stalkMap z).hom ((χ.stalkMap (ρ z)).hom a) = 0
  rw [show (χ.stalkMap (ρ z)).hom a = 0 from ha, map_zero]

lemma chart_stalk_injective (M : Model k T) (hM : IsModel k T M)
    (j : Fin r) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (x : chartScheme k) (hx : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∈ x.asIdeal) :
    Function.Injective (χ.stalkMap x).hom := by
  letI : IsProper M.p := hM.1
  letI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.p
  have ht : modelStalkParameter k M (χ x) ∈
      IsLocalRing.maximalIdeal (M.X.presheaf.stalk (χ x)) := by
    obtain ⟨z, rfl⟩ := reduction_range k x hx 0
    let ρ : specA k 0 ⟶ chartScheme k := Spec.map (CommRingCat.ofHom (reduction k 0))
    change modelStalkParameter k M ((ρ ≫ χ) z) ∈
      IsLocalRing.maximalIdeal (M.X.presheaf.stalk ((ρ ≫ χ) z))
    change modelStalkParameter k M ((Spec.map (CommRingCat.ofHom (reduction k 0)) ≫ χ) z) ∈
      IsLocalRing.maximalIdeal (M.X.presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (reduction k 0)) ≫ χ) z))
    rw [hχ.2 0]
    exact modelStalkParameter_mem_maximalIdeal k M hM 0 ((T.atlas 0).chart j z)
  have hproper : Ideal.span {modelStalkParameter k M (χ x)} ≠ ⊤ := by
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.span_le.mpr (by simpa using ht))
  rw [RingHom.injective_iff_ker_eq_bot, ←
    Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {modelStalkParameter k M (χ x)}) hproper]
  apply le_antisymm
  · apply le_iInf
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simpa only [Ideal.span_singleton_pow] using stalk_kernel_le_power k M hM j χ hχ x hx n
  · rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hproper]
    exact bot_le

lemma chart_dominant (M : Model k T) (hM : IsModel k T M)
    [IsIntegral (genericScheme k M)] (j : Fin r)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) : IsDominant χ := by
  letI : IsIntegral M.X := model_integral k M hM
  obtain ⟨x, hx⟩ := exists_special_point k
  exact dominant_of_stalk_injective χ x (chart_stalk_injective k M hM j χ hχ x hx)

lemma chartToField_injective : Function.Injective (chartToField k) := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  have ht : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
    have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
      (by omega)).2.2.2.2.1
    simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter] using h
  have hi : Function.Injective (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) :=
    IsLocalization.injective (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  exact (IsFractionRing.injective
    (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) (ChartField k)).comp hi

lemma genericChart_dominant (M : Model k T) (hM : IsModel k T M)
    [IsIntegral (genericScheme k M)] (j : Fin r)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) :
    IsDominant (genericChart k M χ hχ.1) := by
  letI : IsDominant χ := chart_dominant k M hM j χ hχ
  letI : IsDominant (Spec.map (CommRingCat.ofHom (chartToField k))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (chartToField k))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (chartToField_injective k)]
    exact bot_le
  letI : IsOpenImmersion (genericInclusion k M) := generic_inclusion_open k M
  haveI : IsDominant (genericChart k M χ hχ.1 ≫ genericInclusion k M) := by
    rw [genericChart_inclusion]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion
    (genericChart k M χ hχ.1) (genericInclusion k M)

lemma genericChart_point (M : Model k T) (hM : IsModel k T M)
    [IsIntegral (genericScheme k M)] (j : Fin r)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) :
    genericChart k M χ hχ.1 (IsLocalRing.closedPoint (ChartField k)) =
      _root_.genericPoint (genericScheme k M) := by
  let f := genericChart k M χ hχ.1
  letI : IsDominant f := genericChart_dominant k M hM j χ hχ
  have he : Set.range f = {f (IsLocalRing.closedPoint (ChartField k))} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg f (Subsingleton.elim _ _)
    · intro hz
      exact ⟨_, hz.symm⟩
  apply IsGenericPoint.eq _ (genericPoint_spec (genericScheme k M))
  rw [isGenericPoint_def, ← he]
  exact f.denseRange.closure_range

end ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

namespace ArithmeticThetaKatoAnnularR0152
open CompletedChartFieldMaps

/-- The actual chart induces the unique geometric function-field embedding,
with the exact accepted Laurent scalar action. -/
theorem completed_chart_field_maps :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (j : Fin r) (χ : Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X), ArithmeticThetaKatoAnnularR0152.IsChartMap k M j χ → ∃! φ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M χ φ ∧ (∀ a : LaurentSeries k, φ (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a) = (Classical.choose (ArithmeticThetaCyclicConstantsR0088.laurent_scalar_graph k)) a) := by
  intro k _ _ r hr _h3 T M hM _ j χ hχ
  obtain ⟨φ, hφ⟩ := exists_fieldMap_of_generic k M χ hχ.1
    (genericChart_point k M hM j χ hχ)
  refine ⟨φ, ⟨hφ, ?_⟩, ?_⟩
  · intro a
    exact fieldMap_scalar k M χ hχ.1 φ hφ a
  · intro ψ hψ
    exact fieldMap_unique k M χ φ ψ hφ hψ.1

end ArithmeticThetaKatoAnnularR0152

#print axioms ArithmeticThetaKatoAnnularR0152.completed_chart_field_maps
