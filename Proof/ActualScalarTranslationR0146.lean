module

public import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced
public import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
public import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
public import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
public import Definitions.Def_FormalGroup_NSeries
public import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
public import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
public import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
public import Definitions.Def_WeierstrassCurve_FormalGroupLaw
public import Definitions.Def_WeierstrassCurve_PointChart
public import Definitions.Def_WeierstrassCurve_ProjModel
public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Definitions.Def_WeierstrassCurve_SectionAtOrigin
public import P2M.Util
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
public import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
public import Theorems.Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
public import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
public import Theorems.Thm_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
public import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
public import ActualGenericGroupLawR0146
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

-- Keep the original elaborated instance paths after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaModelSymmetriesR0137

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

/-- The universal test point retains the specified generic structure map. -/
def universalPoint : SchemeHomOver (genericStructure k M) (genericStructure k M) :=
  ⟨𝟙 _, Category.id_comp _⟩

/-- Naturality reduces the all-test-scheme translation predicate to one genuine
morphism equality on the original generic fiber. -/
lemma isTranslation_iff (G : Law k M) (p : baseScheme k ⟶ M.X)
    (hp : p ≫ M.p = 𝟙 _) (f : genericScheme k M ⟶ genericScheme k M) :
    IsTranslation k M G p hp f ↔
      (G.mul (genericStructure k M) (universalPoint k M)
        (pointOver k M (genericStructure k M) p hp)).val = f := by
  constructor
  · intro h
    simpa [universalPoint] using h (genericStructure k M) (universalPoint k M)
  · intro h V t x
    have hn := G.mul_natural (genericStructure k M) t x.val x.property
      (universalPoint k M) (pointOver k M (genericStructure k M) p hp)
    have hx : schemeHomOverComp x.val x.property (universalPoint k M) = x := by
      apply Subtype.ext
      exact Category.comp_id _
    have hp' : schemeHomOverComp x.val x.property
        (pointOver k M (genericStructure k M) p hp) = pointOver k M t p hp := by
      apply Subtype.ext
      change x.val ≫ (genericStructure k M ≫ genericPoint k M p hp) = _
      rw [← Category.assoc, x.property]
      rfl
    rw [hx, hp'] at hn
    have hv := congrArg Subtype.val hn.symm
    change (G.mul t x (pointOver k M t p hp)).val = x.val ≫ _ at hv
    rw [h] at hv
    exact hv

/-- Generic pullback preserves the actual section transport equation. -/
lemma genericPoint_map (s p : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (hp : p ≫ M.p = 𝟙 _)
    (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) (hsp : s ≫ f = p) :
    genericPoint k M s hs ≫ genericMap k M f hf = genericPoint k M p hp := by
  apply pullback.hom_ext
  · simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericMap, genericInclusion, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hsp]
  · simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericMap, genericStructure, Category.assoc, pullback.lift_snd]

/-- The prescribed scalar automorphism sends the prescribed identity section
exactly to the prescribed scalar marking. -/
lemma scalar_origin (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) a p) :
    genericPoint k M s hs.1 ≫ scalarMap k M rot scal inv ha a =
      genericPoint k M p hp.1 := by
  have hsp : s ≫ (scal a).hom = p := by
    have ht := (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha
      (zeroIndex r hr) 1 s hs).2.1 a
    simp only [mul_one] at ht
    obtain ⟨q, hq, hu⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) a
    exact (hu _ ht).trans (hu _ hp).symm
  exact genericPoint_map k M s p hs.1 hp.1 (scal a).hom
    (modelOver k M id a false (scal a) (ha.2.1 a)) hsp

lemma genericMap_id (h : (𝟙 M.X) ≫ M.p = M.p) :
    genericMap k M (𝟙 M.X) h = 𝟙 (genericScheme k M) := by
  apply pullback.hom_ext
  · change genericMap k M (𝟙 M.X) h ≫ genericInclusion k M =
      𝟙 (genericScheme k M) ≫ genericInclusion k M
    simp only [genericMap, genericInclusion, pullback.lift_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change genericMap k M (𝟙 M.X) h ≫ genericStructure k M =
      𝟙 (genericScheme k M) ≫ genericStructure k M
    simp only [genericMap, genericStructure, pullback.lift_snd]
    exact (Category.id_comp _).symm

lemma genericMap_comp (f g : M.X ⟶ M.X) (hf : f ≫ M.p = M.p)
    (hg : g ≫ M.p = M.p) :
    genericMap k M (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      genericMap k M f hf ≫ genericMap k M g hg := by
  apply pullback.hom_ext <;>
    simp only [genericMap, genericInclusion, genericStructure, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

lemma genericMap_eq_id (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p)
    (h : f = 𝟙 M.X) : genericMap k M f hf = 𝟙 _ := by
  subst f
  exact genericMap_id k M hf

/-- Base change of the specified algebraic-model isomorphism. -/
def genericIso (e : M.X ≅ M.X) (he : e.hom ≫ M.p = M.p) :
    genericScheme k M ≅ genericScheme k M where
  hom := genericMap k M e.hom he
  inv := genericMap k M e.inv (by rw [← he, Iso.inv_hom_id_assoc]; exact he.symm)
  hom_inv_id := by
    rw [← genericMap_comp]
    exact genericMap_eq_id k M _ _ e.hom_inv_id
  inv_hom_id := by
    rw [← genericMap_comp]
    exact genericMap_eq_id k M _ _ e.inv_hom_id

/-- The identity scalar already satisfies the full all-test-scheme comparison. -/
lemma scalar_one (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) 1 p) :
    IsTranslation k M G p hp.1 (scalarMap k M rot scal inv ha 1) := by
  have hps : p = s := by
    obtain ⟨q, hq, hu⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) 1
    exact (hu _ hp).trans (hu _ hs).symm
  subst p
  have hf : scalarMap k M rot scal inv ha 1 = 𝟙 _ := by
    unfold scalarMap
    have he := (algebraized_action_laws k r hr h3 T M hM rot scal inv ha).2.1
    unfold genericMap
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, he, Category.comp_id]
      exact (Category.id_comp _).symm
    · simp only [pullback.lift_snd]
      exact (Category.id_comp _).symm
  intro V t x
  rw [← hG.1, G.mul_one, hf]
  exact (Category.comp_id _).symm

/-- Uniqueness of the accepted elliptic law forces every actual automorphism
over the base that fixes its origin to preserve multiplication. -/
lemma originPreserving_mul (h3 : 3 ≤ r) (heven : Even r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (e : genericScheme k M ≅ genericScheme k M)
    (he : e.hom ≫ genericStructure k M = genericStructure k M)
    (ho : genericPoint k M s hs.1 ≫ e.hom = genericPoint k M s hs.1)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (x y : SchemeHomOver t (genericStructure k M)) :
    ActualGenericGroupLaw.pointsEquiv e he t (G.mul t x y) =
      G.mul t (ActualGenericGroupLaw.pointsEquiv e he t x)
        (ActualGenericGroupLaw.pointsEquiv e he t y) := by
  let L : Law k M := ActualGenericGroupLaw.transport e he G
  have hL : IsOriginLaw k M s hs.1 L := by
    constructor
    · intro W w
      apply Subtype.ext
      change (G.one w).val ≫ e.inv = w ≫ genericPoint k M s hs.1
      rw [hG.1]
      change (w ≫ genericPoint k M s hs.1) ≫ e.inv = _
      have hi : genericPoint k M s hs.1 ≫ e.inv = genericPoint k M s hs.1 := by
        rw [← ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        exact ho.symm
      rw [Category.assoc, hi]
    · intro W w a b
      change (ActualGenericGroupLaw.pointsEquiv e he w).symm (G.mul w _ _) =
        (ActualGenericGroupLaw.pointsEquiv e he w).symm (G.mul w _ _)
      rw [hG.2]
  have hLG : L = G := (actual_generic_group_law k r hr h3 T heven M hM s hs).unique hL hG
  have hm : L.mul t x y = G.mul t x y := congrArg (fun H : Law k M => H.mul t x y) hLG
  have hv := congrArg (ActualGenericGroupLaw.pointsEquiv e he t) hm
  change (ActualGenericGroupLaw.pointsEquiv e he t)
    ((ActualGenericGroupLaw.pointsEquiv e he t).symm (G.mul t _ _)) = _ at hv
  rw [Equiv.apply_symm_apply] at hv
  exact hv.symm

/-- Translation by an actual marked point is represented by an actual
isomorphism of the same generic scheme. -/
lemma exists_translationIso (G : Law k M) (p : baseScheme k ⟶ M.X)
    (hp : p ≫ M.p = 𝟙 _) :
    ∃ τ : genericScheme k M ≅ genericScheme k M,
      τ.hom ≫ genericStructure k M = genericStructure k M ∧
      IsTranslation k M G p hp τ.hom := by
  obtain ⟨τ, hτ, ht⟩ := G.exists_iso_comp_eq_and_comp_hom_eq_mul
    (pointOver k M (𝟙 _) p hp)
  refine ⟨τ, hτ, ?_⟩
  intro V t x
  have hp' : schemeHomOverComp t (Category.comp_id t) (pointOver k M (𝟙 _) p hp) =
      pointOver k M t p hp := by
    apply Subtype.ext
    change t ≫ (𝟙 _ ≫ genericPoint k M p hp) = t ≫ genericPoint k M p hp
    rw [Category.id_comp]
  simpa only [hp'] using (ht t x).symm

/-- The residual automorphism criterion is equivalent to the full frozen
translation predicate; it neither weakens the test-scheme quantifier nor
changes the generic structure map. -/
lemma translation_iff_residual_eq_id (G : Law k M) (p : baseScheme k ⟶ M.X)
    (hp : p ≫ M.p = 𝟙 _) (τ : genericScheme k M ≅ genericScheme k M)
    (hτ : IsTranslation k M G p hp τ.hom)
    (f : genericScheme k M ⟶ genericScheme k M) :
    IsTranslation k M G p hp f ↔ f ≫ τ.inv = 𝟙 _ := by
  rw [isTranslation_iff, (isTranslation_iff k M G p hp τ.hom).mp hτ]
  constructor
  · intro h
    rw [← h]
    exact τ.hom_inv_id
  · intro h
    have hh := congrArg (fun g => g ≫ τ.hom) h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp] using hh.symm

/-- The residual map for an actual scalar fixes the specified generic origin.
The remaining required geometric assertion is that this residual map is the
identity, not merely that it fixes the origin. -/
lemma scalar_residual_origin (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) a p)
    (τ : genericScheme k M ≅ genericScheme k M)
    (hτ : IsTranslation k M G p hp.1 τ.hom) :
    genericPoint k M s hs.1 ≫ (scalarMap k M rot scal inv ha a ≫ τ.inv) =
      genericPoint k M s hs.1 := by
  have hzero := hτ (𝟙 _) (G.one (𝟙 _))
  rw [G.one_mul, hG.1] at hzero
  change (𝟙 _ ≫ genericPoint k M p hp.1) =
    (𝟙 _ ≫ genericPoint k M s hs.1) ≫ τ.hom at hzero
  simp only [Category.id_comp] at hzero
  rw [← Category.assoc, scalar_origin k M h3 hM s hs rot scal inv ha a p hp,
    hzero, Category.assoc, Iso.hom_inv_id]
  exact Category.comp_id _

/-- For each scalar, removing the expected translation leaves a genuine
automorphism over the fixed base which fixes the marked origin and is a group
homomorphism on all test schemes. No identity assertion is assumed here. -/
lemma scalar_residual_is_group_automorphism (h3 : 3 ≤ r) (heven : Even r)
    (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a : kˣ)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) a p) :
    ∃ (τ e : genericScheme k M ≅ genericScheme k M)
      (he : e.hom ≫ genericStructure k M = genericStructure k M),
      IsTranslation k M G p hp.1 τ.hom ∧
      e.hom = scalarMap k M rot scal inv ha a ≫ τ.inv ∧
      genericPoint k M s hs.1 ≫ e.hom = genericPoint k M s hs.1 ∧
      (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
        (x y : SchemeHomOver t (genericStructure k M)),
        ActualGenericGroupLaw.pointsEquiv e he t (G.mul t x y) =
          G.mul t (ActualGenericGroupLaw.pointsEquiv e he t x)
            (ActualGenericGroupLaw.pointsEquiv e he t y)) := by
  obtain ⟨τ, hτover, hτ⟩ := exists_translationIso k M G p hp.1
  let e := genericIso k M (scal a) (modelOver k M id a false (scal a) (ha.2.1 a)) ≪≫ τ.symm
  have heq : e.hom = scalarMap k M rot scal inv ha a ≫ τ.inv := rfl
  have hi : τ.inv ≫ genericStructure k M = genericStructure k M := by
    rw [← hτover, Iso.inv_hom_id_assoc]
    exact hτover.symm
  have he : e.hom ≫ genericStructure k M = genericStructure k M := by
    rw [heq, Category.assoc, hi]
    exact pullback.lift_snd _ _ _
  have ho : genericPoint k M s hs.1 ≫ e.hom = genericPoint k M s hs.1 := by
    rw [heq]
    exact scalar_residual_origin k M h3 hM s hs G hG rot scal inv ha a p hp τ hτ
  refine ⟨τ, e, he, hτ, heq, ho, ?_⟩
  intro V t x y
  exact originPreserving_mul k M h3 heven hM s hs G hG e he ho t x y

/-- Distinct scalar parameters remain distinct on the zeroth infinitesimal
chart, as detected by its actual coordinate x. -/
lemma markedPoint_injective : Function.Injective
    (ArithmeticThetaPolygonCohomologyR0131.markedPoint k 0) := by
  intro a b h
  have hx := RingHom.congr_fun h (coordX k 0)
  simp only [ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137.point_x] at hx
  let : Nontrivial (R k 0) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)).ne_top
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.pow_le_self (by omega)
  have hinj := ((trunc (PowerSeries k) PowerSeries.X 0).comp PowerSeries.C).injective
  apply Units.ext
  exact hinj hx

/-- Distinct unit markings on a fixed component are distinct actual sections. -/
lemma markedLift_parameter_injective (hM : IsModel k T M) (i : Fin r)
    {a b : kˣ} (s p : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M i a s) (hp : MarkedLift k M i b p) (hsp : s = p) : a = b := by
  have h0 := (hs.2 0).symm.trans ((congrArg (fun f => baseInclusion k 0 ≫ f) hsp).trans (hp.2 0))
  let : IsClosedImmersion (M.inclusion 0) :=
    ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGeometricConnectednessR0135.stage_closed k M hM 0
  have hmarks := (cancel_mono (M.inclusion 0)).mp h0
  let : IsOpenImmersion ((T.atlas 0).chart i) := (T.atlas 0).chart_open i
  have hpoints := (cancel_mono ((T.atlas 0).chart i)).mp hmarks
  apply markedPoint_injective k
  exact CommRingCat.hom_ext_iff.mp (Spec.map_injective hpoints)

/-- Separatedness of the proper model detects equality of sections on its
actual generic base, so different scalar markings remain different there. -/
lemma genericMarkedPoint_parameter_injective (hM : IsModel k T M) (i : Fin r)
    {a b : kˣ} (s p : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M i a s) (hp : MarkedLift k M i b p)
    (hsp : genericPoint k M s hs.1 = genericPoint k M p hp.1) : a = b := by
  apply markedLift_parameter_injective k M hM i s p hs hp
  let : IsProper M.p := hM.1
  let : IsReduced (baseScheme k) := inferInstanceAs (IsReduced (Spec (CommRingCat.of (PowerSeries k))))
  let : IsSchemeTheoreticallyDominant (genericBase k) :=
    GenericDualLocalizationR0140.genericBase_schematic k
  apply ext_of_isDominant_of_isSeparated M.p (hs.1.trans hp.1.symm) (genericBase k)
  have h := congrArg (fun f => f ≫ genericInclusion k M) hsp
  simpa only [ArithmeticThetaGenericEvaluationR0140.genericPoint,
    genericInclusion, pullback.lift_fst] using h

/-- The actual scalar orbit of the marked origin is faithful on the generic
fiber, with no assumption on torsion or an algebraic closure. -/
lemma scalar_origin_orbit_injective (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) :
    Function.Injective (fun a : kˣ =>
      genericPoint k M s hs.1 ≫ scalarMap k M rot scal inv ha a) := by
  intro a b h
  obtain ⟨p, hp, _⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) a
  obtain ⟨q, hq, _⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) b
  exact genericMarkedPoint_parameter_injective k M hM (zeroIndex r hr) p q hp hq
    ((scalar_origin k M h3 hM s hs rot scal inv ha a p hp).symm.trans
      (h.trans (scalar_origin k M h3 hM s hs rot scal inv ha b q hq)))

lemma scalar_origin_orbit_infinite (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) :
    (Set.range (fun a : kˣ => genericPoint k M s hs.1 ≫ scalarMap k M rot scal inv ha a)).Infinite := by
  let f : ℕ → kˣ := fun n => Units.mk0 (n + 1 : ℕ) (by exact_mod_cast Nat.succ_ne_zero n)
  have hf : Function.Injective f := by
    intro n m h
    have hv := congrArg Units.val h
    change ((n + 1 : ℕ) : k) = ((m + 1 : ℕ) : k) at hv
    have hn : n + 1 = m + 1 := Nat.cast_injective hv
    omega
  let : Infinite kˣ := Infinite.of_injective f hf
  exact Set.infinite_range_of_injective (scalar_origin_orbit_injective k M h3 hM s hs rot scal inv ha)

lemma genericMap_congr (f g : M.X ⟶ M.X) (hf : f ≫ M.p = M.p)
    (hg : g ≫ M.p = M.p) (h : f = g) : genericMap k M f hf = genericMap k M g hg := by
  subst g
  rfl

lemma scalarMap_one (h3 : 3 ≤ r) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) : scalarMap k M rot scal inv ha 1 = 𝟙 _ := by
  exact genericMap_eq_id k M _ _
    (algebraized_action_laws k r hr h3 T M hM rot scal inv ha).2.1

lemma scalarMap_mul (h3 : 3 ≤ r) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a b : kˣ) :
    scalarMap k M rot scal inv ha (a * b) =
      scalarMap k M rot scal inv ha a ≫ scalarMap k M rot scal inv ha b := by
  have hm := (algebraized_action_laws k r hr h3 T M hM rot scal inv ha).2.2.1 a b
  exact (genericMap_congr k M _ _ _ _ hm).trans (genericMap_comp k M _ _ _ _)

lemma scalarMap_pow (h3 : 3 ≤ r) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a : kˣ) (n : ℕ) :
    iterateHom (scalarMap k M rot scal inv ha a) n = scalarMap k M rot scal inv ha (a ^ n) := by
  induction n with
  | zero => simpa only [iterateHom, pow_zero] using (scalarMap_one k M h3 hM rot scal inv ha).symm
  | succ n ih => rw [iterateHom, ih, pow_succ, scalarMap_mul k M h3 hM]

lemma scalarMap_injective (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) :
    Function.Injective (scalarMap k M rot scal inv ha) := by
  intro a b h
  apply scalar_origin_orbit_injective k M h3 hM s hs rot scal inv ha
  exact congrArg (fun f => genericPoint k M s hs.1 ≫ f) h

/-- The exact order of a scalar is already faithfully detected by its actual
geometric automorphism, before any group-translation comparison is used. -/
lemma scalarMap_iterate_eq_id_iff (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (a : kˣ) (n : ℕ) :
    iterateHom (scalarMap k M rot scal inv ha a) n = 𝟙 _ ↔ a ^ n = 1 := by
  rw [scalarMap_pow k M h3 hM, ← scalarMap_one k M h3 hM rot scal inv ha]
  exact (scalarMap_injective k M h3 hM s hs rot scal inv ha).eq_iff

#print axioms scalarMap_iterate_eq_id_iff
#print axioms scalar_origin_orbit_injective
#print axioms scalar_origin_orbit_infinite
#print axioms markedPoint_injective
#print axioms markedLift_parameter_injective
#print axioms genericMarkedPoint_parameter_injective
#print axioms isTranslation_iff
#print axioms genericPoint_map
#print axioms scalar_origin
#print axioms scalar_one
#print axioms originPreserving_mul
#print axioms exists_translationIso
#print axioms translation_iff_residual_eq_id
#print axioms scalar_residual_origin
#print axioms genericIso
#print axioms scalar_residual_is_group_automorphism
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation

set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-! Universe-polymorphic geometric classification helpers, locally ported
from the checked controlled library. Upstream sources and hashes are recorded
in UniversePortProvenance.json. -/
namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open Polynomial
open scoped Polynomial.Bivariate

namespace VarChangeAlgAux

variable {T : Type u} [CommRing T]

noncomputable def φ₁ (v₁ r : T) : T[X] →+* T[X] := eval₂RingHom C (C v₁ * X + C r)

@[scoped simp] theorem φ₁_C (v₁ r a : T) : φ₁ v₁ r (C a) = C a := by simp [φ₁]
@[scoped simp] theorem φ₁_X (v₁ r : T) : φ₁ v₁ r X = C v₁ * X + C r := by simp [φ₁]

noncomputable def σ (v₁ v₂ r s' t : T) : T[X][Y] →+* T[X][Y] :=
  eval₂RingHom (C.comp (φ₁ v₁ r)) (C (C v₂) * X + C (C s' * X + C t))

@[scoped simp] theorem σ_C (v₁ v₂ r s' t : T) (p : T[X]) : σ v₁ v₂ r s' t (C p) = C (φ₁ v₁ r p) := by simp [σ]
@[scoped simp] theorem σ_X (v₁ v₂ r s' t : T) : σ v₁ v₂ r s' t X = C (C v₂) * X + C (C s' * X + C t) := by simp [σ]

noncomputable def Lpoly (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) : T[X] :=
  C v₂ * (2 * (C s' * X + C t) + (C W.a₁ * (C v₁ * X + C r) + C W.a₃))
noncomputable def Kpoly (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) : T[X] :=
  (C s' * X + C t) ^ 2 + (C W.a₁ * (C v₁ * X + C r) + C W.a₃) * (C s' * X + C t)
    - ((C v₁ * X + C r) ^ 3 + C W.a₂ * (C v₁ * X + C r) ^ 2 + C W.a₄ * (C v₁ * X + C r) + C W.a₆)

theorem σ_polynomial (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) :
    σ v₁ v₂ r s' t W.toAffine.polynomial =
      C (C v₂ ^ 2) * X ^ 2 + C (Lpoly W v₁ v₂ r s' t) * X + C (Kpoly W v₁ v₂ r s' t) := by
  simp only [WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow, σ_C, σ_X, φ₁_C, φ₁_X,
    Lpoly, Kpoly, map_ofNat]
  ring

end VarChangeAlgAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular.VarChangeAlgAux"

namespace VarChangeAlgAux

theorem coeffs_eq_zero_of_cubic {T : Type u} [CommRing T] (k₀ k₁ k₂ k₃ : T)
    (h : C k₀ + C k₁ * X + C k₂ * X ^ 2 + C k₃ * X ^ 3 = (0 : T[X])) :
    k₀ = 0 ∧ k₁ = 0 ∧ k₂ = 0 ∧ k₃ = 0 := by
  have h0 := congrArg (fun p : T[X] => p.coeff 0) h
  have h1 := congrArg (fun p : T[X] => p.coeff 1) h
  have h2 := congrArg (fun p : T[X] => p.coeff 2) h
  have h3 := congrArg (fun p : T[X] => p.coeff 3) h
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_zero] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem coeffs_eq_zero_of_linear {T : Type u} [CommRing T] (k₀ k₁ : T)
    (h : C k₀ + C k₁ * X = (0 : T[X])) : k₀ = 0 ∧ k₁ = 0 := by
  have := coeffs_eq_zero_of_cubic k₀ k₁ 0 0 (by rw [h]; simp)
  exact ⟨this.1, this.2.1⟩

end VarChangeAlgAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular.VarChangeAlgAux"

open VarChangeAlgAux in
theorem solution
    (T : Type u) [CommRing T] (W W' : WeierstrassCurve T)
    (g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
      (v₁ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ r)
    (hy : g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
      (v₂ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
        s' • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ t) :
    ∃ C : WeierstrassCurve.VariableChange T,
      C • W = W' ∧ ((C.u : T) ^ 2 = v₁ ∧ (C.u : T) ^ 3 = v₂) ∧ C.r = r ∧ (C.u : T) ^ 2 * C.s = s' ∧ C.t = t := by
  classical
  rcases subsingleton_or_nontrivial T with hT | hT
  · refine ⟨⟨v₁, r, 0, t⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl⟩ <;> first | exact Subsingleton.elim _ _ | skip
    exact WeierstrassCurve.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)

  set σ' := σ (v₁ : T) (v₂ : T) r s' t with hσ'
  have hmkC : ∀ (V : WeierstrassCurve T) (a : T),
      WeierstrassCurve.Affine.CoordinateRing.mk V (C (C a)) = algebraMap T V.toAffine.CoordinateRing a := by
    intro V a; rfl
  have key : g.toRingHom.comp (WeierstrassCurve.Affine.CoordinateRing.mk W) =
      (WeierstrassCurve.Affine.CoordinateRing.mk W').comp σ' := by
    apply Polynomial.ringHom_ext
    · intro p

      revert p
      suffices h : (g.toRingHom.comp (WeierstrassCurve.Affine.CoordinateRing.mk W)).comp C =
          ((WeierstrassCurve.Affine.CoordinateRing.mk W').comp σ').comp C from fun p => RingHom.congr_fun h p
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, hσ', σ_C, φ₁_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hmkC,
          AlgHom.commutes]
      · simp only [RingHom.comp_apply, hσ', σ_C, φ₁_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hx,
          map_add, map_mul, hmkC, Algebra.smul_def]
    · simp only [RingHom.comp_apply, hσ', σ_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hy, map_add,
        map_mul, hmkC, Algebra.smul_def]
      ring

  have hdvd : W'.toAffine.polynomial ∣ σ' W.toAffine.polynomial := by
    rw [← AdjoinRoot.mk_eq_zero]
    have := RingHom.congr_fun key W.toAffine.polynomial
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W' = AdjoinRoot.mk _ from rfl] at this
    rw [← this, show WeierstrassCurve.Affine.CoordinateRing.mk W = AdjoinRoot.mk _ from rfl, AdjoinRoot.mk_self,
      map_zero]

  obtain ⟨Q, hQ⟩ := hdvd
  rw [hσ', σ_polynomial] at hQ
  set L := Lpoly W (v₁ : T) (v₂ : T) r s' t with hL
  set K := Kpoly W (v₁ : T) (v₂ : T) r s' t with hK
  set A₁ : T[X] := L - C (v₂ : T) ^ 2 * (C W'.a₁ * X + C W'.a₃) with hA₁
  set A₀ : T[X] := K + C (v₂ : T) ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) with hA₀
  have hmon : W'.toAffine.polynomial.Monic := WeierstrassCurve.Affine.monic_polynomial
  have hsplit : (C A₁ * X + C A₀) + W'.toAffine.polynomial * C (C (v₂ : T) ^ 2) =
      C (C (v₂ : T) ^ 2) * X ^ 2 + C L * X + C K := by
    simp only [hA₁, hA₀, WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow]
    ring
  have hdeg2 : W'.toAffine.polynomial.degree = 2 := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, WeierstrassCurve.Affine.natDegree_polynomial]; rfl
  have hdegr : (C A₁ * X + C A₀).degree < W'.toAffine.polynomial.degree := by
    rw [hdeg2]
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hu1 := Polynomial.div_modByMonic_unique (C (C (v₂ : T) ^ 2)) (C A₁ * X + C A₀) hmon ⟨hsplit, hdegr⟩
  have hu2 := Polynomial.div_modByMonic_unique (f := C (C (v₂ : T) ^ 2) * X ^ 2 + C L * X + C K) Q 0 hmon
    ⟨by rw [zero_add]; exact hQ.symm, by
    rw [degree_zero, hdeg2]; exact WithBot.bot_lt_coe _⟩
  have hrem : C A₁ * X + C A₀ = 0 := hu1.2.symm.trans hu2.2
  have hA : A₀ = 0 ∧ A₁ = 0 := by
    have := VarChangeAlgAux.coeffs_eq_zero_of_linear A₀ A₁ (by rw [← hrem]; ring)
    exact this
  obtain ⟨hA₀0, hA₁0⟩ := hA

  have hLin : C ((v₂ : T) * (2 * t + W.a₁ * r + W.a₃) - (v₂ : T) ^ 2 * W'.a₃) +
      C ((v₂ : T) * (2 * s' + W.a₁ * v₁) - (v₂ : T) ^ 2 * W'.a₁) * X = (0 : T[X]) := by
    rw [← hA₁0, hA₁, hL, Lpoly]
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow, map_ofNat]
    ring
  obtain ⟨e₃, e₁⟩ := VarChangeAlgAux.coeffs_eq_zero_of_linear _ _ hLin
  have hCub : C (t ^ 2 + (W.a₁ * r + W.a₃) * t - (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆) + (v₂ : T) ^ 2 * W'.a₆) +
      C (2 * s' * t + W.a₁ * (v₁ : T) * t + (W.a₁ * r + W.a₃) * s' - (3 * (v₁ : T) * r ^ 2 + 2 * W.a₂ * v₁ * r + W.a₄ * v₁)
        + (v₂ : T) ^ 2 * W'.a₄) * X +
      C (s' ^ 2 + W.a₁ * (v₁ : T) * s' - (3 * (v₁ : T) ^ 2 * r + W.a₂ * (v₁ : T) ^ 2) + (v₂ : T) ^ 2 * W'.a₂) * X ^ 2 +
      C (-(v₁ : T) ^ 3 + (v₂ : T) ^ 2) * X ^ 3 = (0 : T[X]) := by
    rw [← hA₀0, hA₀, hK, Kpoly]
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_neg, map_ofNat]
    ring
  obtain ⟨e₆, e₄, e₂, e₀⟩ := VarChangeAlgAux.coeffs_eq_zero_of_cubic _ _ _ _ hCub

  set w₁ : T := ↑v₁⁻¹ with hw₁
  set w₂ : T := ↑v₂⁻¹ with hw₂
  have hv₁ : (v₁ : T) * w₁ = 1 := by rw [hw₁]; exact Units.mul_inv v₁
  have hv₂ : (v₂ : T) * w₂ = 1 := by rw [hw₂]; exact Units.mul_inv v₂
  have hrel : (v₁ : T) ^ 3 = (v₂ : T) ^ 2 := by linear_combination (-1 : T) * e₀
  have f₁ : W'.a₁ = w₂ * (2 * s' + W.a₁ * v₁) := by
    linear_combination (-w₂ ^ 2) * e₁ + (w₂ * (2 * s' + W.a₁ * v₁) - W'.a₁ * ((v₂ : T) * w₂ - 1) - 2 * W'.a₁) * hv₂
  have f₃ : W'.a₃ = w₂ * (2 * t + W.a₁ * r + W.a₃) := by
    linear_combination (-w₂ ^ 2) * e₃ + (w₂ * (2 * t + W.a₁ * r + W.a₃) - W'.a₃ * ((v₂ : T) * w₂ - 1) - 2 * W'.a₃) * hv₂
  have f₂ : W'.a₂ = w₂ ^ 2 * (3 * (v₁ : T) ^ 2 * r + W.a₂ * (v₁ : T) ^ 2 - s' ^ 2 - W.a₁ * v₁ * s') := by
    linear_combination (w₂ ^ 2) * e₂ + (-(W'.a₂) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₂) * hv₂
  have f₄ : W'.a₄ = w₂ ^ 2 * (3 * (v₁ : T) * r ^ 2 + 2 * W.a₂ * v₁ * r + W.a₄ * v₁ - 2 * s' * t - W.a₁ * v₁ * t
      - (W.a₁ * r + W.a₃) * s') := by
    linear_combination (w₂ ^ 2) * e₄ + (-(W'.a₄) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₄) * hv₂
  have f₆ : W'.a₆ = w₂ ^ 2 * (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆ - t ^ 2 - (W.a₁ * r + W.a₃) * t) := by
    linear_combination (w₂ ^ 2) * e₆ + (-(W'.a₆) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₆) * hv₂
  have hu : (((v₂ * v₁⁻¹ : Tˣ))⁻¹ : Tˣ) = v₁ * v₂⁻¹ := by rw [mul_inv_rev, inv_inv]
  refine ⟨⟨v₂ * v₁⁻¹, r, s' * w₁, t⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl⟩
  · apply WeierstrassCurve.ext
    · simp only [WeierstrassCurve.variableChange_a₁, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₁ + (2 * w₂ * s') * hv₁
    · simp only [WeierstrassCurve.variableChange_a₂, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₂ + (w₂ ^ 2 * (-((v₁ : T) * s' * W.a₁) - s' ^ 2 * ((v₁ : T) * w₁ + 1))) * hv₁
    · simp only [WeierstrassCurve.variableChange_a₃, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₃ + ((W.a₃ + r * W.a₁ + 2 * t) * w₂ ^ 3) * hrel
        + ((W.a₃ + r * W.a₁ + 2 * t) * w₂ * ((v₂ : T) * w₂ + 1)) * hv₂
    · simp only [WeierstrassCurve.variableChange_a₄, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₄
        + ((W.a₄ - s' * w₁ * W.a₃ + 2 * r * W.a₂ - (t + r * (s' * w₁)) * W.a₁ + 3 * r ^ 2 - 2 * (s' * w₁) * t)
            * (v₁ : T) * w₂ ^ 4) * hrel
        + ((W.a₄ - s' * w₁ * W.a₃ + 2 * r * W.a₂ - (t + r * (s' * w₁)) * W.a₁ + 3 * r ^ 2 - 2 * (s' * w₁) * t)
            * (v₁ : T) * w₂ ^ 2 * ((v₂ : T) * w₂ + 1)) * hv₂
        + (w₂ ^ 2 * (-(s' * W.a₃) - r * s' * W.a₁ - 2 * s' * t)) * hv₁
    · simp only [WeierstrassCurve.variableChange_a₆, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₆
        + ((W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁) * w₂ ^ 6
            * ((v₁ : T) ^ 3 + (v₂ : T) ^ 2)) * hrel
        + ((W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁) * w₂ ^ 2
            * (((v₂ : T) * w₂) ^ 3 + ((v₂ : T) * w₂) ^ 2 + (v₂ : T) * w₂ + 1)) * hv₂
  · rw [Units.val_mul, mul_pow]
    linear_combination (-w₁ ^ 2) * hrel + ((v₁ : T) * ((v₁ : T) * w₁ + 1)) * hv₁
  · rw [Units.val_mul, mul_pow]
    linear_combination (-(v₂ : T) * w₁ ^ 3) * hrel + ((v₂ : T) * (((v₁ : T) * w₁) ^ 2 + (v₁ : T) * w₁ + 1)) * hv₁
  · rw [Units.val_mul]
    linear_combination (-(s') * w₁ ^ 3) * hrel + (s' * (((v₁ : T) * w₁) ^ 2 + (v₁ : T) * w₁ + 1)) * hv₁

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartExt

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DenseExtAux

section Affine

theorem specMap_appTop_injective {B B' : Type u} [CommRing B] [CommRing B'] (l : B →+* B') (hl : Function.Injective l) :
    Function.Injective (Spec.map (CommRingCat.ofHom l)).appTop := by
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom l)

  intro a b hab
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom l =
      (Spec.map (CommRingCat.ofHom l)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom := hnat.symm
  have h2 := congrArg (fun φ => φ.hom a) h1
  have h3 := congrArg (fun φ => φ.hom b) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  rw [hab] at h2
  have h4 : l ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a) = l ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom b) := by
    rw [h2, h3]
  have h5 := hl h4
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1
  exact hinj h5

theorem hom_ext_of_specMap_comp_eq_of_injective {B B' : Type u} [CommRing B] [CommRing B']
    {Y : Scheme.{u}} [Y.IsSeparated] (u v : Spec (CommRingCat.of B) ⟶ Y)
    (l : B →+* B') (hl : Function.Injective l)
    (h : Spec.map (CommRingCat.ofHom l) ≫ u = Spec.map (CommRingCat.ofHom l) ≫ v) : u = v := by
  let e := equalizer.ι u v
  let k := equalizer.lift (Spec.map (CommRingCat.ofHom l)) h
  have hk : k ≫ e = Spec.map (CommRingCat.ofHom l) := equalizer.lift_ι _ _
  have hinj : Function.Injective e.appTop := by
    have h1 := specMap_appTop_injective l hl
    rw [← hk, Scheme.Hom.comp_appTop] at h1
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h1
    exact h1.of_comp
  haveI : IsIso e := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  rw [← cancel_epi e]
  exact equalizer.condition u v

end Affine

section NZD

open MvPolynomial in

theorem mem_span_of_X_one_mul_mem {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    (p : MvPolynomial (Fin 2) T)
    (hp : X 1 * p ∈ Ideal.span {(MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial)}) :
    p ∈ Ideal.span {(MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial)} := by
  classical
  set F : MvPolynomial (Fin 2) T := MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial with hF
  let e := MvPolynomial.finSuccEquiv T 1

  set z : MvPolynomial (Fin 1) T := MvPolynomial.X 0 with hz
  set g : Polynomial (MvPolynomial (Fin 1) T) :=
    Polynomial.X ^ 3 + Polynomial.C (MvPolynomial.C V.a₂ * z) * Polynomial.X ^ 2
      + Polynomial.C (MvPolynomial.C V.a₄ * z ^ 2 - MvPolynomial.C V.a₁ * z) * Polynomial.X
      + Polynomial.C (MvPolynomial.C V.a₆ * z ^ 3 - z - MvPolynomial.C V.a₃ * z ^ 2) with hg
  have heF : e F = -g := by
    rw [hF, hg, hz, WeierstrassCurve.Projective.polynomial]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      MvPolynomial.algebraMap_eq]
    have e0 : e (MvPolynomial.X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
    have e1 : e (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
      have := @MvPolynomial.finSuccEquiv_X_succ T _ 1 (0 : Fin 1)
      simpa using this
    have eC : ∀ a : T, e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := fun a => by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl
    simp only [e0, e1, eC, map_one]
    try simp only [map_sub, map_mul, map_pow, map_add, Polynomial.C_mul, Polynomial.C_pow]
    ring
  have hgm : g.Monic := by
    rw [hg]
    monicity!

  have hmap : (Ideal.span {F}).map (e : MvPolynomial (Fin 2) T →+* _) = Ideal.span {g} := by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {e F} = _
    rw [heF, Ideal.span_singleton_neg]
  have hp' : Polynomial.C z * e p ∈ Ideal.span {g} := by
    have : e (MvPolynomial.X 1 * p) ∈ (Ideal.span {F}).map (e : MvPolynomial (Fin 2) T →+* _) :=
      Ideal.mem_map_of_mem _ hp
    rw [hmap, map_mul] at this
    have e1 : e (MvPolynomial.X 1) = Polynomial.C z := by
      have := @MvPolynomial.finSuccEquiv_X_succ T _ 1 (0 : Fin 1)
      simpa [hz] using this
    rwa [e1] at this

  rw [Ideal.mem_span_singleton] at hp'
  have h0 : (Polynomial.C z * e p) %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hgm).mpr hp'
  rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic] at h0
  have h1 : e p %ₘ g = 0 := by
    refine Polynomial.ext fun n => ?_
    have hc := congrArg (fun r => Polynomial.coeff r n) h0
    simp only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] at hc
    rw [Polynomial.coeff_zero]
    have hreg : IsLeftRegular z := by rw [hz]; exact (MvPolynomial.isRegular_X).left
    exact hreg (show z * _ = z * 0 by rw [mul_zero]; exact hc)
  have h2 : g ∣ e p := (Polynomial.modByMonic_eq_zero_iff_dvd hgm).mp h1
  obtain ⟨H, hH⟩ := h2
  have hsg : e.symm g = -F := by
    have : g = -e F := by rw [heF, neg_neg]
    rw [this, map_neg, AlgEquiv.symm_apply_apply]
  have hp2 : p = -F * e.symm H := by
    rw [← e.symm_apply_apply p, hH, map_mul, hsg]
  rw [hp2]
  exact Ideal.mul_mem_right _ _ ((Ideal.span {F}).neg_mem (Ideal.mem_span_singleton_self F))

theorem zOverY_mul_eq_zero {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    (b : OriginChartRing V) (hb : zOverY V * b = 0) : b = 0 := by
  classical
  obtain ⟨f, hbij, hsc, hval⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V

  have hfz : f (zOverY V) = Ideal.Quotient.mk _ (MvPolynomial.X 1) := by
    have := hval 1 (MvPolynomial.X 2) (by simpa using MvPolynomial.isHomogeneous_X T 2)
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    convert this using 2
    rfl
  obtain ⟨pb, hpb⟩ := Ideal.Quotient.mk_surjective (f b)
  have h1 : f (zOverY V * b) = 0 := by rw [hb, map_zero]
  rw [map_mul, hfz, ← hpb, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : pb ∈ Ideal.span (Set.range fun _ : Fin 1 =>
      MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial) := by
    have hset : (Set.range fun _ : Fin 1 =>
        MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial) =
        {MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial} := by
      ext x; simp
    rw [hset] at h1 ⊢
    exact mem_span_of_X_one_mul_mem V pb h1
  have h3 : f b = 0 := by rw [← hpb]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  exact hbij.1 (by rw [h3, map_zero])

end NZD

section Charts

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem polynomial_add_X0_cube :
    V.polynomial + MvPolynomial.X 0 ^ 3 = MvPolynomial.X 2 * (MvPolynomial.X 1 ^ 2 + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.C V.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2
      - MvPolynomial.C V.a₂ * MvPolynomial.X 0 ^ 2 - MvPolynomial.C V.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2
      - MvPolynomial.C V.a₆ * MvPolynomial.X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    show (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (MvPolynomial.X 0)) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (MvPolynomial.X i : MvPolynomial (Fin 3) T))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR T V hz)

end Charts

end DenseExtAux

namespace DenseExtAux

section Glue

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem zOverY_pow_mem_nonZeroDivisors (n : ℕ) : zOverY V ^ n ∈ nonZeroDivisors (OriginChartRing V) := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem _
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem ih (by
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun b hb => zOverY_mul_eq_zero V b hb, fun b hb => zOverY_mul_eq_zero V b (by rw [mul_comm]; exact hb)⟩)

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  unfold Away.isLocalizationElem zOverY
  congr 1
  exact pow_one _

theorem awayMap_injective :
    Function.Injective (awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)) := by
  letI := (awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)).toAlgebra
  have hloc := Away.isLocalization_mul (𝒜 := projModelGradingCR V) (coord_mem V 1) (coord_mem V 2)
    (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2) one_ne_zero
  have hM : Submonoid.powers (Away.isLocalizationElem (𝒜 := projModelGradingCR V) (coord_mem V 1) (coord_mem V 2)) ≤
      nonZeroDivisors (OriginChartRing V) := by
    rintro _ ⟨n, rfl⟩
    rw [isLocalizationElem_eq_zOverY]
    exact zOverY_pow_mem_nonZeroDivisors V n
  haveI := hloc
  exact IsLocalization.injective (Away (projModelGradingCR V) (coord V 1 * coord V 2)) hM

theorem hom_ext_originChart {Y : Scheme.{u}} [Y.IsSeparated] (u v : Spec (CommRingCat.of (OriginChartRing V)) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ u =
      Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ v) : u = v :=
  hom_ext_of_specMap_comp_eq_of_injective u v _ (awayMap_injective V) h

theorem specMap_awayMap_comp_originChartι :
    Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ originChartι V =
      Proj.awayι (projModelGradingCR V) (coord V 1 * coord V 2)
        (SetLike.mul_mem_graded (coord_mem V 1) (coord_mem V 2)) (by norm_num) :=
  Proj.SpecMap_awayMap_awayι _ _ _ _ _

theorem specMap_awayMap_comp_zChartι :
    Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 1)
        (mul_comm (coord V 2) (coord V 1) ▸ rfl : coord V 1 * coord V 2 = coord V 2 * coord V 1))) ≫ zChartι V =
      Proj.awayι (projModelGradingCR V) (coord V 1 * coord V 2)
        (SetLike.mul_mem_graded (coord_mem V 1) (coord_mem V 2)) (by norm_num) :=
  Proj.SpecMap_awayMap_awayι _ _ _ _ _

noncomputable def twoChartCover : (projModelCR V).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b (Spec (CommRingCat.of (ZChartRing V))) (Spec (CommRingCat.of (OriginChartRing V))))
    (fun b => match b with
      | true => zChartι V
      | false => originChartι V)
    (by
      intro x
      by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
      · have hx : x ∈ (zChartι V).opensRange := by
          rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
          exact fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
        obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
        exact ⟨true, y, hy⟩
      · have hx : x ∈ (originChartι V).opensRange := by
          rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
          exact h1
        obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
        exact ⟨false, y, hy⟩)
    (fun b => by
      cases b
      · show IsOpenImmersion (originChartι V); infer_instance
      · show IsOpenImmersion (zChartι V); infer_instance)

end Glue

end DenseExtAux

open DenseExtAux

theorem solution
    (T : Type u) [CommRing T] (W : WeierstrassCurve T)
    {Y : Scheme.{u}} [Y.IsSeparated]
    (f g : projModelCR W.toProjective ⟶ Y)
    (h : zChartι W.toProjective ≫ f = zChartι W.toProjective ≫ g) : f = g := by
  have hY : originChartι W.toProjective ≫ f = originChartι W.toProjective ≫ g := by
    apply hom_ext_originChart W.toProjective
    have e1 := specMap_awayMap_comp_originChartι W.toProjective
    have e2 := specMap_awayMap_comp_zChartι W.toProjective
    rw [← Category.assoc, e1, ← e2, Category.assoc, h, ← Category.assoc, e2, ← e1, Category.assoc]
  exact Scheme.Cover.hom_ext (twoChartCover W.toProjective) f g (fun b => by
    cases b
    · exact hY
    · exact h)

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartExt

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace OverlapAux

section Away

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable abbrev toOverlapY : OriginChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)

noncomputable abbrev toOverlapZ : ZChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 1)
    ((rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2).trans (mul_comm _ _))

theorem overlap_identities :
    toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V) = toOverlapY V (xOverY V) ∧
    toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V) = 1 := by
  constructor
  · unfold toOverlapZ toOverlapY xOverZ zOverY xOverY
    rw [awayMap_mk, awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one]
    ring
  · unfold toOverlapZ toOverlapY yOverZ zOverY
    rw [awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, Away.val_mk, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one, mul_one]
    ring

theorem exists_overlap_hom_of_specMap_comp_eq {S : Type u} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    ∃ c : Away (projModelGradingCR V) (coord V 1 * coord V 2) →+* S,
      c.comp (toOverlapY V) = a ∧ c.comp (toOverlapZ V) = b := by
  let P := pullback.lift (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) h
  let e := Proj.pullbackAwayιIso (projModelGradingCR V) (coord_mem V 1) one_pos (coord_mem V 2) one_pos
    (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)
  obtain ⟨c, hc⟩ := Spec.map_surjective (P ≫ e.hom)
  have ha : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapY V)) = Spec.map (CommRingCat.ofHom a) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left]
    exact pullback.lift_fst _ _ _
  have hb : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapZ V)) = Spec.map (CommRingCat.ofHom b) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right]
    exact pullback.lift_snd _ _ _
  rw [← Spec.map_comp] at ha hb
  have ha' := Spec.map_injective ha
  have hb' := Spec.map_injective hb
  refine ⟨c.hom, ?_, ?_⟩
  · ext r; exact congrArg (fun φ => φ.hom r) ha'
  · ext r; exact congrArg (fun φ => φ.hom r) hb'

theorem zChart_mul_originChart_of_specMap_comp_eq {S : Type u} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    b (xOverZ V) * a (zOverY V) = a (xOverY V) ∧ b (yOverZ V) * a (zOverY V) = 1 := by
  obtain ⟨c, hca, hcb⟩ := exists_overlap_hom_of_specMap_comp_eq V a b h
  obtain ⟨h1, h2⟩ := overlap_identities V
  subst hca hcb
  simp only [RingHom.comp_apply]
  refine ⟨?_, ?_⟩
  · calc c (toOverlapZ V (xOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c (toOverlapY V (xOverY V)) := congrArg c h1
  · calc c (toOverlapZ V (yOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c 1 := congrArg c h2
      _ = 1 := map_one c

end Away

end OverlapAux

namespace OverlapAux

section Str

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable def zStr : T →+* ZChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

noncomputable def oStr : T →+* OriginChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

theorem zChartι_comp_projModelStrCR : zChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (zStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem originChartι_comp_projModelStrCR :
    originChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (oStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem zChart_ringHom_ext {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (zStr V) = g₂.comp (zStr V))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = zStr V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Str

section Laurent

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  unfold Away.isLocalizationElem zOverY
  congr 1
  exact pow_one _

theorem specMap_comp_zChartι_eq_of_laurent
    (Φ : OriginChartRing V →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      PowerSeries.C t)
    (lam : ZChartRing V →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V)))
    (hlamy : lam (yOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) = 1)
    (hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)))) :
    Spec.map (CommRingCat.ofHom lam) ≫ zChartι V =
      Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp Φ)) ≫ originChartι V := by
  classical
  set a : OriginChartRing V →+* LaurentSeries T := (HahnSeries.ofPowerSeries ℤ T).comp Φ with ha

  have hrange : Set.range (Spec.map (CommRingCat.ofHom a) ≫ originChartι V).base ⊆ Set.range (zChartι V).base := by
    rintro _ ⟨p, rfl⟩
    have hmem : (Spec.map (CommRingCat.ofHom a)).base p ∈
        originChartι V ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
      rw [Proj.awayι_preimage_basicOpen _ _ _ (coord_mem V 2) one_pos, isLocalizationElem_eq_zOverY]
      show a (zOverY V) ∉ p.asIdeal
      exact fun h => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)
    have : (originChartι V).base ((Spec.map (CommRingCat.ofHom a)).base p) ∈ (zChartι V).opensRange := by
      rw [Proj.opensRange_awayι]; exact hmem
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp this
    exact ⟨y, by rw [Scheme.Hom.comp_base]; exact hy⟩

  obtain ⟨μ, hμ⟩ := Spec.map_surjective
    (IsOpenImmersion.lift (zChartι V) (Spec.map (CommRingCat.ofHom a) ≫ originChartι V) hrange)
  have hfac : Spec.map μ ≫ zChartι V = Spec.map (CommRingCat.ofHom a) ≫ originChartι V := by
    rw [hμ]; exact IsOpenImmersion.lift_fac _ _ _

  have hμlam : μ.hom = lam := by
    apply zChart_ringHom_ext V
    ·
      have h1 := congrArg (· ≫ projModelStrCR V) hfac
      simp only [Category.assoc, zChartι_comp_projModelStrCR, originChartι_comp_projModelStrCR, ← Spec.map_comp] at h1
      have h2 := Spec.map_injective h1
      refine RingHom.ext fun t => ?_
      have h3 := congrArg (fun φ => φ.hom t) h2
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
      rw [RingHom.comp_apply, RingHom.comp_apply, h3]
      have e1 : a (oStr V t) = HahnSeries.C t := by
        show HahnSeries.ofPowerSeries ℤ T
          (Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t))) = _
        rw [hΦc, HahnSeries.ofPowerSeries_C]
      have e2 : lam (zStr V t) = HahnSeries.C t := hlamc t
      rw [e1, e2]
    · obtain ⟨e1, -⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (xOverZ V) * a (zOverY V) = lam (xOverZ V) * a (zOverY V) := by rw [e1, ha]; exact hlamx.symm
      exact hunit.mul_right_cancel this
    · obtain ⟨-, e2⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (yOverZ V) * a (zOverY V) = lam (yOverZ V) * a (zOverY V) := by rw [e2, ha]; exact hlamy.symm
      exact hunit.mul_right_cancel this
  have : CommRingCat.ofHom lam = μ := by rw [← hμlam]; rfl
  rw [this, hfac]

end Laurent

end OverlapAux

namespace WMLocal

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection

section Restrict

variable {T : Type u} [CommRing T] (W W' : WeierstrassCurve T)

noncomputable abbrev cZ : T →+* ZChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem zChartι_comp_projModelStrCR :
    zChartι W.toProjective ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (cZ W)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem preimage_opensRange_zChartι (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange = (zChartι W.toProjective).opensRange := by
  ext x
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  change Ψ.hom x ∈ Proj.basicOpen (projModelGradingCR W'.toProjective) (coord W'.toProjective 2) ↔
    x ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)
  rw [← not_iff_not, not_mem_basicOpen_iff_mem_range_kwZeroSect W', not_mem_basicOpen_iff_mem_range_kwZeroSect W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hinj : Function.Injective Ψ.hom := (Scheme.homeoOfIso Ψ).injective
    apply hinj
    rw [← ht, ← Scheme.Hom.comp_apply, hΨO]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [← Scheme.Hom.comp_apply, hΨO]⟩

theorem exists_ringEquiv_zChartRing_of_iso (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (cZ W' t) = cZ W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by

  have hrange : Set.range (zChartι W.toProjective ≫ Ψ.hom) = Set.range (zChartι W'.toProjective) := by
    have h := preimage_opensRange_zChartι W W' Ψ hΨO
    have hsurj : Function.Surjective Ψ.hom := (Scheme.homeoOfIso Ψ).surjective
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have : zChartι W.toProjective p ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        rw [h]; exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_apply] using this
    · rintro ⟨p', rfl⟩
      obtain ⟨x, hx⟩ := hsurj (zChartι W'.toProjective p')
      have : x ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        show Ψ.hom x ∈ (zChartι W'.toProjective).opensRange
        rw [hx]; exact ⟨p', rfl⟩
      rw [h] at this
      obtain ⟨p, rfl⟩ := this
      exact ⟨p, by rw [Scheme.Hom.comp_apply, hx]⟩
  let δ : Spec (CommRingCat.of (ZChartRing W.toProjective)) ≅ Spec (CommRingCat.of (ZChartRing W'.toProjective)) :=
    IsOpenImmersion.isoOfRangeEq (zChartι W.toProjective ≫ Ψ.hom) (zChartι W'.toProjective) hrange
  have hδ : δ.hom ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective δ.hom
  obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective δ.inv
  have h12 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.hom_inv_id, Spec.map_id])
  have h21 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.inv_hom_id, Spec.map_id])
  let e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective :=
    RingEquiv.ofRingHom φ₁.hom φ₂.hom (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h12 a)
      (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h21 a)
  have he : CommRingCat.ofHom e.toRingHom = φ₁ := rfl
  refine ⟨e, ?_, by rw [he, hφ₁, hδ]⟩

  have h2 : Spec.map φ₁ ≫ Spec.map (CommRingCat.ofHom (cZ W')) = Spec.map (CommRingCat.ofHom (cZ W)) := by
    rw [← zChartι_comp_projModelStrCR W', hφ₁, ← Category.assoc, hδ, Category.assoc, hΨ, zChartι_comp_projModelStrCR W]
  have h3 : CommRingCat.ofHom (cZ W') ≫ φ₁ = CommRingCat.ofHom (cZ W) :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  intro t
  have hv := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (ZChartRing W.toProjective) => f.hom t) h3
  change φ₁.hom (cZ W' t) = cZ W t at hv
  exact hv

end Restrict

section FormalPoint

variable {T : Type u} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

omit [IsLocalRing T] in
theorem originChartι_comp_projModelStrCR (V : WeierstrassCurve T) :
    originChartι V.toProjective ≫ projModelStrCR V.toProjective = Spec.map (CommRingCat.ofHom (cY V)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_formalChart_of_iso
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW) :
    ∃ χ' : OriginChartRing W'.toProjective →+* PowerSeries T,
      (∀ t : T, χ' (cY W' t) = PowerSeries.C t) ∧
      PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0 ∧
      PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0 ∧
      Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  obtain ⟨hO', hχx', hχz'⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W'.toProjective
  have hO'' : (kwZeroSect T W').1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W')) ≫ originChartι W'.toProjective := hO'
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hOW : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let P : Spec (CommRingCat.of (PowerSeries T)) ⟶ projModelCR W'.toProjective :=
    Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom

  have hred : (PowerSeries.constantCoeff (R := T)).comp Φ = kwYChartEval T W := by
    apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
    · intro t
      have h := hΦc t
      have h2 := RingHom.congr_fun (kwYChartEval_section T W) t
      simp only [RingHom.comp_apply, RingHom.id_apply] at h h2
      rw [RingHom.comp_apply, h, PowerSeries.constantCoeff_C]
      exact h2.symm
    · rw [RingHom.comp_apply, hΦx, map_neg, PowerSeries.constantCoeff_X, neg_zero]; exact hχx.symm
    · rw [RingHom.comp_apply, hΦz, map_neg, WeierstrassCurve.constantCoeff_formalW, neg_zero]; exact hχz.symm

  have hrange : Set.range P ⊆ Set.range (originChartι W'.toProjective) := by

    let c := IsLocalRing.closedPoint (PowerSeries T)
    have hc : P c ∈ Set.range (originChartι W'.toProjective) := by

      have hcc : Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := T))) (IsLocalRing.closedPoint T) = c := by
        apply PrimeSpectrum.ext
        change Ideal.comap (PowerSeries.constantCoeff (R := T)) (IsLocalRing.maximalIdeal T) =
          IsLocalRing.maximalIdeal (PowerSeries T)
        haveI : IsLocalHom (PowerSeries.constantCoeff (R := T)) :=
          ⟨fun a ha => (PowerSeries.isUnit_iff_constantCoeff).mpr ha⟩
        exact congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := T)))
      have h1 : P c = ((kwZeroSect T W).1 ≫ Ψ.hom) (IsLocalRing.closedPoint T) := by
        rw [← hcc, hOW]
        simp only [P, ← Scheme.Hom.comp_apply, Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hred]
      rw [h1, hΨO, hO'', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rintro _ ⟨z, rfl⟩
    have hz : z ⤳ c := (PrimeSpectrum.le_iff_specializes z c).mp (IsLocalRing.le_maximalIdeal z.isPrime.ne_top)
    have hPz : P z ⤳ P c := hz.map P.continuous
    have hopen : IsOpen (Set.range (originChartι W'.toProjective)) := (originChartι W'.toProjective).isOpenEmbedding.isOpen_range
    exact hPz.mem_open hopen hc

  let Q := IsOpenImmersion.lift (originChartι W'.toProjective) P hrange
  have hQ : Q ≫ originChartι W'.toProjective = P := IsOpenImmersion.lift_fac _ _ hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective Q

  have hmod : Spec.map (CommRingCat.ofHom ((PowerSeries.constantCoeff (R := T)).comp φ.hom)) ≫
      originChartι W'.toProjective = (kwZeroSect T W').1 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]
    simp only [P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hred]
    rw [← hOW, hΨO]
  rw [hO''] at hmod
  have hmod' : (PowerSeries.constantCoeff (R := T)).comp φ.hom = kwYChartEval T W' := by
    have := Spec.map_injective ((cancel_mono (originChartι W'.toProjective)).mp hmod)
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨φ.hom, ?_, by rw [← RingHom.comp_apply, hmod']; exact hχx',
    by rw [← RingHom.comp_apply, hmod']; exact hχz', by rw [show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]⟩
  ·
    have h2 : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (cY W')) = Spec.map (CommRingCat.ofHom (Φ.comp (cY W))) := by
      rw [← originChartι_comp_projModelStrCR W', hφ, ← Category.assoc, hQ]
      simp only [P, Category.assoc, hΨ]
      rw [originChartι_comp_projModelStrCR W, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : CommRingCat.ofHom (cY W') ≫ φ = CommRingCat.ofHom (Φ.comp (cY W)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact h2)
    intro t
    have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (PowerSeries T) => f.hom t) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    exact this.trans (hΦc t)

end FormalPoint

section Subst

variable {T : Type u} [CommRing T] [IsLocalRing T]

theorem formalChart_zOverY_eq (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    χ (zOverY V.toProjective) = - PowerSeries.subst (- χ (xOverY V.toProjective)) V.formalW := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  set α : PowerSeries T := - χ (xOverY V.toProjective) with hα
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0

  let ρ : OriginChartRing V.toProjective →+* PowerSeries T := (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ
  have hρc : ∀ t : T, ρ (cY V t) = PowerSeries.C t := by
    intro t
    show PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t)) = _
    rw [hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  have hρx : ρ (xOverY V.toProjective) = χ (xOverY V.toProjective) := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective)) = _
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, neg_neg]
  have hρz : ρ (zOverY V.toProjective) = - PowerSeries.subst α V.formalW := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective)) = _
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom]

  have mem_of_cc : ∀ f : PowerSeries T, PowerSeries.constantCoeff f = 0 → f ∈ IsLocalRing.maximalIdeal (PowerSeries T) := by
    intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, hf]
    exact not_isUnit_zero
  have h1 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V χ
    (fun t => by change χ ((cY V) t) = _; rw [hc t, PowerSeries.algebraMap_eq])
  have h2 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V ρ
    (fun t => by change ρ ((cY V) t) = _; rw [hρc t, PowerSeries.algebraMap_eq])
  rw [hρx, hρz] at h2
  rw [← hρz] at h2 ⊢
  refine WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal _ _ _ _ _ _ _ _
    (mem_of_cc _ hx0) (mem_of_cc _ hz0) (mem_of_cc _ ?_) h1 h2
  rw [hρz, map_neg, neg_eq_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hα0 _ V.constantCoeff_formalW

theorem formalChart_eq_subst_comp (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW)
    (hαs : PowerSeries.HasSubst (- χ (xOverY V.toProjective))) :
    χ = (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ := by
  apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext V
  · intro t
    change χ (cY V t) = PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t))
    rw [hc, hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective))
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, neg_neg]
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective))
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom, formalChart_zOverY_eq V χ hc hx0 hz0 Φ hΦc hΦx hΦz]

end Subst

section UnitCoeff

variable {T : Type u} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

theorem isUnit_coeff_one_formalChart
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (Φ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hΦc' : ∀ t : T, Φ' (cY W' t) = PowerSeries.C t)
    (hΦx' : Φ' (xOverY W'.toProjective) = - PowerSeries.X) (hΦz' : Φ' (zOverY W'.toProjective) = - W'.formalW)
    (χ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hc' : ∀ t : T, χ' (cY W' t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0)
    (hχ' : Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom) :
    IsUnit (PowerSeries.coeff 1 (χ' (xOverY W'.toProjective))) := by

  have hΨ' : Ψ.inv ≫ projModelStrCR W.toProjective = projModelStrCR W'.toProjective := by
    rw [← hΨ, Iso.inv_hom_id_assoc]
  have hΨO' : (kwZeroSect T W').1 ≫ Ψ.inv = (kwZeroSect T W).1 := by
    rw [← hΨO, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨χ'', hc'', hx0'', hz0'', hχ''⟩ := exists_formalChart_of_iso W' W Ψ.symm hΨ' hΨO' Φ' hΦc' hΦx' hΦz'
  simp only [Iso.symm_hom] at hχ''

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  set β : PowerSeries T := - χ'' (xOverY W.toProjective) with hβ
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hβ0 : PowerSeries.constantCoeff β = 0 := by rw [hβ, map_neg, hx0'', neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hβs : PowerSeries.HasSubst β := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have e1 := formalChart_eq_subst_comp W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz' hαs
  have e2 := formalChart_eq_subst_comp W χ'' hc'' hx0'' hz0'' Φ hΦc hΦx hΦz hβs

  have key : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫
          Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective := by
    have h1 : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
        Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := by
      rw [← Category.assoc, hχ', Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : Spec.map (CommRingCat.ofHom χ') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ') := by
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : Spec.map (CommRingCat.ofHom χ'') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ) := by
      rw [e2, CommRingCat.ofHom_comp, Spec.map_comp]
    calc Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective
        = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := h1
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom Φ') ≫ originChartι W'.toProjective ≫ Ψ.inv) := by
          rw [h2, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom χ'') ≫ originChartι W.toProjective) := by rw [hχ'']
      _ = _ := by rw [h3, Category.assoc]
  have key2 : CommRingCat.ofHom Φ =
      CommRingCat.ofHom Φ ≫ CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom ≫
        CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (originChartι W.toProjective)).mp
    simpa only [Spec.map_comp, Category.assoc] using key

  have hsub : PowerSeries.subst α β = PowerSeries.X := by
    have := congrArg (fun f : CommRingCat.of (OriginChartRing W.toProjective) ⟶ CommRingCat.of (PowerSeries T) =>
      f.hom (xOverY W.toProjective)) key2
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    rw [hΦx] at this
    change -PowerSeries.X = PowerSeries.substAlgHom (R := T) hαs (PowerSeries.substAlgHom (R := T) hβs (-PowerSeries.X)) at this
    rw [map_neg, map_neg, PowerSeries.coe_substAlgHom hβs, PowerSeries.subst_X hβs,
      PowerSeries.coe_substAlgHom hαs] at this
    exact (neg_inj.mp this).symm

  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.mpr hβ0
  have hprod : PowerSeries.X * (a * PowerSeries.subst α b) = PowerSeries.X * 1 := by
    calc PowerSeries.X * (a * PowerSeries.subst α b) = (PowerSeries.X * a) * PowerSeries.subst α b := by ring
      _ = PowerSeries.subst α (PowerSeries.X : PowerSeries T) * PowerSeries.subst α b := by rw [← ha, PowerSeries.subst_X hαs]
      _ = PowerSeries.subst α β := by rw [← PowerSeries.subst_mul hαs, ← hb]
      _ = PowerSeries.X * 1 := by rw [hsub, mul_one]
  have hone : a * PowerSeries.subst α b = 1 := by
    ext n
    have := congrArg (PowerSeries.coeff (n + 1)) hprod
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at this
  have hau : IsUnit a := ⟨⟨a, PowerSeries.subst α b, hone, (mul_comm _ _).trans hone⟩, rfl⟩
  have hcoeff : PowerSeries.coeff 1 (χ' (xOverY W'.toProjective)) = - PowerSeries.constantCoeff a := by
    have : χ' (xOverY W'.toProjective) = - (PowerSeries.X * a) := by rw [← ha, hα, neg_neg]
    rw [this, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hcoeff]
  exact ((PowerSeries.isUnit_iff_constantCoeff).mp hau).neg

end UnitCoeff

section LaurentCore

variable {T : Type u} [CommRing T]

local notation "ofPS" => HahnSeries.ofPowerSeries ℤ T

theorem single_one_mul_single_neg_one' :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem coeff_ofPS_mul_single' (g : PowerSeries T) (k n : ℤ) :
    (ofPS g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem coeff_single_neg_mul_ofPS' (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single', if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single', if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem laurent_core (α a w u : PowerSeries T) (hα : α = PowerSeries.X * a) (ha : IsUnit (PowerSeries.constantCoeff a))
    (hwu : w * u = PowerSeries.X ^ 3) (hu : PowerSeries.constantCoeff u = 1) (hαs : PowerSeries.HasSubst α)
    (Lx Ly : LaurentSeries T)
    (hx : Lx * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = HahnSeries.ofPowerSeries ℤ T (-α))
    (hy : Ly * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = 1) :
    (∀ n : ℤ, n < -2 → Lx.coeff n = 0) ∧ IsUnit (Lx.coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → Ly.coeff n = 0) ∧ IsUnit (Ly.coeff (-3)) := by

  have haU : IsUnit a := PowerSeries.isUnit_iff_constantCoeff.mpr ha
  have huU : IsUnit u := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hu]; exact isUnit_one)
  obtain ⟨ai, hai⟩ : ∃ ai, a * ai = 1 := ⟨↑haU.unit⁻¹, haU.mul_val_inv⟩
  set su := PowerSeries.subst α u with hsu
  have hsuU : IsUnit su := by rw [hsu, ← PowerSeries.coe_substAlgHom hαs]; exact huU.map _

  have hsw : PowerSeries.subst α w * su = PowerSeries.X ^ 3 * a ^ 3 := by
    rw [hsu, ← PowerSeries.subst_mul hαs, hwu, ← PowerSeries.coe_substAlgHom hαs, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, mul_pow]

  set Z : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZ
  set Zi : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZi
  have hZZi : Z * Zi = 1 := single_one_mul_single_neg_one'
  have hofX : ofPS PowerSeries.X = Z := HahnSeries.ofPowerSeries_X
  have haai : ofPS a * ofPS ai = 1 := by rw [← map_mul, hai, map_one]

  have ex : Lx * (Z ^ 3 * ofPS a ^ 3) = Z * ofPS a * ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hx
    simp only [map_neg, mul_neg, neg_neg, neg_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX, hα, map_mul, hofX] at this
    rw [this]
  have ey : Ly * (Z ^ 3 * ofPS a ^ 3) = - ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hy
    simp only [map_neg, mul_neg, neg_neg, neg_mul, one_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX] at this
    rw [this]
  have hU : IsUnit (Z ^ 3 * ofPS a ^ 3) :=
    ((IsUnit.of_mul_eq_one Zi hZZi).pow 3).mul ((haU.map (HahnSeries.ofPowerSeries ℤ T)).pow 3)

  have hLx : Lx = HahnSeries.single (-2 : ℤ) (1 : T) * ofPS (su * ai ^ 2) := by
    apply hU.mul_right_cancel
    rw [ex]
    have : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 2 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_mul, map_pow]
    calc Z * ofPS a * ofPS su
        = Z * ofPS a * ofPS su * (Z * Zi) ^ 2 * (ofPS a * ofPS ai) ^ 2 := by rw [hZZi, haai]; ring
      _ = Zi ^ 2 * (ofPS su * ofPS ai ^ 2) * (Z ^ 3 * ofPS a ^ 3) := by ring
  have hLy : Ly = HahnSeries.single (-3 : ℤ) (1 : T) * ofPS (-(su * ai ^ 3)) := by
    apply hU.mul_right_cancel
    rw [ey]
    have : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 3 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_neg, map_mul, map_pow]
    calc - ofPS su = - ofPS su * (Z * Zi) ^ 3 * (ofPS a * ofPS ai) ^ 3 := by rw [hZZi, haai]; ring
      _ = Zi ^ 3 * -(ofPS su * ofPS ai ^ 3) * (Z ^ 3 * ofPS a ^ 3) := by ring

  have haiU : IsUnit (PowerSeries.constantCoeff ai) :=
    IsUnit.of_mul_eq_one (PowerSeries.constantCoeff a) (by rw [mul_comm, ← map_mul, hai, map_one])
  have hsu0 : IsUnit (PowerSeries.constantCoeff su) := PowerSeries.isUnit_iff_constantCoeff.mp hsuU
  obtain ⟨h2a, h2b⟩ := coeff_single_neg_mul_ofPS' (T := T) 2 (su * ai ^ 2)
  obtain ⟨h3a, h3b⟩ := coeff_single_neg_mul_ofPS' (T := T) 3 (-(su * ai ^ 3))
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_, ?_⟩
  · rw [hLx]; exact h2a n (by exact_mod_cast hn)
  · rw [hLx, show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, h2b, map_mul, map_pow]
    exact hsu0.mul (haiU.pow 2)
  · rw [hLy]; exact h3a n (by exact_mod_cast hn)
  · rw [hLy, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, h3b, map_neg, map_mul, map_pow]
    exact (hsu0.mul (haiU.pow 3)).neg

end LaurentCore

section Glue

open OverlapAux

theorem w3_main
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) := by

  obtain ⟨Φ', hΦc', hΦx', hΦz'⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W'
  obtain ⟨χ', hc', hx0, hz0, hχ'⟩ := exists_formalChart_of_iso W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz

  have hwU : IsUnit (HahnSeries.ofPowerSeries ℤ T W.formalW) := by
    have h3 : IsUnit (HahnSeries.ofPowerSeries ℤ T (W.formalW * W.wUnitFactor)) := by
      rw [W.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
      exact (IsUnit.of_mul_eq_one _ single_one_mul_single_neg_one').pow 3
    rw [map_mul] at h3
    exact isUnit_of_mul_isUnit_left h3
  have hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective))) := by
    rw [hΦz, map_neg]; exact hwU.neg
  have hO2 := OverlapAux.specMap_comp_zChartι_eq_of_laurent W.toProjective Φ hΦc lam hlamc hlamx hlamy hunit

  have hpt : Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp χ')) ≫ originChartι W'.toProjective =
      Spec.map (CommRingCat.ofHom (lam.comp e)) ≫ zChartι W'.toProjective := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hχ', CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, he, ← Category.assoc (Spec.map (CommRingCat.ofHom lam)), hO2, CommRingCat.ofHom_comp,
      Spec.map_comp]
    simp only [Category.assoc]
  obtain ⟨h1, h2⟩ := OverlapAux.zChart_mul_originChart_of_specMap_comp_eq W'.toProjective
    ((HahnSeries.ofPowerSeries ℤ T).comp χ') (lam.comp e) hpt
  simp only [RingHom.comp_apply] at h1 h2

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  have hξ : χ' (xOverY W'.toProjective) = - α := by rw [hα, neg_neg]
  have hζ : χ' (zOverY W'.toProjective) = - PowerSeries.subst α W'.formalW :=
    formalChart_zOverY_eq W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz'
  rw [hξ, hζ] at h1
  rw [hζ] at h2
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  have haU : IsUnit (PowerSeries.constantCoeff a) := by
    have h := isUnit_coeff_one_formalChart W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz Φ' hΦc' hΦx' hΦz' χ' hc' hx0 hz0 hχ'
    rw [hξ, ha, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    simpa using h
  exact laurent_core α a W'.formalW W'.wUnitFactor ha haU W'.formalW_mul_wUnitFactor W'.constantCoeff_wUnitFactor hαs
    _ _ h1 h2

end Glue

end WMLocal

theorem solution
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) :=
  WMLocal.w3_main T W W' Ψ hΨ hΨO e he Φ hΦc hΦx hΦz lam hlamc hlamx hlamy

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WMLocal

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection

section Restrict

variable {T : Type u} [CommRing T] (W W' : WeierstrassCurve T)

noncomputable abbrev cZ : T →+* ZChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem zChartι_comp_projModelStrCR :
    zChartι W.toProjective ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (cZ W)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem preimage_opensRange_zChartι (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange = (zChartι W.toProjective).opensRange := by
  ext x
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  change Ψ.hom x ∈ Proj.basicOpen (projModelGradingCR W'.toProjective) (coord W'.toProjective 2) ↔
    x ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)
  rw [← not_iff_not, not_mem_basicOpen_iff_mem_range_kwZeroSect W', not_mem_basicOpen_iff_mem_range_kwZeroSect W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hinj : Function.Injective Ψ.hom := (Scheme.homeoOfIso Ψ).injective
    apply hinj
    rw [← ht, ← Scheme.Hom.comp_apply, hΨO]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [← Scheme.Hom.comp_apply, hΨO]⟩

theorem exists_ringEquiv_zChartRing_of_iso (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (cZ W' t) = cZ W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by

  have hrange : Set.range (zChartι W.toProjective ≫ Ψ.hom) = Set.range (zChartι W'.toProjective) := by
    have h := preimage_opensRange_zChartι W W' Ψ hΨO
    have hsurj : Function.Surjective Ψ.hom := (Scheme.homeoOfIso Ψ).surjective
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have : zChartι W.toProjective p ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        rw [h]; exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_apply] using this
    · rintro ⟨p', rfl⟩
      obtain ⟨x, hx⟩ := hsurj (zChartι W'.toProjective p')
      have : x ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        show Ψ.hom x ∈ (zChartι W'.toProjective).opensRange
        rw [hx]; exact ⟨p', rfl⟩
      rw [h] at this
      obtain ⟨p, rfl⟩ := this
      exact ⟨p, by rw [Scheme.Hom.comp_apply, hx]⟩
  let δ : Spec (CommRingCat.of (ZChartRing W.toProjective)) ≅ Spec (CommRingCat.of (ZChartRing W'.toProjective)) :=
    IsOpenImmersion.isoOfRangeEq (zChartι W.toProjective ≫ Ψ.hom) (zChartι W'.toProjective) hrange
  have hδ : δ.hom ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective δ.hom
  obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective δ.inv
  have h12 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.hom_inv_id, Spec.map_id])
  have h21 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.inv_hom_id, Spec.map_id])
  let e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective :=
    RingEquiv.ofRingHom φ₁.hom φ₂.hom (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h12 a)
      (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h21 a)
  have he : CommRingCat.ofHom e.toRingHom = φ₁ := rfl
  refine ⟨e, ?_, by rw [he, hφ₁, hδ]⟩

  have h2 : Spec.map φ₁ ≫ Spec.map (CommRingCat.ofHom (cZ W')) = Spec.map (CommRingCat.ofHom (cZ W)) := by
    rw [← zChartι_comp_projModelStrCR W', hφ₁, ← Category.assoc, hδ, Category.assoc, hΨ, zChartι_comp_projModelStrCR W]
  have h3 : CommRingCat.ofHom (cZ W') ≫ φ₁ = CommRingCat.ofHom (cZ W) :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  intro t
  have hv := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (ZChartRing W.toProjective) => f.hom t) h3
  change φ₁.hom (cZ W' t) = cZ W t at hv
  exact hv

end Restrict

end WMLocal

theorem solution
    (T : Type u) [CommRing T] (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (fromZeroRingHom (projModelGradingCR W'.toProjective) _ (algebraMap T ((projModelGradingCR W'.toProjective) 0) t)) =
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
  WMLocal.exists_ringEquiv_zChartRing_of_iso W W' Ψ hΨ hΨO

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace WMLocal

variable {T : Type u} [CommRing T]

abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev cY (V : WeierstrassCurve T) : T →+* OriginChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev ofPS (T : Type u) [CommRing T] : PowerSeries T →+* LaurentSeries T := HahnSeries.ofPowerSeries ℤ T

theorem formalW_eq_X_pow_three_mul (V : WeierstrassCurve T) :
    ∃ v : PowerSeries T, V.formalW = PowerSeries.X ^ 3 * v ∧ PowerSeries.constantCoeff v = 1 := by
  obtain ⟨v, hv⟩ := V.isUnit_wUnitFactor.exists_right_inv
  refine ⟨v, ?_, ?_⟩
  · calc V.formalW = V.formalW * (V.wUnitFactor * v) := by rw [hv, mul_one]
      _ = PowerSeries.X ^ 3 * v := by rw [← mul_assoc, V.formalW_mul_wUnitFactor]
  · have h := congrArg PowerSeries.constantCoeff hv
    rwa [map_mul, V.constantCoeff_wUnitFactor, one_mul, map_one] at h

theorem zChart_ringHom_ext (V : WeierstrassCurve T) {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V.toProjective →+* B) (h0 : g₁.comp (cZ V) = g₂.comp (cZ V))
    (hx : g₁ (xOverZ V.toProjective) = g₂ (xOverZ V.toProjective))
    (hy : g₁ (yOverZ V.toProjective) = g₂ (yOverZ V.toProjective)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = cZ V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext a
    have := RingHom.congr_fun h' (e a)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

section laurent
variable (V : WeierstrassCurve T)

theorem single_one_mul_single_neg_one :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem single_neg (n : ℕ) :
    (HahnSeries.single (-(n : ℤ)) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ n := by
  rw [HahnSeries.single_pow, one_pow]; congr 1; simp

theorem single_neg_two :
    (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 2 := single_neg 2

theorem single_neg_three :
    (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 3 := single_neg 3

theorem single_one_pow_three_mul_single_neg_three :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
  rw [single_neg_three]
  calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 3
      = (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 3 := by ring
    _ = 1 := by rw [single_one_mul_single_neg_one, one_pow]

theorem laurent_equation :
    ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval
      (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
      (-(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) = 0 := by
  set U : LaurentSeries T := ofPS T V.wUnitFactor with hU
  set F : LaurentSeries T := ofPS T V.formalW with hF
  set Zp : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZp
  set Zm : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZm
  have hpm : Zp * Zm = 1 := single_one_mul_single_neg_one
  have h2 : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 2 := single_neg 2
  have h3 : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 3 := single_neg 3
  rw [h2, h3]
  set ι : LaurentSeries T := U * Zm ^ 3 with hι
  have hFU : F * U = Zp ^ 3 := by
    rw [hF, hU, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  have hFι : F * ι = 1 := by
    rw [hι, ← mul_assoc, hFU]
    calc Zp ^ 3 * Zm ^ 3 = (Zp * Zm) ^ 3 := by ring
      _ = 1 := by rw [hpm, one_pow]
  have hx : U * Zm ^ 2 = ι * Zp := by
    rw [hι]
    calc U * Zm ^ 2 = U * Zm ^ 2 * (Zp * Zm) := by rw [hpm, mul_one]
      _ = U * Zm ^ 3 * Zp := by ring
  have hrel : F = Zp ^ 3 + HahnSeries.C V.a₁ * Zp * F + HahnSeries.C V.a₂ * Zp ^ 2 * F
      + HahnSeries.C V.a₃ * F ^ 2 + HahnSeries.C V.a₄ * Zp * F ^ 2 + HahnSeries.C V.a₆ * F ^ 3 := by
    have h := congrArg (ofPS T) V.formalW_eq
    simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C] at h
    rw [hF, hZp]
    exact h
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]
  rw [hx]
  linear_combination (ι ^ 3) * hrel
    - (ι ^ 2 - HahnSeries.C V.a₁ * Zp * ι ^ 2 - HahnSeries.C V.a₂ * Zp ^ 2 * ι ^ 2
        - HahnSeries.C V.a₃ * ι * (ι * F + 1)
        - HahnSeries.C V.a₄ * Zp * ι * (ι * F + 1)
        - HahnSeries.C V.a₆ * (ι ^ 2 * F ^ 2 + ι * F + 1)) * hFι

end laurent

section embed
variable (V : WeierstrassCurve T)

theorem exists_laurentEmbedding_core :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) ∧
      lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  set xL : LaurentSeries T := ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) with hxL
  set yL : LaurentSeries T := -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) with hyL
  let ev : Polynomial (Polynomial T) →+* LaurentSeries T :=
    (Polynomial.evalEvalRingHom xL yL).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (HahnSeries.C : T →+* LaurentSeries T)))
  have hevCC : ∀ t : T, ev (Polynomial.C (Polynomial.C t)) = HahnSeries.C t := by
    intro t; simp [ev]
  have hevCX : ev (Polynomial.C Polynomial.X) = xL := by simp [ev]
  have hevX : ev Polynomial.X = yL := by simp [ev]
  have hev : ev (WeierstrassCurve.Affine.polynomial V.toAffine) = 0 := by
    have h1 : ev (WeierstrassCurve.Affine.polynomial V.toAffine)
        = ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval xL yL := by
      rw [WeierstrassCurve.Affine.map_polynomial]
      rfl
    rw [h1]
    exact laurent_equation V
  let lam0 : (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}) →+* LaurentSeries T :=
    Ideal.Quotient.lift _ ev (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hev, mul_zero])
  have hfx : f (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  have hfy : f (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this
  refine ⟨lam0.comp f, ?_, ?_, ?_⟩
  · intro t
    rw [RingHom.comp_apply, show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show lam0 (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) = _
    rw [Ideal.Quotient.lift_mk, hevCC]
  · rw [RingHom.comp_apply, hfx]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevCX]
  · rw [RingHom.comp_apply, hfy]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevX]

theorem laurentEmbedding_mul_formalW (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    lam (xOverZ V.toProjective) * ofPS T V.formalW = ofPS T PowerSeries.X ∧
      lam (yOverZ V.toProjective) * ofPS T V.formalW = -1 := by
  have hFU : ofPS T V.formalW * ofPS T V.wUnitFactor = HahnSeries.single (1 : ℤ) (1 : T) ^ 3 := by
    rw [← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  constructor
  · rw [hx, mul_comm, ← mul_assoc, hFU, single_neg_two, HahnSeries.ofPowerSeries_X]
    calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 2
        = HahnSeries.single (1 : ℤ) (1 : T) * (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 2 := by ring
      _ = HahnSeries.single (1 : ℤ) (1 : T) := by rw [single_one_mul_single_neg_one, one_pow, mul_one]
  · rw [hy, neg_mul, mul_comm, ← mul_assoc, hFU, single_one_pow_three_mul_single_neg_three]

theorem exists_laurentEmbedding (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t, Φ (cY V t) = PowerSeries.C t) (hΦx : Φ (xOverY V.toProjective) = -PowerSeries.X)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1 := by
  obtain ⟨lam, hc, hx, hy⟩ := exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := laurentEmbedding_mul_formalW V lam hx hy
  refine ⟨lam, hc, ?_, ?_⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

theorem laurentEmbedding_unique (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW)
    (lam lam' : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy : lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1)
    (hc' : ∀ t, lam' (cZ V t) = HahnSeries.C t)
    (hx' : lam' (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy' : lam' (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1) : lam = lam' := by

  have hunit : IsUnit (ofPS T (Φ (zOverY V.toProjective))) := by
    rw [hΦz, map_neg, IsUnit.neg_iff]
    refine isUnit_iff_exists_inv.mpr ⟨ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T), ?_⟩
    rw [← mul_assoc, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X,
      single_one_pow_three_mul_single_neg_three]
  apply zChart_ringHom_ext V
  · exact RingHom.ext fun t => (hc t).trans (hc' t).symm
  · exact hunit.mul_right_cancel (hx.trans hx'.symm)
  · exact hunit.mul_right_cancel (hy.trans hy'.symm)

end embed

section lead
variable (V : WeierstrassCurve T)

theorem coeff_ofPS_mul_single (g : PowerSeries T) (k n : ℤ) :
    (ofPS T g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem laurentEmbedding_lead (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ n : ℤ, n < -2 → (lam (xOverZ V.toProjective)).coeff n = 0) ∧
      (lam (xOverZ V.toProjective)).coeff (-2) = 1 ∧
      (∀ n : ℤ, n < -3 → (lam (yOverZ V.toProjective)).coeff n = 0) ∧
      (lam (yOverZ V.toProjective)).coeff (-3) = -1 := by
  have h0 : PowerSeries.coeff 0 V.wUnitFactor = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact V.constantCoeff_wUnitFactor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hx, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [hx, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor
  · intro n hn
    rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_pos (by omega), neg_zero]
  · rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor

end lead

section extras
variable (V : WeierstrassCurve T)

theorem coeff_single_neg_mul_ofPS (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single, if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem isUnit_ofPS_X : IsUnit (ofPS T PowerSeries.X) := by
  rw [HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (-1 : ℤ) (1 : T), single_one_mul_single_neg_one⟩

theorem isUnit_ofPS_of_isUnit {f : PowerSeries T} (hf : IsUnit f) : IsUnit (ofPS T f) := hf.map _

theorem exists_ringEquiv_zChartRing_coordinateRing :
    ∃ e : ZChartRing V.toProjective ≃+* (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}),
      (∀ t, e (cZ V t) = Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) ∧
      e (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) ∧
      e (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨RingEquiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro t
    show f (cZ V t) = _
    rw [show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this

end extras

section filtration
variable (V : WeierstrassCurve T)

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem single_mul_eval₂_xL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p : Polynomial T) (d : ℕ)
    (hd : p.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) *
          Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p
        = ofPS T G ∧ PowerSeries.constantCoeff G = p.coeff d := by
  classical
  refine ⟨∑ i ∈ Finset.range (d + 1), PowerSeries.C (p.coeff i) * u ^ i * PowerSeries.X ^ (2 * (d - i)), ?_, ?_⟩
  · rw [Polynomial.eval₂_eq_sum, Polynomial.sum_over_range' _ _ (d + 1) (by omega), Finset.mul_sum, map_sum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hid : i ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
      rw [map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, mul_pow,
        single_neg_two, ← pow_mul]

      have hZ : (HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) : LaurentSeries T)
          = HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) := by
        rw [← pow_add, HahnSeries.single_pow, one_pow]
        congr 1
        have : 2 * (d - i) + 2 * i = 2 * d := by omega
        rw [this]
        simp
      rw [hZ]
      have hpm : (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i) = 1 := by
        rw [← mul_pow, single_one_mul_single_neg_one, one_pow]
      calc HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i)
            * (HahnSeries.C (p.coeff i) * ((ofPS T u) ^ i * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)))
          = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i))
            * (HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)) := by ring
        _ = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) := by
          rw [hpm, mul_one]
    · intro n; simp
  · rw [map_sum]
    rw [Finset.sum_eq_single d]
    · simp [hu]
    · intro i hi hne
      have hid : i < d := lt_of_le_of_ne (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) hne
      have : 2 * (d - i) ≠ 0 := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h

theorem coeff_neg_of_single_mul_eq_ofPS {N : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (N : ℤ) (1 : T) * f = ofPS T G) : f.coeff (-(N : ℤ)) = PowerSeries.constantCoeff G := by
  have := congrArg (fun g : LaurentSeries T => g.coeff 0) h
  rw [show (0 : ℤ) = -(N : ℤ) + N by ring, HahnSeries.coeff_single_mul_add, one_mul] at this
  rw [this, show -(N : ℤ) + N = ((0 : ℕ) : ℤ) by simp, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end filtration

section filtration2
variable (V : WeierstrassCurve T)

theorem single_mul_eval₂_xL_mul_yL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (q : Polynomial T) (d : ℕ)
    (hd : q.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) *
          (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
        = ofPS T G ∧ PowerSeries.constantCoeff G = -q.coeff d := by
  obtain ⟨G, hG, hG0⟩ := single_mul_eval₂_xL u hu q d hd
  refine ⟨-(G * u), ?_, by rw [map_neg, map_mul, hG0, hu, mul_one]⟩
  have hsplit : (HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
      = HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T) := by
    rw [HahnSeries.single_mul_single, mul_one]
    norm_num
  have h33 : (HahnSeries.single (3 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
    rw [HahnSeries.single_mul_single, mul_one]; norm_num
  rw [hsplit, map_neg, map_mul, ← hG]
  calc HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T)
        * (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
      = -(HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T)
          * Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * ofPS T u * (HahnSeries.single (3 : ℤ) (1 : T) * HahnSeries.single (-3 : ℤ) (1 : T))) := by ring
    _ = _ := by rw [h33, mul_one]

theorem laurentEmbedding_normalForm (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)))
    (a : ZChartRing V.toProjective) :
    ∃ p q : Polynomial T,
      a = Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) p + Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) q * yOverZ V.toProjective ∧
      lam a = Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
        + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨e, hec, hex, hey⟩ := exists_ringEquiv_zChartRing_coordinateRing V

  let evB : Polynomial (Polynomial T) →+* ZChartRing V.toProjective :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (cZ V) (xOverZ V.toProjective)) (yOverZ V.toProjective)
  have hfacB : e.symm.toRingHom.comp (Ideal.Quotient.mk _) = evB := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · refine RingHom.ext fun t => ?_
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C]
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact (hec t).symm
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
        apply e.injective; rw [RingEquiv.apply_symm_apply, hex]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      apply e.injective; rw [RingEquiv.apply_symm_apply, hey]
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := V.toAffine) (e a)
  have hpq' : e a = Ideal.Quotient.mk _ (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hpq, WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one,
      map_add, map_mul]
    rfl
  have ha : a = evB (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hfacB, RingHom.comp_apply, ← hpq']
    simp
  refine ⟨p, q, ?_, ?_⟩
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, map_add, map_mul, hy]
    congr 2 <;> rw [Polynomial.hom_eval₂, hx] <;> congr 1 <;> exact RingHom.ext hc

end filtration2

section filtration3
variable (V : WeierstrassCurve T)

theorem coeff_of_single_mul_eq_ofPS {K : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (K : ℤ) (1 : T) * f = ofPS T G) :
    (∀ n : ℤ, n < -(K : ℤ) → f.coeff n = 0) ∧ f.coeff (-(K : ℤ)) = PowerSeries.constantCoeff G := by
  have hf : f = HahnSeries.single (-(K : ℤ)) (1 : T) * ofPS T G := by
    rw [← h, ← mul_assoc, HahnSeries.single_mul_single, mul_one, neg_add_cancel, HahnSeries.single_zero_one, one_mul]
  rw [hf]
  exact coeff_single_neg_mul_ofPS K G

abbrev Ex (u : PowerSeries T) (p : Polynomial T) : LaurentSeries T :=
  Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p

abbrev yLs (u : PowerSeries T) : LaurentSeries T := -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T))

theorem single_nat_eq_ofPS_X_pow (k : ℕ) :
    (HahnSeries.single (k : ℤ) (1 : T) : LaurentSeries T) = ofPS T (PowerSeries.X ^ k) := by
  rw [map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow]; simp

theorem coeff_even (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m) (hq : q = 0 ∨ q.natDegree + 2 ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m : ℕ) : ℤ)) = p.coeff m := by
  obtain ⟨Gp, hGp, hGp0⟩ := single_mul_eval₂_xL u hu p m hp
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGp).2, hGp0]
  rcases hq with rfl | hq
  · simp
  · obtain ⟨Gq, hGq, -⟩ := single_mul_eval₂_xL_mul_yL u hu q (m - 2) (by omega)
    have hvan := (coeff_of_single_mul_eq_ofPS hGq).1 (-((2 * m : ℕ) : ℤ)) (by push_cast; omega)
    rw [hvan, add_zero]

theorem coeff_odd (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m + 1) (hq : q.natDegree ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m + 3 : ℕ) : ℤ)) = -q.coeff m := by
  obtain ⟨Gq, hGq, hGq0⟩ := single_mul_eval₂_xL_mul_yL u hu q m hq
  obtain ⟨Gp, hGp, -⟩ := single_mul_eval₂_xL u hu p (m + 2) (by omega)
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGq).2, hGq0]

  obtain ⟨Gp', hGp', -⟩ := single_mul_eval₂_xL u hu p (m + 1) hp
  have h' : HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) * (Ex u p) = ofPS T (PowerSeries.X * Gp') := by
    have hs : (HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
        = HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single ((2 * (m + 1) : ℕ) : ℤ) (1 : T) := by
      rw [HahnSeries.single_mul_single, one_mul]; norm_num; ring
    rw [hs, mul_assoc, hGp', map_mul, HahnSeries.ofPowerSeries_X]
  rw [(coeff_of_single_mul_eq_ofPS h').2, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_add]

theorem laurentEmbedding_filtration (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧ c₁ = (lam a).coeff (-2)) ∧
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = cZ V c₂ * yOverZ V.toProjective + cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧
        c₂ = -((lam a).coeff (-3))) := by
  classical
  have hu := V.constantCoeff_wUnitFactor

  have keyq : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      q ≠ 0 → 2 * q.natDegree + 3 ≤ M := by
    intro p q M hvan hq0
    by_contra hlt
    push Not at hlt
    by_cases hpq : p.natDegree ≤ q.natDegree + 1
    · have h := coeff_odd V.wUnitFactor hu p q q.natDegree hpq le_rfl
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hq0 (Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp h.symm))
    · push Not at hpq
      have hp0 : p ≠ 0 := by rintro rfl; simp at hpq
      have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl (Or.inr (by omega))
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  have keyp : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      (q = 0 ∨ q.natDegree + 2 ≤ 2) → M < 4 → p.natDegree ≤ 1 := by
    intro p q M hvan hq hM
    by_contra hlt
    push Not at hlt
    have hp0 : p ≠ 0 := by rintro rfl; simp at hlt
    have hq' : q = 0 ∨ q.natDegree + 2 ≤ p.natDegree := hq.imp id (fun h => by omega)
    have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl hq'
    rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  constructor
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q = 0 := by
      by_contra hq0
      have := keyq p q 2 (by exact_mod_cast hvan) hq0
      omega
    subst hq
    have hp : p.natDegree ≤ 1 := keyp p 0 2 (by exact_mod_cast hvan) (Or.inl rfl) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    refine ⟨p.coeff 0, p.coeff 1, ?_, ?_⟩
    · rw [ha, hpeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    · have h := coeff_even V.wUnitFactor hu p 0 1 hp (Or.inl rfl)
      rw [hla]
      exact_mod_cast h.symm
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q.natDegree = 0 := by
      by_cases hq0 : q = 0
      · rw [hq0, Polynomial.natDegree_zero]
      · have := keyq p q 3 (by exact_mod_cast hvan) hq0
        omega
    have hp : p.natDegree ≤ 1 := keyp p q 3 (by exact_mod_cast hvan) (Or.inr (by omega)) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    have hqeq := Polynomial.eq_C_of_natDegree_eq_zero hq
    refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_, ?_⟩
    · rw [ha, hpeq, hqeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      ring_nf
    · have h := coeff_odd V.wUnitFactor hu p q 0 (by omega) (by omega)
      rw [hla]
      have h2 : (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
          + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))).coeff (-3) = -q.coeff 0 := by
        simpa using h
      rw [h2, neg_neg]

end filtration3

end WMLocal

end

theorem solution
    (T : Type u) [CommRing T] (V : WeierstrassCurve T)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t : T, lam (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
        HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) =
        HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) = 1 ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₁ = (lam a).coeff (-2)) ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ c₂ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₂) *
            yOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₂ = -((lam a).coeff (-3))) := by
  obtain ⟨lam, hc, hx, hy⟩ := WMLocal.exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := WMLocal.laurentEmbedding_mul_formalW V lam hx hy
  obtain ⟨hF2, hF3⟩ := WMLocal.laurentEmbedding_filtration V lam hc hx hy
  refine ⟨lam, hc, ?_, ?_, hF2, hF3⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

p2m_open "HomogeneousLocalization Polynomial AlgebraicGeometry.Polynomial"

namespace WMLocal
variable {T : Type u} [CommRing T]

noncomputable abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T ((projModelGradingCR V.toProjective) 0))
end WMLocal

namespace WMLocal

section Ext

theorem zChart_ringHom_ext {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T) {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))) = g₂.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = ((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))) r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Ext

section W4

theorem triangular_of_coeff {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (x y : A) (x' y' : A') (g : A' →+* A) (lam : A →+* LaurentSeries T)
    (hF2 : ∀ a : A, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = c c₁ * x + c c₀ ∧ c₁ = (lam a).coeff (-2))
    (hF3 : ∀ a : A, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = c c₂ * y + c c₁ * x + c c₀ ∧ c₂ = -((lam a).coeff (-3)))
    (hx₁ : ∀ n : ℤ, n < -2 → (lam (g x')).coeff n = 0) (hx₂ : IsUnit ((lam (g x')).coeff (-2)))
    (hy₁ : ∀ n : ℤ, n < -3 → (lam (g y')).coeff n = 0) (hy₂ : IsUnit ((lam (g y')).coeff (-3))) :
    ∃ (v₁ v₂ : Tˣ) (r s' t : T),
      g x' = c v₁ * x + c r ∧ g y' = c v₂ * y + c s' * x + c t := by
  obtain ⟨p₀, p₁, hex, hp₁⟩ := hF2 (g x') hx₁
  obtain ⟨q₀, q₁, q₂, hey, hq₂⟩ := hF3 (g y') hy₁
  have hu₁ : IsUnit p₁ := hp₁ ▸ hx₂
  have hu₂ : IsUnit q₂ := by rw [hq₂]; exact hy₂.neg
  refine ⟨hu₁.unit, hu₂.unit, p₀, q₁, q₀, ?_, ?_⟩
  · rw [hu₁.unit_spec, hex]
  · rw [hu₂.unit_spec, hey]

end W4

section Generic

theorem symm_triangular {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A') (e : A' ≃+* A) (he : ∀ t, e (c' t) = c t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e x' = c v₁ * x + c r) (hy : e y' = c v₂ * y + c s' * x + c t) :
    e.symm x = c' ↑v₁⁻¹ * x' + c' (-(↑v₁⁻¹ * r)) ∧
      e.symm y = c' ↑v₂⁻¹ * y' + c' (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) * x' + c' (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  have he' : ∀ t, e.symm (c t) = c' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  have hx' : x' = c' v₁ * e.symm x + c' r := by
    have := congrArg e.symm hx
    rwa [RingEquiv.symm_apply_apply, map_add, map_mul, he', he'] at this
  have hy' : y' = c' v₂ * e.symm y + c' s' * e.symm x + c' t := by
    have := congrArg e.symm hy
    rwa [RingEquiv.symm_apply_apply, map_add, map_add, map_mul, map_mul, he', he', he'] at this
  have hv₁ : c' ↑v₁⁻¹ * c' v₁ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hv₂ : c' ↑v₂⁻¹ * c' v₂ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have ex0 : e.symm x = c' ↑v₁⁻¹ * x' - c' ↑v₁⁻¹ * c' r := by
    linear_combination (-(c' ↑v₁⁻¹)) * hx' + (-(e.symm x)) * hv₁
  have ey0 : e.symm y = c' ↑v₂⁻¹ * y' - c' ↑v₂⁻¹ * c' s' * c' ↑v₁⁻¹ * x' +
      c' ↑v₂⁻¹ * (c' s' * c' ↑v₁⁻¹ * c' r - c' t) := by
    linear_combination (-(c' ↑v₂⁻¹)) * hy' + (-(e.symm y)) * hv₂ + (-(c' ↑v₂⁻¹ * c' s')) * ex0
  constructor
  · simp only [map_neg, map_mul]
    linear_combination ex0
  · simp only [map_neg, map_mul, map_sub]
    linear_combination ey0

theorem exists_algHom_triangular_of_charts {T : Type*} [CommRing T] {A A' C C' : Type*}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C'] [Algebra T C] [Algebra T C']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A')
    (fA : A →+* C) (hfA : Function.Bijective fA) (hfAc : fA.comp c = algebraMap T C)
    (fA' : A' →+* C') (hfA'c : fA'.comp c' = algebraMap T C')
    (ε : A →+* A') (hε : ∀ t, ε (c t) = c' t)
    (a b k d m : T) (hx : ε x = c' a * x' + c' b) (hy : ε y = c' k * y' + c' d * x' + c' m) :
    ∃ g : C →ₐ[T] C', g (fA x) = a • fA' x' + algebraMap T C' b ∧
      g (fA y) = k • fA' y' + d • fA' x' + algebraMap T C' m := by
  let E : A ≃+* C := RingEquiv.ofBijective fA hfA
  have hE : ∀ z, E.symm (fA z) = z := fun z => E.symm_apply_apply z
  have hc : ∀ t, fA (c t) = algebraMap T C t := fun t => RingHom.congr_fun hfAc t
  have hc' : ∀ t, fA' (c' t) = algebraMap T C' t := fun t => RingHom.congr_fun hfA'c t
  let g₀ : C →+* C' := fA'.comp (ε.comp E.symm.toRingHom)
  have hg₀ : ∀ z, g₀ (fA z) = fA' (ε z) := fun z => by
    show fA' (ε (E.symm (fA z))) = _; rw [hE]
  let g : C →ₐ[T] C' :=
    { toRingHom := g₀
      commutes' := fun t => by
        show g₀ (algebraMap T C t) = algebraMap T C' t
        rw [← hc, hg₀, hε, hc'] }
  refine ⟨g, ?_, ?_⟩
  · show g₀ (fA x) = _
    rw [hg₀, hx, map_add, map_mul, hc', hc', Algebra.smul_def]
  · show g₀ (fA y) = _
    rw [hg₀, hy, map_add, map_add, map_mul, map_mul, hc', hc', hc', Algebra.smul_def, Algebra.smul_def]

end Generic

section Charts

variable {T : Type u} [CommRing T]

theorem exists_zChart_to_coordinateRing (V : WeierstrassCurve T) :
    ∃ f : ZChartRing V.toProjective →+* V.toAffine.CoordinateRing, Function.Bijective f ∧
      f.comp (cZ V) = algebraMap T V.toAffine.CoordinateRing ∧
      f (xOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V (C X) ∧
      f (yOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V X := by
  obtain ⟨f, hbij, hc, hval⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨f, hbij, hc, ?_, ?_⟩
  · have := hval 1 (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X T 0)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]
  · have := hval 1 (MvPolynomial.X 1) (by simpa using MvPolynomial.isHomogeneous_X T 1)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]

theorem exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv (W W' : WeierstrassCurve T)
    (e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective) (he : ∀ t, e (cZ W' t) = cZ W t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e (xOverZ W'.toProjective) = cZ W v₁ * xOverZ W.toProjective + cZ W r)
    (hy : e (yOverZ W'.toProjective) = cZ W v₂ * yOverZ W.toProjective + cZ W s' * xOverZ W.toProjective + cZ W t) :
    ∃ g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing,
      g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
        ((v₁⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ (-(↑v₁⁻¹ * r)) ∧
      g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
        ((v₂⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
          (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) +
          algebraMap T _ (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  obtain ⟨fW, hbW, hcW, hxW, hyW⟩ := exists_zChart_to_coordinateRing W
  obtain ⟨fW', -, hcW', hxW', hyW'⟩ := exists_zChart_to_coordinateRing W'
  obtain ⟨ex, ey⟩ := symm_triangular (cZ W) (cZ W') (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ W'.toProjective) (yOverZ W'.toProjective) e he v₁ v₂ r s' t hx hy
  have he' : ∀ t, e.symm (cZ W t) = cZ W' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  obtain ⟨g, hgx, hgy⟩ := exists_algHom_triangular_of_charts (cZ W) (cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) fW hbW hcW fW' hcW'
    e.symm.toRingHom he' _ _ _ _ _ ex ey
  rw [hxW, hxW'] at hgx
  rw [hyW, hyW', hxW'] at hgy
  exact ⟨g, hgx, hgy⟩

end Charts

end WMLocal

open WMLocal HomogeneousLocalization in
open IsLocalRing in

theorem solution
    (T : Type u) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (W W' : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit W'.Δ)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by
  classical

  obtain ⟨e, hec, heι⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv.solution T W W' Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.solution T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff.solution T W W' Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := WMLocal.triangular_of_coeff (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W' e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := WMLocal.symm_triangular (WMLocal.cZ W) (WMLocal.cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular.solution T W W' g w₁ w₂ r₁ s₁ t₁ hgx hgy
  subst hC

  obtain ⟨φ, hφ, hvc, _, _⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W.toProjective C
  refine ⟨C, rfl, φ, hφ, hvc, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]

  obtain ⟨a, haι, hac, hax, hay⟩ := WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom W.toProjective C φ hφ hvc
  have hec' : ∀ b : T, e.symm (WMLocal.cZ W b) = WMLocal.cZ (C • W) b := fun b => by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hec b).symm
  have hae : a = e.symm.toRingHom := by
    apply WMLocal.zChart_ringHom_ext W.toProjective
    · refine RingHom.ext fun b => ?_
      change a (WMLocal.cZ W b) = e.symm (WMLocal.cZ W b)
      rw [hec']
      exact hac b
    · change a (xOverZ W.toProjective) = e.symm (xOverZ W.toProjective)
      rw [hax, ex, hu2, hCr]
      rfl
    · change a (yOverZ W.toProjective) = e.symm (yOverZ W.toProjective)
      rw [hay, ey, hCs, hu3, hCt]
      rfl
  apply ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartExt.solution T (C • W)
  rw [haι, hae]

  have hcomp : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => ?_
    show e.symm (e z) = z
    exact e.symm_apply_apply z
  have hee : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  symm
  calc zChartι (C • W).toProjective ≫ Ψ.inv
      = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
          zChartι (C • W).toProjective ≫ Ψ.inv := by rw [hee, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι (C • W).toProjective) ≫ Ψ.inv) := by
        simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ((zChartι W.toProjective ≫ Ψ.hom) ≫ Ψ.inv) := by rw [heι]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ zChartι W.toProjective := by
        rw [Category.assoc, Ψ.hom_inv_id, Category.comp_id]

#print axioms solution
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange

/-! Finiteness of origin-fixing automorphisms, including on the actual model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms
open CategoryTheory AlgebraicGeometry WeierstrassProjModel NeronModelInfra
open WeierstrassCurve.DrinfeldGlobal

lemma finite_variableChanges (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) W) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  apply (Nat.card_pos_iff.mp ?_).2
  by_cases hj0 : W.j = 0
  · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero h2 h3 W hj0]
    exact Nat.card_pos
  · by_cases hj1728 : W.j = 1728
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728 h2 h3 W hj1728]
      exact Nat.card_pos
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728 h2 h3 W hj0 hj1728]
      decide

lemma variableChangeHom_unique {F : Type u} [CommRing F]
    (W : WeierstrassCurve.Projective F) (C : WeierstrassCurve.VariableChange F)
    (φ ψ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : IsVariableChangeHom W C φ) (hψ : IsVariableChangeHom W C ψ) : φ = ψ := by
  apply GradedRingHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    exact (hφ.1 a).trans (hψ.1 a).symm
  · intro i
    fin_cases i
    · exact hφ.2.1.trans hψ.2.1.symm
    · exact hφ.2.2.1.trans hψ.2.2.1.symm
    · exact hφ.2.2.2.trans hψ.2.2.2.symm

def OriginIso (F : Type u) [CommRing F] (W : WeierstrassCurve F) :=
  { e : projModelCR W.toProjective ≅ projModelCR W.toProjective //
    e.hom ≫ projModelStrCR W.toProjective = projModelStrCR W.toProjective ∧
    (kwZeroSect F W).1 ≫ e.hom = (kwZeroSect F W).1 }

def Represents {F : Type u} [CommRing F] (W : WeierstrassCurve F)
    (e : OriginIso F W) (C : WeierstrassCurve.VariableChange F) : Prop :=
  ∃ (hC : C • W = W)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
    IsVariableChangeHom W.toProjective C φ ∧
    eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫
      Proj.map φ hφ = e.val.inv

lemma represented_unique {F : Type u} [CommRing F] (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) (e f : OriginIso F W)
    (he : Represents W e C) (hf : Represents W f C) : e = f := by
  obtain ⟨hC, φ, hφ, hvc, heq⟩ := he
  obtain ⟨hC', ψ, hψ, hvc', hfq⟩ := hf
  have h : φ = ψ := variableChangeHom_unique W.toProjective C φ ψ hvc hvc'
  subst ψ
  apply Subtype.ext
  have hinv : e.val.inv = f.val.inv := heq.symm.trans hfq
  have hi : e.val.symm = f.val.symm := Iso.ext hinv
  exact congrArg Iso.symm hi

lemma finite_originIso (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] : Finite (OriginIso F W) := by
  classical
  have hex : ∀ e : OriginIso F W, ∃ C : WeierstrassCurve.VariableChange F, Represents W e C := by
    intro e
    exact UniversePorts.VariableChange.solution F W W
      (WeierstrassCurve.IsElliptic.isUnit (W := W)) (WeierstrassCurve.IsElliptic.isUnit (W := W))
      e.val e.property.1 e.property.2
  choose C hC using hex
  let c : OriginIso F W → MulAction.stabilizer (WeierstrassCurve.VariableChange F) W :=
    fun e => ⟨C e, (hC e).choose⟩
  let : Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) W) := finite_variableChanges F W
  apply Finite.of_injective c
  intro e f h
  have hc : C e = C f := congrArg Subtype.val h
  exact represented_unique W (C f) e f (hc ▸ hC e) (hC f)

#print axioms finite_originIso
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms

namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

def ActualOriginIso (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) :=
  { e : genericScheme k M ≅ genericScheme k M //
    e.hom ≫ genericStructure k M = genericStructure k M ∧
    genericPoint k M s hs ≫ e.hom = genericPoint k M s hs }

lemma finite_actualOriginIso (h3 : 3 ≤ r) (heven : Even r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    Finite (ActualOriginIso k M s hs.1) := by
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T heven M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k r hr h3 T heven M hM s hs X Y hX hY a ha c hc
  let : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  let := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 heven
  let : Finite (FiniteOriginAutomorphisms.OriginIso (LaurentSeries k) (curve k r)) :=
    FiniteOriginAutomorphisms.finite_originIso (LaurentSeries k) (curve k r)
  have hEinv : E.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hE.1, Iso.inv_hom_id_assoc]
  have hOinv : origin k r ≫ E.inv = genericPoint k M s hs.1 := by
    rw [← hE.2.2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let f : ActualOriginIso k M s hs.1 → FiniteOriginAutomorphisms.OriginIso (LaurentSeries k) (curve k r) :=
    fun e => ⟨E.symm ≪≫ e.val ≪≫ E, by
      constructor
      · change (E.inv ≫ e.val.hom ≫ E.hom) ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r = _
        rw [Category.assoc, Category.assoc, hE.1, e.property.1, hEinv]
        rfl
      · change origin k r ≫ (E.inv ≫ e.val.hom ≫ E.hom) = origin k r
        rw [← Category.assoc, hOinv, ← Category.assoc, e.property.2, hE.2.2]⟩
  apply Finite.of_injective f
  intro e g h
  apply Subtype.ext
  apply Iso.ext
  apply (cancel_epi E.inv).mp
  apply (cancel_mono E.hom).mp
  have hh := congrArg (fun z : FiniteOriginAutomorphisms.OriginIso (LaurentSeries k) (curve k r) => z.val.hom) h
  simpa only [f, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hh

#print axioms finite_actualOriginIso
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation

/-! Infinite rational sections determine morphisms on the actual curve.
The commuting-family argument below supplies the final translation comparison. -/
namespace ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.CurveDensity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
lemma section_eq_of_point_eq (F : Type u) [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (p q : Spec (.of F) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (h : p (IsLocalRing.closedPoint F) = q (IsLocalRing.closedPoint F)) : p = q := by
  let : IsClosedImmersion q := isClosedImmersion_of_comp_eq_id f q hq
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := q) (IsLocalRing.closedPoint F) (IsLocalRing.closedPoint F) h
  let : Surjective (pullback.fst p q) := ⟨fun x => ⟨z, Subsingleton.elim _ _⟩⟩
  let : IsIso (pullback.fst p q) := isIso_of_isClosedImmersion_of_surjective _
  have he : pullback.fst p q = pullback.snd p q := by
    have hc := congrArg (fun g => g ≫ f) (pullback.condition (f := p) (g := q))
    simpa only [Category.assoc, hp, hq, Category.comp_id] using hc
  apply (cancel_epi (pullback.fst p q)).mp
  rw [pullback.condition, he]
lemma stalk_dim_le_one (F : Type u) [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show (closure ({x} : Set X)).Nonempty from ⟨x, subset_closure (Set.mem_singleton x)⟩)
    isClosed_closure.isLocallyClosed
  have hxy : y ≤ x := specializes_iff_mem_closure.mpr hy
  have hdim := SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed F f 1 y hyclosed
  rw [ringKrullDim_stalk_eq_coheight] at hdim ⊢
  exact (WithBot.coe_le_coe.mpr (Order.coheight_anti hxy)).trans hdim.le
lemma dense_of_infinite (F : Type u) [Field F] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f]
    (D : Set X) (hD : D.Infinite) : Dense D := by
  by_contra hn
  have hη : genericPoint X ∉ closure D := by
    intro hη
    apply hn
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) isClosed_closure
  exact hD ((Scheme.finite_of_isClosed_of_genericPoint_notMem
    (stalk_dim_le_one F f) isClosed_closure hη).subset subset_closure)
lemma eq_of_infinite_sections (F : Type u) [Field F] {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f]
    (g : Y ⟶ Spec (.of F)) [IsSeparated g]
    (a b : X ⟶ Y) (hab : a ≫ g = b ≫ g)
    {I : Type*} [Infinite I] (p : I → (Spec (.of F) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) (hinj : Function.Injective p)
    (heq : ∀ i, p i ≫ a = p i ≫ b) : a = b := by
  let pts : I → X := fun i => p i (IsLocalRing.closedPoint F)
  have hi : Function.Injective pts := by
    intro i j hij
    exact hinj (section_eq_of_point_eq F f (p i) (p j) (hp i) (hp j) hij)
  apply Scheme.Hom.eq_of_forall_comp_eq_of_dense_of_isReduced a b g hab
    (Set.range pts) (dense_of_infinite F f _ (Set.infinite_range_of_injective hi))
  rintro _ ⟨i, rfl⟩
  exact ⟨F, inferInstance, p i, ⟨IsLocalRing.closedPoint F, rfl⟩, heq i⟩
#print axioms section_eq_of_point_eq
#print axioms dense_of_infinite
#print axioms eq_of_infinite_sections
open NeronModelInfra WeierstrassProjModel ActualGenericGroupLaw

def OriginIso {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (o : Spec (.of F) ⟶ X) :=
  {e : X ≅ X // e.hom ≫ f = f ∧ o ≫ e.hom = o}

lemma comp_id_point {F : Type u} [Field F] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of F)} (p : SchemeHomOver (𝟙 _) f) :
    schemeHomOverComp (𝟙 _) (Category.comp_id _) p = p :=
  Subtype.ext (Category.id_comp _)

lemma commutingFamily_translations (F : Type u) [Field F] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
    (G : RelativeGroupLaw F f) (hc : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    [Finite (OriginIso f (G.one (𝟙 _)).val)]
    {I : Type*} [Infinite I] (A : I → (X ≅ X))
    (hover : ∀ a, (A a).hom ≫ f = f)
    (hcomm : ∀ a b, (A a).hom ≫ (A b).hom = (A b).hom ≫ (A a).hom)
    (hinj : Function.Injective (fun a => (G.one (𝟙 _)).val ≫ (A a).hom)) :
    ∀ a {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x : SchemeHomOver t f),
      x.val ≫ (A a).hom =
        (G.mul t x (schemeHomOverComp t (Category.comp_id t)
          (pointsEquiv (A a) (hover a) (𝟙 _) (G.one (𝟙 _))))).val := by
  classical
  let P : I → SchemeHomOver (𝟙 _) f := fun a =>
    pointsEquiv (A a) (hover a) (𝟙 _) (G.one (𝟙 _))
  choose τ hτover hτ using fun a => G.exists_iso_comp_eq_and_comp_hom_eq_mul (P a)
  have hOτ (a : I) : (G.one (𝟙 _)).val ≫ (τ a).hom = (P a).val := by
    simpa only [comp_id_point, G.one_mul] using hτ a (𝟙 _) (G.one (𝟙 _))
  let R : I → OriginIso f (G.one (𝟙 _)).val := fun a =>
    ⟨A a ≪≫ (τ a).symm, by
      constructor
      · change ((A a).hom ≫ (τ a).inv) ≫ f = f
        have hi : (τ a).inv ≫ f = f := by
          rw [← hτover a, Iso.inv_hom_id_assoc]
          exact (hτover a).symm
        rw [Category.assoc, hi, hover a]
      · change (G.one (𝟙 _)).val ≫ ((A a).hom ≫ (τ a).inv) = _
        rw [← Category.assoc]
        change (P a).val ≫ (τ a).inv = _
        rw [← hOτ a, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  have hnorm (a : I) (x : SchemeHomOver (𝟙 _) f) :
      x.val ≫ (A a).hom =
        (G.mul (𝟙 _) (pointsEquiv (R a).val (R a).property.1 (𝟙 _) x) (P a)).val := by
    have ht := hτ a (𝟙 _) (pointsEquiv (R a).val (R a).property.1 (𝟙 _) x)
    rw [comp_id_point] at ht
    change (x.val ≫ ((A a).hom ≫ (τ a).inv)) ≫ (τ a).hom = _ at ht
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht
  obtain ⟨β, hβ⟩ := Finite.exists_infinite_fiber R
  let B := R ⁻¹' {β}
  let : Infinite B := hβ
  intro a V t x
  let Q := pointsEquiv β.val β.property.1 (𝟙 _) (P a)
  obtain ⟨σ, hσover, hσ⟩ := G.exists_iso_comp_eq_and_comp_hom_eq_mul Q
  have heq : (A a).hom = σ.hom := by
    apply eq_of_infinite_sections F f f _ _ ((hover a).trans hσover.symm)
      (fun b : B => (P b.val).val) (fun b => (P b.val).property)
    · intro b c h
      exact Subtype.ext (hinj h)
    · intro b
      have hb : R b.val = β := b.property
      calc
        (P b.val).val ≫ (A a).hom = (P a).val ≫ (A b.val).hom := by
          change ((G.one (𝟙 _)).val ≫ (A b.val).hom) ≫ (A a).hom =
            ((G.one (𝟙 _)).val ≫ (A a).hom) ≫ (A b.val).hom
          rw [Category.assoc, hcomm b.val a, Category.assoc]
        _ = (G.mul (𝟙 _) Q (P b.val)).val := by rw [hnorm, hb]
        _ = (G.mul (𝟙 _) (P b.val) Q).val := by rw [hc]
        _ = (P b.val).val ≫ σ.hom := by
          simpa only [comp_id_point] using (hσ (𝟙 _) (P b.val)).symm
  have hQ : P a = Q := by
    apply Subtype.ext
    have h := hσ (𝟙 _) (G.one (𝟙 _))
    rw [comp_id_point, G.one_mul, ← heq] at h
    exact h
  rw [heq]
  simpa only [← hQ] using hσ t x
#print axioms commutingFamily_translations
end ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.CurveDensity
namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ActualScalarTranslation

theorem actual_scalar_translation :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
    ∀ (G : Law k M), IsOriginLaw k M s hs.1 G →
    ∀ (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv), ∀ (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (zeroIndex r hr) a p),
    IsTranslation k M G p hp.1 (scalarMap k M rot scal inv ha a) := by
  intro k _ _ r hr h3 T he M hM s hs G hG rot scal inv ha a p hp
  let : IsIntegral (genericScheme k M) := generic_integral k h3 M hM
  let : SmoothOfRelativeDimension 1 (genericStructure k M) :=
    generic_relative_one k h3 M hM s hs
  let : IsProper (genericStructure k M) := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  let : IsLocallyNoetherian (genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  let : CompactSpace (genericScheme k M) :=
    (quasiCompact_iff_compactSpace (genericStructure k M)).mp inferInstance
  have ho : (G.one (𝟙 _)).val = genericPoint k M s hs.1 := by
    rw [hG.1]
    exact Category.id_comp _
  let : Finite (CurveDensity.OriginIso (genericStructure k M) (G.one (𝟙 _)).val) := by
    rw [ho]
    exact finite_actualOriginIso k M h3 he hM s hs
  let : Infinite kˣ := (Set.infinite_range_iff
    (scalar_origin_orbit_injective k M h3 hM s hs rot scal inv ha)).mp
      (scalar_origin_orbit_infinite k M h3 hM s hs rot scal inv ha)
  let A : kˣ → (genericScheme k M ≅ genericScheme k M) := fun b =>
    genericIso k M (scal b) (modelOver k M id b false (scal b) (ha.2.1 b))
  have hA (b : kˣ) : (A b).hom = scalarMap k M rot scal inv ha b := rfl
  have hover (b : kˣ) : (A b).hom ≫ genericStructure k M = genericStructure k M := by
    exact pullback.lift_snd _ _ _
  have hc (b c : kˣ) : (A b).hom ≫ (A c).hom = (A c).hom ≫ (A b).hom := by
    rw [hA, hA, ← scalarMap_mul k M h3 hM, mul_comm, scalarMap_mul k M h3 hM]
  have hi : Function.Injective (fun b => (G.one (𝟙 _)).val ≫ (A b).hom) := by
    simpa only [ho, hA] using scalar_origin_orbit_injective k M h3 hM s hs rot scal inv ha
  intro V t x
  have ht := CurveDensity.commutingFamily_translations (LaurentSeries k) (X := genericScheme k M)
    (genericStructure k M) G hG.2 A hover hc hi a t x
  have hpoint : schemeHomOverComp t (Category.comp_id t)
      (ActualGenericGroupLaw.pointsEquiv (A a) (hover a) (𝟙 _) (G.one (𝟙 _))) =
      pointOver k M t p hp.1 := by
    apply Subtype.ext
    change t ≫ ((G.one (𝟙 _)).val ≫ (A a).hom) = t ≫ genericPoint k M p hp.1
    rw [ho, hA, scalar_origin k M h3 hM s hs rot scal inv ha a p hp]
  rw [hpoint] at ht
  exact ht.symm
#print axioms actual_scalar_translation
end ArithmeticThetaMarkedGroupLawR0146
