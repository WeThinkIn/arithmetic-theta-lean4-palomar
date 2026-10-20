module

public import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
public import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
public import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
public import ProjectiveCubicChartR0145
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
public import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace CompactifiedCoordinateIsomorphism
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

omit [CharZero k] in
lemma projective_proper : IsProper (projectiveStructure k r) :=
  WeierstrassProjModel.projModelStrCR_isProper (curve k r).toProjective

lemma complement_dominant (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    IsDominant (complement k M s).ι := by
  letI := generic_integral k h3 M hM
  obtain ⟨x⟩ := complement_nonempty k h3 M hM s hs
  exact AlgebraicGeometry.Opens.isDominant_ι ((complement k M s).isOpen.dense ⟨x.1, x.2⟩)

/-- Agreement with the complete affine restriction determines a compactification. -/
lemma compactification_unique (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (e e' : genericScheme k M ≅ projectiveCurve k r)
    (he : IsCompactificationIso k M s hs.1 a c e)
    (he' : IsCompactificationIso k M s hs.1 a c e') : e = e' := by
  letI := generic_integral k h3 M hM
  letI := projective_proper k (r := r)
  letI := complement_dominant k h3 M hM s hs
  apply Iso.ext
  exact ext_of_isDominant_of_isSeparated (projectiveStructure k r)
    (he.1.trans he'.1.symm) (complement k M s).ι (he.2.1.trans he'.2.1.symm)

lemma missing_point_dvr (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (x : genericScheme k M) (hx : x ∉ Set.range (complement k M s).ι.base) :
    letI := generic_integral k h3 M hM
    IsDiscreteValuationRing ((genericScheme k M).presheaf.stalk x) := by
  letI := generic_integral k h3 M hM
  letI := generic_relative_one k h3 M hM s hs
  have hx' : x ∈ ((s.ker.comap (genericInclusion k M)).support : Set (genericScheme k M)) := by
    rw [Scheme.Opens.range_ι] at hx
    change ¬ ¬ x ∈ ((s.ker.comap (genericInclusion k M)).support : Set (genericScheme k M)) at hx
    exact not_not.mp hx
  rw [generic_identity_support_singleton k M hM s hs.1
    (IsLocalRing.closedPoint (LaurentSeries k)), Set.mem_singleton_iff] at hx'
  subst x
  exact SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section
    (X := genericScheme k M) (genericStructure k M) (genericPoint k M s hs.1) (genericPoint_structure k M s hs.1)

/-- Properness extends the prescribed affine map across the actual identity. -/
lemma exists_extension (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (ha : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (hc : IsChartIso k r c) :
    ∃ f : genericScheme k M ⟶ projectiveCurve k r,
      f ≫ projectiveStructure k r = genericStructure k M ∧
      (complement k M s).ι ≫ f = a.hom ≫ c.hom ≫ chartInclusion k r := by
  letI := generic_integral k h3 M hM
  letI : Nonempty (complementScheme k M s) := complement_nonempty k h3 M hM s hs
  letI := projective_proper k (r := r)
  apply exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
    (C := genericScheme k M) (U := complementScheme k M s)
    (genericStructure k M) (complement k M s).ι (missing_point_dvr k h3 M hM s hs)
    (projectiveStructure k r) (a.hom ≫ c.hom ≫ chartInclusion k r)
  rw [Category.assoc, Category.assoc, hc.1]
  exact ha.1

namespace ValuationExtension
open CategoryTheory.Limits
open P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk.AlgebraicGeometry.ExtendDVR
section
variable {κ : Type u} [Field κ] {C : Scheme.{u}} [IsIntegral C]
variable (c : C ⟶ Spec (CommRingCat.of κ))
variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of κ))
theorem exists_valuation_chart [IsProper p] (t : Spec C.functionField ⟶ P) (ht : t ≫ p = ηK ≫ c)
    (x : C) (hx : ValuationRing (C.presheaf.stalk x)) :
    ∃ (V : C.Opens) (_ : x ∈ V) (g : (V : Scheme.{u}) ⟶ P) (a : Spec C.functionField ⟶ (V : Scheme.{u})),
      g ≫ p = V.ι ≫ c ∧ a ≫ V.ι = ηK ∧ a ≫ g = t := by
  haveI := hx

  have hV : ValuativeCriterion p := by
    have h := (inferInstance : IsProper p)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
      C.fromSpecStalk x = ηK := specMap_algebraMap_fromSpecStalk x
  have hsq : CommSq t (Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField))) p
      (C.fromSpecStalk x ≫ c) := ⟨by rw [ht, ← Category.assoc]; exact (congrArg (· ≫ c) hspec).symm⟩
  haveI : hsq.HasLift :=
    ValuativeCriterion.existence hV (ValuativeCommSq.mk (C.presheaf.stalk x) C.functionField _ _ hsq)

  haveI : LocallyOfFiniteType p := by
    have h := (inferInstance : IsProper p)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.2
  obtain ⟨V, hxV, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' c p hsq.lift hsq.fac_right
  refine ⟨V, hxV, g, Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
    V.fromSpecStalkOfMem x hxV, hg₂, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]; exact hspec
  · rw [Category.assoc, ← hg₁, hsq.fac_left]


end
theorem exists_valuation_extension
    {κ : Type u} [Field κ] {C U P : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of κ)) [IsIntegral C]
    (u : U ⟶ C) [IsOpenImmersion u] [Nonempty U]

    (hreg : ∀ x : C, x ∉ Set.range u.base → ValuationRing (C.presheaf.stalk x))
    (p : P ⟶ Spec (CommRingCat.of κ)) [IsProper p]
    (f : U ⟶ P) (hf : f ≫ p = u ≫ c) :
    ∃ g : C ⟶ P, g ≫ p = c ∧ u ≫ g = f := by
  classical

  have hηmem : ∀ z : Spec C.functionField, (ηK (C := C)).base z ∈ Set.range u.base := by
    intro z
    rw [ηK_base]
    exact genericPoint_mem_of_isOpen u.isOpenEmbedding.isOpen_range (Set.range_nonempty _)
  let ηU : Spec C.functionField ⟶ U := IsOpenImmersion.lift u ηK (by rintro _ ⟨z, rfl⟩; exact hηmem z)
  have hηU : ηU ≫ u = ηK := IsOpenImmersion.lift_fac u ηK _

  let ι := {x : C // x ∉ Set.range u.base}
  have hex : ∀ i : ι, ∃ (V : C.Opens) (_ : i.1 ∈ V) (g : (V : Scheme.{u}) ⟶ P) (a : Spec C.functionField ⟶ (V : Scheme.{u})),
      g ≫ p = V.ι ≫ c ∧ a ≫ V.ι = ηK ∧ a ≫ g = ηU ≫ f := fun i =>
    exists_valuation_chart c p (ηU ≫ f) (by rw [Category.assoc, hf, ← Category.assoc, hηU]) i.1 (hreg i.1 i.2)
  choose V hV g a hg ha hag using hex

  let X : Option ι → Scheme.{u} := fun o => o.elim U (fun i => (V i : Scheme.{u}))
  let j : ∀ o : Option ι, X o ⟶ C := fun o => match o with
    | none => u
    | some i => (V i).ι
  haveI hj : ∀ o : Option ι, IsOpenImmersion (j o) := by
    rintro (_ | i)
    · change IsOpenImmersion u; infer_instance
    · change IsOpenImmersion (V i).ι; infer_instance
  have hcov : ∀ y : C, ∃ (o : Option ι) (z : X o), (j o).base z = y := by
    intro y
    by_cases hy : y ∈ Set.range u.base
    · obtain ⟨z, hz⟩ := hy
      exact ⟨none, z, hz⟩
    · exact ⟨some ⟨y, hy⟩, ⟨y, hV ⟨y, hy⟩⟩, rfl⟩
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers (Option ι) X j hcov (fun o => hj o)

  let gl : ∀ o : Option ι, X o ⟶ P := fun o => match o with
    | none => f
    | some i => g i
  have hgl : ∀ o : Option ι, gl o ≫ p = j o ≫ c := by
    rintro (_ | i)
    · exact hf
    · exact hg i
  let w : ∀ o : Option ι, Spec C.functionField ⟶ X o := fun o => match o with
    | none => ηU
    | some i => a i
  have hw : ∀ o : Option ι, w o ≫ j o = ηK := by
    rintro (_ | i)
    · exact hηU
    · exact ha i
  have hwg : ∀ o : Option ι, w o ≫ gl o = ηU ≫ f := by
    rintro (_ | i)
    · rfl
    · exact hag i

  haveI : IsSeparated p := inferInstance
  have hcompat : ∀ o₁ o₂ : Option ι,
      pullback.fst (𝒰.f o₁) (𝒰.f o₂) ≫ gl o₁ = pullback.snd (𝒰.f o₁) (𝒰.f o₂) ≫ gl o₂ := fun o₁ o₂ =>
    fst_comp_eq_snd_comp c p (j o₁) (j o₂) (gl o₁) (gl o₂) (hgl o₁) (hgl o₂) (w o₁) (w o₂) (hw o₁) (hw o₂)
      ((hwg o₁).trans (hwg o₂).symm)
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 gl hcompat, ?_, ?_⟩
  · apply Scheme.Cover.hom_ext 𝒰
    intro o
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact hgl o
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 gl hcompat none

end ValuationExtension

lemma roots_distinct (h3 : 3 ≤ r) (he : Even r) :
    root k r 0 ≠ root k r 1 ∧ root k r 0 ≠ root k r 2 ∧ root k r 1 ≠ root k r 2 := by
  obtain ⟨m, hm⟩ := he
  have hrm : r = 2 * m := by omega
  clear hm
  subst r
  have h := ArithmeticThetaTateIdentities.general_two_torsion_distinct (k := k) m (by omega)
  have hi : Function.Injective (algebraMap (PowerSeries k) (LaurentSeries k)) :=
    IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  simp only [root, rootSeries]
  change _ ≠ algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateX (2*m) ((2*m)/2) 1) ∧
    _ ≠ algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateX (2*m) ((2*m)/2) (-1)) ∧
    algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateX (2*m) ((2*m)/2) 1) ≠
    algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaTateSeries.tateX (2*m) ((2*m)/2) (-1))
  rw [show 2*m/2 = m by omega]
  exact ⟨fun h01 => h.1 (hi h01), fun h02 => h.2.1 (hi h02), fun h12 => h.2.2 (hi h12)⟩

lemma curve_elliptic (h3 : 3 ≤ r) (he : Even r) : (curve k r).IsElliptic := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨h01, h02, h12⟩ := roots_distinct k h3 he
  constructor
  rw [isUnit_iff_ne_zero]
  have hΔ : (curve k r).Δ =
      16 * (root k r 0 - root k r 1)^2 * (root k r 0 - root k r 2)^2 *
        (root k r 1 - root k r 2)^2 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve]
    ring
  rw [hΔ]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (sub_ne_zero.mpr h01)))
    (pow_ne_zero _ (sub_ne_zero.mpr h02))) (pow_ne_zero _ (sub_ne_zero.mpr h12))

omit [CharZero k] in
lemma projective_integral : IsIntegral (projectiveCurve k r) := by
  letI : GeometricallyIntegral (projectiveStructure k r) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso (curve k r)
      (WeierstrassProjModel.projModel_pullback_iso_baseChange (curve k r).toProjective)
  exact GeometricallyIntegral.isIntegral_of_subsingleton (projectiveStructure k r)

lemma projective_relative_one (h3 : 3 ≤ r) (he : Even r) :
    SmoothOfRelativeDimension 1 (projectiveStructure k r) := by
  letI := curve_elliptic k h3 he
  exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (curve k r).toProjective

omit [CharZero k] in
lemma chart_open : IsOpenImmersion (chartInclusion k r) := by
  unfold chartInclusion
  infer_instance

lemma chart_dominant [Nonempty (Spec (CommRingCat.of (ChartRing k r)))] :
    IsDominant (chartInclusion k r) := by
  letI := projective_integral k (r := r)
  letI := chart_open k (r := r)
  exact ⟨(chartInclusion k r).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩

lemma exists_iso_extension (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (ha : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (hc : IsChartIso k r c) :
    ∃ e : genericScheme k M ≅ projectiveCurve k r,
      e.hom ≫ projectiveStructure k r = genericStructure k M ∧
      (complement k M s).ι ≫ e.hom = a.hom ≫ c.hom ≫ chartInclusion k r := by
  letI := generic_integral k h3 M hM
  letI := projective_integral k (r := r)
  letI := projective_relative_one k h3 he
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := projective_proper k (r := r)
  letI := chart_open k (r := r)
  letI : Nonempty (complementScheme k M s) := complement_nonempty k h3 M hM s hs
  letI : Nonempty (Spec (CommRingCat.of (ChartRing k r))) :=
    Nonempty.map (fun x => c.hom (a.hom x)) inferInstance
  letI := complement_dominant k h3 M hM s hs
  letI := chart_dominant k (r := r)
  obtain ⟨f, hfb, hfa⟩ := exists_extension k h3 M hM s hs X Y a ha c hc
  have hb : (c.inv ≫ a.inv ≫ (complement k M s).ι) ≫ genericStructure k M =
      chartInclusion k r ≫ projectiveStructure k r := by
    change c.inv ≫ a.inv ≫ complementStructure k M s = _
    rw [← ha.1]
    simp only [Iso.inv_hom_id_assoc]
    rw [← hc.1]
    simp
  obtain ⟨g, hgb, hga⟩ := ValuationExtension.exists_valuation_extension
    (C := projectiveCurve k r) (projectiveStructure k r) (chartInclusion k r)
    (fun x _ => valuationRing_stalk_of_smoothOfRelativeDimension_one
      (C := projectiveCurve k r) (projectiveStructure k r) x)
    (genericStructure k M) (c.inv ≫ a.inv ≫ (complement k M s).ι) hb
  have hfg : f ≫ g = 𝟙 _ := by
    apply ext_of_isDominant_of_isSeparated (genericStructure k M)
      (by rw [Category.assoc, hgb, hfb, Category.id_comp]) (complement k M s).ι
    rw [← Category.assoc, hfa]
    simp only [Category.assoc, hga, Iso.hom_inv_id_assoc, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    apply ext_of_isDominant_of_isSeparated (projectiveStructure k r)
      (by rw [Category.assoc, hfb, hgb, Category.id_comp]) (chartInclusion k r)
    rw [← Category.assoc, hga]
    simp only [Category.assoc, hfa, Iso.inv_hom_id_assoc, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hfb, hfa⟩

lemma section_eq_of_range_subset {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of F)) [IsSeparated f]
    (p q : Spec (CommRingCat.of F) ⟶ C)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (h : Set.range p ⊆ Set.range q) : p = q := by
  haveI : IsClosedImmersion (p ≫ f) := hp ▸ inferInstance
  haveI : IsClosedImmersion (q ≫ f) := hq ▸ inferInstance
  haveI : IsClosedImmersion p := IsClosedImmersion.of_comp p f
  haveI : IsClosedImmersion q := IsClosedImmersion.of_comp q f
  have hrad : p.ker.radical = p.ker := by
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply,
      Ideal.radical_eq_iff, RingHom.ker_eq_comap_bot]
    exact Ideal.isRadical_bot.comap _
  have hk : q.ker ≤ p.ker := by
    rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    change (p.ker.support : Set C) ⊆ q.ker.support
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    exact closure_mono h
  let l := IsClosedImmersion.lift q p hk
  have hl : l ≫ q = p := IsClosedImmersion.lift_fac q p hk
  have hlid : l = 𝟙 _ := by
    calc l = l ≫ q ≫ f := by rw [hq, Category.comp_id]
         _ = p ≫ f := by rw [← Category.assoc, hl]
         _ = 𝟙 _ := hp
  rw [← hl, hlid, Category.id_comp]

lemma origin_not_chart (k : Type u) [Field k] [CharZero k] (r : ℕ)
    (q : Spec (CommRingCat.of (LaurentSeries k))) :
    origin k r q ∉ Set.range (chartInclusion k r) := by
  open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization in
  obtain ⟨hO, hx, hz⟩ :=
    WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval (curve k r).toProjective
  change (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (curve k r)).val q ∉
    Set.range (WeierstrassCurve.DrinfeldGlobal.zChartι (curve k r).toProjective)
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  rw [hO, Scheme.Hom.comp_apply]
  change ¬ (Spec.map (CommRingCat.ofHom (WeierstrassProjModel.kwYChartEval (LaurentSeries k)
    (curve k r))) q) ∈
    WeierstrassCurve.DrinfeldGlobal.originChartι (curve k r).toProjective ⁻¹ᵁ
      Proj.basicOpen (WeierstrassProjModel.projModelGradingCR (curve k r).toProjective)
        (WeierstrassCurve.DrinfeldGlobal.coord (curve k r).toProjective 2)
  rw [Proj.awayι_preimage_basicOpen (WeierstrassProjModel.projModelGradingCR (curve k r).toProjective)
    (WeierstrassCurve.DrinfeldGlobal.coord_mem (curve k r).toProjective 1) one_pos
    (WeierstrassCurve.DrinfeldGlobal.coord_mem (curve k r).toProjective 2) one_pos]
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (WeierstrassCurve.DrinfeldGlobal.coord_mem (curve k r).toProjective 1)
      (WeierstrassCurve.DrinfeldGlobal.coord_mem (curve k r).toProjective 2) =
      WeierstrassCurve.DrinfeldGlobal.zOverY (curve k r).toProjective := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem,
      WeierstrassCurve.DrinfeldGlobal.zOverY, HomogeneousLocalization.Away.mk,
      HomogeneousLocalization.val_mk, pow_one]
  rw [he]
  intro h
  apply (PrimeSpectrum.mem_basicOpen _ _).mp h
  change WeierstrassProjModel.kwYChartEval (LaurentSeries k) (curve k r)
    (WeierstrassCurve.DrinfeldGlobal.zOverY (curve k r).toProjective) ∈ q.asIdeal
  rw [hz]
  exact Ideal.zero_mem _

lemma iso_extension_origin (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (e : genericScheme k M ≅ projectiveCurve k r)
    (hb : e.hom ≫ projectiveStructure k r = genericStructure k M)
    (ha : (complement k M s).ι ≫ e.hom = a.hom ≫ c.hom ≫ chartInclusion k r) :
    genericPoint k M s hs.1 ≫ e.hom = origin k r := by
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  have ho : origin k r ≫ projectiveStructure k r = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect (LaurentSeries k) (curve k r)).property
  have hib : e.inv ≫ genericStructure k M = projectiveStructure k r := by
    rw [← hb, Iso.inv_hom_id_assoc]
  have hp : (origin k r ≫ e.inv) ≫ genericStructure k M = 𝟙 _ := by
    rw [Category.assoc, hib, ho]
  have hsec : origin k r ≫ e.inv = genericPoint k M s hs.1 := by
    apply section_eq_of_range_subset (C := genericScheme k M)
      (genericStructure k M) _ _ hp (genericPoint_structure k M s hs.1)
    rintro x ⟨q, rfl⟩
    have hn : e.inv (origin k r q) ∉ complement k M s := by
      intro hm
      let z : complementScheme k M s := ⟨e.inv (origin k r q), hm⟩
      have hz := congrArg (fun f => f z) ha
      have heq : e.hom (e.inv (origin k r q)) = origin k r q := by
        rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
        rfl
      change e.hom (e.inv (origin k r q)) =
        chartInclusion k r (c.hom (a.hom z)) at hz
      exact origin_not_chart k r q ⟨c.hom (a.hom z), hz.symm.trans heq⟩
    have hm : e.inv (origin k r q) ∈
        ((s.ker.comap (genericInclusion k M)).support : Set (genericScheme k M)) := by
      change ¬ ¬ e.inv (origin k r q) ∈
        ((s.ker.comap (genericInclusion k M)).support : Set (genericScheme k M)) at hn
      exact not_not.mp hn
    rw [generic_identity_support_singleton k M hM s hs.1 q,
      Set.mem_singleton_iff] at hm
    exact ⟨q, hm.symm⟩
  rw [← hsec, Category.assoc, e.inv_hom_id, Category.comp_id]

end CompactifiedCoordinateIsomorphism
/-- The prescribed affine coordinate isomorphism extends uniquely across the actual identity. -/
theorem compactified_coordinate_isomorphism :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (a : CategoryTheory.Iso (ArithmeticThetaCubicModelR0144.complementScheme k M s) (ArithmeticThetaCubicModelR0144.cubicScheme k r)), ArithmeticThetaCubicModelR0144.IsCoordinateIso k M s X Y a → ∀ (c : CategoryTheory.Iso (ArithmeticThetaCubicModelR0144.cubicScheme k r) (AlgebraicGeometry.Spec (CommRingCat.of (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k r)))), ArithmeticThetaCompactifiedDifferentialR0145.IsChartIso k r c → ∃! e : CategoryTheory.Iso (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k r), ArithmeticThetaCompactifiedDifferentialR0145.IsCompactificationIso k M s hs.1 a c e := by
  intro k _ _ r hr h3 T he M hM s hs X Y _hX _hY a ha c hc
  obtain ⟨e, hb, he⟩ := CompactifiedCoordinateIsomorphism.exists_iso_extension
    k h3 he M hM s hs X Y a ha c hc
  have h : IsCompactificationIso k M s hs.1 a c e :=
    ⟨hb, he, CompactifiedCoordinateIsomorphism.iso_extension_origin k M hM s hs a c e hb he⟩
  exact ⟨e, h, fun e' h' =>
    CompactifiedCoordinateIsomorphism.compactification_unique k h3 M hM s hs a c e' e h' h⟩

#print axioms compactified_coordinate_isomorphism

end ArithmeticThetaCompactifiedDifferentialR0145
