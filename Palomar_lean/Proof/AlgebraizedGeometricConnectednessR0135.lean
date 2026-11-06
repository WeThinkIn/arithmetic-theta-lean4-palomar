module

public import AlgebraizedGenericSmoothnessR0135
public import PolygonGlobalFunctionsR0131
public import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete

public import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
public import Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
public import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
public import P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete
public import ProperFormalFunctions

@[expose] public section

/-! Geometric connectedness of every algebraization of the prescribed polygon.
The finite-stage inclusions are identified with the genuine parameter-power
subschemes. Accepted proper formal functions separates global sections; the
accepted finite-stage constants and completeness then identify global sections
with power series. Flat base change gives constants on the generic fiber and
all its scalar extensions, which implies geometric connectedness. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGeometricConnectednessR0135
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131

open ArithmeticThetaGeometricPrerequisites
open P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete

lemma iso_appTop_bijective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Bijective e.hom.appTop := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))
  exact ConcreteCategory.bijective_of_isIso e.hom.appTop

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

def modelScalar : PowerSeries k →+* Γ(M.X, ⊤) :=
  M.p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom

abbrev parameter : M.X.IdealSheafData :=
  parameterIdeal (PowerSeries k) M.X M.p PowerSeries.X

lemma stage_closed (hM : IsModel k T M) (n : ℕ) : IsClosedImmersion (M.inclusion n) := by
  let : IsClosedImmersion (baseInclusion k n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.of_isPullback (hM.2.2.1 n).flip inferInstance

lemma pullback_kernel (n : ℕ) :
    (pullback.fst M.p (baseInclusion k n)).ker = parameter k M ^ (n+1) := by
  let : IsClosedImmersion (baseInclusion k n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply]
  rw [FormalBridge.parameter_ideal_affine]
  have h := (SolH0T2.ker_ι_app M.p ((Ideal.span {PowerSeries.X}) ^ (n+1)) U.2).1
  change RingHom.ker ((pullback.fst M.p (baseInclusion k n)).app U.1).hom = _ at h
  rw [h, Ideal.map_pow, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
  rfl

lemma inclusion_kernel (hM : IsModel k T M) (n : ℕ) :
    (M.inclusion n).ker = parameter k M ^ (n+1) := by
  rw [← (hM.2.2.1 n).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact pullback_kernel k M n

/-- The actual finite polygon is the actual parameter-power closed subscheme. -/
lemma exists_stageParameterIso (hM : IsModel k T M) (n : ℕ) :
    ∃ e : (T.atlas n).X ≅ (parameter k M ^ (n+1)).subscheme,
      e.hom ≫ (parameter k M ^ (n+1)).subschemeι = M.inclusion n := by
  let := stage_closed k M hM n
  let e := asIso (M.inclusion n).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (inclusion_kernel k M hM n))
  refine ⟨e, ?_⟩
  have h := inclusion_kernel k M hM n
  change ((M.inclusion n).toImage ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h)) ≫ _ = _
  have he : eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫
      (parameter k M ^ (n+1)).subschemeι = (M.inclusion n).ker.subschemeι := by
    generalize parameter k M ^ (n+1) = J at h ⊢
    subst J
    simp
  rw [Category.assoc, he]
  exact (M.inclusion n).toImage_imageι

def stageParameterIso (hM : IsModel k T M) (n : ℕ) :
    (T.atlas n).X ≅ (parameter k M ^ (n+1)).subscheme :=
  (exists_stageParameterIso k M hM n).choose

lemma stageParameterIso_over (hM : IsModel k T M) (n : ℕ) :
    (stageParameterIso k M hM n).hom ≫ (parameter k M ^ (n+1)).subschemeι =
      M.inclusion n :=
  (exists_stageParameterIso k M hM n).choose_spec

/-- Formal-functions uniqueness separates genuine global functions by all stages. -/
lemma stages_jointly_injective (hM : IsModel k T M) (s t : Γ(M.X, ⊤))
    (hst : ∀ n, (M.inclusion n).appTop s = (M.inclusion n).appTop t) : s = t := by
  let := hM.1
  let family (n : ℕ) := (parameter k M ^ n).subschemeι.appTop s
  have hf : CompatibleFormalFunctions M.X (parameter k M) family := by
    intro m n h
    change ((parameter k M ^ n).subschemeι.appTop ≫
      (Scheme.IdealSheafData.inclusion h).appTop) s = _
    rw [← Scheme.Hom.comp_appTop, Scheme.IdealSheafData.inclusion_subschemeι]
  obtain ⟨z, hz, hu⟩ := proper_formal_functions_h0 (PowerSeries k) PowerSeries.X M.X M.p family hf
  apply (hu s (fun n => rfl)).trans
  symm
  apply hu t
  intro n
  cases n with
  | zero =>
    have : IsEmpty (parameter k M ^ 0).subscheme := by simp; infer_instance
    have : Subsingleton Γ((parameter k M ^ 0).subscheme, ⊤) := inferInstance
    exact Subsingleton.elim _ _
  | succ n =>
    apply (iso_appTop_bijective (stageParameterIso k M hM n)).1
    change (((parameter k M ^ (n+1)).subschemeι).appTop ≫
      (stageParameterIso k M hM n).hom.appTop) t =
      (((parameter k M ^ (n+1)).subschemeι).appTop ≫
      (stageParameterIso k M hM n).hom.appTop) s
    rw [← Scheme.Hom.comp_appTop, stageParameterIso_over]
    exact (hst n).symm


lemma scalar_naturality {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    (q : Y ⟶ Spec (CommRingCat.of B)) (i : Y ⟶ X) (f : A →+* B)
    (h : i ≫ p = q ≫ Spec.map (CommRingCat.ofHom f)) (a : A) :
    i.appTop (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
      q.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a)) := by
  have H := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop h)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at H
  rw [H]
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom f)) a).symm

lemma stage_modelScalar (hM : IsModel k T M) (n : ℕ) (a : PowerSeries k) :
    (M.inclusion n).appTop (modelScalar k M a) =
      globalBase k r n hr (T.atlas n) (trunc (PowerSeries k) PowerSeries.X n a) :=
  scalar_naturality M.p (T.atlas n).p (M.inclusion n)
    (trunc (PowerSeries k) PowerSeries.X n) (hM.2.2.1 n).w a

lemma stageScalar_bijective (h3 : 3 ≤ r) (n : ℕ) :
    Function.Bijective (globalBase k r n hr (T.atlas n)) :=
  polygon_global_functions k r n hr h3 (T.overlap n) (T.overlap_spec n) (T.atlas n)

lemma transition_scalar (n N : ℕ) (h : n ≤ N) (a : R k N) :
    (T.transition n N h).appTop (globalBase k r N hr (T.atlas N) a) =
      globalBase k r n hr (T.atlas n) (truncReduce (PowerSeries k) PowerSeries.X n N h a) :=
  scalar_naturality (T.atlas N).p (T.atlas n).p (T.transition n N h)
    (truncReduce (PowerSeries k) PowerSeries.X n N h) (T.transition_spec n N h).1 a

/-- The global scalar map is bijective, using every actual finite stage and
formal-functions uniqueness on the genuine parameter ideal. -/
lemma modelScalar_bijective (h3 : 3 ≤ r) (hM : IsModel k T M) :
    Function.Bijective (modelScalar k M) := by
  classical
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  have hsep : (⨅ n : ℕ, I^n) = ⊥ := by
    rw [show I = IsLocalRing.maximalIdeal (PowerSeries k) from
      (PowerSeries.maximalIdeal_eq_span_X).symm]
    exact Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hsmod (x y : PowerSeries k) (n : ℕ) :
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule (PowerSeries k) (PowerSeries k))] ↔ x-y ∈ I^n := by
    rw [SModEq.sub_mem]
    simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hall : a ∈ ⨅ n : ℕ, I^n := by
      rw [Ideal.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n =>
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        apply (stageScalar_bijective k (T := T) h3 n).1
        change globalBase k r n hr (T.atlas n) (trunc (PowerSeries k) PowerSeries.X n a) = _
        rw [← stage_modelScalar k M hM, ha, map_zero, map_zero]
    rwa [hsep] at hall
  · intro s
    have hex : ∀ n, ∃ a : PowerSeries k,
        globalBase k r n hr (T.atlas n) (trunc (PowerSeries k) PowerSeries.X n a) =
          (M.inclusion n).appTop s := by
      intro n
      obtain ⟨a, ha⟩ := (stageScalar_bijective k (T := T) h3 n).2 ((M.inclusion n).appTop s)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨a, ha⟩
    choose a ha using hex
    have hc {n N : ℕ} (h : n ≤ N) : a N - a n ∈ I^(n+1) := by
      apply Ideal.Quotient.eq.mp
      apply (stageScalar_bijective k (T := T) h3 n).1
      have H := congrArg (fun z => (T.transition n N h).appTop z) (ha N)
      rw [transition_scalar k n N h] at H
      change globalBase k r n hr (T.atlas n) (trunc (PowerSeries k) PowerSeries.X n (a N)) =
        ((M.inclusion N).appTop ≫ (T.transition n N h).appTop) s at H
      rw [← Scheme.Hom.comp_appTop, hM.2.2.2 n N h] at H
      exact H.trans (ha n).symm
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete
      (I := I) (M := PowerSeries k)) (f := a) (fun {n N} h => by
        rw [hsmod]
        have H := hc h
        rw [← neg_sub, neg_mem_iff] at H
        exact Ideal.pow_le_pow_right (Nat.le_succ n) H)
    refine ⟨L, stages_jointly_injective k M hM _ s (fun n => ?_)⟩
    rw [stage_modelScalar k M hM, ← ha n]
    congr 1
    apply Ideal.Quotient.eq.mpr
    have h₁ : a (n+1) - L ∈ I^(n+1) := (hsmod _ _ _).mp (hL (n+1))
    have h₂ := hc (Nat.le_succ n)
    have he : L - a n = (a (n+1) - a n) - (a (n+1) - L) := by ring
    rw [he]
    exact sub_mem h₂ h₁

/-- Flat localization carries the actual global scalar isomorphism to k((t)). -/
lemma genericScalar_bijective (h3 : 3 ≤ r) (hM : IsModel k T M) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
      (genericStructure k M).appTop).hom := by
  let := hM.1
  let : Module.Flat (PowerSeries k) (LaurentSeries k) :=
    IsLocalization.flat (LaurentSeries k) (Submonoid.powers (PowerSeries.X : PowerSeries k))
  have : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.p
  have : QuasiSeparatedSpace M.X := quasiSeparatedSpace_of_quasiSeparated M.p
  have H := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat M.p (LaurentSeries k)
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv ≫ M.p.appTop) := by
    have : IsIso ((forget CommRingCat).map
        ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv ≫ M.p.appTop)) :=
      (isIso_iff_bijective _).mpr (modelScalar_bijective k M h3 hM)
    exact isIso_of_reflects_iso _ (forget CommRingCat)
  have hIso := H.isIso_inl_of_isIso (by infer_instance)
  let : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
      (genericStructure k M).appTop) := hIso
  exact ConcreteCategory.bijective_of_isIso _

/-- The scalar isomorphism persists after every algebra extension of k((t)). -/
lemma generic_geometricallyConnected (h3 : 3 ≤ r) (hM : IsModel k T M) :
    GeometricallyConnected (genericStructure k M) := by
  let := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  have : CompactSpace ↥(pullback M.p (genericBase k)) :=
    QuasiCompact.compactSpace_of_compactSpace (genericStructure k M)
  have : QuasiSeparatedSpace ↥(pullback M.p (genericBase k)) :=
    quasiSeparatedSpace_of_quasiSeparated (genericStructure k M)
  apply geometricallyConnected_of_bijective_algebraMap_sections
  intro A _ _
  change Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (pullback.snd (genericStructure k M)
      (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) A)))).appLE ⊤ ⊤ le_top).hom
  rw [SolH0T2.appLE_top_top]
  exact bijective_appTop_pullback_snd_of_bijective_appTop (genericStructure k M)
    (genericScalar_bijective k M h3 hM) A

end ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGeometricConnectednessR0135

namespace ArithmeticThetaProjectiveEffectivityR0135

theorem algebraized_geometric_connectedness :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
      ∀ M : ArithmeticThetaProjectiveEffectivityR0135.Model k T,
      ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
      AlgebraicGeometry.GeometricallyConnected
        (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) := by
  intro k _ _ r hr h3 T M hM
  exact AlgebraizedGeometricConnectednessR0135.generic_geometricallyConnected k M h3 hM

end ArithmeticThetaProjectiveEffectivityR0135
#print axioms ArithmeticThetaProjectiveEffectivityR0135.algebraized_geometric_connectedness
