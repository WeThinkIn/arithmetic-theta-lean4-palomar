import ProjectiveTowerEffectivityR0135
import TateNodeGenericFiber
import Theorems.Thm_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
import Theorems.Thm_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective

/-! Generic smoothness of every proper flat algebraization of the prescribed
infinitesimal polygon. Actual stalk quotients modulo t² transfer regularity
from the algebraic node; proper specialization and localization give regular
generic stalks of dimension at most one. All scalar maps come from the
prescribed structure morphisms. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135
open CategoryTheory AlgebraicGeometry ArithmeticThetaNodeCharts

variable (k : Type u) [Field k] [CharZero k]

/-- The Laurent-series action on the localized node is the unique extension
of its actual power-series action. -/
def nodeGenericScalar : LaurentSeries k →+* GenericNode k :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries k)
    (show IsUnit (((toGeneric k).comp (algebraMap (Base k) (Node k))) PowerSeries.X)
      from IsLocalization.Away.algebraMap_isUnit (t k))

omit [CharZero k] in
lemma nodeGenericScalar_base (c : PowerSeries k) :
    nodeGenericScalar k (algebraMap (PowerSeries k) (LaurentSeries k) c) =
      toGeneric k (algebraMap (Base k) (Node k) c) :=
  IsLocalization.Away.lift_eq _ _ c

omit [CharZero k] in
lemma genericTorus_equiv_scalar (e : GenericNode k ≃+* GenericTorus k)
    (he : e.toRingHom.comp ((toGeneric k).comp (quotientMap k)) = genericTorusMap k) :
    e.toRingHom.comp (nodeGenericScalar k) = LaurentPolynomial.C := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries k))
  apply RingHom.ext
  intro c
  change e (nodeGenericScalar k (algebraMap (PowerSeries k) (LaurentSeries k) c)) = _
  rw [nodeGenericScalar_base]
  have hc := RingHom.congr_fun he (MvPolynomial.C c)
  simp only [RingHom.comp_apply, quotient_C, genericTorusMap, MvPolynomial.eval₂Hom_C] at hc
  convert hc using 1 <;> rfl

lemma laurentPolynomial_smooth (K : Type u) [Field K] :
    (LaurentPolynomial.C : K →+* LaurentPolynomial K).Smooth := by
  let : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
    IsScalarTower.of_algebraMap_eq' (by ext c; simp)
  let : Algebra.Smooth (Polynomial K) (LaurentPolynomial K) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial K)
  let : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth K (LaurentPolynomial K) :=
    Algebra.Smooth.comp K (Polynomial K) (LaurentPolynomial K)
  exact (RingHom.smooth_algebraMap).mpr inferInstance

/-- Smoothness of the algebraic node after inverting the parameter, with
the coefficient action fixed by localization. -/
lemma nodeGenericScalar_smooth : (nodeGenericScalar k).Smooth := by
  obtain ⟨e, he, _⟩ := node_generic_torus_equivalence k
  have hs : (e.toRingHom.comp (nodeGenericScalar k)).Smooth := by
    rw [genericTorus_equiv_scalar k e he]
    exact laurentPolynomial_smooth (LaurentSeries k)
  have h := hs.comp (RingHom.Smooth.of_bijective (f := e.symm.toRingHom) e.symm.bijective)
  simpa only [← RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom,
    RingHom.id_comp] using h

lemma nodeGenericSpec_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (nodeGenericScalar k))) :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (nodeGenericScalar_smooth k)

omit [CharZero k] in
/-- The localized node is the categorical base change along the specific
power-series-to-Laurent-series homomorphism. -/
lemma nodeGeneric_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (toGeneric k)))
      (Spec.map (CommRingCat.ofHom (nodeGenericScalar k)))
      (Spec.map (CommRingCat.ofHom (algebraMap (Base k) (Node k))))
      (genericBase k) := by
  have hcomm : (nodeGenericScalar k).comp
      (algebraMap (PowerSeries k) (LaurentSeries k)) =
      (toGeneric k).comp (algebraMap (Base k) (Node k)) :=
    RingHom.ext (nodeGenericScalar_base k)
  let : IsLocalization
      ((Submonoid.powers (PowerSeries.X : PowerSeries k)).map
        (algebraMap (Base k) (Node k))) (GenericNode k) := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away (t k) (GenericNode k))
  exact AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap (Base k) (Node k))
      (nodeGenericScalar k) hcomm (Submonoid.powers (PowerSeries.X : PowerSeries k)))

/-- Smoothness of the actual generic structure map of the algebraic node. -/
lemma algebraicNode_generic_smooth :
    Smooth (CategoryTheory.Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap (Base k) (Node k))))
      (genericBase k)) := by
  let := nodeGenericSpec_smooth k
  have hs : Smooth ((nodeGeneric_isPullback k).isoPullback.inv ≫
      Spec.map (CommRingCat.ofHom (nodeGenericScalar k))) := inferInstance
  have heq := (nodeGeneric_isPullback k).isoPullback_inv_snd
  rw [heq] at hs
  exact hs

open ArithmeticThetaInfinitesimalPolygonR0129
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

/-- Finite presentation of the actual model map follows from properness over
the noetherian power-series ring. -/
lemma model_finitePresentation (hM : IsModel k T M) :
    LocallyOfFinitePresentation M.p := by
  let := hM.1
  infer_instance

lemma generic_proper (hM : IsModel k T M) : IsProper (genericStructure k M) := by
  let := hM.1
  unfold genericStructure
  infer_instance

lemma generic_finitePresentation (hM : IsModel k T M) :
    LocallyOfFinitePresentation (genericStructure k M) := by
  let := model_finitePresentation k M hM
  unfold genericStructure
  infer_instance

/-- The generic inclusion is the open immersion obtained by inverting t. -/
lemma generic_inclusion_open :
    IsOpenImmersion (CategoryTheory.Limits.pullback.fst M.p (genericBase k)) := by
  let : IsOpenImmersion (genericBase k) :=
    IsOpenImmersion.of_isLocalization (S := LaurentSeries k) (PowerSeries.X : PowerSeries k)
  infer_instance

/-- Every point of a proper model specializes to the closed fiber. -/
lemma specializes_closedFiber (hM : IsModel k T M) (x : M.X) :
    ∃ y : M.X, x ⤳ y ∧ M.p y = IsLocalRing.closedPoint (PowerSeries k) := by
  let := hM.1
  exact M.p.isClosedMap.specializingMap (IsLocalRing.specializes_closedPoint (M.p x))

omit [CharZero k] in
lemma closedPoint_in_baseInclusion :
    IsLocalRing.closedPoint (PowerSeries k) ∈ Set.range (baseInclusion k 0) := by
  change IsLocalRing.closedPoint (PowerSeries k) ∈
    Set.range (PrimeSpectrum.comap (trunc (PowerSeries k) PowerSeries.X 0))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  change RingHom.ker (trunc (PowerSeries k) PowerSeries.X 0) ≤
    IsLocalRing.maximalIdeal (PowerSeries k)
  simp only [trunc, Ideal.mk_ker, Nat.zero_add, pow_one,
    PowerSeries.maximalIdeal_eq_span_X, le_refl]

/-- The specializations supplied by properness land in the actual node charts
of the specified tower, via the prescribed model inclusion. -/
lemma specializes_specialChart (hM : IsModel k T M) (x : M.X) :
    ∃ (i : Fin r) (z : specA k 0),
      x ⤳ M.inclusion 0 ((T.atlas 0).chart i z) := by
  obtain ⟨y, hxy, hy⟩ := specializes_closedFiber k M hM x
  obtain ⟨b, hb⟩ := closedPoint_in_baseInclusion k
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (hM.2.2.1 0) y b
    (hy.trans hb.symm)
  obtain ⟨i, z, hz⟩ := (T.atlas 0).covers w
  refine ⟨i, z, ?_⟩
  rw [hz, hw]
  exact hxy

/-- The coefficient action on a model stalk comes from the specified p. -/
def modelStalkScalar (x : M.X) : PowerSeries k →+* M.X.presheaf.stalk x :=
  (M.X.presheaf.germ ⊤ x trivial).hom.comp
    (M.p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom)

def modelStalkParameter (x : M.X) : M.X.presheaf.stalk x :=
  modelStalkScalar k M x PowerSeries.X

/-- The actual finite-stage inclusions give surjective stalk quotient maps,
whose kernels are the prescribed parameter powers. -/
lemma inclusion_stalk_quotient (hM : IsModel k T M) (n : ℕ)
    (y : (T.atlas n).X) :
    Function.Surjective ((M.inclusion n).stalkMap y).hom ∧
      RingHom.ker ((M.inclusion n).stalkMap y).hom =
        Ideal.span {(modelStalkParameter k M (M.inclusion n y)) ^ (n+1)} := by
  have H := AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    (trunc (PowerSeries k) PowerSeries.X n) Ideal.Quotient.mk_surjective
    M.p (M.inclusion n) (T.atlas n).p (hM.2.2.1 n) y
  refine ⟨H.1, ?_⟩
  rw [H.2]
  change Ideal.map (modelStalkScalar k M (M.inclusion n y))
    (RingHom.ker (trunc (PowerSeries k) PowerSeries.X n)) = _
  simp only [trunc, Ideal.mk_ker, ← Ideal.span_singleton_pow, Ideal.map_pow, Ideal.map_span,
    Set.image_singleton, modelStalkParameter]

/-- A canonical quotient identification, with the value on every model
stalk element specified. -/
def inclusionStalkEquiv (hM : IsModel k T M) (n : ℕ) (y : (T.atlas n).X) :
    (M.X.presheaf.stalk (M.inclusion n y) ⧸
      Ideal.span {(modelStalkParameter k M (M.inclusion n y)) ^ (n+1)}) ≃+*
      (T.atlas n).X.presheaf.stalk y :=
  (Ideal.quotEquivOfEq (inclusion_stalk_quotient k M hM n y).2.symm).trans
    (RingHom.quotientKerEquivOfSurjective (inclusion_stalk_quotient k M hM n y).1)

lemma inclusionStalkEquiv_mk (hM : IsModel k T M) (n : ℕ) (y : (T.atlas n).X)
    (s : M.X.presheaf.stalk (M.inclusion n y)) :
    inclusionStalkEquiv k M hM n y (Ideal.Quotient.mk _ s) =
      ((M.inclusion n).stalkMap y).hom s := rfl

/-- Include a prescribed finite node chart in the algebraized model. -/
def modelChart (n : ℕ) (i : Fin r) : specA k n ⟶ M.X :=
  (T.atlas n).chart i ≫ M.inclusion n

lemma modelChart_over (hM : IsModel k T M) (n : ℕ) (i : Fin r) :
    modelChart k M n i ≫ M.p = structureMap k n ≫ baseInclusion k n := by
  rw [modelChart, Category.assoc, (hM.2.2.1 n).w, ← Category.assoc,
    (T.atlas n).chart_over i]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Passing through the atlas chart preserves the actual kernel, because its
stalk map is an isomorphism. -/
lemma modelChart_stalk_quotient (hM : IsModel k T M) (n : ℕ)
    (i : Fin r) (z : specA k n) :
    Function.Surjective ((modelChart k M n i).stalkMap z).hom ∧
      RingHom.ker ((modelChart k M n i).stalkMap z).hom =
        Ideal.span {(modelStalkParameter k M (modelChart k M n i z)) ^ (n+1)} := by
  let : IsOpenImmersion ((T.atlas n).chart i) := (T.atlas n).chart_open i
  have hb := ConcreteCategory.bijective_of_isIso (((T.atlas n).chart i).stalkMap z)
  have h := inclusion_stalk_quotient k M hM n ((T.atlas n).chart i z)
  constructor
  · rw [modelChart, Scheme.Hom.stalkMap_comp]
    intro v
    obtain ⟨w, hw⟩ := hb.2 v
    obtain ⟨s, hs⟩ := h.1 w
    refine ⟨s, ?_⟩
    change (((T.atlas n).chart i).stalkMap z).hom
      (((M.inclusion n).stalkMap ((T.atlas n).chart i z)).hom s) = v
    rw [hs]
    exact hw
  · rw [modelChart, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    rw [RingHom.ker_comp_of_injective _ hb.1]
    exact h.2

section ScalarNaturality
variable {O S : Type u} [CommRing O] [CommRing S]
variable {X Y : Scheme.{u}}

def stalkScalarOf (f : X ⟶ Spec (CommRingCat.of O)) (x : X) :
    O →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)

lemma stalkScalarOf_comp (f : X ⟶ Spec (CommRingCat.of O)) (g : Y ⟶ X) (y : Y) :
    ((g.stalkMap y).hom).comp (stalkScalarOf f (g y)) = stalkScalarOf (g ≫ f) y := by
  ext a
  exact g.germ_stalkMap_apply ⊤ y trivial
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))

lemma stalkScalarOf_spec (q : O →+* S) (z : Spec (CommRingCat.of S)) (a : O) :
    stalkScalarOf (Spec.map (CommRingCat.ofHom q)) z a =
      (StructureSheaf.toStalk S z).hom (q a) := by
  unfold stalkScalarOf
  simp only [RingHom.comp_apply]
  have h := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [← h]
  rfl
/-- The scalar map factors through the prescribed map of local rings. -/
lemma stalkScalarOf_factor (f : X ⟶ Spec (CommRingCat.of O)) (x : X) :
    stalkScalarOf f x = (f.stalkMap x).hom.comp
      (StructureSheaf.toStalk O (f x)).hom := by
  ext a
  exact (f.germ_stalkMap_apply ⊤ x trivial
    ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Flatness of the geometric map gives flatness of the actual stalk action. -/
lemma stalkScalarOf_flat (f : X ⟶ Spec (CommRingCat.of O)) [Flat f] (x : X) :
    (stalkScalarOf f x).Flat := by
  rw [stalkScalarOf_factor]
  apply RingHom.Flat.comp ?_ (Flat.stalkMap f x)
  change (algebraMap O ((Spec.structureSheaf O).presheaf.stalk (f x))).Flat
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat _ (f x).asIdeal.primeCompl)
end ScalarNaturality

lemma modelStalkScalar_flat (hM : IsModel k T M) (x : M.X) :
    (modelStalkScalar k M x).Flat := by
  let := hM.2.1
  exact stalkScalarOf_flat M.p x

/-- The actual uniformizer acts injectively, by flatness over k[[t]]. -/
lemma modelStalkParameter_regular (hM : IsModel k T M) (x : M.X) :
    IsLeftRegular (modelStalkParameter k M x) := by
  letI := (modelStalkScalar k M x).toAlgebra
  letI : Module.Flat (PowerSeries k) (M.X.presheaf.stalk x) :=
    modelStalkScalar_flat k M hM x
  have h : IsSMulRegular (M.X.presheaf.stalk x) (PowerSeries.X : PowerSeries k) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (R := PowerSeries k) (M := M.X.presheaf.stalk x)
      (mem_nonZeroDivisors_iff_ne_zero.mpr PowerSeries.X_ne_zero)
  exact h


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The chart stalk map sends the model's actual base parameter to xy in
the explicit truncated node stalk. -/
lemma modelChart_stalk_parameter (hM : IsModel k T M) (n : ℕ)
    (i : Fin r) (z : specA k n) :
    ((modelChart k M n i).stalkMap z).hom
      (modelStalkParameter k M (modelChart k M n i z)) =
      (StructureSheaf.toStalk (A k n) z).hom
        (coordX k n * coordY k n) := by
  have hc := RingHom.congr_fun
    (stalkScalarOf_comp M.p (modelChart k M n i) z) PowerSeries.X
  change ((modelChart k M n i).stalkMap z).hom
    (modelStalkParameter k M (modelChart k M n i z)) =
    stalkScalarOf (modelChart k M n i ≫ M.p) z PowerSeries.X at hc
  rw [modelChart_over k M hM] at hc
  rw [structureMap, baseInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at hc
  have hs := stalkScalarOf_spec ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
    z PowerSeries.X
  exact hc.trans (hs.trans (congrArg (StructureSheaf.toStalk (A k n) z).hom
    (coordX_mul_coordY k n).symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity lifts both node coordinates, and the kernel computation
gives their equation modulo the precise parameter power in the model stalk. -/
lemma exists_modelStalk_nodeCoordinates (hM : IsModel k T M) (n : ℕ)
    (i : Fin r) (z : specA k n) :
    ∃ x y : M.X.presheaf.stalk (modelChart k M n i z),
      ((modelChart k M n i).stalkMap z).hom x =
        (StructureSheaf.toStalk (A k n) z).hom (coordX k n) ∧
      ((modelChart k M n i).stalkMap z).hom y =
        (StructureSheaf.toStalk (A k n) z).hom (coordY k n) ∧
      x * y - modelStalkParameter k M (modelChart k M n i z) ∈
        Ideal.span {(modelStalkParameter k M (modelChart k M n i z)) ^ (n+1)} := by
  have H := modelChart_stalk_quotient k M hM n i z
  obtain ⟨x, hx⟩ := H.1 ((StructureSheaf.toStalk (A k n) z).hom (coordX k n))
  obtain ⟨y, hy⟩ := H.1 ((StructureSheaf.toStalk (A k n) z).hom (coordY k n))
  refine ⟨x, y, hx, hy, ?_⟩
  rw [← H.2, RingHom.mem_ker, map_sub, map_mul, hx, hy,
    modelChart_stalk_parameter k M hM, map_mul, sub_self]

/-- The parameter belongs to the maximal ideal at every finite-stage point
of the model; no unrelated local algebra structure is used. -/
lemma modelStalkParameter_mem_maximalIdeal (hM : IsModel k T M) (n : ℕ)
    (y : (T.atlas n).X) :
    modelStalkParameter k M (M.inclusion n y) ∈
      IsLocalRing.maximalIdeal (M.X.presheaf.stalk (M.inclusion n y)) := by
  let f := ((M.inclusion n).stalkMap y).hom
  let t := modelStalkParameter k M (M.inclusion n y)
  have hz : f (t ^ (n+1)) = 0 := by
    apply RingHom.mem_ker.mp
    rw [(inclusion_stalk_quotient k M hM n y).2]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hn : IsNilpotent (f t) := ⟨n+1, by simpa only [map_pow] using hz⟩
  change ¬ IsUnit t
  intro ht
  exact hn.not_isUnit (ht.map f)

/-- The actual truncation of the algebraic node. -/
def nodeTruncation (n : ℕ) : specA k n ⟶ Spec (CommRingCat.of (Node k)) :=
  Spec.map (CommRingCat.ofHom (trunc (Node k) (t k) n))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma nodeTruncation_stalk_quotient (n : ℕ) (z : specA k n) :
    Function.Surjective ((nodeTruncation k n).stalkMap z).hom ∧
      RingHom.ker ((nodeTruncation k n).stalkMap z).hom =
        Ideal.span {((StructureSheaf.toStalk (Node k) (nodeTruncation k n z)).hom (t k)) ^ (n+1)} := by
  have H := AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    (trunc (Node k) (t k) n) Ideal.Quotient.mk_surjective
    (𝟙 _) (nodeTruncation k n) (𝟙 _) IsPullback.of_id_snd z
  refine ⟨H.1, ?_⟩
  rw [H.2]
  change Ideal.map (stalkScalarOf (𝟙 _) (nodeTruncation k n z))
    (RingHom.ker (trunc (Node k) (t k) n)) = _
  have hid : stalkScalarOf (𝟙 (Spec (CommRingCat.of (Node k)))) (nodeTruncation k n z) =
      (StructureSheaf.toStalk (Node k) (nodeTruncation k n z)).hom := by
    apply RingHom.ext
    intro a
    rfl
  rw [hid]
  simp only [trunc, Ideal.mk_ker, ← Ideal.span_singleton_pow, Ideal.map_pow,
    Ideal.map_span, Set.image_singleton]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma nodeStalk_regular (p : Spec (CommRingCat.of (Node k))) :
    IsRegularLocalRing ((Spec (CommRingCat.of (Node k))).presheaf.stalk p) := by
  let := (ArithmeticThetaAnnularGeometry.algebraic_node_regular_normal k).1
  exact IsRegularLocalRing.of_ringEquiv (StructureSheaf.stalkIso (Node k) p).toRingEquiv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma nodeStalk_parameter_regular (p : Spec (CommRingCat.of (Node k))) :
    IsLeftRegular ((StructureSheaf.toStalk (Node k) p).hom (t k)) := by
  let := (node_flat_domain_parameter k).1
  let p' : PrimeSpectrum (Node k) := p
  letI : Module.Flat (Node k) ((Spec.structureSheaf (Node k)).presheaf.stalk p') :=
    IsLocalization.flat _ p'.asIdeal.primeCompl
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (R := Node k) (M := (Spec.structureSheaf (Node k)).presheaf.stalk p')
    (mem_nonZeroDivisors_iff_ne_zero.mpr (node_flat_domain_parameter k).2.2.1)
  exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma nodeStalk_parameter_mem_maximalIdeal (n : ℕ) (z : specA k n) :
    (StructureSheaf.toStalk (Node k) (nodeTruncation k n z)).hom (t k) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (Node k))).presheaf.stalk
        (nodeTruncation k n z)) := by
  let f := ((nodeTruncation k n).stalkMap z).hom
  let a := (StructureSheaf.toStalk (Node k) (nodeTruncation k n z)).hom (t k)
  have hz : f (a ^ (n+1)) = 0 := by
    apply RingHom.mem_ker.mp
    rw [(nodeTruncation_stalk_quotient k n z).2]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hn : IsNilpotent (f a) := ⟨n+1, by simpa only [map_pow] using hz⟩
  change ¬ IsUnit a
  intro ha
  exact hn.not_isUnit (ha.map f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma nodeStalk_dimension_le_two (n : ℕ) (z : specA k n) :
    ringKrullDim ((Spec (CommRingCat.of (Node k))).presheaf.stalk
      (nodeTruncation k n z)) ≤ 2 := by
  let p : PrimeSpectrum (Node k) := nodeTruncation k n z
  have ht : t k ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem (n+1)
    change trunc (Node k) (t k) n (t k ^ (n+1)) ∈ z.asIdeal
    have hz : trunc (Node k) (t k) n (t k ^ (n+1)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
    rw [hz]
    exact z.asIdeal.zero_mem
  have hxy : x k ∈ p.asIdeal ∨ y k ∈ p.asIdeal := by
    apply p.isPrime.mem_or_mem
    rwa [node_xy]
  letI := ArithmeticThetaAnnularGeometry.CompletedNodeSupport.residue_parameter_isMaximal k
  letI : Field (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.Resid
      (ArithmeticThetaNodeCharts.parameter k)) := Ideal.Quotient.field _
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2 := by
    rcases hxy with hx | hy
    · exact ArithmeticThetaAnnularGeometry.CompletedNodeSupport.branch_local_dimension_le_two
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.branchY
          (ArithmeticThetaNodeCharts.parameter k)).toRingHom
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.branchY_surjective _)
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.ker_branchY _)
        p.asIdeal hx
    · exact ArithmeticThetaAnnularGeometry.CompletedNodeSupport.branch_local_dimension_le_two
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.branchX
          (ArithmeticThetaNodeCharts.parameter k)).toRingHom
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.branchX_surjective _)
        (ArithmeticThetaAnnularGeometry.AlgebraicNodeSupport.CrossingResolutionR1.ker_branchX _)
        p.asIdeal hy
  exact (ringKrullDim_eq_of_ringEquiv (StructureSheaf.stalkIso (Node k) p).toRingEquiv).symm.le.trans hd

section FirstOrderComparison
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- A surjection whose kernel is contained in the square of the maximal ideal
preserves the minimal number of generators, by Nakayama's lemma. -/
lemma maximalIdeal_spanFinrank_eq_of_ker_le_sq
    (f : A →+* B) (hf : Function.Surjective f)
    (hk : RingHom.ker f ≤ IsLocalRing.maximalIdeal A ^ 2) :
    (IsLocalRing.maximalIdeal A).spanFinrank =
      (IsLocalRing.maximalIdeal B).spanFinrank := by
  classical
  letI : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hmap := IsLocalRing.map_maximalIdeal_of_surjective f hf
  apply le_antisymm
  · obtain ⟨s, hs, hspan⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B)).exists_span_finset_card_eq_spanFinrank
    have hfcopy := hf
    choose lift hlift using hfcopy
    let J : Ideal A := Ideal.span (lift '' (s : Set B))
    have hJmap : J.map f = IsLocalRing.maximalIdeal B := by
      change (Ideal.span (lift '' (s : Set B))).map f = _
      rw [Ideal.map_span, ← Set.image_comp]
      simpa only [Function.comp_def, hlift, Set.image_id', Ideal.submodule_span_eq] using hspan
    have hJ : J ≤ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.maximalIdeal_comap f, ← Ideal.map_le_iff_le_comap]
      exact hJmap.le
    have hcomap : IsLocalRing.maximalIdeal A = J ⊔ RingHom.ker f := by
      rw [← IsLocalRing.maximalIdeal_comap f, ← hJmap,
        Ideal.comap_map_of_surjective _ hf, RingHom.ker_eq_comap_bot]
    have hgen : J = IsLocalRing.maximalIdeal A := by
      apply le_antisymm hJ
      apply Submodule.le_of_le_smul_of_le_jacobson_bot
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _)
      rw [Ideal.smul_eq_mul, ← pow_two]
      exact hcomap.le.trans (sup_le_sup_left hk J)
    rw [← hgen]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (s.finite_toSet.image lift)).trans
      ((Set.ncard_image_le s.finite_toSet).trans (by simpa using hs.le))
  · rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg f (IsNoetherian.noetherian _)

/-- First-order thickenings of a regular parameter determine regularity of
Noetherian local rings. The comparison is between actual surjective maps. -/
lemma regularLocal_of_common_firstOrder_quotient
    (f : A →+* C) (g : B →+* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (tA : A) (tB : B)
    (hA : tA ∈ IsLocalRing.maximalIdeal A) (hB : tB ∈ IsLocalRing.maximalIdeal B)
    (rA : IsLeftRegular tA) (rB : IsLeftRegular tB)
    (kf : RingHom.ker f = Ideal.span {tA ^ 2})
    (kg : RingHom.ker g = Ideal.span {tB ^ 2})
    (regB : IsRegularLocalRing B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  haveI : IsNoetherianRing C := isNoetherianRing_of_surjective A C f hf
  have hdA : ringKrullDim C + 1 = ringKrullDim A := by
    have he := RingHom.quotientKerEquivOfSurjective hf
    rw [← ringKrullDim_eq_of_ringEquiv he, kf]
    exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (show IsSMulRegular A (tA ^ 2) from rA.pow 2)
      (Ideal.pow_mem_of_mem _ hA 2 (by decide))
  have hdB : ringKrullDim C + 1 = ringKrullDim B := by
    have he := RingHom.quotientKerEquivOfSurjective hg
    rw [← ringKrullDim_eq_of_ringEquiv he, kg]
    exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (show IsSMulRegular B (tB ^ 2) from rB.pow 2)
      (Ideal.pow_mem_of_mem _ hB 2 (by decide))
  have hdim := hdA.symm.trans hdB
  have heA := maximalIdeal_spanFinrank_eq_of_ker_le_sq f hf
    (by rw [kf]; exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_pow hA 2)))
  have heB := maximalIdeal_spanFinrank_eq_of_ker_le_sq g hg
    (by rw [kg]; exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_pow hB 2)))
  refine ⟨?_, hdim⟩
  letI := regB
  rw [isRegularLocalRing_iff, heA, ← heB, hdim]
  exact IsRegularLocalRing.spanFinrank_maximalIdeal

end FirstOrderComparison

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual first-order chart identifies both stalk quotients, transferring
regularity of the algebraic node to the algebraized model. -/
lemma modelChart_stalk_regular (hM : IsModel k T M) (i : Fin r) (z : specA k 1) :
    IsRegularLocalRing (M.X.presheaf.stalk (modelChart k M 1 i z)) ∧
      ringKrullDim (M.X.presheaf.stalk (modelChart k M 1 i z)) ≤ 2 := by
  let := hM.1
  let : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.p
  have H := regularLocal_of_common_firstOrder_quotient
    ((modelChart k M 1 i).stalkMap z).hom ((nodeTruncation k 1).stalkMap z).hom
    (modelChart_stalk_quotient k M hM 1 i z).1 (nodeTruncation_stalk_quotient k 1 z).1
    (modelStalkParameter k M (modelChart k M 1 i z))
    ((StructureSheaf.toStalk (Node k) (nodeTruncation k 1 z)).hom (t k))
    (modelStalkParameter_mem_maximalIdeal k M hM 1 ((T.atlas 1).chart i z))
    (nodeStalk_parameter_mem_maximalIdeal k 1 z)
    (modelStalkParameter_regular k M hM _) (nodeStalk_parameter_regular k _)
    (modelChart_stalk_quotient k M hM 1 i z).2 (nodeTruncation_stalk_quotient k 1 z).2
    (nodeStalk_regular k _)
  exact ⟨H.1, H.2.le.trans (nodeStalk_dimension_le_two k 1 z)⟩


lemma closedPoint_in_baseInclusion_all (n : ℕ) :
    IsLocalRing.closedPoint (PowerSeries k) ∈ Set.range (baseInclusion k n) := by
  change IsLocalRing.closedPoint (PowerSeries k) ∈
    Set.range (PrimeSpectrum.comap (trunc (PowerSeries k) PowerSeries.X n))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  change RingHom.ker (trunc (PowerSeries k) PowerSeries.X n) ≤
    IsLocalRing.maximalIdeal (PowerSeries k)
  simp only [trunc, Ideal.mk_ker, PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.pow_le_self (Nat.succ_ne_zero n)

lemma specializes_firstOrderChart (hM : IsModel k T M) (x : M.X) :
    ∃ (i : Fin r) (z : specA k 1), x ⤳ modelChart k M 1 i z := by
  obtain ⟨y, hxy, hy⟩ := specializes_closedFiber k M hM x
  obtain ⟨b, hb⟩ := closedPoint_in_baseInclusion_all k 1
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (hM.2.2.1 1) y b
    (hy.trans hb.symm)
  obtain ⟨i, z, hz⟩ := (T.atlas 1).covers w
  refine ⟨i, z, ?_⟩
  change x ⤳ M.inclusion 1 ((T.atlas 1).chart i z)
  rw [hz, hw]
  exact hxy

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma generic_modelStalk_parameter_unit
    (z : ↥(CategoryTheory.Limits.pullback M.p (genericBase k) : Scheme)) :
    IsUnit (modelStalkParameter k M (CategoryTheory.Limits.pullback.fst M.p (genericBase k) z)) := by
  let j := CategoryTheory.Limits.pullback.fst M.p (genericBase k)
  let g := CategoryTheory.Limits.pullback.snd M.p (genericBase k)
  have hc := RingHom.congr_fun (stalkScalarOf_comp M.p j z) PowerSeries.X
  have hs := RingHom.congr_fun (stalkScalarOf_comp (genericBase k) g z) PowerSeries.X
  have hcomm : j ≫ M.p = g ≫ genericBase k := CategoryTheory.Limits.pullback.condition
  rw [hcomm] at hc
  have he : (j.stalkMap z).hom (modelStalkParameter k M (j z)) =
      (g.stalkMap z).hom (stalkScalarOf (genericBase k) (g z) PowerSeries.X) :=
    hc.trans hs.symm
  apply isUnit_of_map_unit (j.stalkMap z).hom
  rw [he]
  apply IsUnit.map
  have hspec := stalkScalarOf_spec
    (algebraMap (PowerSeries k) (LaurentSeries k)) (g z) PowerSeries.X
  rw [show stalkScalarOf (genericBase k) (g z) PowerSeries.X = _ from hspec]
  exact (IsLocalization.Away.algebraMap_isUnit (S := LaurentSeries k)
    (PowerSeries.X : PowerSeries k)).map (StructureSheaf.toStalk (LaurentSeries k) (g z)).hom

lemma modelStalkParameter_specializes {x y : M.X} (h : x ⤳ y) :
    (M.X.presheaf.stalkSpecializes h).hom (modelStalkParameter k M y) =
      modelStalkParameter k M x := by
  exact TopCat.Presheaf.germ_stalkSpecializes_apply M.X.presheaf (U := ⊤) (y := y) trivial h
    (M.p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom PowerSeries.X))

section LocalDimension
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

lemma localization_nonmax_dimension_le_one (hdim : ringKrullDim A ≤ 2)
    (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A) :
    ringKrullDim (Localization.AtPrime p) ≤ 1 := by
  have hlt : p < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm : (IsLocalRing.maximalIdeal A).height ≤ 2 := by
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← h2] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hh : p.height ≤ 1 := by
    have h3 := h1.trans hm
    have hne : p.height ≠ ⊤ := by
      intro htop
      rw [htop] at h3
      exact absurd h3 (by decide)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h3 ⊢
    have h4 : n + 1 ≤ 2 := by exact_mod_cast h3
    exact_mod_cast (by omega : n ≤ 1)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact WithBot.coe_le_coe.mpr hh
end LocalDimension

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Generic points are proper generizations of regular first-order stalks. -/
lemma generic_modelStalk_regular (hM : IsModel k T M)
    (z : ↥(CategoryTheory.Limits.pullback M.p (genericBase k) : Scheme)) :
    IsRegularLocalRing (M.X.presheaf.stalk (CategoryTheory.Limits.pullback.fst M.p (genericBase k) z)) ∧
      ringKrullDim (M.X.presheaf.stalk (CategoryTheory.Limits.pullback.fst M.p (genericBase k) z)) ≤ 1 := by
  let a := CategoryTheory.Limits.pullback.fst M.p (genericBase k) z
  obtain ⟨i, w, haw⟩ := specializes_firstOrderChart k M hM a
  let b := modelChart k M 1 i w
  have hb := modelChart_stalk_regular k M hM i w
  letI := hb.1
  letI : IsDomain (M.X.presheaf.stalk b) :=
    ArithmeticThetaAnnularGeometry.CompletedNodeSupport.LocalSurface.regular_local_domain _
  letI : IsRegularRing (M.X.presheaf.stalk b) :=
    ArithmeticThetaAnnularGeometry.CompletedNodeSupport.LocalSurface.regular_ring_dim_two _ hb.2
  let f := (M.X.presheaf.stalkSpecializes haw).hom
  let p : Ideal (M.X.presheaf.stalk b) := (IsLocalRing.maximalIdeal (M.X.presheaf.stalk a)).comap f
  letI : p.IsPrime := Ideal.comap_isPrime f _
  letI : Algebra (M.X.presheaf.stalk b) (M.X.presheaf.stalk a) := f.toAlgebra
  letI : IsLocalization.AtPrime (M.X.presheaf.stalk a) p :=
    Scheme.isLocalization_atPrime_stalk_of_specializes haw
  have hp : p ≠ IsLocalRing.maximalIdeal (M.X.presheaf.stalk b) := by
    intro heq
    have ht := modelStalkParameter_mem_maximalIdeal k M hM 1 ((T.atlas 1).chart i w)
    change modelStalkParameter k M b ∈ IsLocalRing.maximalIdeal (M.X.presheaf.stalk b) at ht
    rw [← heq] at ht
    change ¬ IsUnit (f (modelStalkParameter k M b)) at ht
    rw [show f (modelStalkParameter k M b) = modelStalkParameter k M a from
      modelStalkParameter_specializes k M haw] at ht
    exact ht (generic_modelStalk_parameter_unit k M z)
  let e := (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (M.X.presheaf.stalk a)).toRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e,
    (ringKrullDim_eq_of_ringEquiv e).symm.le.trans (localization_nonmax_dimension_le_one hb.2 p hp)⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma genericFiber_stalk_regular (hM : IsModel k T M)
    (z : ↥(CategoryTheory.Limits.pullback M.p (genericBase k) : Scheme)) :
    IsRegularLocalRing ((CategoryTheory.Limits.pullback M.p (genericBase k) : Scheme).presheaf.stalk z) ∧
      ringKrullDim ((CategoryTheory.Limits.pullback M.p (genericBase k) : Scheme).presheaf.stalk z) ≤ 1 := by
  let j := CategoryTheory.Limits.pullback.fst M.p (genericBase k)
  letI : IsOpenImmersion j := generic_inclusion_open k M
  let e := CategoryTheory.Iso.commRingCatIsoToRingEquiv (asIso (j.stalkMap z))
  have h := generic_modelStalk_regular k M hM z
  letI := h.1
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.le.trans h.2⟩

section FirstOrderNode
variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A first-order equation xy=t modulo t² already places t in the
coordinate ideal of a local ring. The correction factor is a unit because
t belongs to the maximal ideal. -/
lemma parameter_mem_coordinateIdeal_of_firstOrder (t x y : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hxy : x * y - t ∈ Ideal.span {t ^ 2}) :
    t ∈ Ideal.span ({x, y} : Set A) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hxy
  have heq : x * y = t * (1 + t * a) := by
    calc
      x * y = (x * y - t) + t := by ring
      _ = (t ^ 2 * a) + t := by rw [ha]
      _ = t * (1 + t * a) := by ring
  have hu : IsUnit (1 + t * a) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    change 1 - (1 + t * a) ∈ IsLocalRing.maximalIdeal A
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using
      (IsLocalRing.maximalIdeal A).neg_mem
        ((IsLocalRing.maximalIdeal A).mul_mem_right a ht)
  obtain ⟨v, hv⟩ := hu
  have ht' : t = x * y * (↑v⁻¹ : A) := by
    rw [heq, ← hv, mul_assoc, Units.mul_inv, mul_one]
  rw [ht']
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
    (Ideal.subset_span (Set.mem_insert x {y})))

/-- Removing the redundant parameter leaves exactly two local generators.
This is the nodal part of the intended first-order regularity argument. -/
lemma maximalIdeal_eq_pair_of_firstOrder (t x y : A)
    (hgen : IsLocalRing.maximalIdeal A = Ideal.span ({t, x, y} : Set A))
    (hxy : x * y - t ∈ Ideal.span {t ^ 2}) :
    IsLocalRing.maximalIdeal A = Ideal.span ({x, y} : Set A) := by
  have ht : t ∈ IsLocalRing.maximalIdeal A := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_insert t {x, y})
  have ht' := parameter_mem_coordinateIdeal_of_firstOrder t x y ht hxy
  rw [hgen]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ht'
    · exact Ideal.subset_span hz
  · apply Ideal.span_mono
    exact Set.subset_insert t {x, y}

/-- The first-order nodal generators prove regularity once the local
dimension lower bound is supplied. -/
lemma regularLocal_of_firstOrder [IsNoetherianRing A] (t x y : A)
    (hgen : IsLocalRing.maximalIdeal A = Ideal.span ({t, x, y} : Set A))
    (hxy : x * y - t ∈ Ideal.span {t ^ 2})
    (hdim : 2 ≤ ringKrullDim A) : IsRegularLocalRing A := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [maximalIdeal_eq_pair_of_firstOrder t x y hgen hxy]
  have hspan : (Ideal.span ({x, y} : Set A)).spanFinrank ≤ 2 := by
    classical
    have hh := Submodule.spanFinrank_span_le_ncard_of_finite (R := A)
      (Finset.finite_toSet ({x, y} : Finset A))
    simp only [Set.ncard_coe_finset] at hh
    simpa only [Finset.coe_insert, Finset.coe_singleton, Ideal.submodule_span_eq]
      using hh.trans Finset.card_le_two
  exact le_trans (by exact_mod_cast hspan) hdim

end FirstOrderNode

end ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135

#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.algebraicNode_generic_smooth
#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.specializes_specialChart
#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.maximalIdeal_eq_pair_of_firstOrder
#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.regularLocal_of_firstOrder

#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.exists_modelStalk_nodeCoordinates
#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.modelStalkParameter_regular

#print axioms ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.modelChart_stalk_regular

namespace ArithmeticThetaProjectiveEffectivityR0135
open AlgebraicGeometry AlgebraizedGenericSmoothnessR0135

/-- Every proper flat algebraization of the prescribed infinitesimal polygon
has smooth generic fiber for its actual Laurent-series structure map. -/
theorem algebraized_generic_smoothness :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ M : Model k T, IsModel k T M → Smooth (genericStructure k M) := by
  intro k _ _ r hr _ T M hM
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  letI := generic_finitePresentation k M hM
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro z _
  have h := genericFiber_stalk_regular k M hM z
  exact Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
    (genericStructure k M) z h.1 h.2

end ArithmeticThetaProjectiveEffectivityR0135

#print axioms ArithmeticThetaProjectiveEffectivityR0135.algebraized_generic_smoothness
