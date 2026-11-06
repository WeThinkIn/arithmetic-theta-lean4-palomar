module

public import CompletedModelChartMapsR0152
public import CompletedMarkedChartIdealR0152
public import ActualSplitTorsionKernelR0152
public import CompletedChartFieldMapsR0152
public import KatoDivisorFieldBaseChangeR0151
public import RationalOrderUniqueR0066
public import SectionLocalDVRR0066
public import Mathlib.RingTheory.Flat.TorsionFree
public import SectionHeightOneR0066
public import HeightOneDVRR0066

@[expose] public section

-- Keep the original elaborated instance paths after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

/-! Transport of the actual Kato divisor to completed annular charts. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152.AnnularDivisor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140

variable (k : Type u) [Field k] [CharZero k]
abbrev GenericRing := ArithmeticThetaLocalOrdersR0066.GenericChart k

abbrev genericChartScheme : Scheme.{u} := Spec (.of (GenericRing k))

def genericChartInclusion : genericChartScheme k ⟶ chartScheme k :=
  Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k))

def genericScalar : LaurentSeries k →+* GenericRing k :=
  IsLocalization.Away.lift (S := LaurentSeries k) PowerSeries.X
    (g := (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k).comp
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k)) (by
        change IsUnit (algebraMap (Chart k) (GenericRing k)
          (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
        exact IsLocalization.Away.algebraMap_isUnit _)

lemma genericScalar_base (a : PowerSeries k) :
    genericScalar k (algebraMap (PowerSeries k) (LaurentSeries k) a) =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.base k a) :=
  IsLocalization.Away.lift_eq _ _ a

lemma generic_base_square :
    genericChartInclusion k ≫ chartBase k =
      Spec.map (CommRingCat.ofHom (genericScalar k)) ≫ genericBase k := by
  rw [genericChartInclusion, chartBase, genericBase, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (genericScalar_base k a).symm

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def chartGenericMap (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) : genericChartScheme k ⟶ genericScheme k M :=
  pullback.lift (genericChartInclusion k ≫ χ)
    (Spec.map (CommRingCat.ofHom (genericScalar k))) (by
      rw [Category.assoc, hχ, generic_base_square])

@[reassoc (attr := simp)]
lemma chartGenericMap_inclusion (M : Model k T) (χ : chartScheme k ⟶ M.X)
    (hχ : χ ≫ M.p = chartBase k) :
    chartGenericMap k M χ hχ ≫ genericInclusion k M =
      genericChartInclusion k ≫ χ := pullback.lift_fst _ _ _

/-- Every vertical power is a unit on the genuine generic chart. -/
lemma vertical_power_unit (n : ℕ) : IsUnit
    (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ n) :=
  (IsLocalization.Away.algebraMap_isUnit
    (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)).pow n

open ArithmeticThetaPolygonCartierR0133.MarkedIdealTowerBaseChangeR0133
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

/-- The ideal of an actual marked section on the generic completed chart.
This follows by pulling back the completed ideal through the localization map. -/
lemma generic_marked_ideal (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i j : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) :
    specIdeal ((genericPoint k M p hp.1).ker.comap (chartGenericMap k M χ hχ.1)) =
      Ideal.span {(ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (markedEquation k (hr := hr) j i a))} := by
  rw [← genericPoint_ker k M hM p hp.1,
    ← Scheme.IdealSheafData.comap_comp, chartGenericMap_inclusion,
    Scheme.IdealSheafData.comap_comp]
  change specIdeal ((p.ker.comap χ).comap
    (Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)))) = _
  rw [specIdeal_comap]
  change (markedChartIdeal k M p χ).map _ = _
  rw [(completed_marked_chart_ideal k r hr h3 T M hM i j a p hp χ hχ).1,
    Ideal.map_span, Set.image_singleton]

lemma genericScalar_field (a : LaurentSeries k) :
    ArithmeticThetaLocalOrdersR0066.toFunctionField k (genericScalar k a) =
      CompletedChartFieldMaps.laurentInclusion k a := by
  have hh : (ArithmeticThetaLocalOrdersR0066.toFunctionField k).comp (genericScalar k) =
      CompletedChartFieldMaps.laurentInclusion k := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries k) (K := LaurentSeries k)
    intro b
    rw [RingHom.comp_apply, genericScalar_base,
      CompletedChartFieldMaps.laurentInclusion_base]
    rfl
  exact RingHom.congr_fun hh a

/-- The specified field square remains the actual generic-point square after
passing from the model to its generic fiber. -/
lemma field_square (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ) :
    Spec.map (CommRingCat.ofHom φ) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) =
    Spec.map (CommRingCat.ofHom (ArithmeticThetaLocalOrdersR0066.toFunctionField k)) ≫
      chartGenericMap k M χ hχ := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, Category.assoc, chartGenericMap_inclusion, ← Category.assoc]
  change _ = (Spec.map (CommRingCat.ofHom (ArithmeticThetaLocalOrdersR0066.toFunctionField k)) ≫
    Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k))) ≫ χ
  rw [← Spec.map_comp]
  exact hφ

lemma specIdeal_support {R : Type u} [CommRing R]
    (I : (Spec (.of R)).IdealSheafData) (x : PrimeSpectrum R) :
    x ∈ I.support ↔ specIdeal I ≤ x.asIdeal := by
  rw [I.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) trivial,
    Spec_zeroLocus]
  change ((I.ideal ⟨⊤, isAffineOpen_top _⟩).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom ≤ x.asIdeal) ↔ _
  suffices hh : (I.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of R)).inv.hom = specIdeal I by rw [hh]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv).symm

/-- Scheme-theoretic ideal pullback detects precisely the actual marked point. -/
lemma generic_marked_point_iff (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i j : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (x : genericChartScheme k) :
    chartGenericMap k M χ hχ.1 x =
        genericPoint k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k)) ↔
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (markedEquation k (hr := hr) j i a) ∈ x.asIdeal := by
  letI : IsClosedImmersion (genericPoint k M p hp.1) := genericPoint_closed k M hM p hp.1
  have hs := specIdeal_support ((genericPoint k M p hp.1).ker.comap
    (chartGenericMap k M χ hχ.1)) x
  rw [generic_marked_ideal k h3 M hM i j a p hp χ hχ,
    Ideal.span_singleton_le_iff_mem, Scheme.IdealSheafData.support_comap] at hs
  change (chartGenericMap k M χ hχ.1 x ∈
    ((genericPoint k M p hp.1).ker.support : Set (genericScheme k M))) ↔ _ at hs
  rw [Scheme.Hom.support_ker, (genericPoint k M p hp.1).isClosedEmbedding.isClosed_range.closure_eq] at hs
  change (chartGenericMap k M χ hχ.1 x ∈ Set.range (genericPoint k M p hp.1)) ↔ _ at hs
  rw [← hs]
  constructor
  · intro hx
    exact ⟨_, hx.symm⟩
  · rintro ⟨z, hz⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint (LaurentSeries k))] at hz
    exact hz.symm

open ArithmeticThetaLocalOrdersR0066

lemma section_mem_iff_eq (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1)
    (side : Bool) (a : k) (ha : a ≠ 0) :
    sectionEquation k side a ∈ P ↔ P = sectionIdeal k side a := by
  letI : (sectionIdeal k side a).IsPrime := section_prime k side a ha
  have hheight := section_height_one k side a ha (sectionIdeal k side a) rfl
  constructor
  · intro h
    exact (Ideal.eq_of_le_of_height_le (I := sectionIdeal k side a)
      (Ideal.span_le.mpr (by simpa using h)) (by rw [hP, hheight])).symm
  · rintro rfl
    exact Ideal.subset_span (Set.mem_singleton _)

/-- At height one the two boundary equations identify the two adjacent
marked primes, and there are no other primes over this marked section. -/
lemma marked_equation_mem_iff (j i : Fin r) (a : kˣ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (markedEquation k (hr := hr) j i a) ∈ P ↔
      (j = i ∧ P = sectionIdeal k true (a : k)) ∨
      (next r hr j = i ∧ P = sectionIdeal k false ((a⁻¹ : kˣ) : k)) := by
  classical
  have hx := section_mem_iff_eq k P hP true (a : k) a.ne_zero
  have hy := section_mem_iff_eq k P hP false ((a⁻¹ : kˣ) : k) (a⁻¹).ne_zero
  change (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
    (ArithmeticThetaAnnularTorsionPrereqR0053.cx k -
      ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C (a : k))) ∈ P ↔ _) at hx
  change (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
    (ArithmeticThetaAnnularTorsionPrereqR0053.cy k -
      ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C ((a⁻¹ : kˣ) : k))) ∈ P ↔ _) at hy
  unfold markedEquation
  rw [map_mul, Ideal.IsPrime.mul_mem_iff_mem_or_mem (inferInstance : P.IsPrime)]
  split_ifs <;> simp_all only [map_one, Ideal.one_notMem, false_or, or_false,
    true_and, false_and]

instance genericSchemeAlgebra : Algebra (GenericRing k) (genericChartScheme k).functionField :=
  (StructureSheaf.toStalk (GenericRing k)
    (_root_.genericPoint (genericChartScheme k))).hom.toAlgebra

instance genericSchemeFractionRing :
    IsFractionRing (GenericRing k) (genericChartScheme k).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (GenericRing k))

def chartFieldEquiv : ChartField k ≃ₐ[GenericRing k] (genericChartScheme k).functionField :=
  FractionRing.algEquiv (GenericRing k) (genericChartScheme k).functionField

lemma chartFieldEquiv_square :
    Spec.map (CommRingCat.ofHom (chartFieldEquiv k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ArithmeticThetaLocalOrdersR0066.toFunctionField k)) =
    (genericChartScheme k).fromSpecStalk (_root_.genericPoint (genericChartScheme k)) := by
  rw [← Spec.map_comp, Spec.fromSpecStalk_eq']
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (chartFieldEquiv k).commutes a

lemma generic_field_map (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ) :
    ArithmeticThetaGeometricNormR0150.IsFieldMap (chartGenericMap k M χ hχ)
      ((chartFieldEquiv k).toRingHom.comp φ) := by
  change _ = Spec.map (CommRingCat.ofHom φ ≫
    CommRingCat.ofHom (chartFieldEquiv k).toRingHom) ≫ _
  rw [Spec.map_comp, Category.assoc, field_square k M χ hχ φ hφ,
    ← Category.assoc, chartFieldEquiv_square]

/-- A geometric field map gives injective maps on all stalks. -/
lemma stalk_injective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (α : Y.functionField →+* X.functionField)
    (hα : ArithmeticThetaGeometricNormR0150.IsFieldMap f α) (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply α.injective
  have hs := DFunLike.congr_fun
    (ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.stalk_field_square f α hα x)
  simp only [RingHom.comp_apply] at hs
  rw [← hs a, ← hs b, hab]

/-- Flatness is proved from the actual field map and the DVR stalks of the
smooth curve. It is not added to the annular hypotheses. -/
lemma flat_to_smooth_curve {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (F : Type u) [Field F]
    (p : Y ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 p]
    (f : X ⟶ Y) (α : Y.functionField →+* X.functionField)
    (hα : ArithmeticThetaGeometricNormR0150.IsFieldMap f α) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  letI := (f.stalkMap x).hom.toAlgebra
  rw [← (f.stalkMap x).hom.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
  by_cases hx : f x = _root_.genericPoint Y
  · have hf : IsField (Y.presheaf.stalk (f x)) := by
      rw [hx]
      exact Field.toIsField Y.functionField
    letI := hf.toField
    infer_instance
  · letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed p (f x)
      (ArithmeticThetaGeometricNormR0150.NormOrders.smooth_closed_of_ne_generic F p (f x) hx)
    letI : Module.IsTorsionFree (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (stalk_injective f α hα x)
    infer_instance

/-- The ideal of a closed field-valued point becomes the maximal ideal at
its actual stalk. The proof retains the canonical factorization of the point. -/
lemma point_stalk_ideal {Y : Scheme.{u}} (F : Type u) [Field F]
    (e : Spec (.of F) ⟶ Y) [IsClosedImmersion e] :
    specIdeal (e.ker.comap (Y.fromSpecStalk (e (IsLocalRing.closedPoint F)))) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (e (IsLocalRing.closedPoint F))) := by
  have h : IsPullback (Spec.map (Scheme.stalkClosedPointTo e)) (𝟙 _)
      (Y.fromSpecStalk (e (IsLocalRing.closedPoint F))) e :=
    IsPullback.of_vert_isIso_mono ⟨by
      rw [Category.id_comp]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk e⟩
  rw [AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange h]
  change specIdeal ((Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo e).hom)).ker) = _
  change Ideal.map _ _ = _
  rw [ArithmeticThetaPolygonCartierR0133.GlobalMarkedIdealChartsR0133.spec_kernel]
  rw [RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot (R := F),
    IsLocalRing.maximalIdeal_comap]

/-- The residue ideal transported by the stalk map is exactly the stalk of
the pulled-back point ideal. -/
lemma pullback_point_stalk_ideal {X Y : Scheme.{u}} (F : Type u) [Field F]
    (e : Spec (.of F) ⟶ Y) [IsClosedImmersion e] (f : X ⟶ Y)
    (x : X) (hx : f x = e (IsLocalRing.closedPoint F)) :
    specIdeal ((e.ker.comap f).comap (X.fromSpecStalk x)) =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    Scheme.IdealSheafData.comap_comp]
  change specIdeal (((e.ker.comap (Y.fromSpecStalk (f x))).comap
    (Spec.map (CommRingCat.ofHom (f.stalkMap x).hom)))) = _
  rw [specIdeal_comap]
  congr 1
  rw [hx]
  exact point_stalk_ideal F e

lemma mapped_maximal_of_point_ideal {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (F : Type u) [Field F]
    (e : Spec (.of F) ⟶ Y) [IsClosedImmersion e]
    (f : Spec (.of R) ⟶ Y) (x : Spec (.of R))
    (hx : f x = e (IsLocalRing.closedPoint F))
    (hI : specIdeal (e.ker.comap f) = x.asIdeal) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal ((Spec (.of R)).presheaf.stalk x) := by
  rw [← pullback_point_stalk_ideal F e f x hx, Spec.fromSpecStalk_eq']
  change specIdeal ((e.ker.comap f).comap
    (Spec.map (CommRingCat.ofHom (StructureSheaf.toStalk R x).hom))) = _
  rw [specIdeal_comap, hI]
  letI : Algebra R ((Spec (.of R)).presheaf.stalk x) :=
    (StructureSheaf.toStalk R x).hom.toAlgebra
  letI : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal
    ((Spec (.of R)).presheaf.stalk x)

lemma generic_marked_ideal_eq_prime (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i j : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1)
    (hx : chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩ =
      genericPoint k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k))) :
    specIdeal ((genericPoint k M p hp.1).ker.comap (chartGenericMap k M χ hχ.1)) = P := by
  classical
  have hm := (generic_marked_point_iff k h3 M hM i j a p hp χ hχ ⟨P, inferInstance⟩).mp hx
  obtain ⟨hj, he⟩ | ⟨hj, he⟩ := (marked_equation_mem_iff k j i a P hP).mp hm
  · subst i
    rw [generic_marked_ideal k h3 M hM j j a p hp χ hχ]
    simp only [markedEquation, ite_true,
      if_neg (CompletedMarkedChartIdealR0152.next_ne hr h3 j), mul_one]
    exact he.symm
  · have hn : j ≠ i := by
      intro heq
      exact CompletedMarkedChartIdealR0152.next_ne hr h3 j (hj.trans heq.symm)
    rw [generic_marked_ideal k h3 M hM i j a p hp χ hχ]
    simp only [markedEquation, if_neg hn, if_pos hj, one_mul]
    exact he.symm

lemma generic_chart_stalk_dvr (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing ((genericChartScheme k).presheaf.stalk ⟨P, inferInstance⟩) := by
  letI := height_one_dvr k P hP
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (Spec.stalkIso (.of (GenericRing k)) ⟨P, inferInstance⟩).symm.commRingCatIsoToRingEquiv

/-- At every prime over a marked section the actual stalk fiber has length one. -/
lemma marked_fiber_length (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i j : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1)
    (hx : chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩ =
      genericPoint k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k))) :
    ArithmeticThetaDegreeAssembly.stalkFiberLength (chartGenericMap k M χ hχ.1)
      ⟨P, inferInstance⟩ = 1 := by
  letI : IsClosedImmersion (genericPoint k M p hp.1) := genericPoint_closed k M hM p hp.1
  letI := generic_chart_stalk_dvr k P hP
  have he := mapped_maximal_of_point_ideal (LaurentSeries k) (genericPoint k M p hp.1)
    (chartGenericMap k M χ hχ.1) ⟨P, inferInstance⟩ hx
    (generic_marked_ideal_eq_prime k h3 M hM i j a p hp χ hχ P hP hx)
  unfold ArithmeticThetaDegreeAssembly.stalkFiberLength
  rw [he, ← pow_one (IsLocalRing.maximalIdeal
    ((genericChartScheme k).presheaf.stalk ⟨P, inferInstance⟩)),
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  rfl

lemma addVal_equiv {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (e : A ≃+* B) (a : A) :
    IsDiscreteValuationRing.addVal B (e a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hπ' : Irreducible (e π) := hπ.map e.toMulEquiv
  have hu : IsDiscreteValuationRing.addVal B (e (v : A)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (v.isUnit.map e.toRingHom)
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_mul,
    hu,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr v.isUnit,
    hπ.addVal_pow, hπ'.addVal_pow]

lemma exactOrder_of_addVal (P : Ideal (GenericRing k)) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] (a : GenericRing k) (n : ℕ)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P)
      (algebraMap (GenericRing k) (Localization.AtPrime P) a) = n) :
    ExactOrder k P a n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  unfold ExactOrder
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  simp only [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow, h]
  simp
  exact_mod_cast Nat.lt_succ_self n

lemma stalk_scalar_square (x : genericChartScheme k) (a : GenericRing k) :
    algebraMap ((genericChartScheme k).presheaf.stalk x) (genericChartScheme k).functionField
      (StructureSheaf.toStalk (GenericRing k) x a) =
    algebraMap (GenericRing k) (genericChartScheme k).functionField a := by
  exact ConcreteCategory.congr_hom
    (StructureSheaf.toStalk_stalkSpecializes (_root_.genericPoint_specializes x)) a

/-- The concrete ideal-power notion of order agrees with the order on the
spectrum of the actual generic chart, through its canonical fraction field. -/
lemma hasOrder_scheme_ord (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1)
    (f : ChartField k) (hf : f ≠ 0) :
    HasOrder k P f
      (Scheme.ord (chartFieldEquiv k f) (⟨P, inferInstance⟩ : genericChartScheme k)) := by
  let x : genericChartScheme k := ⟨P, inferInstance⟩
  letI := height_one_dvr k P hP
  letI := generic_chart_stalk_dvr k P hP
  have hx : Order.coheight x = 1 := by
    rw [← idealHeight_eq_coheight (.of (GenericRing k)) x]
    exact hP
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective (GenericRing k) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hab : f * toFunctionField k b = toFunctionField k a := by
    rw [← he]
    exact div_mul_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0)
  have ha0 : a ≠ 0 := by
    intro ha
    apply hf
    rw [← he, ha, map_zero, zero_div]
  have hnonzero (v : GenericRing k) (hv : v ≠ 0) :
      algebraMap (GenericRing k) (Localization.AtPrime P) v ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime P)
      P.primeCompl_le_nonZeroDivisors)).mpr hv
  obtain ⟨na, hna⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hnonzero a ha0))
  obtain ⟨nb, hnb⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hnonzero b hb0))
  refine ⟨a, b, na, nb, hb0, hab, exactOrder_of_addVal k P a na hna.symm,
    exactOrder_of_addVal k P b nb hnb.symm, ?_⟩
  letI : Algebra (GenericRing k) ((genericChartScheme k).presheaf.stalk x) :=
    (StructureSheaf.toStalk (GenericRing k) x).hom.toAlgebra
  let e : ((genericChartScheme k).presheaf.stalk x) ≃ₐ[GenericRing k] Localization.AtPrime P :=
    (StructureSheaf.stalkIso (GenericRing k) x).symm
  have hval (v : GenericRing k) :
      Ring.ord ((genericChartScheme k).presheaf.stalk x)
        (StructureSheaf.toStalk (GenericRing k) x v) =
      IsDiscreteValuationRing.addVal (Localization.AtPrime P)
        (algebraMap (GenericRing k) (Localization.AtPrime P) v) := by
    rw [Ring.ord_eq_addVal, ← addVal_equiv e.toRingEquiv]
    exact congrArg (IsDiscreteValuationRing.addVal (Localization.AtPrime P)) (e.commutes v)
  have hsnonzero (v : GenericRing k) (hv : v ≠ 0) :
      StructureSheaf.toStalk (GenericRing k) x v ≠ 0 := by
    intro hh
    have hh' := e.commutes v
    rw [show e (algebraMap (GenericRing k) ((genericChartScheme k).presheaf.stalk x) v) = 0 by
      change e (StructureSheaf.toStalk (GenericRing k) x v) = 0
      rw [hh, map_zero]] at hh'
    exact hnonzero v hv hh'.symm
  have hfrac : (chartFieldEquiv k f) *
      algebraMap ((genericChartScheme k).presheaf.stalk x) (genericChartScheme k).functionField
        (StructureSheaf.toStalk (GenericRing k) x b) =
      algebraMap ((genericChartScheme k).presheaf.stalk x) (genericChartScheme k).functionField
        (StructureSheaf.toStalk (GenericRing k) x a) := by
    rw [stalk_scalar_square, stalk_scalar_square,
      ← (chartFieldEquiv k).commutes b, ← (chartFieldEquiv k).commutes a, ← map_mul]
    exact congrArg (chartFieldEquiv k) hab
  have ho := ArithmeticThetaCurveDegree.principalOrder_eq_sub_lengths
    (genericChartScheme k) x hx (chartFieldEquiv k f)
    ((map_ne_zero_iff _ (chartFieldEquiv k).injective).mpr hf)
    (StructureSheaf.toStalk (GenericRing k) x a) (StructureSheaf.toStalk (GenericRing k) x b)
    (hsnonzero a ha0) (hsnonzero b hb0) hfrac
  change Scheme.ord (chartFieldEquiv k f) x =
    ((Ring.ord ((genericChartScheme k).presheaf.stalk x)
      (StructureSheaf.toStalk (GenericRing k) x a)).toNat : ℤ) -
    ((Ring.ord ((genericChartScheme k).presheaf.stalk x)
      (StructureSheaf.toStalk (GenericRing k) x b)).toNat : ℤ) at ho
  rw [hval a, hval b, ← hna, ← hnb] at ho
  exact ho.symm

lemma support_inf {X : Scheme.{u}} (I J : X.IdealSheafData) :
    (I ⊓ J).support = I.support ⊔ J.support := by
  rw [← Scheme.IdealSheafData.support_radical (I ⊓ J),
    Scheme.IdealSheafData.radical_inf, ← Scheme.IdealSheafData.radical_mul,
    Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.support_mul]

lemma mem_support_iInf {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (I : ι → X.IdealSheafData) (x : X) :
    x ∈ (⨅ i, I i).support ↔ ∃ i, x ∈ (I i).support := by
  have hs {s : Set ι} (hs : s.Finite) :
      x ∈ ((⨅ i ∈ s, I i).support : Set X) ↔ ∃ i ∈ s, x ∈ (I i).support := by
    refine hs.induction_on _ (by simp) fun {i s} hi hs ih => ?_
    rw [show (⨅ j ∈ insert i s, I j) = I i ⊓ ⨅ j ∈ s, I j by
      simp only [Set.mem_insert_iff, iInf_or, iInf_inf_eq, iInf_iInf_eq_left], support_inf]
    simp only [TopologicalSpace.Closeds.coe_sup, Set.mem_union, ih,
      Set.mem_insert_iff, exists_eq_or_imp]
    rfl
  simpa using hs (s := Set.univ) Set.finite_univ

lemma mem_point_support {Y : Scheme.{u}} (F : Type u) [Field F]
    (e : Spec (.of F) ⟶ Y) [IsClosedImmersion e] (y : Y) :
    y ∈ e.ker.support ↔ y = e (IsLocalRing.closedPoint F) := by
  change y ∈ (e.ker.support : Set Y) ↔ _
  rw [Scheme.Hom.support_ker, e.isClosedEmbedding.isClosed_range.closure_eq]
  constructor
  · rintro ⟨z, hz⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint F)] at hz
    exact hz.symm
  · intro h
    exact ⟨_, h.symm⟩

open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151

lemma splitKernel_points {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (M : Model k T) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (G : Law k M)
    (p : Fin c × Fin c → (baseScheme k ⟶ M.X)) (hp : ∀ ab, p ab ≫ M.p = 𝟙 _)
    (h : SplitKernel k M s hs G p hp) (y : genericScheme k M) :
    multiplication k M G c y = identityPoint k M s hs ↔
      ∃ ab, y = genericPoint k M (p ab) (hp ab) (IsLocalRing.closedPoint (LaurentSeries k)) := by
  letI := genericPoint_closed k M hM s hs
  letI (ab : Fin c × Fin c) := genericPoint_closed k M hM (p ab) (hp ab)
  unfold identityPoint
  rw [← mem_point_support (LaurentSeries k) (genericPoint k M s hs)]
  change multiplication k M G c y ∈ (genericPoint k M s hs).ker.support ↔ _
  have hpre : multiplication k M G c y ∈ (genericPoint k M s hs).ker.support ↔
      y ∈ ((genericPoint k M s hs).ker.comap (multiplication k M G c)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  rw [hpre, show (genericPoint k M s hs).ker.comap (multiplication k M G c) =
      ⨅ ab, (genericPoint k M (p ab) (hp ab)).ker from h, mem_support_iInf]
  exact exists_congr (fun ab => mem_point_support (LaurentSeries k)
    (genericPoint k M (p ab) (hp ab)) y)

/-- All local orders of the geometric pullback agree with the source divisor.
The generic-image case, marked points, and all other closed points are explicit. -/
lemma scheme_order_pullback {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (h3 : 3 ≤ 2*c) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex (2*c) hr) 1 s)
    (G : Law k M) [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (ζ : kˣ) (p : Fin c × Fin c → (baseScheme k ⟶ M.X))
    (hp : ∀ ab, MarkedLift k M (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) (p ab))
    (hker : SplitKernel k M s hs.1 G p (fun ab => (hp ab).1))
    (j : Fin (2*c)) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (g : (genericScheme k M).functionField) (hg : HasKatoDivisor k M s hs.1 G c g)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    Scheme.ord (chartFieldEquiv k (φ g)) (⟨P, inferInstance⟩ : genericChartScheme k) =
      katoOrder k M s hs.1 G c (chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩) := by
  let f : genericChartScheme k ⟶ genericScheme k M := chartGenericMap k M χ hχ.1
  let α := (chartFieldEquiv k).toRingHom.comp φ
  have hα := generic_field_map k M χ hχ.1 φ hφ
  let x : genericChartScheme k := ⟨P, inferInstance⟩
  let q : genericScheme k M ⟶ Spec (.of (LaurentSeries k)) := genericStructure k M
  letI : SmoothOfRelativeDimension 1 q := generic_relative_one k h3 M hM s hs
  letI : Flat f := flat_to_smooth_curve (X := genericChartScheme k) (Y := genericScheme k M)
    (LaurentSeries k) q f α hα
  have hx : Order.coheight x = 1 := by
    rw [← idealHeight_eq_coheight (.of (GenericRing k)) x]
    exact hP
  change Scheme.ord (α g) x = katoOrder k M s hs.1 G c (f x)
  rw [← hg.2 (f x)]
  by_cases hy : f x = _root_.genericPoint (genericScheme k M)
  · rw [DivisorFieldBaseChange.ord_map_above_generic f α hα x hy g hg.1,
      hy, NormOrders.ord_generic]
  · rw [DivisorFieldBaseChange.ord_map_flat f α hα x hx
      (NormOrders.smooth_coheight_one_of_ne_generic (X := genericScheme k M)
        (LaurentSeries k) q (f x) hy) g hg.1]
    by_cases hi : f x = identityPoint k M s hs.1
    · rw [marked_fiber_length k h3 M hM (zeroIndex (2*c) hr) j 1 s hs χ hχ P hP hi]
      simp
    · by_cases ht : multiplication k M G c (f x) = identityPoint k M s hs.1
      · obtain ⟨ab, hab⟩ := (splitKernel_points k M hM s hs.1 G p
          (fun ab => (hp ab).1) hker (f x)).mp ht
        rw [marked_fiber_length k h3 M hM (torsionIndex (r := 2*c) c ab.1) j
          (ζ ^ ab.2.val) (p ab) (hp ab) χ hχ P hP hab]
        simp
      · rw [hg.2]
        simp only [katoOrder, if_neg hi, if_neg ht, sub_self, zero_mul]

lemma next_zero_iff {r : ℕ} (hr : 0 < r) (j : Fin r) :
    next r hr j = zeroIndex r hr ↔ j.val + 1 = r := by
  change (⟨(j.val+1)%r, _⟩ : Fin r) = ⟨0, _⟩ ↔ _
  rw [Fin.ext_iff]
  change (j.val+1)%r = 0 ↔ j.val+1 = r
  by_cases hj : j.val+1 < r
  · rw [Nat.mod_eq_of_lt hj]
    omega
  · have he : j.val+1 = r := by omega
    rw [he, Nat.mod_self]
    simp

lemma torsionIndex_exists_iff (c : ℕ) (hc : 0 < c) (j : Fin (2*c)) :
    (∃ a : Fin c, j = torsionIndex (r := 2*c) c a) ↔ 2*c ∣ c*j.val := by
  conv_rhs => lhs; rw [Nat.mul_comm 2 c]
  rw [Nat.mul_dvd_mul_iff_left hc]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, rfl⟩
  · rintro ⟨a, ha⟩
    have hab : a < c := by have := j.isLt; omega
    exact ⟨⟨a, hab⟩, Fin.ext ha⟩

lemma next_torsionIndex_exists_iff (c : ℕ) (hc : 0 < c) (hr : 0 < 2*c)
    (j : Fin (2*c)) :
    (∃ a : Fin c, next (2*c) hr j = torsionIndex (r := 2*c) c a) ↔
      2*c ∣ c*(j.val+1) := by
  rw [torsionIndex_exists_iff c hc]
  change 2*c ∣ c*((j.val+1)%(2*c)) ↔ _
  by_cases hj : j.val+1 < 2*c
  · rw [Nat.mod_eq_of_lt hj]
  · have he : j.val+1 = 2*c := by omega
    rw [he, Nat.mod_self]
    simp

lemma inverse_power_is_power (c : ℕ) (hc : 0 < c) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) c) (b : Fin c) :
    ∃ b' : Fin c, ((ζ ^ b.val)⁻¹ : kˣ).val = (ζ : k) ^ b'.val := by
  letI : NeZero c := ⟨by omega⟩
  have hh : (((ζ : k) ^ b.val)⁻¹) ^ c = 1 := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm b.val c, pow_mul, hζ.pow_eq_one, one_pow, inv_one]
  obtain ⟨n, hn, he⟩ := hζ.eq_pow_of_pow_eq_one hh
  exact ⟨⟨n, hn⟩, by simpa using he.symm⟩

lemma inverse_power_surjective (c : ℕ) (hc : 0 < c) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) c) (b : Fin c) :
    ∃ b' : Fin c, ((ζ ^ b'.val)⁻¹ : kˣ).val = (ζ : k) ^ b.val := by
  obtain ⟨b', hb'⟩ := inverse_power_is_power k c hc ζ hζ b
  refine ⟨b', ?_⟩
  have hh := congrArg (fun a : k => a⁻¹) hb'
  simpa using hh.symm

lemma chart_identity_iff {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (h3 : 3 ≤ 2*c) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex (2*c) hr) 1 s)
    (j : Fin (2*c)) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩ = identityPoint k M s hs.1 ↔
      IsIdentityPrime k c j.val P := by
  have hh := (generic_marked_point_iff k h3 M hM (zeroIndex (2*c) hr) j 1 s hs χ hχ
    ⟨P, inferInstance⟩).trans
    (marked_equation_mem_iff k j (zeroIndex (2*c) hr) 1 P hP)
  have hj : j = zeroIndex (2*c) hr ↔ j.val = 0 := Fin.ext_iff
  simpa only [identityPoint, IsIdentityPrime, hj, next_zero_iff, inv_one, Units.val_one] using hh

lemma chart_torsion_iff {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (hc : 0 < c) (h3 : 3 ≤ 2*c) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (G : Law k M)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c)
    (p : Fin c × Fin c → (baseScheme k ⟶ M.X))
    (hp : ∀ ab, MarkedLift k M (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) (p ab))
    (hker : SplitKernel k M s hs G p (fun ab => (hp ab).1))
    (j : Fin (2*c)) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    multiplication k M G c (chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩) =
      identityPoint k M s hs ↔ IsTorsionPrime k c j.val (ζ : k) P := by
  rw [splitKernel_points k M hM s hs G p (fun ab => (hp ab).1) hker]
  have hmark (ab : Fin c × Fin c) :=
    (generic_marked_point_iff k h3 M hM (torsionIndex (r := 2*c) c ab.1) j
      (ζ ^ ab.2.val) (p ab) (hp ab) χ hχ ⟨P, inferInstance⟩).trans
      (marked_equation_mem_iff k j (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) P hP)
  constructor
  · rintro ⟨ab, hab⟩
    obtain ⟨hj, he⟩ | ⟨hj, he⟩ := (hmark ab).mp hab
    · exact ⟨true, ab.2, (torsionIndex_exists_iff c hc j).mp ⟨ab.1, hj⟩,
        by simpa only [Units.val_pow_eq_pow_val] using he⟩
    · obtain ⟨b, hb⟩ := inverse_power_is_power k c hc ζ hζ ab.2
      refine ⟨false, b, (next_torsionIndex_exists_iff c hc hr j).mp ⟨ab.1, hj⟩, ?_⟩
      exact he.trans (congrArg (sectionIdeal k false) hb)
  · rintro ⟨side, b, hj, he⟩
    cases side with
    | true =>
      obtain ⟨a, ha⟩ := (torsionIndex_exists_iff c hc j).mpr hj
      refine ⟨(a,b), (hmark (a,b)).mpr (Or.inl ⟨ha, ?_⟩)⟩
      simpa only [Units.val_pow_eq_pow_val] using he
    | false =>
      obtain ⟨a, ha⟩ := (next_torsionIndex_exists_iff c hc hr j).mpr hj
      obtain ⟨b', hb'⟩ := inverse_power_surjective k c hc ζ hζ b
      exact ⟨(a,b'), (hmark (a,b')).mpr
        (Or.inr ⟨ha, he.trans (congrArg (sectionIdeal k false) hb').symm⟩)⟩

lemma kato_coefficient_eq {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (hc : 0 < c) (h3 : 3 ≤ 2*c) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex (2*c) hr) 1 s)
    (G : Law k M) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c)
    (p : Fin c × Fin c → (baseScheme k ⟶ M.X))
    (hp : ∀ ab, MarkedLift k M (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val) (p ab))
    (hker : SplitKernel k M s hs.1 G p (fun ab => (hp ab).1))
    (j : Fin (2*c)) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ)
    (P : Ideal (GenericRing k)) [P.IsPrime] (hP : P.height = 1) :
    katoOrder k M s hs.1 G c (chartGenericMap k M χ hχ.1 ⟨P, inferInstance⟩) =
      divisorCoefficient k c j.val (ζ : k) P := by
  classical
  simp only [katoOrder, chart_identity_iff k h3 M hM s hs j χ hχ P hP,
    chart_torsion_iff k hc h3 M hM s hs.1 G ζ hζ p hp hker j χ hχ P hP,
    divisorCoefficient, numeratorOrder, denominatorOrder]
  split_ifs <;> simp

end ArithmeticThetaKatoAnnularR0152.AnnularDivisor

#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.generic_marked_ideal
#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.field_square


#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.flat_to_smooth_curve
#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.marked_equation_mem_iff

#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.pullback_point_stalk_ideal

#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.marked_fiber_length

#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.hasOrder_scheme_ord

#print axioms ArithmeticThetaKatoAnnularR0152.AnnularDivisor.scheme_order_pullback

namespace ArithmeticThetaKatoAnnularR0152
open AnnularDivisor
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaAlgebraizedMarkedLineR0136

/-- The actual Kato principal divisor on every completed annular chart. -/
theorem kato_annular_divisor :
∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin (2*c) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin (2*c) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∀ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c g → ∀ (j : Fin (2*c)) (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k)) [P.IsPrime], P.height = 1 → ArithmeticThetaLocalOrdersR0066.HasOrder k P (φ j g) (ArithmeticThetaLocalOrdersR0066.divisorCoefficient k c j.val (ζ : k) P) := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ g hg j P _ hP
  classical
  let p := fun ab : Fin c × Fin c => Classical.choose
    (marked_section_algebraization k (2*c) hr h3 T M hM
      (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val))
  have hp : ∀ ab, MarkedLift k M (torsionIndex (r := 2*c) c ab.1)
      (ζ ^ ab.2.val) (p ab) := fun ab => (Classical.choose_spec
    (marked_section_algebraization k (2*c) hr h3 T M hM
      (torsionIndex (r := 2*c) c ab.1) (ζ ^ ab.2.val))).1
  have hker := actual_split_torsion_kernel k c hc hcop hr h3 T M hM s hs G hG ζ hζ p hp
  have ho := scheme_order_pullback k h3 M hM s hs G ζ p hp hker j (χ j) (hχ j)
    (φ j) (hφ j) g hg P hP
  have hh := hasOrder_scheme_ord k P hP (φ j g)
    ((map_ne_zero_iff (φ j) (φ j).injective).mpr hg.1)
  rw [ho, kato_coefficient_eq k (by omega) h3 M hM s hs G ζ hζ p hp hker
    j (χ j) (hχ j) P hP] at hh
  exact hh

end ArithmeticThetaKatoAnnularR0152
#print axioms ArithmeticThetaKatoAnnularR0152.kato_annular_divisor
