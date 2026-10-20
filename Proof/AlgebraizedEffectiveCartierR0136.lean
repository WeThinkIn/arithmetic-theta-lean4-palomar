module

public import AlgebraizedMarkedSmoothnessR0136
public import AlgebraizedSplitMarkedDivisorR0136
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
public import Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
public import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
public import Theorems.Thm_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
namespace AlgebraizedEffectiveCartierR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135

lemma laurent_relative_one (S : Type u) [CommRing S] :
    (LaurentPolynomial.C : S →+* LaurentPolynomial S).IsStandardSmoothOfRelativeDimension 1 := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 S (MvPolynomial PUnit.{1} S) := by
    simpa using P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr.SplitTorusSmoothEngine.isStandardSmoothOfRelativeDimension_mvPolynomial S PUnit.{1}
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 S (Polynomial S) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv S PUnit.{1})
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial S) (LaurentPolynomial S) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := LaurentPolynomial S) Polynomial.X
  have hp := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 S (Polynomial S))
  have hl := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 0).mpr
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial S) (LaurentPolynomial S))
  convert hl.comp hp using 1
  ext z
  simp [LaurentPolynomial.algebraMap_eq_toLaurent]

variable (k : Type u) [Field k] [CharZero k]

lemma raw_relative_one :
    ((algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))).IsStandardSmoothOfRelativeDimension 1 := by
  obtain ⟨e, he, _⟩ := (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
  have hc : e.toRingHom.comp
      ((algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
        (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))) = LaurentPolynomial.C := by
    apply RingHom.ext
    intro z
    change e ((ArithmeticThetaNodeCharts.toXChart k)
      (ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.C z))) = _
    simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using
      RingHom.congr_fun he (MvPolynomial.C z)
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 (PowerSeries k)
      (LaurentPolynomial (PowerSeries k)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp (laurent_relative_one (PowerSeries k))
  let ae : ArithmeticThetaNodeCharts.XChart k ≃ₐ[PowerSeries k]
      LaurentPolynomial (PowerSeries k) := AlgEquiv.ofRingEquiv (R := PowerSeries k)
      (f := e) (by intro z; exact RingHom.congr_fun hc z)
  have ha : Algebra.IsStandardSmoothOfRelativeDimension 1 (PowerSeries k)
      (ArithmeticThetaNodeCharts.XChart k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 ae.symm
  have hf := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr ha
  convert hf using 1

lemma open_relative_one (n : ℕ) : SmoothOfRelativeDimension 1 (rightLeg k n ≫ structureMap k n) := by
  let f : PowerSeries k →+* RawOpen k true :=
    (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)).comp
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
  have hf : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom f)) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (raw_relative_one k))
  have sq := (trunc_isPushout f PowerSeries.X (openParameter k true) rfl n).op.map Scheme.Spec
  let := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have hs := MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) sq.flip hf
  rw [rightLeg, structureMap, ← Spec.map_comp]
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
    ((restriction k n true).comp (base k n))))
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
    (truncMap f PowerSeries.X (openParameter k true) rfl n))) at hs
  have heq : (restriction k n true).comp (base k n) =
      truncMap f PowerSeries.X (openParameter k true) rfl n := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  rw [heq]
  exact hs

/-- The smooth neighborhood has dimension one because its actual special
fiber contains the prescribed Laurent chart through the marked point. -/
lemma section_relative_one {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i a s) :
    ∃ W : M.X.Opens, s (IsLocalRing.closedPoint (PowerSeries k)) ∈ W ∧
      SmoothOfRelativeDimension 1 (W.ι ≫ M.p) := by
  obtain ⟨U, hU, hsm⟩ := algebraized_marked_smoothness k r hr h3 T M hM i a s hs
  let := hsm
  let x : U := ⟨s (IsLocalRing.closedPoint (PowerSeries k)), hU _⟩
  obtain ⟨V, d, hxV, hd⟩ :=
    Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp (U.ι ≫ M.p) x
  let W : M.X.Opens := U.ι ''ᵁ V
  have hxW : s (IsLocalRing.closedPoint (PowerSeries k)) ∈ W := ⟨x, hxV, rfl⟩
  have hWd : SmoothOfRelativeDimension d (W.ι ≫ M.p) := by
    rw [← Scheme.Hom.isoImage_inv_ι U.ι V, Category.assoc]
    let := hd
    have h : SmoothOfRelativeDimension (0 + d)
        ((U.ι.isoImage V).inv ≫ V.ι ≫ U.ι ≫ M.p) := inferInstance
    simpa only [zero_add, Category.assoc] using h
  let Q := M.inclusion 0 ⁻¹ᵁ W
  have sq := (isPullback_morphismRestrict (M.inclusion 0) W).paste_vert (hM.2.2.1 0)
  let := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hQ : SmoothOfRelativeDimension d (Q.ι ≫ (T.atlas 0).p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq hWd
  let j := rightLeg k 0 ≫ (T.atlas 0).chart i
  let : IsOpenImmersion ((T.atlas 0).chart i) := (T.atlas 0).chart_open i
  let : IsOpenImmersion j := inferInstance
  let Ω := j ⁻¹ᵁ Q
  have hj : j ≫ (T.atlas 0).p = rightLeg k 0 ≫ structureMap k 0 := by
    dsimp only [j]
    rw [Category.assoc, (T.atlas 0).chart_over]
  have hΩd : SmoothOfRelativeDimension d (Ω.ι ≫ j ≫ (T.atlas 0).p) := by
    rw [← morphismRestrict_ι_assoc j Q]
    let := hQ
    have h : SmoothOfRelativeDimension (0 + d) ((j ∣_ Q) ≫ Q.ι ≫ (T.atlas 0).p) := inferInstance
    simpa only [zero_add] using h
  have hΩ1 : SmoothOfRelativeDimension 1 (Ω.ι ≫ j ≫ (T.atlas 0).p) := by
    rw [hj]
    let := open_relative_one k 0
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1)
      (Ω.ι ≫ rightLeg k 0 ≫ structureMap k 0))
  obtain ⟨b, hb⟩ := AlgebraizedGenericSmoothnessR0135.closedPoint_in_baseInclusion k
  obtain ⟨v, hv⟩ := SmoothMarkedSections.factor_open k r 0 hr (T.atlas 0) i a
  have hvb : M.inclusion 0 (j (v b)) = s (IsLocalRing.closedPoint (PowerSeries k)) := by
    change (v ≫ j ≫ M.inclusion 0) b = _
    rw [← Category.assoc, hv, ← hs.2 0]
    change s (baseInclusion k 0 b) = _
    rw [hb]
  have : Nonempty Ω := ⟨⟨v b, show M.inclusion 0 (j (v b)) ∈ W from hvb ▸ hxW⟩⟩
  have he : d = 1 :=
    P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd.AlgebraicGeometry.FibreCritPt.SmoothOfRelativeDimension.eq_of_nonempty
      _ hΩd hΩ1
  exact ⟨W, hxW, he ▸ hWd⟩

lemma section_invertible {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i a s) :
    s.ker.IsInvertible := by
  obtain ⟨W, hx, hW⟩ := section_relative_one k h3 M hM i a s hs
  let := hM.1
  let := hW
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens M.p W s hs.1 hx

/-- Pairwise disjoint section supports make their actual kernels comaximal. -/
lemma kernels_comaximal {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (i j : Fin r) (hij : i ≠ j) :
    (s i).ker ⊔ (s j).ker = ⊤ := by
  let := AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM (s i) (hs i).1
  let := AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM (s j) (hs j).1
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_sup]
  apply TopologicalSpace.Closeds.ext
  change ((s i).ker.support : Set M.X) ∩ (s j).ker.support = ∅
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker,
    (s i).isClosedEmbedding.isClosed_range.closure_eq,
    (s j).isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.disjoint_iff_inter_eq_empty.mp
    (AlgebraizedSplitMarkedDivisorR0136.sections_disjoint k M hM a s hs i j hij)

lemma ideal_product_apply {X : Scheme.{u}} {ι : Type*} (q : Finset ι)
    (J : ι → X.IdealSheafData) (U : X.affineOpens) :
    (∏ i ∈ q, J i).ideal U = ∏ i ∈ q, (J i).ideal U := by
  classical
  induction q using Finset.induction with
  | empty => simp
  | insert i q hi ih => simp [Finset.prod_insert, hi, Scheme.IdealSheafData.ideal_mul, ih]

lemma markedIdeal_eq_product {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) :
    markedIdeal k M s = ∏ i, (s i).ker := by
  classical
  apply Scheme.IdealSheafData.ext
  funext U
  rw [markedIdeal, Scheme.IdealSheafData.ideal_iInf, iInf_apply, ideal_product_apply]
  symm
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
    (J := fun i => (s i).ker.ideal U) (by
      intro i _ j _ hij
      apply Ideal.isCoprime_iff_sup_eq.mpr
      have hh := congrArg (fun I : M.X.IdealSheafData => I.ideal U)
        (kernels_comaximal k M hM a s hs i j hij)
      simpa only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply] using hh)
  simpa using h

lemma invertible_product {X : Scheme.{u}} {ι : Type*} (q : Finset ι)
    (J : ι → X.IdealSheafData) (h : ∀ i ∈ q, (J i).IsInvertible) :
    (∏ i ∈ q, J i).IsInvertible := by
  classical
  induction q using Finset.induction with
  | empty => simpa using (Scheme.IdealSheafData.isInvertible_top (X := X))
  | insert i q hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end AlgebraizedEffectiveCartierR0136
/-- The actual marked union on the algebraized model is an effective Cartier ideal. -/
theorem algebraized_effective_cartier :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∀ (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)),
      LiftFamily k M a s →
      ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (markedIdeal k M s) := by
  intro k _ _ r hr h3 T M hM a s hs
  have hI : (markedIdeal k M s).IsInvertible := by
    rw [AlgebraizedEffectiveCartierR0136.markedIdeal_eq_product k M hM a s hs]
    apply AlgebraizedEffectiveCartierR0136.invertible_product
    intro i _
    exact AlgebraizedEffectiveCartierR0136.section_invertible k h3 M hM i (a i) (s i) (hs i)
  intro x
  obtain ⟨U, f, hx, g, hg, hIg⟩ := hI x
  exact ⟨M.X.affineBasicOpen f, hx, g, isRegular_iff_mem_nonZeroDivisors.mpr hg, hIg⟩

end ArithmeticThetaAlgebraizedMarkedLineR0136

#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.algebraized_effective_cartier

