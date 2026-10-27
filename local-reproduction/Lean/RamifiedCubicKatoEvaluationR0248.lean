import PeriodOneNormDefinitionsR0248

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

namespace ArithmeticThetaPeriodOneNormR0248
namespace RamifiedCubicKatoEvaluation
open CategoryTheory AlgebraicGeometry

variable (k : Type) [Field k] [CharZero k]

/-- The structural scalar embedding and the two literal coordinates determine
the entire affine-chart map. -/
theorem chart_evaluation_unique (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    (a b : ChartRing k W →+* Series k)
    (ha : IsChartEvaluation k W r a) (hb : IsChartEvaluation k W r b) : a = b := by
  apply ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.WMLocal.zChart_ringHom_ext W
  · apply RingHom.ext
    intro t
    have h := (ha.1 t).trans (hb.1 t).symm
    simpa only [RingHom.comp_apply,
      ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.chartScalar_apply] using h
  · exact ha.2.1.trans hb.2.1.symm
  · exact ha.2.2.trans hb.2.2.symm

/-- The actual generic-point square upgrades affine-coordinate uniqueness to
uniqueness on the projective function field. -/
theorem evaluation_unique (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    [IsIntegral (Curve k W)]
    (ev ev' : (Curve k W).functionField →+* Series k)
    (he : IsEvaluation k W r ev) (he' : IsEvaluation k W r ev') : ev = ev' := by
  obtain ⟨a, ha, hs⟩ := he
  obtain ⟨b, hb, ht⟩ := he'
  have hab := chart_evaluation_unique k W r a b ha hb
  subst b
  suffices h : CommRingCat.ofHom ev = CommRingCat.ofHom ev' from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono ((Curve k W).fromSpecStalk (genericPoint (Curve k W)))).mp
  exact hs.symm.trans ht

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaGeometricNormR0150 ArithmeticThetaKatoExistenceR0151

section ModelTransport
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k))
variable [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
variable [SmoothOfRelativeDimension 1 (genericStructure k M)]
variable (W : WeierstrassCurve (LaurentSeries k)) [W.IsElliptic]
variable [IsIntegral (Curve k W)] [IsLocallyNoetherian (Curve k W)]
variable (G : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) W)
    (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) W G)
variable (E : genericScheme k M ≅ Curve k W)
    (hE : E.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W =
      genericStructure k M)
    (hO : genericPoint k M s hs ≫ E.hom =
      ArithmeticThetaGeneralEllipticKatoR0168.origin (LaurentSeries k) W)

include hG hO hE

/-- Pull back the given cubic law through the pointed coordinate isomorphism. -/
theorem transported_origin_law :
    ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs (transport E hE G) := by
  constructor
  · intro V t
    apply Subtype.ext
    change (G.one t).val ≫ E.inv = t ≫ genericPoint k M s hs
    rw [hG.1, ← hO]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro V t x y
    change (pointsEquiv E hE t).symm (G.mul t _ _) =
      (pointsEquiv E hE t).symm (G.mul t _ _)
    rw [hG.2]

/-- The full normalized Kato predicate survives the actual pointed isomorphism:
orders are transported at every point and determinant norms at every coprime
multiplication map. -/
theorem kato_to_model
    (α : (Curve k W).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap E.hom α) (c : ℕ)
    (g : (Curve k W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
      (LaurentSeries k) W G c g) :
    ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs (transport E hE G) c (α g) := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : SmoothOfRelativeDimension 1
      (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hb : IsPullback E.hom (genericStructure k M)
      (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W)
      (Spec.map (CommRingCat.ofHom (RingHom.id (LaurentSeries k)))) := by
    simp only [show CommRingCat.ofHom (RingHom.id (LaurentSeries k)) = 𝟙 _ from rfl,
      Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa using hE⟩
  have hN (n : ℕ) : (transport E hE G).schemeNsmul n ≫ E.hom =
      E.hom ≫ G.schemeNsmul n :=
    ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transported_schemeNsmul
      E hE G n
  have ho (x : genericScheme k M) :
      E.hom x = ArithmeticThetaGeneralEllipticKatoR0168.originPoint (LaurentSeries k) W ↔
        x = identityPoint k M s hs := by
    have he : E.hom (identityPoint k M s hs) =
        ArithmeticThetaGeneralEllipticKatoR0168.originPoint (LaurentSeries k) W :=
      congrArg (fun f => f (IsLocalRing.closedPoint (LaurentSeries k))) hO
    rw [← he]
    exact (Scheme.homeoOfIso E).injective.eq_iff
  refine ⟨⟨DivisorFieldBaseChange.map_ne_zero α hg.1.1, ?_⟩, ?_⟩
  · intro x
    rw [DivisorFieldBaseChange.basechange_order
      (X := genericScheme k M) (Y := Curve k W) (LaurentSeries k) (LaurentSeries k)
      (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W)
      (genericStructure k M) (RingHom.id _) E.hom hb α hα g hg.1.1 x, hg.1.2]
    have hm : G.schemeNsmul c (E.hom x) = E.hom ((transport E hE G).schemeNsmul c x) :=
      (congrArg (fun f => f x) (hN c)).symm
    classical
    simp only [ArithmeticThetaGeneralEllipticKatoR0168.katoOrder,
      ArithmeticThetaGeometricNormR0150.katoOrder, hm, ho]
    rfl
  · intro n hn hcn φm hφm
    obtain ⟨hfinite, hetale, hsurj, _, φ, hφ, _⟩ :=
      ArithmeticThetaGeneralEllipticKatoR0168.general_multiplication_degree
        (LaurentSeries k) W G hG n hn
    letI := hfinite
    letI := hetale
    letI := hsurj
    have hcart : IsPullback E.hom ((transport E hE G).schemeNsmul n)
        (G.schemeNsmul n) E.hom := by
      exact ActualKatoFieldBaseChange.endomorphism_cartesian
        (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W)
        (genericStructure k M) E.hom
        (Spec.map (CommRingCat.ofHom (RingHom.id (LaurentSeries k)))) hb
        (G.schemeNsmul n) ((transport E hE G).schemeNsmul n)
        (G.schemeNsmul_over n) ((transport E hE G).schemeNsmul_over n) (hN n)
    have hnorm := geometric_norm_base_change
      (Curve k W) (Curve k W) (genericScheme k M) (genericScheme k M) _ _ _ _ hcart
      φ φm α α hφ hφm hα hα g
    rw [hg.2 n hn hcn φ hφ] at hnorm
    exact hnorm.symm

/-- Specialize the accepted unsplit polygon formula to the transported cubic
function. The same composite field map is used for every integer c. -/
theorem expansion_through_model (h3 : 3 ≤ r) (he : Even r)
    (hM : IsModel k T M) (hsM : MarkedLift k M (zeroIndex r hr) 1 s)
    (α : (Curve k W).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap E.hom α)
    (χ : Fin r → (ArithmeticThetaKatoAnnularR0152.chartScheme k ⟶ M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (φ : Fin r → (genericScheme k M).functionField →+*
      ArithmeticThetaKatoAnnularR0152.ChartField k)
    (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j))
    (v : ArithmeticThetaKatoAnnularR0152.ChartField k →+* Series k)
    (hv : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 v)
    (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (g : (Curve k W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
      (LaurentSeries k) W G c g) :
    ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c 0
      ((v.comp ((φ (zeroIndex r hr)).comp α)) g) := by
  have hL := transported_origin_law k M s hs W G hG E hE hO
  have hgM := kato_to_model k M s hs W G hG E hE hO α hα c g hg
  obtain ⟨f, hf, hu⟩ := ArithmeticThetaUnsplitExpansionR0158.unsplit_kato_full_expansion
    k r c hc hcop hr h3 he T M hM s hsM (transport E hE G) hL χ hχ φ hφ
  obtain ⟨f₀, hf₀, huniq⟩ := actual_kato_function_existence
    k r hr h3 T he M hM s hsM (transport E hE G) hL c hc hcop
  have heq : α g = f := (huniq (α g) hgM).trans (huniq f hf.1).symm
  change ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c 0 (v (φ _ (α g)))
  rw [heq]
  exact hf.2 (zeroIndex r hr) v hv

end ModelTransport

/-- A map from the function field factors through every nonempty affine open.
This supplies the exact generic-point square rather than an abstract extension. -/
theorem factor_generic_chart {X : Scheme} [IsIntegral X]
    {B L : Type} [CommRing B] [Field L]
    (i : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion i]
    [Nonempty (Spec (CommRingCat.of B))] (ev : X.functionField →+* L) :
    ∃ a : B →+* L, Spec.map (CommRingCat.ofHom a) ≫ i =
      Spec.map (CommRingCat.ofHom ev) ≫ X.fromSpecStalk (_root_.genericPoint X) := by
  let f := Spec.map (CommRingCat.ofHom ev) ≫ X.fromSpecStalk (_root_.genericPoint X)
  have hmem (z : Spec (CommRingCat.of L)) : f z ∈ Set.range i := by
    have hpt : f z = _root_.genericPoint X := by
      change X.fromSpecStalk (_root_.genericPoint X)
        ((Spec.map (CommRingCat.ofHom ev)) z) = _
      rw [show (Spec.map (CommRingCat.ofHom ev)) z =
        IsLocalRing.closedPoint X.functionField from Subsingleton.elim _ _]
      exact Scheme.fromSpecStalk_closedPoint
    rw [hpt]
    exact ((_root_.genericPoint_spec X).mem_open_set_iff
      i.isOpenEmbedding.isOpen_range).mpr (by simpa using Set.range_nonempty i)
  let l := IsOpenImmersion.lift i f (by rintro _ ⟨z, rfl⟩; exact hmem z)
  refine ⟨(Spec.preimage l).hom, ?_⟩
  change Spec.map (Spec.preimage l) ≫ i = f
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac i f _

/-- The faithful annular map has exactly the frozen coefficientwise Laurent
scalar map, including negative powers of the parameter. -/
theorem annular_scalars
    (v : ArithmeticThetaKatoAnnularR0152.ChartField k →+* Series k)
    (hv : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 v) :
    v.comp (ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps.laurentInclusion k) =
      baseMap k := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro b
  change v (ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps.laurentInclusion k
    (algebraMap (PowerSeries k) (LaurentSeries k) b)) = _
  rw [ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps.laurentInclusion_base, hv.1]
  apply HahnSeries.ext
  funext n
  change ((PowerSeries.map (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k) b :
    PowerSeries (Coeff k)) : LaurentSeries (Coeff k)).coeff n =
      ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k ((b : LaurentSeries k).coeff n)
  simp only [PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

/-- Concrete geometric constituents of the expansion map. All squares are
specified on the actual model and its pointed cubic isomorphism. -/
structure ModelEvaluation {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) [IsIntegral (genericScheme k M)]
    (W : WeierstrassCurve (LaurentSeries k)) [IsIntegral (Curve k W)]
    (E : genericScheme k M ≅ Curve k W) where
  fieldMap : (Curve k W).functionField →+* (genericScheme k M).functionField
  fieldSquare : IsFieldMap E.hom fieldMap
  charts : Fin r → (ArithmeticThetaKatoAnnularR0152.chartScheme k ⟶ M.X)
  chartSquares : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (charts j)
  chartFields : Fin r → (genericScheme k M).functionField →+*
    ArithmeticThetaKatoAnnularR0152.ChartField k
  chartFieldSquares : ∀ j,
    ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (charts j) (chartFields j)
  annular : ArithmeticThetaKatoAnnularR0152.ChartField k →+* Series k
  annular_spec : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 annular

namespace ModelEvaluation
variable {k} {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable {M : Model k T} [IsIntegral (genericScheme k M)]
variable {W : WeierstrassCurve (LaurentSeries k)} [IsIntegral (Curve k W)]
variable {E : genericScheme k M ≅ Curve k W}

def composite (D : ModelEvaluation k M W E) : (Curve k W).functionField →+* Series k :=
  D.annular.comp ((D.chartFields (zeroIndex r hr)).comp D.fieldMap)

theorem injective (D : ModelEvaluation k M W E) : Function.Injective D.composite :=
  D.composite.injective

/-- The composite really evaluates the same generic point through the chosen
completed annulus, then the specified coordinate isomorphism. -/
theorem generic_square (D : ModelEvaluation k M W E) :
    Spec.map (CommRingCat.ofHom D.composite) ≫
      (Curve k W).fromSpecStalk (_root_.genericPoint (Curve k W)) =
    Spec.map (CommRingCat.ofHom (D.annular.comp (D.chartFields (zeroIndex r hr)))) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) ≫ E.hom := by
  change Spec.map (CommRingCat.ofHom
      ((D.annular.comp (D.chartFields (zeroIndex r hr))).comp D.fieldMap)) ≫ _ = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← D.fieldSquare]

open ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

/-- The composite fixes the prescribed structural embedding of k((t)). -/
theorem scalars (D : ModelEvaluation k M W E)
    (hE : E.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W =
      genericStructure k M) :
    D.composite.comp (scalarHom (LaurentSeries k)
      (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W)) = baseMap k := by
  have hs : D.fieldMap.comp (scalarHom (LaurentSeries k)
      (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W)) =
      scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) := by
    suffices h : CommRingCat.ofHom (D.fieldMap.comp (scalarHom (LaurentSeries k)
        (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W))) =
        CommRingCat.ofHom (scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)) from
      congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, scalarHom_square, ← Category.assoc,
      ← D.fieldSquare, Category.assoc, hE, scalarHom_square]
  apply RingHom.ext
  intro b
  change D.annular (D.chartFields (zeroIndex r hr) (D.fieldMap (scalarHom (X := Curve k W) (LaurentSeries k)
    (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W) b))) = _
  have hsb := RingHom.congr_fun hs b
  simp only [RingHom.comp_apply] at hsb
  rw [hsb]
  rw [scalarHom_apply, fieldMap_scalar k M (D.charts (zeroIndex r hr))
    (D.chartSquares (zeroIndex r hr)).1 (D.chartFields (zeroIndex r hr))
    (D.chartFieldSquares (zeroIndex r hr))]
  exact RingHom.congr_fun (annular_scalars k D.annular D.annular_spec) b

/-- Every affine factor of the constructed generic map automatically has the
correct scalar action. Only its two coordinate values require further work. -/
theorem chart_scalars (D : ModelEvaluation k M W E)
    (hE : E.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W =
      genericStructure k M)
    (a : ChartRing k W →+* Series k)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W =
      Spec.map (CommRingCat.ofHom D.composite) ≫
        (Curve k W).fromSpecStalk (_root_.genericPoint (Curve k W))) :
    ∀ b, a (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W b) =
      baseMap k b := by
  have h : a.comp (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W) =
      baseMap k := by
    suffices h : CommRingCat.ofHom
        (a.comp (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W)) =
        CommRingCat.ofHom (baseMap k) from congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hc : Spec.map (CommRingCat.ofHom
        (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W)) =
        chartInclusion k W ≫
          ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W :=
      Spec.map_preimage _
    rw [hc, ← Category.assoc, ha, Category.assoc, ← scalarHom_square,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.scalars hE]
  exact fun b => RingHom.congr_fun h b

/-- The entire Kato expansion, for every law and every allowed c, uses this
one composite. No divisibility of r by c is required. -/
theorem expansion [IsLocallyNoetherian (genericScheme k M)]
    [SmoothOfRelativeDimension 1 (genericStructure k M)] [W.IsElliptic]
    [IsLocallyNoetherian (Curve k W)]
    (D : ModelEvaluation k M W E) (h3 : 3 ≤ r) (he : Even r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (hE : E.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.structureMap (LaurentSeries k) W =
      genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom =
      ArithmeticThetaGeneralEllipticKatoR0168.origin (LaurentSeries k) W)
    (G : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) W)
    (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) W G)
    (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (g : (Curve k W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
      (LaurentSeries k) W G c g) :
    ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c 0 (D.composite g) :=
  expansion_through_model k M s hs.1 W G hG E hE hO h3 he hM hs
    D.fieldMap D.fieldSquare D.charts D.chartSquares D.chartFields D.chartFieldSquares
    D.annular D.annular_spec c hc hcop g hg

end ModelEvaluation

/-- Construct all maps used in the expansion from the accepted geometric
providers. This construction is independent of c and of the group law. -/
theorem model_evaluation_exists {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    [IsIntegral (genericScheme k M)]
    (W : WeierstrassCurve (LaurentSeries k)) [IsIntegral (Curve k W)]
    (E : genericScheme k M ≅ Curve k W) : Nonempty (ModelEvaluation k M W E) := by
  obtain ⟨α, hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  have hcharts : ∀ j : Fin r, ∃ χ, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j χ := by
    intro j
    obtain ⟨χ, hχ, _⟩ := ArithmeticThetaKatoAnnularR0152.completed_model_chart_maps
      k r hr h3 T M hM j
    exact ⟨χ, hχ⟩
  choose χ hχ using hcharts
  have hfields : ∀ j : Fin r, ∃ φ, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) φ := by
    intro j
    obtain ⟨φ, hφ, _⟩ := ArithmeticThetaKatoAnnularR0152.completed_chart_field_maps
      k r hr h3 T M hM j (χ j) (hχ j)
    exact ⟨φ, hφ.1⟩
  choose φ hφ using hfields
  obtain ⟨v, hv, _⟩ := ArithmeticThetaAnnularNormBridgeR0156.faithful_annular_evaluation
    k 1 1 (by decide)
  exact ⟨⟨α, hα, χ, hχ, φ, hφ, v, hv.1⟩⟩

/-- On the completed chart, the field evaluation agrees with the continuous
power-series evaluation used by the finite-stage coordinate realizations. -/
theorem annular_on_chart
    (v : ArithmeticThetaKatoAnnularR0152.ChartField k →+* Series k)
    (hv : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 v)
    (b : ArithmeticThetaKatoAnnularR0152.Chart k) :
    v (ArithmeticThetaKatoAnnularR0152.chartToField k b) =
      HahnSeries.ofPowerSeries ℤ (Coeff k)
        (ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation k 1 1 b) := by
  let f : ArithmeticThetaKatoAnnularR0152.Chart k →+* Series k :=
    (HahnSeries.ofPowerSeries ℤ (Coeff k)).comp
      (ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation k 1 1)
  have hf : Function.Injective f := HahnSeries.ofPowerSeries_injective.comp
    (ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation_injective
      k 1 1 (by decide))
  obtain ⟨v₀, hv₀⟩ := ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.field_extension
    k f hf
  have hspec : ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 v₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c
      rw [hv₀]
      change HahnSeries.ofPowerSeries ℤ (Coeff k)
        (ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation k 1 1 _) = _
      rw [ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation_base]
      rfl
    · rw [hv₀]
      simp [f, ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation_x]
    · rw [hv₀]
      simp [f, ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation_y,
        ArithmeticThetaLaurentNormR0064.t, HahnSeries.ofPowerSeries_X]
    · intro N c hc e he
      rw [hv₀]
      have h := ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation_filtered
        k 1 1 N c hc
      change _ ∈ (Ideal.span {PowerSeries.X}) ^ N at h
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h
      change (HahnSeries.ofPowerSeries ℤ (Coeff k)
        (ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.chartEvaluation k 1 1 c)).coeff e = 0
      by_cases hneg : e < 0
      · simp [PowerSeries.coeff_coe, hneg]
      · simpa [PowerSeries.coeff_coe, hneg] using h e.natAbs (by omega)
  have heq := ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation.evaluation_unique
    k 1 1 v v₀ hv hspec
  rw [heq, hv₀]
  rfl

namespace CoordinateCompletion

open ArithmeticThetaScaledTateBridgeR0046

/-- Maps into a nilpotent parameter quotient are determined on the dense node
polynomials. The proof uses the actual completed-node approximation theorem. -/
theorem completed_hom_ext {B : Type} [CommRing B] (n : ℕ)
    (f g : ArithmeticThetaKatoAnnularR0152.Chart k →+* B)
    (hnode : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) = g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k))
    (hf : f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0)
    (hg : g (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0) : f = g := by
  have hparam : completedParameter k 1 = ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
    simp [completedParameter, t, ArithmeticThetaScaledTateBridgeR0046.parameter, ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaScaledAnnularR0050.tau, completedBaseMap]
  have hkill (q : ArithmeticThetaKatoAnnularR0152.Chart k →+* B)
      (hq : q (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0)
      (z : ArithmeticThetaKatoAnnularR0152.Chart k) (hz : z ∈ completedPower k 1 (n+1)) : q z = 0 := by
    have hm := Ideal.mem_map_of_mem q hz
    rw [completedPower, hparam, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm
    simpa only [Ideal.span_singleton_pow, hq, Ideal.span_singleton_zero, Ideal.mem_bot] using hm
  apply RingHom.ext
  intro z
  obtain ⟨p, hp⟩ := (completion_reductions k 1 (by decide)).2.2.2.2.2.2 (n+1) z
  have h₁ := hkill f hf _ hp
  have h₂ := hkill g hg _ hp
  rw [map_sub, sub_eq_zero] at h₁ h₂
  exact h₁.trans ((RingHom.congr_fun hnode _).trans h₂.symm)

open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaCoefficientNormDescentR0157.CoefficientPolygonTowerR0157

variable (l : Type) [Field l] [CharZero l] (ι : k →+* l)
variable (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l)
    (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)

theorem node_equation (r n : ℕ) (i : Fin r) :
    nodeMap k l ι ρ hρ n (equation k r n i) = equation l r n i := by
  unfold equation
  split_ifs <;> simp only [map_mul, map_sub, map_one, nodeMap_x, nodeMap_y]

/-- Literal finite coordinate numerators commute with coefficient extension.
This transports both ideal-power realizations, including the factor 1/2 in y. -/
theorem node_numerator (odd : Bool) (r n : ℕ) (i : Fin r) :
    nodeMap k l ι ρ hρ n (numerator k odd r n i) = numerator l odd r n i := by
  have ht : nodeMap k l ι ρ hρ n (tau k n) = tau l n := by
    simp only [tau, nodeMap_base, coefficientMap_parameter]
  have hg (v : A k n) : nodeMap k l ι ρ hρ n (geometric k n v) =
      geometric l n (nodeMap k l ι ρ hρ n v) := by simp [geometric]
  have hterm (v : A k n) : nodeMap k l ι ρ hρ n (term k odd n v) =
      term l odd n (nodeMap k l ι ρ hρ n v) := by
    cases odd <;> simp [term, hg]
  have hhalf : nodeMap k l ι ρ hρ n
      (base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹))) =
      base l n (trunc (PowerSeries l) PowerSeries.X n (PowerSeries.C (2 : l)⁻¹)) := by
    rw [nodeMap_base]
    change base l n (trunc (PowerSeries l) PowerSeries.X n
      (PowerSeries.map ι (PowerSeries.C (2 : k)⁻¹))) = _
    simp only [PowerSeries.map_C, map_inv₀, map_ofNat]
  have hite (P : Prop) [Decidable P] (x y : A k n) :
      nodeMap k l ι ρ hρ n (if P then x else y) =
        if P then nodeMap k l ι ρ hρ n x else nodeMap k l ι ρ hρ n y := by
    split_ifs <;> rfl
  simp only [numerator, hite, map_mul, map_add, map_sub, map_one,
    map_ofNat, map_natCast, map_pow, map_sum, hhalf, hterm, hg,
    node_equation, nodeMap_x, nodeMap_y, ht]

/-- The explicit finite specialization after coefficient extension. -/
def finiteEvaluation (a : lˣ) (n : ℕ) : A k n →+* R l n :=
  (ArithmeticThetaPolygonCohomologyR0131.markedPoint l n a).comp (nodeMap k l ι ρ hρ n)

/-- The continuous evaluation and the actual finite chart maps give the same
map at every thickness. -/
theorem finite_reduction (a : lˣ)
    (σ : ArithmeticThetaKatoAnnularR0152.Chart k →+* PowerSeries l)
    (hbase : ∀ b, σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = PowerSeries.map ι b)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = PowerSeries.C (a : l))
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = PowerSeries.C (a : l)⁻¹ * PowerSeries.X)
    (n : ℕ) :
    (trunc (PowerSeries l) PowerSeries.X n).comp σ =
      (finiteEvaluation k l ι ρ hρ a n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n) := by
  let f := (trunc (PowerSeries l) PowerSeries.X n).comp σ
  let g := (finiteEvaluation k l ι ρ hρ a n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)
  have hb (b : PowerSeries k) : f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) := by
    simp only [f, g, finiteEvaluation, RingHom.comp_apply, hbase,
      ArithmeticThetaKatoAnnularR0152.CompletedMarkedChartIdealR0152.reduction_base, nodeMap_base,
      ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143.marked_base]
    rfl
  have hnode : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hb
    · intro i
      fin_cases i
      · change f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
          g (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)
        simp only [f, g, finiteEvaluation, RingHom.comp_apply, hx,
          ArithmeticThetaKatoAnnularR0152.CompletedMarkedChartIdealR0152.reduction_x, nodeMap_x,
          ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143.marked_x]
      · change f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
          g (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)
        simp only [f, g, finiteEvaluation, RingHom.comp_apply, hy,
          ArithmeticThetaKatoAnnularR0152.CompletedMarkedChartIdealR0152.reduction_y, nodeMap_y,
          ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143.marked_y,
          ArithmeticThetaTateSeries.monomial, pow_one]
  have hf : f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0 := by
    change (trunc (PowerSeries l) PowerSeries.X n
      (σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X))) ^ (n+1) = 0
    rw [hbase, PowerSeries.map_X, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _)
  have hg : g (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0 := by
    change g (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) ^ (n+1) = 0
    rw [← hb]
    exact hf
  exact completed_hom_ext k n f g hnode hf hg

/-- Finite specialization evaluates the full prescribed numerator modulo every
parameter power; no truncation bound is discarded. -/
theorem finite_numerator (odd : Bool) (r n : ℕ) (h3 : 3 ≤ r)
    (i : Fin r) (a : lˣ) (ha : i.val = 0 → (a : l) ≠ 1) :
    finiteEvaluation k l ι ρ hρ a n (numerator k odd r n i) =
      (finiteEvaluation k l ι ρ hρ a n (equation k r n i)) ^ degree odd *
        trunc (PowerSeries l) PowerSeries.X n
          (if odd then ArithmeticThetaTateSeries.tateY r i.val (a : l)
            else ArithmeticThetaTateSeries.tateX r i.val (a : l)) := by
  simp only [finiteEvaluation, RingHom.comp_apply, node_numerator, node_equation]
  exact ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143.numerator_at_marked
    l odd r n h3 i a ha

end CoordinateCompletion


namespace ScalarPoint
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation)
open ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140 (baseRestriction)
open ArithmeticThetaTateSeries

variable (l : Type) [Field l] [CharZero l]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (i : Fin r) (p : baseScheme l ⟶ M.X) (f : ∀ n, A k n →+* R l n)
    (hp : ∀ n, Spec.map (CommRingCat.ofHom (f n)) ≫ chartMap k M n i =
      baseRestriction l n ≫ p)

/-- A finite frame pulled through the actual coefficient-extended point. -/
def frame (d n : ℕ) :=
  pullFrame (Spec.map (CommRingCat.ofHom (f n))) (chartFrame k h3 M hM s hs d n i) ≫
    (squareIso (chartMap k M n i) (Spec.map (CommRingCat.ofHom (f n))) p
      (baseRestriction l n) (hp n) (powerModule k M s d)).inv

instance frame_isIso (d n : ℕ) : IsIso (frame k l h3 M hM s hs i p f hp d n) := by
  letI := chartFrame_isIso k h3 M hM s hs d n i
  letI := pullFrame_isIso (Spec.map (CommRingCat.ofHom (f n)))
    (chartFrame k h3 M hM s hs d n i)
  unfold frame
  infer_instance

lemma frame_eval (d n : ℕ) (φ : Dual k M s d) (v : A k n)
    (hv : chartFrame k h3 M hM s hs d n i ≫ pulledInclusion (chartMap k M n i) φ =
      fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv v)) :
    frame k l h3 M hM s hs i p f hp d n ≫
      pulledInclusion (baseRestriction l n) (pulledInclusion p φ) =
    fromSection (SheafOfModules.unit (specR l n).ringCatSheaf : (specR l n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (R l n))).inv (f n v)) := by
  have he := squareIso_inclusion (chartMap k M n i)
    (Spec.map (CommRingCat.ofHom (f n))) p (baseRestriction l n) (hp n)
    (powerModule k M s d) φ
  rw [← he]
  simp only [frame, Category.assoc, Iso.inv_hom_id_assoc]
  rw [pullFrame_evaluation _ _ _ _ hv]
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (f n))) v).symm

include h3 hM hs hp

lemma finite_iso (d n : ℕ) (hu : IsUnit (f n (equation k r n i))) :
    IsIso (pulledInclusion (baseRestriction l n)
      (pulledInclusion p (idealInclusion (s.ker^d)))) := by
  have he := frame_eval k l h3 M hM s hs i p f hp d n
    (idealInclusion (s.ker^d)) (equation k r n i ^ d)
    (chartFrame_inclusion k h3 M hM s hs d n i)
  have hh := multiplication_unit (X := specR l n) _
    ((show IsUnit (f n (equation k r n i ^ d)) by simpa only [map_pow] using hu.pow d).map
      (Scheme.ΓSpecIso (CommRingCat.of (R l n))).inv.hom)
  rw [← he] at hh
  letI := hh
  exact IsIso.of_isIso_comp_left (frame k l h3 M hM s hs i p f hp d n) _

lemma finite_value (odd : Bool) (φ : Dual k M s (degree odd))
    (hφ : RealizesCoordinate k odd M s φ) (g : PowerSeries l) (n : ℕ)
    (hvnum : f n (numerator k odd r n i) =
      f n (equation k r n i) ^ degree odd * q l n g) :
    pulledInclusion (baseRestriction l n) (pulledInclusion p φ) =
    pulledInclusion (baseRestriction l n)
      (pulledInclusion p (idealInclusion (s.ker^degree odd)) ≫ scalarMap l g) := by
  have hv := frame_eval k l h3 M hM s hs i p f hp (degree odd) n φ
    (numerator k odd r n i) (chartFrame_value k h3 M hM s hs odd φ hφ n i)
  have hj := frame_eval k l h3 M hM s hs i p f hp (degree odd) n
    (idealInclusion (s.ker^degree odd)) (equation k r n i ^ degree odd)
    (chartFrame_inclusion k h3 M hM s hs (degree odd) n i)
  apply (cancel_epi (frame k l h3 M hM s hs i p f hp (degree odd) n)).mp
  rw [hv]
  have hm : pulledInclusion (baseRestriction l n)
      (pulledInclusion p (idealInclusion (s.ker^degree odd)) ≫ scalarMap l g) =
    pulledInclusion (baseRestriction l n) (pulledInclusion p (idealInclusion (s.ker^degree odd))) ≫
      fromSection (SheafOfModules.unit (specR l n).ringCatSheaf : (specR l n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R l n))).inv (q l n g)) := by
    simp only [pulledInclusion, Functor.map_comp, Category.assoc]
    rw [scalarMap, pullback_multiplication, base_value]
  rw [hm, ← Category.assoc, hj]
  apply unit_hom_ext
  change _ = (fromSection (SheafOfModules.unit (specR l n).ringCatSheaf : (specR l n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R l n))).inv (q l n g))).app ⊤
      ((fromSection (SheafOfModules.unit (specR l n).ringCatSheaf : (specR l n).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (R l n))).inv
          (f n (equation k r n i ^ degree odd)))).app ⊤ (1 : Γ(specR l n, ⊤)))
  simp [fromSection_apply, hvnum, map_mul, map_pow]

/-- Completeness over the extended coefficient field upgrades every finite
numerator identity to equality of the actual pulled sheaf morphisms. -/
theorem full_value (odd : Bool) (φ : Dual k M s (degree odd))
    (hφ : RealizesCoordinate k odd M s φ) (g : PowerSeries l)
    (hu : ∀ n, IsUnit (f n (equation k r n i)))
    (hv : ∀ n, f n (numerator k odd r n i) =
      f n (equation k r n i) ^ degree odd * q l n g) :
    IsIso (pulledInclusion p (idealInclusion (s.ker^degree odd))) ∧
      pulledInclusion p φ = pulledInclusion p (idealInclusion (s.ker^degree odd)) ≫
        scalarMap l g := by
  have hF := ((power_invertible k h3 M hM s hs (degree odd)).isInvertible_module.pullback p)
  have hG := Scheme.Modules.isInvertible_unit (baseScheme l)
  constructor
  · apply ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.base_isIso_of_pullbacks
      l _ _ hF hG
    intro n
    letI := unitPullback_isIso (baseRestriction l n)
    have hh := finite_iso k l h3 M hM s hs i p f hp (degree odd) n (hu n)
    change IsIso ((Scheme.Modules.pullback (baseRestriction l n)).map
      (pulledInclusion p (idealInclusion (s.ker^degree odd))) ≫
        unitPullback (baseRestriction l n)) at hh
    letI := hh
    exact IsIso.of_isIso_comp_right _ (unitPullback (baseRestriction l n))
  · apply ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.base_hom_ext
      l _ _ hF hG
    intro n
    letI := unitPullback_isIso (baseRestriction l n)
    apply (cancel_mono (unitPullback (baseRestriction l n))).mp
    exact finite_value k l h3 M hM s hs i p f hp odd φ hφ g n (hv n)


omit hp in
/-- The point obtained from a completed chart has the prescribed finite maps,
so its coordinate sheaf values are the full literal Tate sums. -/
theorem completed_value
    (ι : k →+* l)
    (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l)
    (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)
    (a : lˣ) (ha : i.val = 0 → (a : l) ≠ 1)
    (σ : ArithmeticThetaKatoAnnularR0152.Chart k →+* PowerSeries l)
    (hbase : ∀ b, σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) = PowerSeries.map ι b)
    (hx : σ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = PowerSeries.C (a : l))
    (hy : σ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = PowerSeries.C (a : l)⁻¹ * PowerSeries.X)
    (χ : ArithmeticThetaKatoAnnularR0152.chartScheme k ⟶ M.X)
    (hχ : ArithmeticThetaKatoAnnularR0152.IsChartMap k M i χ)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ) :
    let p := Spec.map (CommRingCat.ofHom σ) ≫ χ
    IsIso (pulledInclusion p (idealInclusion (s.ker^degree odd))) ∧
      pulledInclusion p φ = pulledInclusion p (idealInclusion (s.ker^degree odd)) ≫
        scalarMap l (if odd then tateY r i.val (a : l) else tateX r i.val (a : l)) := by
  let p := Spec.map (CommRingCat.ofHom σ) ≫ χ
  let f := CoordinateCompletion.finiteEvaluation k l ι ρ hρ a
  have hp (n : ℕ) : Spec.map (CommRingCat.ofHom (f n)) ≫ chartMap k M n i =
      baseRestriction l n ≫ p := by
    rw [show chartMap k M n i = Spec.map (CommRingCat.ofHom
      (ArithmeticThetaKatoAnnularR0152.reduction k n)) ≫ χ from (hχ.2 n).symm]
    dsimp [p]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CoordinateCompletion.finite_reduction k l ι ρ hρ a σ hbase hx hy n,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  apply full_value k l h3 M hM s hs i p f hp odd φ hφ
  · intro n
    change IsUnit (ArithmeticThetaPolygonCohomologyR0131.markedPoint l n a
      (ArithmeticThetaCoefficientNormDescentR0157.CoefficientPolygonTowerR0157.nodeMap k l ι ρ hρ n
        (equation k r n i)))
    rw [CoordinateCompletion.node_equation, marked_equation]
    exact (scalarEquation_unit l r i a ha).map (q l n)
  · intro n
    exact CoordinateCompletion.finite_numerator k l ι ρ hρ odd r n h3 i a ha

end ScalarPoint


namespace LiteralCoordinates
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaAnnularNormBridgeR0156.FaithfulAnnularEvaluation

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    [IsIntegral (genericScheme k M)] [IsIntegral (Curve k (ramifiedCurve k r))]
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k r)))
    (hc : IsChartIso k r c)
    (E : genericScheme k M ≅ Curve k (ramifiedCurve k r))
    (hE : IsCompactificationIso k M s hs.1 a c E)
    (D : ModelEvaluation k M (ramifiedCurve k r) E)

/-- The completed annular map gives the actual point over k(w)[[t]]. -/
def point : baseScheme (Coeff k) ⟶ M.X :=
  Spec.map (CommRingCat.ofHom (chartEvaluation k 1 1)) ≫ D.charts (zeroIndex r hr)

/-- The generic point of the full series and the completed point have the same
map into the algebraized model. -/
theorem point_square :
    Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ (Coeff k))) ≫ point k M E D =
    Spec.map (CommRingCat.ofHom (D.annular.comp (D.chartFields (zeroIndex r hr)))) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) ≫
        genericInclusion k M := by
  have hv : D.annular.comp (ArithmeticThetaKatoAnnularR0152.chartToField k) =
      (HahnSeries.ofPowerSeries ℤ (Coeff k)).comp (chartEvaluation k 1 1) :=
    RingHom.ext (annular_on_chart k D.annular D.annular_spec)
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    D.chartFieldSquares (zeroIndex r hr), ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hv,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

include h3 hM hs
/-- Both actual ideal-power coordinate maps evaluate at w to the literal full
Tate sums; this is an equality of sheaf maps over k(w)[[t]]. -/
theorem point_value (odd : Bool) (φ : Dual k M s (degree odd))
    (hφ : RealizesCoordinate k odd M s φ) :
    IsIso (pulledInclusion (point k M E D) (idealInclusion (s.ker^degree odd))) ∧
      pulledInclusion (point k M E D) φ =
        pulledInclusion (point k M E D) (idealInclusion (s.ker^degree odd)) ≫
          scalarMap (Coeff k) (if odd then ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k)
            else ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k)) := by
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  have hw := (ArithmeticThetaLaurentNormR0064.coefficient_nonzero k 1 one_ne_zero).2.1 1 (by decide)
  simp only [pow_one] at hw
  let u : (Coeff k)ˣ := Units.mk0 _ hw.1
  obtain ⟨ρ, hρ, _⟩ := (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps
    k (Coeff k) (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k)).2.1
  apply ScalarPoint.completed_value k (Coeff k) h3 M hM s hs (zeroIndex r hr)
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k) ρ hρ.1 u
    (fun _ => hw.2) (chartEvaluation k 1 1) (chartEvaluation_base k 1 1)
    ?_ ?_ (D.charts (zeroIndex r hr)) (D.chartSquares (zeroIndex r hr)) odd φ hφ
  · simpa [ArithmeticThetaAnnularNormBridgeR0156.coordinate, u] using chartEvaluation_x k 1 1
  · simpa [ArithmeticThetaAnnularNormBridgeR0156.coordinate, u] using chartEvaluation_y k 1 1

include hX hY ha hc hE
/-- The faithful geometric composite sends both projective affine coordinates
to the complete literal Tate sums at the transcendental coordinate. -/
theorem isEvaluation : IsEvaluation k (ramifiedCurve k r) r D.composite := by
  letI : Nonempty (complementScheme k M s) := complement_nonempty k h3 M hM s hs
  letI : Nonempty (Spec (CommRingCat.of (ArithmeticThetaPeriodOneNormR0248.ChartRing k (ramifiedCurve k r)))) :=
    Nonempty.map (fun z => c.hom (a.hom z)) inferInstance
  letI : IsOpenImmersion (ArithmeticThetaPeriodOneNormR0248.chartInclusion k (ramifiedCurve k r)) :=
    CompactifiedCoordinateIsomorphism.chart_open k
  obtain ⟨χ, hχ⟩ := factor_generic_chart
    (ArithmeticThetaPeriodOneNormR0248.chartInclusion k (ramifiedCurve k r)) D.composite
  let l : Spec (CommRingCat.of (Series k)) ⟶ complementScheme k M s :=
    Spec.map (CommRingCat.ofHom χ) ≫ c.inv ≫ a.inv
  have hlχ : Spec.map (CommRingCat.ofHom χ) = l ≫ a.hom ≫ c.hom := by simp [l]
  have hl : l ≫ (complement k M s).ι =
      Spec.map (CommRingCat.ofHom (D.annular.comp (D.chartFields (zeroIndex r hr)))) ≫
        (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) := by
    apply (cancel_mono E.hom).mp
    rw [Category.assoc, hE.2.1]
    have h := hχ.trans D.generic_square
    simpa only [hlχ, Category.assoc, ArithmeticThetaPeriodOneNormR0248.chartInclusion,
      ArithmeticThetaLegendreComparisonR0177.chartInclusion,
      ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion] using h
  have hlm : l ≫ complementInclusion k M s =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ (Coeff k))) ≫ point k M E D := by
    rw [complementInclusion, ← Category.assoc, hl, Category.assoc]
    exact (point_square k M E D).symm
  have hv (odd : Bool) :
      χ (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
         else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
      HahnSeries.ofPowerSeries ℤ (Coeff k)
        (if odd then ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k)
         else ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k)) := by
    let φ : Dual k M s (degree odd) := match odd with | true => Y | false => X
    have hφ : RealizesCoordinate k odd M s φ := by cases odd <;> assumption
    have hev := point_value k h3 M hM s hs E D odd φ hφ
    letI : IsIso (pulledInclusion (point k M E D) (idealInclusion (s.ker ^ degree odd))) := hev.1
    letI : IsIso (pulledInclusion (complementInclusion k M s)
      (idealInclusion (s.ker ^ degree odd))) := (ha.2 odd).1
    have hcval : regularValue
        (pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker ^ degree odd)))
        (pulledInclusion (complementInclusion k M s) φ) =
        a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
          (cubicCoordinate k r odd)) := by
      have hh := (ha.2 odd).2 ⊤
        ((inv (pulledInclusion (complementInclusion k M s)
          (idealInclusion (s.ker ^ degree odd)))).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))
      change regularValue (pulledInclusion (complementInclusion k M s)
        (idealInclusion (s.ker ^ degree odd))) (pulledInclusion (complementInclusion k M s) φ) =
        _ * (show Γ(complementScheme k M s, ⊤) from
          (pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker ^ degree odd))).app ⊤
            ((inv (pulledInclusion (complementInclusion k M s)
              (idealInclusion (s.ker ^ degree odd)))).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))) at hh
      rw [inverse_inclusion_one, mul_one] at hh
      simpa using hh
    have hpval : regularValue (pulledInclusion (point k M E D) (idealInclusion (s.ker ^ degree odd)))
        (pulledInclusion (point k M E D) φ) =
          (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries (Coeff k)))).inv
            (if odd then ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k)
             else ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k)) := by
      rw [hev.2]
      change (Scheme.Modules.Hom.app (X := baseScheme (Coeff k))
        (inv (pulledInclusion (point k M E D) (idealInclusion (s.ker ^ degree odd))) ≫
          pulledInclusion (point k M E D) (idealInclusion (s.ker ^ degree odd)) ≫
            scalarMap (Coeff k) _) ⊤) (1 : Γ(baseScheme (Coeff k), ⊤)) = _
      rw [IsIso.inv_hom_id_assoc]
      simp [scalarMap, fromSection_apply]

    have hsquare := ArithmeticThetaHodgeFourTorsionR0147.MarkedCoordinateChart.square_regularValue
      (complementInclusion k M s) l (point k M E D)
      (Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ (Coeff k))))
      hlm (idealInclusion (s.ker ^ degree odd)) φ
    rw [hcval, hpval] at hsquare
    apply (Scheme.ΓSpecIso (CommRingCat.of (Series k))).inv.hom.injective
    have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom χ))
      (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
       else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)
    rw [hlχ] at hnat
    have hbval := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ (Coeff k))))
      (if odd then ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k)
       else ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k))
    calc
      _ = (l ≫ a.hom ≫ c.hom).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k r))).inv _) := hnat
      _ = l.appTop (a.hom.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv (cubicCoordinate k r odd))) := by
        simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hc.2 odd]
      _ = _ := hsquare
      _ = _ := hbval.symm
  exact ⟨χ, ⟨D.chart_scalars hE.1 χ hχ, hv false, hv true⟩, hχ⟩

end LiteralCoordinates


#print axioms LiteralCoordinates.point_square
#print axioms LiteralCoordinates.point_value
#print axioms LiteralCoordinates.isEvaluation
#print axioms ScalarPoint.full_value
#print axioms ScalarPoint.completed_value
#print axioms chart_evaluation_unique
#print axioms evaluation_unique
#print axioms transported_origin_law
#print axioms kato_to_model
#print axioms expansion_through_model
#print axioms ModelEvaluation.generic_square
#print axioms ModelEvaluation.expansion
#print axioms model_evaluation_exists
#print axioms factor_generic_chart
#print axioms annular_scalars
#print axioms ModelEvaluation.scalars
#print axioms ModelEvaluation.chart_scalars
#print axioms CoordinateCompletion.node_equation
#print axioms CoordinateCompletion.node_numerator
#print axioms annular_on_chart
#print axioms CoordinateCompletion.completed_hom_ext
#print axioms CoordinateCompletion.finite_numerator
#print axioms CoordinateCompletion.finite_reduction

end RamifiedCubicKatoEvaluation

open CategoryTheory AlgebraicGeometry
open RamifiedCubicKatoEvaluation
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145

/-- The unique faithful evaluation of the specified ramified cubic fixes the
structural scalars and both literal coordinates, and carries every normalized
Kato function to its full unsplit polygon expansion. -/
theorem ramified_cubic_kato_evaluation : ∀ (k : Type) [Field k] [CharZero k] (r : ℕ), 3 ≤ r → Even r → ∀ [(ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r).IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r))] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r))], ∃! ev : (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r)).functionField →+* ArithmeticThetaPeriodOneNormR0248.Series k, ArithmeticThetaPeriodOneNormR0248.IsEvaluation k (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r) r ev ∧ Function.Injective ev ∧ ∀ (G : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r)), ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r) G → ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ g : (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r)).functionField, ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.ramifiedCurve k r) G c g → ArithmeticThetaUnsplitExpansionR0158.HasExpansion k r c 0 (ev g) := by
  intro k _ _ r h3 he _ _ _
  have hr : 0 < r := by omega
  obtain ⟨T, M, hM⟩ := ArithmeticThetaTateCuspsR0181.TateFullLevelMarking.model_exists k r h3 hr
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3 M hM s hs
  letI : IsLocallyNoetherian (genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  obtain ⟨D⟩ := model_evaluation_exists k h3 M hM (ramifiedCurve k r) E
  have hev := LiteralCoordinates.isEvaluation k h3 M hM s hs X Y hX hY a ha c hc E hE D
  refine ⟨D.composite, ⟨hev, D.injective, ?_⟩, ?_⟩
  · intro G hG c hc hcop g hg
    exact D.expansion h3 he hM s hs hE.1 hE.2.2 G hG c hc hcop g hg
  · intro ev heval
    exact evaluation_unique k (ramifiedCurve k r) r ev D.composite heval.1 hev

#print axioms ramified_cubic_kato_evaluation

end ArithmeticThetaPeriodOneNormR0248
