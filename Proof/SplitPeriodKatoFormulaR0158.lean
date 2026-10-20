module

public import ExactKatoAnnularFormulaR0157
public import RamifiedKatoBaseChangeR0155
public import RamifiedLiteralQuotientR0156
public import CompatibleFormalSectionBasisR0134
public import CompatibleProjectiveEmbeddingsR0135
public import ProjectiveTowerEffectivityR0135

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158
namespace SplitPeriodKatoFormulaR0158
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaRamifiedPeriodR0154 ArithmeticThetaRamifiedPeriodR0155
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaAnnularNormBridgeR0156 (literalTheta ramified_literal_quotient)
/-- A coarse polygon model is supplied by the accepted effective projective tower. -/
private lemma exists_model (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    ∃ (T : Tower k r hr) (M : Model k T), IsModel k T M := by
  obtain ⟨T, _⟩ := ArithmeticThetaInfinitesimalPolygonR0129.proper_flat_polygon_tower k r hr h3
  obtain ⟨b, hb, hbr, _⟩ :=
    ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis k r hr h3 T (fun _ => 1) 3 (by omega)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩

private theorem ramified_formula :
∀ (k : Type) [Field k] [CharZero k] (c d : ℕ) (hd : 0 < d) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < ((2*c)*d)) (h3 : 3 ≤ ((2*c)*d)) (he : Even ((2*c)*d)) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k ((2*c)*d) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex ((2*c)*d) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin ((2*c)*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin ((2*c)*d) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (hcr : c ∣ ((2*c)*d)), ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∀ j : Fin ((2*c)*d), φ j g = ArithmeticThetaAnnularNormBridgeR0156.literalTheta k ((2*c)*d) c hr hc hcr hcop (ζ : k) hζ j) := by
  intro k _ _ c d hd hc hcop hr h3 he T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ hcr
  classical
  have hr₀ : 0 < 2*c := by omega
  have h3₀ : 3 ≤ 2*c := by omega
  have he₀ : Even (2*c) := ⟨c, by omega⟩
  obtain ⟨T₀, M₀, hM₀⟩ := exists_model k (2*c) hr₀ h3₀
  letI : AlgebraicGeometry.IsIntegral (genericScheme k M₀) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3₀ M₀ hM₀
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k M₀ hM₀
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme k M₀) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M₀)
  obtain ⟨s₀, hs₀, _⟩ := marked_section_algebraization k (2*c) hr₀ h3₀ T₀ M₀ hM₀
    (zeroIndex (2*c) hr₀) 1
  obtain ⟨G₀, hG₀, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k (2*c) hr₀ h3₀ T₀ he₀ M₀ hM₀ s₀ hs₀
  have Hχ : ∀ j : Fin (2*c), ∃ χj, IsChartMap k M₀ j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k (2*c) hr₀ h3₀ T₀ M₀ hM₀ j
    exact ⟨χj, hj⟩
  choose χ₀ hχ₀ using Hχ
  have Hφ : ∀ j : Fin (2*c), ∃ φj, IsChartFieldMap k M₀ (χ₀ j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k (2*c) hr₀ h3₀ T₀ M₀ hM₀ j (χ₀ j) (hχ₀ j)
    exact ⟨φj, hj.1⟩
  choose φ₀ hφ₀ using Hφ
  obtain ⟨f₀, hf₀, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.exact_kato_annular_formula
    k c hc hcop hr₀ h3₀ T₀ M₀ hM₀ s₀ hs₀ G₀ hG₀ ζ hζ χ₀ hχ₀ φ₀ hφ₀
  have Hρ : ∀ q : Fin d, ∃ (ρq : Chart k →+* Chart k) (Eq : ChartField k →+* ChartField k),
      IsChartRamification k d hd q ρq ∧ ExtendsChart k ρq Eq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := completed_chart_ramification k d hd q
    obtain ⟨Eq, hEq, _⟩ := hρq.2.2
    exact ⟨ρq, Eq, hρq.1, hEq⟩
  choose ρ E hρ hE using Hρ
  obtain ⟨F, hF, _⟩ := ramified_model_morphism k d hd (2*c) hr₀ h3₀ hr
    T₀ T M₀ hM₀ M hM ρ hρ χ₀ hχ₀ χ hχ
  obtain ⟨ell, hell, _⟩ := ramified_laurent_extension k d hd
  obtain ⟨b, hb, _⟩ := ramified_generic_base_change k d hd (2*c) hr₀ h3₀ hr
    T₀ T M₀ hM₀ M hM ρ hρ χ₀ hχ₀ χ hχ F hF.1 ell hell.1
  obtain ⟨α, hα, _⟩ := ramified_function_field_expansion k d hd (2*c) hr₀ h3₀ hr
    T₀ T M₀ hM₀ M hM ρ hρ χ₀ hχ₀ χ hχ F hF.1 ell hell.1 b hb.1
    φ₀ hφ₀ φ hφ E hE
  have hexp : ∀ j, φ j (α f₀) = literalTheta k ((2*c)*d) c hr hc hcr hcop (ζ : k) hζ j := by
    intro j
    rw [hα.2.2.2.1 j f₀, hf₀.2]
    exact ramified_literal_quotient k c hc hcop (ζ : k) hζ d hd hr hcr ρ hρ E hE j
  have hbase := ramified_kato_base_change k d hd (2*c) hr₀ h3₀ hr
    T₀ T M₀ hM₀ M hM ρ hρ χ₀ hχ₀ χ hχ F hF.1 ell hell.1 b hb.1
    he₀ he s₀ hs₀ s hs G₀ hG₀ G hG
  have hK := (actual_kato_field_base_change k (2*c) hr₀ h3₀ T₀ he₀ M₀ hM₀ s₀ hs₀ G₀ hG₀
    k ((2*c)*d) hr h3 T he M hM s hs G hG ell b hbase α hα.1 c hc hcop).2 f₀ hf₀.1
  obtain ⟨g, hg, huniq⟩ := actual_kato_function_existence
    k ((2*c)*d) hr h3 T he M hM s hs G hG c hc hcop
  exact ⟨α f₀, ⟨hK, hexp⟩, fun f hf => (huniq f hf.1).trans (huniq (α f₀) hK).symm⟩
end SplitPeriodKatoFormulaR0158

/-- The full normalized Kato formula on every specified even split polygon. -/
theorem split_period_kato_formula :
∀ (k : Type) [Field k] [CharZero k] (r c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (hcr : c ∣ r), ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∀ j : Fin r, φ j g = ArithmeticThetaAnnularNormBridgeR0156.literalTheta k r c hr hc hcr hcop (ζ : k) hζ j) := by
  intro k _ _ r c hc hcop hr h3 he T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ hcr
  have hc2 : Nat.Coprime c 2 := hcop.of_dvd_right (by decide)
  have hdiv : 2*c ∣ r := hc2.symm.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he) hcr
  obtain ⟨d, rfl⟩ := hdiv
  have hd : 0 < d := Nat.pos_of_mul_pos_left hr
  exact SplitPeriodKatoFormulaR0158.ramified_formula k c d hd hc hcop hr h3 he
    T M hM s hs G hG ζ hζ χ hχ φ hφ hcr

#print axioms split_period_kato_formula
end ArithmeticThetaUnsplitExpansionR0158
