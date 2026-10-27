import CoefficientGenericKatoSquareR0157
import CoefficientFunctionFieldExpansionR0157
import LiteralCoefficientTransportR0157
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Descent of the full literal theta norm through ramification and coefficient extension. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace LiteralNormDescentR0157
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152 ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaAnnularNormBridgeR0156 (literalTheta ramified_literal_quotient literal_split_geometric_norm)

private lemma exists_model (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    ∃ (T : Tower k r hr) (M : Model k T), IsModel k T M := by
  obtain ⟨T, _⟩ := proper_flat_polygon_tower k r hr h3
  obtain ⟨b, hb, hbr, _⟩ :=
    ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis k r hr h3 T (fun _ => 1) 3 (by omega)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩

/-- Injectivity descends a norm equation along a genuine cartesian endomorphism square. -/
private lemma descend_norm {X Xb S Sb : Scheme}
    [IsIntegral X] [IsIntegral Xb]
    (p : X ⟶ S) (pb : Xb ⟶ Sb) (b : Xb ⟶ X) (i : Sb ⟶ S)
    (H : IsPullback b pb p i) (m : X ⟶ X) (mb : Xb ⟶ Xb)
    (hm : m ≫ p = p) (hmb : mb ≫ pb = pb) (hw : mb ≫ b = b ≫ m)
    [IsFinite m] [Etale m] [Surjective m]
    (μ : X.functionField →+* X.functionField) (hμ : IsFieldMap m μ)
    (α : X.functionField →+* Xb.functionField) (hα : IsFieldMap b α)
    (f : X.functionField)
    (hn : ∀ μb : Xb.functionField →+* Xb.functionField,
      IsFieldMap mb μb → fieldNorm μb (α f) = α f) : fieldNorm μ f = f := by
  have Hm := ActualKatoFieldBaseChange.endomorphism_cartesian p pb b i H m mb hm hmb hw
  letI : IsFinite mb := MorphismProperty.of_isPullback (P := @IsFinite) Hm inferInstance
  letI : Etale mb := MorphismProperty.of_isPullback (P := @Etale) Hm inferInstance
  letI : Surjective mb := MorphismProperty.of_isPullback (P := @Surjective) Hm inferInstance
  obtain ⟨μb, hμb⟩ := ActualMultiplicationFieldNorm.exists_fieldMap mb
  apply α.injective
  exact (geometric_norm_base_change X X Xb Xb m mb b b Hm μ μb α α hμ hμb hα hα f).trans
    (hn μb hμb)

private lemma local_eq_literal (k : Type) [Field k] [CharZero k]
    (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c)
    (ζ : k) (hζ : IsPrimitiveRoot ζ c) (j : Fin (2*c)) :
    ArithmeticThetaRatioRegularityR0067.LocalTheta k c ζ hc hcop hζ j =
      literalTheta k (2*c) c hr hc (dvd_mul_left c 2) hcop ζ hζ j := by
  unfold ArithmeticThetaRatioRegularityR0067.LocalTheta ArithmeticThetaLocalOrdersR0066.localFunction
    ArithmeticThetaGenericOverlapR0065.numerator ArithmeticThetaGenericOverlapR0065.denominator
    ArithmeticThetaLocalNormR0054.localNumerator ArithmeticThetaLocalNormR0054.localDenominator
    literalTheta
  simp only [map_mul, map_pow, map_neg]

/-- A split coefficient field suffices; the multiplier need not divide the original period. -/
private theorem split_norm (k : Type) [Field k] [CharZero k]
    (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c)
    (T : Tower k (2*c) hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex (2*c) hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    [IsIntegral (genericScheme k M)]
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c)
    (χ : Fin (2*c) → (chartScheme k ⟶ M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (φ : Fin (2*c) → ((genericScheme k M).functionField →+* ChartField k))
    (hφ : ∀ j, IsChartFieldMap k M (χ j) (φ j))
    (f : (genericScheme k M).functionField)
    (hf : ∀ j, φ j f = ArithmeticThetaRatioRegularityR0067.LocalTheta k c (ζ : k) hc hcop hζ j)
    (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d)
    (ζd : kˣ) (hζd : IsPrimitiveRoot (ζd : k) d)
    (μ : (genericScheme k M).functionField →+* (genericScheme k M).functionField)
    (hμ : IsFieldMap (multiplication k M G d) μ) : fieldNorm μ f = f := by
  classical
  have hrd : 0 < (2*c)*d := Nat.mul_pos hr hd
  have h3d : 3 ≤ (2*c)*d := h3.trans (Nat.le_mul_of_pos_right (2*c) hd)
  have he : Even (2*c) := ⟨c, by omega⟩
  have hed : Even ((2*c)*d) := he.mul_right d
  have hcr : c ∣ (2*c)*d := dvd_mul_of_dvd_left (dvd_mul_left c 2) d
  obtain ⟨Tb, Mb, hMb⟩ := exists_model k ((2*c)*d) hrd h3d
  letI : IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3d Mb hMb
  obtain ⟨sb, hsb, _⟩ := marked_section_algebraization k ((2*c)*d) hrd h3d Tb Mb hMb
    (zeroIndex ((2*c)*d) hrd) 1
  obtain ⟨Gb, hGb, _⟩ := actual_generic_group_law k ((2*c)*d) hrd h3d Tb hed Mb hMb sb hsb
  have Hχ : ∀ j : Fin ((2*c)*d), ∃ χj, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k ((2*c)*d) hrd h3d Tb Mb hMb j
    exact ⟨χj, hj⟩
  choose χb hχb using Hχ
  have Hφ : ∀ j : Fin ((2*c)*d), ∃ φj, IsChartFieldMap k Mb (χb j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k ((2*c)*d) hrd h3d Tb Mb hMb j (χb j) (hχb j)
    exact ⟨φj, hj.1⟩
  choose φb hφb using Hφ
  have Hρ : ∀ q : Fin d, ∃ (ρq : Chart k →+* Chart k) (Eq : ChartField k →+* ChartField k),
      ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρq ∧
      ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρq Eq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := ArithmeticThetaRamifiedPeriodR0154.completed_chart_ramification k d hd q
    obtain ⟨Eq, hEq, _⟩ := hρq.2.2
    exact ⟨ρq, Eq, hρq.1, hEq⟩
  choose ρ E hρ hE using Hρ
  obtain ⟨F, hF, _⟩ := ArithmeticThetaRamifiedPeriodR0154.ramified_model_morphism
    k d hd (2*c) hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k d hd
  obtain ⟨b, hb, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_generic_base_change
    k d hd (2*c) hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1
  obtain ⟨α, hα, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_function_field_expansion
    k d hd (2*c) hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    φ hφ φb hφb E hE
  have hbase := ArithmeticThetaRamifiedPeriodR0155.ramified_kato_base_change
    k d hd (2*c) hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    he hed s hs sb hsb G hG Gb hGb
  have hexp : ∀ j, φb j (α f) = literalTheta k ((2*c)*d) c hrd hc hcr hcop (ζ : k) hζ j := by
    intro j
    rw [hα.2.2.2.1 j f, hf]
    exact ramified_literal_quotient k c hc hcop (ζ : k) hζ d hd hrd hcr ρ hρ E hE j
  obtain ⟨rot, scal, inv, ha⟩ := ArithmeticThetaModelSymmetriesR0137.algebraized_annular_actions
    k ((2*c)*d) hrd h3d Tb Mb hMb
  obtain ⟨hfinite, hetale, hsurj, _⟩ :=
    multiplication_finite_etale_degree k (2*c) hr h3 T he M hM s hs G hG d hd
  letI := hfinite
  letI := hetale
  letI := hsurj
  apply descend_norm (X := genericScheme k M) (Xb := genericScheme k Mb)
    (genericStructure k M) (genericStructure k Mb) b
    (Spec.map (CommRingCat.ofHom ell)) hbase.1
    (multiplication k M G d) (multiplication k Mb Gb d)
    (MultiplicationDifferential.multiplication_over k M G d)
    (MultiplicationDifferential.multiplication_over k Mb Gb d) (hbase.2.2 d) μ hμ α hα.1 f
  intro μb hμb
  exact literal_split_geometric_norm k ((2*c)*d) hrd h3d Tb hed Mb hMb sb hsb Gb hGb
    rot scal inv ha χb hχb φb hφb c hc hcop hcr (ζ : k) hζ d hd hcd
    (dvd_mul_left d (2*c)) ζd hζd μb hμb (α f) hexp

end LiteralNormDescentR0157

open LiteralNormDescentR0157
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152 ArithmeticThetaKatoExistenceR0151

/-- The complete literal theta quotient is fixed by every positive coprime multiplication norm. -/
theorem literal_norm_descent :
∀ (k : Type) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin (2*c) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin (2*c) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (f : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (hf : ∀ j : Fin (2*c), φ j f = ArithmeticThetaRatioRegularityR0067.LocalTheta k c (ζ : k) hc hcop hζ j), ∀ (d : ℕ), 0 < d → Nat.Coprime c d → ∀ μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ → ArithmeticThetaGeometricNormR0150.fieldNorm μ f = f := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ f hf d hd hcd μ hμ
  classical
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  have he : Even (2*c) := ⟨c, by omega⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  letI : NeZero (d : k) := ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)⟩
  obtain ⟨zd, hzd⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot l d
  let ζd : lˣ := Units.mk0 zd (hzd.ne_zero (Nat.ne_of_gt hd))
  have hζd : IsPrimitiveRoot (ζd : l) d := hzd
  let ζl : lˣ := Units.map ι.toMonoidHom ζ
  have hζl : IsPrimitiveRoot (ζl : l) c := hζ.map_of_injective ι.injective
  obtain ⟨Tl, Ml, hMl⟩ := exists_model l (2*c) hr h3
  letI : IsIntegral (genericScheme l Ml) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral l h3 Ml hMl
  obtain ⟨sl, hsl, _⟩ := marked_section_algebraization l (2*c) hr h3 Tl Ml hMl (zeroIndex (2*c) hr) 1
  obtain ⟨Gl, hGl, _⟩ := actual_generic_group_law l (2*c) hr h3 Tl he Ml hMl sl hsl
  have Hχ : ∀ j : Fin (2*c), ∃ χj, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps l (2*c) hr h3 Tl Ml hMl j
    exact ⟨χj, hj⟩
  choose χl hχl using Hχ
  have Hφ : ∀ j : Fin (2*c), ∃ φj, IsChartFieldMap l Ml (χl j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps l (2*c) hr h3 Tl Ml hMl j (χl j) (hχl j)
    exact ⟨φj, hj.1⟩
  choose φl hφl using Hφ
  obtain ⟨Hell, Hρ, HE⟩ := coefficient_completed_maps k l ι
  obtain ⟨ell, hell, _⟩ := Hell
  obtain ⟨ρ, hρ, _⟩ := Hρ
  obtain ⟨E, hE, _⟩ := HE ρ hρ.1
  obtain ⟨F, hF, _⟩ := coefficient_model_base_change k l ι (2*c) hr h3 T Tl M hM Ml hMl
    ρ hρ.1 χ hχ χl hχl
  obtain ⟨b, hb, _⟩ := coefficient_generic_kato_square k l ι (2*c) hr h3 T Tl M hM Ml hMl
    ρ hρ.1 χ hχ χl hχl F hF ell hell he s hs sl hsl G hG Gl hGl
  obtain ⟨α, hα, _⟩ := coefficient_function_field_expansion k l ι (2*c) hr h3 T Tl M hM Ml hMl
    ρ hρ.1 E hE χ hχ χl hχl F hF ell hell b hb.1 φ hφ φl hφl
  have hexp : ∀ j, φl j (α f) =
      ArithmeticThetaRatioRegularityR0067.LocalTheta l c (ζl : l) hc hcop hζl j := by
    intro j
    rw [hα.2.2 j f, hf j, local_eq_literal k c hc hcop hr (ζ : k) hζ j,
      local_eq_literal l c hc hcop hr (ζl : l) hζl j]
    exact literal_coefficient_transport k l ι ρ hρ.1 E hE (2*c) c hr hc (dvd_mul_left c 2)
      hcop (ζ : k) hζ hζl j
  obtain ⟨hfinite, hetale, hsurj, _⟩ :=
    multiplication_finite_etale_degree k (2*c) hr h3 T he M hM s hs G hG d hd
  letI := hfinite
  letI := hetale
  letI := hsurj
  apply descend_norm (X := genericScheme k M) (Xb := genericScheme l Ml)
    (genericStructure k M) (genericStructure l Ml) b
    (Spec.map (CommRingCat.ofHom ell)) hb.2.1
    (multiplication k M G d) (multiplication l Ml Gl d)
    (MultiplicationDifferential.multiplication_over k M G d)
    (MultiplicationDifferential.multiplication_over l Ml Gl d) (hb.2.2.2 d) μ hμ α hα.1 f
  intro μl hμl
  exact split_norm l c hc hcop hr h3 Tl Ml hMl sl hsl Gl hGl ζl hζl χl hχl φl hφl
    (α f) hexp d hd hcd ζd hζd μl hμl

end ArithmeticThetaCoefficientNormDescentR0157
#print axioms ArithmeticThetaCoefficientNormDescentR0157.literal_norm_descent
