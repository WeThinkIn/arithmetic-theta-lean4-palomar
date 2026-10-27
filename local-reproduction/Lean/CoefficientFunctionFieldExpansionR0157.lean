import CoefficientModelBaseChangeR0157

/-! Coefficient extension on geometric function fields and full completed expansions. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace CoefficientFunctionFieldExpansionR0157
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {Tl : Tower l r hr}
variable (M : Model k T) (Ml : Model l Tl)
variable [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme l Ml)]

/-- The prescribed integral square gives equality already on spectra of the
completed fraction fields, before constructing the function-field pullback. -/
lemma chart_square
    (F : Ml.X ⟶ M.X) (b : genericScheme l Ml ⟶ genericScheme k M)
    (hb : b ≫ genericInclusion k M = genericInclusion l Ml ≫ F)
    (χ : chartScheme k ⟶ M.X) (χl : chartScheme l ⟶ Ml.X)
    (ρ : Chart k →+* Chart l)
    (hc : χl ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ)
    (φl : (genericScheme l Ml).functionField →+* ChartField l)
    (hφl : IsChartFieldMap l Ml χl φl)
    (E : ChartField k →+* ChartField l) (hE : ExtendsChart k l ρ E) :
    Spec.map (CommRingCat.ofHom φl) ≫
        (genericScheme l Ml).fromSpecStalk (_root_.genericPoint _) ≫ b =
      Spec.map (CommRingCat.ofHom (E.comp φ)) ≫
        (genericScheme k M).fromSpecStalk (_root_.genericPoint _) := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  have he : Spec.map (CommRingCat.ofHom E) ≫ Spec.map (CommRingCat.ofHom (chartToField k)) =
      Spec.map (CommRingCat.ofHom (chartToField l)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom z)) (RingHom.ext hE)
  change _ = (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom E) ≫ _) ≫ _
  rw [Spec.map_comp]
  simp only [Category.assoc]
  have hleft := congrArg (fun z => z ≫ F) hφl
  simp only [Category.assoc] at hleft
  rw [hb, hleft, hc, hφ, ← Category.assoc, ← he, Category.assoc]

/-- Full Laurent scalars commute with extension by fraction-ring uniqueness. -/
lemma laurent_naturality (ι : k →+* l) (ρ : Chart k →+* Chart l)
    (hρ : IsChartMap k l ι ρ) (E : ChartField k →+* ChartField l)
    (hE : ExtendsChart k l ρ E) (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : IsLaurentMap k l ι ell) :
    E.comp (laurentInclusion k) = (laurentInclusion l).comp ell := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro a
  change E (laurentInclusion k (algebraMap (PowerSeries k) (LaurentSeries k) a)) =
    laurentInclusion l (ell (algebraMap (PowerSeries k) (LaurentSeries k) a))
  rw [laurentInclusion_base, hell, laurentInclusion_base, hE, hρ.1]

end CoefficientFunctionFieldExpansionR0157

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

/-- The unique geometric coefficient pullback preserves every Laurent scalar
and every full completed-chart expansion, including the zero function. -/
theorem coefficient_function_field_expansion :
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (Tl : ArithmeticThetaInfinitesimalPolygonR0129.Tower l r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (Ml : ArithmeticThetaProjectiveEffectivityR0135.Model l Tl) (hMl : ArithmeticThetaProjectiveEffectivityR0135.IsModel l Tl Ml) (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l) (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ) (E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField l) (hE : ArithmeticThetaCoefficientNormDescentR0157.ExtendsChart k l ρ E) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (χl : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme l) Ml.X) (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j)) (F : Quiver.Hom Ml.X M.X) (hF : ArithmeticThetaCoefficientNormDescentR0157.IsModelMap k l ι T Tl M Ml ρ χ χl F) (ell : LaurentSeries k →+* LaurentSeries l) (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml)] (b : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (hb : ArithmeticThetaCoefficientNormDescentR0157.IsGenericLift k l T Tl M Ml F b) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (φl : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml)) →+* ArithmeticThetaKatoAnnularR0152.ChartField l)) (hφl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap l Ml (χl j) (φl j)), ∃! α : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml)), ArithmeticThetaGeometricNormR0150.IsFieldMap b α ∧ (∀ a : LaurentSeries k, α (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a) = ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml)) (LaurentSeries l) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure l Ml) (ell a)) ∧ (∀ (j : Fin r) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), φl j (α g) = E (φ j g)) := by
  intro k l _ _ _ _ ι r hr h3 T Tl M hM Ml hMl ρ hρ E hE χ hχ χl hχl F hF ell hell _ _ b hb φ hφ φl hφl
  have hs j := CoefficientFunctionFieldExpansionR0157.chart_square k l M Ml F b hb
    (χ j) (χl j) ρ (hF.2 j) (φ j) (hφ j) (φl j) (hφl j) E hE
  let j : Fin r := ⟨0, hr⟩
  have hη : b (_root_.genericPoint (genericScheme l Ml)) =
      _root_.genericPoint (genericScheme k M) := by
    have hp := congrArg (fun f => f (IsLocalRing.closedPoint (ChartField l))) (hs j)
    have hpoint {X : Scheme} [IsIntegral X] (z : Spec (.of X.functionField)) :
        X.fromSpecStalk (_root_.genericPoint X) z = _root_.genericPoint X := by
      calc
        X.fromSpecStalk (_root_.genericPoint X) z =
            X.fromSpecStalk (_root_.genericPoint X) _ :=
          congrArg _ (Subsingleton.elim _ _)
        _ = _ := Scheme.fromSpecStalk_closedPoint
    have hl := hpoint (X := genericScheme l Ml)
      ((Spec.map (CommRingCat.ofHom (φl j))) (IsLocalRing.closedPoint (ChartField l)))
    have hk := hpoint (X := genericScheme k M)
      ((Spec.map (CommRingCat.ofHom (E.comp (φ j)))) (IsLocalRing.closedPoint (ChartField l)))
    exact (congrArg b hl).symm.trans (hp.trans hk)
  obtain ⟨α, hα⟩ := ActualMultiplicationFieldNorm.exists_stalk_square b _ _ hη
  have hc (j : Fin r) : (φl j).comp α = E.comp (φ j) := by
    suffices he : CommRingCat.ofHom ((φl j).comp α) =
        CommRingCat.ofHom (E.comp (φ j)) from congrArg CommRingCat.Hom.hom he
    apply Spec.map_injective
    apply (cancel_mono ((genericScheme k M).fromSpecStalk
      (_root_.genericPoint (genericScheme k M)))).mp
    change Spec.map (CommRingCat.ofHom α ≫ CommRingCat.ofHom (φl j)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, ← hα]
    exact hs j
  refine ⟨α, ⟨hα, ?_, fun j g => RingHom.congr_fun (hc j) g⟩, ?_⟩
  · intro a
    apply (φl j).injective
    rw [show φl j (α (baseScalar (LaurentSeries k) (genericStructure k M) a)) =
        E (φ j (baseScalar (LaurentSeries k) (genericStructure k M) a)) from
      RingHom.congr_fun (hc j) _]
    rw [fieldMap_scalar k M (χ j) (hχ j).1 (φ j) (hφ j),
      fieldMap_scalar l Ml (χl j) (hχl j).1 (φl j) (hφl j)]
    exact RingHom.congr_fun
      (CoefficientFunctionFieldExpansionR0157.laurent_naturality k l ι ρ hρ E hE ell hell) a
  · intro β hβ
    exact ActualMultiplicationFieldNorm.fieldMap_unique b α β hα hβ.1

end ArithmeticThetaCoefficientNormDescentR0157

#print axioms ArithmeticThetaCoefficientNormDescentR0157.coefficient_function_field_expansion
