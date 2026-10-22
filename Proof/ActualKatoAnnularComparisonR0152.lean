module

public import KatoAnnularOverlapR0152
public import KatoAnnularDivisorR0152
public import CompletedModelChartMapsR0152
public import LocalThetaRatioConstantR0088
public import ActualKatoFunctionExistenceR0151

@[expose] public section

/-! The actual normalized Kato function differs from the full annular theta
products by a unique nonzero structural Laurent scalar. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152

/-- Constant comparison on every completed chart of the actual model. -/
theorem actual_kato_annular_comparison :
∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c), ∃ (χ : Fin (2*c) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (φ : Fin (2*c) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) ∧ (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) ∧ ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∃! v : LaurentSeries k, v ≠ 0 ∧ ∀ j : Fin (2*c), ArithmeticThetaCyclicConstantsR0088.ScalarValue k v (ArithmeticThetaRatioRegularityR0067.ratio k (φ j g) (ArithmeticThetaRatioRegularityR0067.LocalTheta k c (ζ : k) hc hcop hζ j))) := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ
  classical
  choose χ hχ using fun j =>
    (completed_model_chart_maps k (2*c) hr h3 T M hM j).exists
  choose φ hφ using fun j =>
    (completed_chart_field_maps k (2*c) hr h3 T M hM j (χ j) (hχ j)).exists
  have hfield : ∀ j, IsChartFieldMap k M (χ j) (φ j) := fun j => (hφ j).1
  have he : Even (2*c) := ⟨c, by omega⟩
  obtain ⟨g, hg, _⟩ := ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
    k (2*c) hr h3 T he M hM s hs G hG c hc hcop
  refine ⟨χ, φ, g, hχ, hfield, hg, ?_⟩
  exact ArithmeticThetaCyclicConstantsR0088.local_theta_ratio_constant
    k c (ζ : k) hc hcop hζ hr (fun j => φ j g)
    (kato_annular_overlap k (2*c) hr h3 T M hM χ hχ φ hfield g)
    (kato_annular_divisor k c hc hcop hr h3 T M hM s hs G hG ζ hζ
      χ hχ φ hfield g hg.1)

#print axioms actual_kato_annular_comparison
end ArithmeticThetaKatoAnnularR0152
