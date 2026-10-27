import LiteralNormDescentR0157
import LiteralQuotientAlgebraizationR0153

/-! Exact identification of the actual normalized Kato function on the 2c-model. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
open ArithmeticThetaKatoExistenceR0151 ArithmeticThetaGeometricNormR0150

/-- The unique normalized Kato function has the complete literal annular expansions. -/
theorem exact_kato_annular_formula :
∀ (k : Type) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin (2*c) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin (2*c) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) , ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ (∀ j : Fin (2*c), φ j g = ArithmeticThetaRatioRegularityR0067.LocalTheta k c (ζ : k) hc hcop hζ j) := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ
  obtain ⟨f, ⟨hf, hexp⟩, _⟩ :=
    ArithmeticThetaSplitNormR0153.literal_quotient_algebraization
      k c hc hcop hr h3 T M hM s hs G hG ζ hζ χ hχ φ hφ
  have hnorm := literal_norm_descent
    k c hc hcop hr h3 T M hM s hs G hG ζ hζ χ hχ φ hφ f hexp
  have hK : IsKatoFunction k M s hs.1 G c f := ⟨hf, hnorm⟩
  refine ⟨f, ⟨hK, hexp⟩, ?_⟩
  intro g hg
  have he : Even (2*c) := ⟨c, by omega⟩
  obtain ⟨μ₂, hμ₂, _, _, _, _⟩ :=
    actual_multiplication_field_norm k (2*c) hr h3 T he M hM s hs G hG 2 (by decide)
  obtain ⟨μ₃, hμ₃, _, _, _, _⟩ :=
    actual_multiplication_field_norm k (2*c) hr h3 T he M hM s hs G hG 3 (by decide)
  have hc2 : Nat.Coprime c 2 := hcop.of_dvd_right (by decide)
  have hc3 : Nat.Coprime c 3 := hcop.of_dvd_right (by decide)
  exact actual_normalized_kato_uniqueness k (2*c) hr h3 T he M hM s hs G hG
    μ₂ μ₃ hμ₂ hμ₃ g f hg.1.1.1 hf.1
    (fun x => (hg.1.1.2 x).trans (hf.2 x).symm)
    (hg.1.2 2 (by decide) hc2 μ₂ hμ₂) (hnorm 2 (by decide) hc2 μ₂ hμ₂)
    (hg.1.2 3 (by decide) hc3 μ₃ hμ₃) (hnorm 3 (by decide) hc3 μ₃ hμ₃)

#print axioms exact_kato_annular_formula
end ArithmeticThetaCoefficientNormDescentR0157
