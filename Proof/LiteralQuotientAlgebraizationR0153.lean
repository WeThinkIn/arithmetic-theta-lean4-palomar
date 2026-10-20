module

public import ActualKatoAnnularComparisonR0152

@[expose] public section

/-! Algebraization of the literal complete quotient on every specified chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
open AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaKatoExistenceR0151 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps
open ArithmeticThetaCyclicConstantsR0088 ArithmeticThetaRatioRegularityR0067

/-- The literal quotient determines a unique actual rational function with its Kato divisor. -/
theorem literal_quotient_algebraization :
∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hr : 0 < 2*c) (h3 : 3 ≤ 2*c) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*c) hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*c) hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (χ : Fin (2*c) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin (2*c) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)), ∃! f : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c f ∧ ∀ j : Fin (2*c), φ j f = ArithmeticThetaRatioRegularityR0067.LocalTheta k c (ζ : k) hc hcop hζ j := by
  intro k _ _ c hc hcop hr h3 T M hM s hs G hG _ _ ζ hζ χ hχ φ hφ
  have he : Even (2*c) := ⟨c, by omega⟩
  obtain ⟨g, hg, _⟩ := actual_kato_function_existence
    k (2*c) hr h3 T he M hM s hs G hG c hc hcop
  obtain ⟨v, ⟨hv, hvg⟩, _⟩ := local_theta_ratio_constant
    k c (ζ : k) hc hcop hζ hr (fun j => φ j g)
    (kato_annular_overlap k (2*c) hr h3 T M hM χ hχ φ hφ g)
    (kato_annular_divisor k c hc hcop hr h3 T M hM s hs G hG ζ hζ
      χ hχ φ hφ g hg.1)
  let ι := scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
  let f := ι v⁻¹ * g
  have hι : ι v⁻¹ ≠ 0 := (map_ne_zero ι).mpr (inv_ne_zero hv)
  have hf : HasKatoDivisor k M s hs.1 G c f := by
    refine ⟨mul_ne_zero hι hg.1.1, ?_⟩
    intro x
    change Scheme.ord (ι v⁻¹ * g) x = _
    rw [Scheme.ord_mul hι hg.1.1,
      ActualKatoFunctionExistence.scalar_order (X := genericScheme k M) (LaurentSeries k)
        (genericStructure k M) v⁻¹ (inv_ne_zero hv), zero_add]
    exact hg.1.2 x
  have hexp : ∀ j, φ j f = LocalTheta k c (ζ : k) hc hcop hζ j := by
    intro j
    have hratio : laurentInclusion k v =
        φ j g / LocalTheta k c (ζ : k) hc hcop hζ j :=
      (Classical.choose_spec (laurent_scalar_graph k)).1.2 _ _ |>.mp (hvg j)
    have hv' : laurentInclusion k v ≠ 0 := (map_ne_zero _).mpr hv
    have ht : LocalTheta k c (ζ : k) hc hcop hζ j ≠ 0 := by
      intro ht
      rw [ht, div_zero] at hratio
      exact hv' hratio
    change φ j (ι v⁻¹ * g) = _
    rw [map_mul, show φ j (ι v⁻¹) = laurentInclusion k v⁻¹ from
      fieldMap_scalar k M (χ j) (hχ j).1 (φ j) (hφ j) v⁻¹,
      map_inv₀, (div_eq_iff ht).mp hratio.symm]
    rw [← mul_assoc, inv_mul_cancel₀ hv', one_mul]
  refine ⟨f, ⟨hf, hexp⟩, ?_⟩
  intro f' hf'
  exact (φ ⟨0, hr⟩).injective ((hf'.2 ⟨0, hr⟩).trans (hexp ⟨0, hr⟩).symm)

#print axioms literal_quotient_algebraization
end ArithmeticThetaSplitNormR0153
