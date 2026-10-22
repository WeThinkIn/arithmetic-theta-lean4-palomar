module

public import CompletedActionEquivarianceR0153
public import SplitMultiplicationNormR0153
public import CompletedScalingExtensionR0153

@[expose] public section

/-! The actual completed expansion of the pulled-back multiplication norm.
The geometric maps, completed scalings and field action are constructed from
proved providers; the final identity holds for every rational function. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153

/-- Completed-chart product formula for the actual split multiplication norm. -/
theorem completed_norm_product :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) d), ∃ (μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (e : kˣ → (ArithmeticThetaKatoAnnularR0152.Chart k ≃+* ArithmeticThetaKatoAnnularR0152.Chart k)) (E : kˣ → (ArithmeticThetaKatoAnnularR0152.ChartField k ≃+* ArithmeticThetaKatoAnnularR0152.ChartField k)), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ ∧ (∀ a, ArithmeticThetaSplitNormR0153.IsScaling k a (e a) ∧ ArithmeticThetaSplitNormR0153.ExtendsScaling k (e a) (E a)) ∧ (∀ (j : Fin r) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), φ j (μ (ArithmeticThetaGeometricNormR0150.fieldNorm μ g)) = ∏ ab : Fin d × Fin d, E (ζ ^ ab.2.val) (φ (ArithmeticThetaSplitNormR0153.shift (hr := hr) j (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1)) g)) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ rot scal inv ha χ hχ φ hφ d hd hdiv ζ hζ
  classical
  obtain ⟨μ, hμ, _⟩ :=
    ArithmeticThetaGeometricNormR0150.actual_multiplication_field_norm
      k r hr h3 T he M hM s hs G hG d hd
  obtain ⟨σ, hσ, _⟩ :=
    marked_field_action k r hr h3 T he M hM s hs G hG rot scal inv ha
  have hex : ∀ a : kˣ, ∃ e : ArithmeticThetaKatoAnnularR0152.Chart k ≃+*
      ArithmeticThetaKatoAnnularR0152.Chart k,
      ∃ E : ArithmeticThetaKatoAnnularR0152.ChartField k ≃+*
        ArithmeticThetaKatoAnnularR0152.ChartField k,
        IsScaling k a e ∧ ExtendsScaling k e E := by
    intro a
    obtain ⟨e, ⟨he, hE⟩, _⟩ := completed_scaling_extension k a
    obtain ⟨E, hE, _⟩ := hE
    exact ⟨e, E, he, hE⟩
  choose e E heE using hex
  refine ⟨μ, e, E, hμ, heE, ?_⟩
  intro j g
  rw [split_multiplication_norm k r hr h3 T he M hM s hs G hG
    rot scal inv ha σ hσ.1 d hd hdiv ζ hζ μ hμ g, map_prod]
  apply Finset.prod_congr rfl
  intro ab _
  exact completed_action_equivariance k r hr h3 T he M hM rot scal inv ha
    σ hσ.1 χ hχ φ hφ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)
    (e (ζ ^ ab.2.val)) (E (ζ ^ ab.2.val))
    (heE (ζ ^ ab.2.val)).1 (heE (ζ ^ ab.2.val)).2 j g

#print axioms completed_norm_product
end ArithmeticThetaSplitNormR0153
