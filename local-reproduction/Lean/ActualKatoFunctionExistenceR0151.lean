import ActualKatoDivisorPrincipalR0151
import SimultaneousKatoNormalizationR0151

/-! Existence and uniqueness with every positive coprime multiplication norm. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKatoExistenceR0151
namespace ActualKatoFunctionExistence
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150
open SimultaneousKatoNormalization

lemma scalar_order {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : Type u) [Field F] (p : X ⟶ Spec (.of F))
    (a : F) (ha : a ≠ 0) (x : X) :
    Scheme.ord (scalarHom F p a) x = 0 := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact Scheme.ord_of_isUnit
    (((isUnit_iff_ne_zero.mpr ha).map (Scheme.ΓSpecIso (.of F)).inv.hom).map p.appTop.hom)
    (by trivial)

end ActualKatoFunctionExistence
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open SimultaneousKatoNormalization ActualKatoFunctionExistence

/-- The actual generic Tate curve has a unique Kato function invariant under
all positive multiplication norms prime to c, including multiplication by one. -/
theorem actual_kato_function_existence :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _ c hc hc6
  obtain ⟨g, hg⟩ := actual_kato_divisor_principal k r hr h3 T he M hM s hs G hG c hc hc6
  obtain ⟨a, ha, hnorm⟩ := simultaneous_kato_normalization
    k r hr h3 T he M hM s hs G hG c hc hc6 g hg
  let ι := scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
  let f := ι a * g
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  have hf : HasKatoDivisor k M s hs.1 G c f := by
    refine ⟨mul_ne_zero hιa hg.1, ?_⟩
    intro x
    change Scheme.ord (ι a * g) x = _
    rw [Scheme.ord_mul hιa hg.1, scalar_order (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) a ha, zero_add]
    exact hg.2 x
  obtain ⟨φ₂, hφ₂, _, _, _, _⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 2 (by decide)
  obtain ⟨φ₃, hφ₃, _, _, _, _⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 3 (by decide)
  obtain ⟨hf₂, hf₃⟩ := hnorm φ₂ φ₃ hφ₂ hφ₃
  change fieldNorm φ₂ f = f at hf₂
  change fieldNorm φ₃ f = f at hf₃
  have hc2 : Nat.Coprime c 2 := hc6.of_dvd_right (by decide)
  have hc3 : Nat.Coprime c 3 := hc6.of_dvd_right (by decide)
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · intro d hd hcd φ hφ
    have hN := coprime_torsion_divisor_norm k r hr h3 T he M hM s hs G hG
      c d hc hd hcd φ hφ f hf.1 hf.2
    have hcomm (n : ℕ) (hn : 0 < n)
        (ψ : (genericScheme k M).functionField →+* (genericScheme k M).functionField)
        (hψ : IsFieldMap (multiplication k M G n) ψ) :
        fieldNorm ψ (fieldNorm φ f) = fieldNorm φ (fieldNorm ψ f) := by
      obtain ⟨hfd, hed, hsd, _⟩ :=
        multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG d hd
      obtain ⟨hfn, hen, hsn, _⟩ :=
        multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG n hn
      letI := hfd
      letI := hed
      letI := hsd
      letI := hfn
      letI := hen
      letI := hsn
      apply commuting_norms (multiplication k M G d) (multiplication k M G n)
        ?_ φ ψ hφ hψ f
      change G.schemeNsmul d ≫ G.schemeNsmul n = G.schemeNsmul n ≫ G.schemeNsmul d
      rw [schemeNsmul_comp, schemeNsmul_comp, Nat.mul_comm d n]
    apply actual_normalized_kato_uniqueness k r hr h3 T he M hM s hs G hG
      φ₂ φ₃ hφ₂ hφ₃ (fieldNorm φ f) f hN.1 hf.1
      (fun x => (hN.2 x).trans (hf.2 x).symm)
    · rw [hcomm 2 (by decide) φ₂ hφ₂, hf₂]
    · exact hf₂
    · rw [hcomm 3 (by decide) φ₃ hφ₃, hf₃]
    · exact hf₃
  · intro f' hf'
    exact actual_normalized_kato_uniqueness k r hr h3 T he M hM s hs G hG
      φ₂ φ₃ hφ₂ hφ₃ f' f hf'.1.1 hf.1
      (fun x => (hf'.1.2 x).trans (hf.2 x).symm)
      (hf'.2 2 (by decide) hc2 φ₂ hφ₂) hf₂
      (hf'.2 3 (by decide) hc3 φ₃ hφ₃) hf₃

#print axioms actual_kato_function_existence
end ArithmeticThetaKatoExistenceR0151
