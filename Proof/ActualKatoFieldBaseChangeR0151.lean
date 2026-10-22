module

public import ActualKatoFunctionExistenceR0151
public import KatoDivisorFieldBaseChangeR0151
public import GeometricNormBaseChangeR0150

@[expose] public section

/-! Actual Kato functions commute with every specified geometric field base change. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKatoExistenceR0151
namespace ActualKatoFieldBaseChange
open CategoryTheory AlgebraicGeometry

/-- A compatible pair of endomorphisms over a cartesian structural square
forms a cartesian square. Both endomorphisms are the specified maps. -/
theorem endomorphism_cartesian {X Xb S Sb : Scheme.{u}}
    (p : X ⟶ S) (pb : Xb ⟶ Sb) (b : Xb ⟶ X) (i : Sb ⟶ S)
    (h : IsPullback b pb p i) (f : X ⟶ X) (fb : Xb ⟶ Xb)
    (hf : f ≫ p = p) (hfb : fb ≫ pb = pb) (hw : fb ≫ b = b ≫ f) :
    IsPullback b fb f b := by
  have hbig : IsPullback b (fb ≫ pb) (f ≫ p) i := by
    rw [hf, hfb]
    exact h
  exact hbig.of_bot hw.symm h

end ActualKatoFieldBaseChange
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147

/-- Existence and choice-independent naturality for actual Kato functions,
with every positive coprime multiplication norm. -/
theorem actual_kato_field_base_change :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (kb : Type u) [Field kb] [CharZero kb] (rb : ℕ) (hrb : 0 < rb) (h3b : 3 ≤ rb) (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower kb rb hrb) (heb : Even rb) (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model kb Tb) (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel kb Tb Mb) (sb : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme kb) Mb.X) (hsb : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift kb Mb (ArithmeticThetaIdentitySectionsR0138.zeroIndex rb hrb) 1 sb) (Gb : ArithmeticThetaMarkedGroupLawR0146.Law kb Mb) (hGb : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw kb Mb sb hsb.1 Gb) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb)] (ι : LaurentSeries k →+* LaurentSeries kb) (b : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsTateBaseChange k kb M Mb s hs.1 sb hsb.1 G Gb ι b → ∀ (α : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb))), ArithmeticThetaGeometricNormR0150.IsFieldMap b α → ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → (∃ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ∃ gb : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g ∧ ArithmeticThetaKatoExistenceR0151.IsKatoFunction kb Mb sb hsb.1 Gb c gb ∧ α g = gb) ∧ (∀ (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g → ArithmeticThetaKatoExistenceR0151.IsKatoFunction kb Mb sb hsb.1 Gb c (α g)) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _
    kb _ _ rb hrb h3b Tb heb Mb hMb sb hsb Gb hGb _ _ ι b hb α hα c hc hc6
  have hnatural (g : (genericScheme k M).functionField)
      (hg : IsKatoFunction k M s hs.1 G c g) :
      IsKatoFunction kb Mb sb hsb.1 Gb c (α g) := by
    refine ⟨kato_divisor_field_base_change k r hr h3 T he M hM s hs G hG
      kb rb hrb h3b Tb heb Mb hMb sb hsb Gb hGb ι b hb α hα c hc hc6 g hg.1, ?_⟩
    intro d hd hcd φb hφb
    obtain ⟨hfinite, hetale, hsurj, _⟩ :=
      multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG d hd
    letI := hfinite
    letI := hetale
    letI := hsurj
    obtain ⟨φ, hφ⟩ := ActualMultiplicationFieldNorm.exists_fieldMap
      (multiplication k M G d)
    have hcart : IsPullback b (multiplication kb Mb Gb d) (multiplication k M G d) b :=
      ActualKatoFieldBaseChange.endomorphism_cartesian
        (genericStructure k M) (genericStructure kb Mb) b
        (Spec.map (CommRingCat.ofHom ι)) hb.1
        (multiplication k M G d) (multiplication kb Mb Gb d)
        (MultiplicationDifferential.multiplication_over k M G d)
        (MultiplicationDifferential.multiplication_over kb Mb Gb d) (hb.2.2 d)
    have hnorm := geometric_norm_base_change
      (genericScheme k M) (genericScheme k M) (genericScheme kb Mb) (genericScheme kb Mb)
      (multiplication k M G d) (multiplication kb Mb Gb d) b b hcart
      φ φb α α hφ hφb hα hα g
    rw [hg.2 d hd hcd φ hφ] at hnorm
    exact hnorm.symm
  obtain ⟨g, hg, _⟩ := actual_kato_function_existence k r hr h3 T he M hM s hs G hG c hc hc6
  obtain ⟨gb, hgb, huniq⟩ := actual_kato_function_existence
    kb rb hrb h3b Tb heb Mb hMb sb hsb Gb hGb c hc hc6
  exact ⟨⟨g, gb, hg, hgb, huniq (α g) (hnatural g hg)⟩, hnatural⟩

#print axioms ActualKatoFieldBaseChange.endomorphism_cartesian
#print axioms actual_kato_field_base_change
end ArithmeticThetaKatoExistenceR0151
