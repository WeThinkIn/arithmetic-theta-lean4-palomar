module

public import KatoExistenceDefinitionsR0151
public import GeometricNormCompositionR0151
public import CoprimeTorsionDivisorNormR0150
public import ActualNormalizedKatoUniquenessR0150

@[expose] public section

/-! Simultaneous normalization over the original structural Laurent field. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKatoExistenceR0151
namespace SimultaneousKatoNormalization
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

lemma schemeNsmul_comp {F : Type u} [Field F] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of F)} (G : WeierstrassProjModel.RelativeGroupLaw F p)
    (a b : ℕ) : G.schemeNsmul a ≫ G.schemeNsmul b = G.schemeNsmul (a*b) := by
  have h := congrArg Subtype.val
    (CoprimeTorsion.nsmul_mul G p b a ⟨𝟙 X, Category.id_comp p⟩)
  simpa only [← comp_schemeNsmul, Category.id_comp] using h

lemma commuting_norms {X : Scheme.{u}} [IsIntegral X]
    (f h : X ⟶ X) [IsFinite f] [Etale f] [Surjective f]
    [IsFinite h] [Etale h] [Surjective h]
    (hf : f ≫ h = h ≫ f)
    (φ ψ : X.functionField →+* X.functionField)
    (hφ : IsFieldMap f φ) (hψ : IsFieldMap h ψ) (z : X.functionField) :
    fieldNorm ψ (fieldNorm φ z) = fieldNorm φ (fieldNorm ψ z) := by
  obtain ⟨h₁, _, hn₁⟩ := geometric_norm_composition X X X f h φ ψ hφ hψ
  obtain ⟨h₂, _, hn₂⟩ := geometric_norm_composition X X X h f ψ φ hψ hφ
  have he : ψ.comp φ = φ.comp ψ :=
    ActualMultiplicationFieldNorm.fieldMap_unique (f ≫ h) _ _ h₁ (hf.symm ▸ h₂)
  rw [hn₁, hn₂, he]

def scalarHom {X : Scheme.{u}} [IsIntegral X] (F : Type u) [Field F]
    (p : X ⟶ Spec (.of F)) : F →+* X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom)

lemma scalarHom_apply {X : Scheme.{u}} [IsIntegral X] (F : Type u) [Field F]
    (p : X ⟶ Spec (.of F)) (a : F) : scalarHom F p a = baseScalar F p a := rfl

def normHom {X : Scheme.{u}} [IsIntegral X]
    (φ : X.functionField →+* X.functionField) : X.functionField →* X.functionField := by
  letI := φ.toAlgebra
  exact Algebra.norm X.functionField

lemma normHom_apply {X : Scheme.{u}} [IsIntegral X]
    (φ : X.functionField →+* X.functionField) (z : X.functionField) :
    normHom φ z = fieldNorm φ z := rfl

lemma explicit_normalization {F L : Type*} [Field F] [Field L]
    (ι : F →+* L) (N₂ N₃ : L →* L)
    (h₂ : ∀ a, N₂ (ι a) = ι (a^4)) (h₃ : ∀ a, N₃ (ι a) = ι (a^9))
    (g : L) (hg : g ≠ 0) (A B : F) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAg : N₂ g = ι A * g) (hBg : N₃ g = ι B * g)
    (hc : N₃ (N₂ g) = N₂ (N₃ g)) :
    ∃ a : F, a ≠ 0 ∧ N₂ (ι a * g) = ι a * g ∧ N₃ (ι a * g) = ι a * g := by
  have hAB : A^9 * B = B^4 * A := by
    apply ι.injective
    apply mul_right_cancel₀ hg
    simpa only [hAg, hBg, map_mul, h₂, h₃, mul_assoc] using hc
  have hcompat : A^8 = B^3 := by
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    calc
      A^8 * (A*B) = A^9 * B := by ring
      _ = B^4 * A := hAB
      _ = B^3 * (A*B) := by ring
  let a := B / A^3
  have ha : a ≠ 0 := div_ne_zero hB (pow_ne_zero _ hA)
  have ha₃ : a^3 * A = 1 := by
    calc
      a^3 * A = B^3 / A^8 := by dsimp [a]; field_simp [hA]
      _ = 1 := by rw [← hcompat]; exact div_self (pow_ne_zero _ hA)
  have ha₈ : a^8 * B = 1 := by
    calc
      a^8 * B = (B^3)^3 / (A^8)^3 := by dsimp [a]; field_simp [hA]
      _ = 1 := by rw [hcompat]; exact div_self (pow_ne_zero _ (pow_ne_zero _ hB))
  have ha₄ : a^4 * A = a := by
    calc
      a^4 * A = a * (a^3 * A) := by ring
      _ = a := by rw [ha₃, mul_one]
  have ha₉ : a^9 * B = a := by
    calc
      a^9 * B = a * (a^8 * B) := by ring
      _ = a := by rw [ha₈, mul_one]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [map_mul, h₂, hAg, ← mul_assoc, ← map_mul, ha₄]
  · rw [map_mul, h₃, hBg, ← mul_assoc, ← map_mul, ha₉]

lemma exists_defect {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : Type u) [Field F] (p : X ⟶ Spec (.of F))
    [SmoothOfRelativeDimension 1 p] [IsProper p]
    [GeometricallyReduced p] [GeometricallyConnected p]
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (hord : ∀ x, Scheme.ord f x = Scheme.ord g x) :
    ∃ A : F, A ≠ 0 ∧ f = scalarHom F p A * g := by
  obtain ⟨A, hA⟩ := ActualNormalizedKatoUniqueness.exists_baseScalar_of_ord_zero F p
    (f/g) (div_ne_zero hf hg)
    (ActualNormalizedKatoUniqueness.ord_div_eq_zero f g hf hg hord)
  change scalarHom F p A = f/g at hA
  have hAz : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hA
    exact div_ne_zero hf hg hA.symm
  exact ⟨A, hAz, (div_eq_iff hg).mp hA.symm⟩

end SimultaneousKatoNormalization
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open SimultaneousKatoNormalization

/-- Every raw Kato function is normalized by one nonzero scalar over the
original Laurent field, simultaneously for both actual multiplication norms. -/
theorem simultaneous_kato_normalization :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∀ (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c g → ∃ a : LaurentSeries k, a ≠ 0 ∧ ∀ (φ₂ φ₃ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G 2) φ₂ → ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G 3) φ₃ → (ArithmeticThetaGeometricNormR0150.fieldNorm φ₂ (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a * g) = (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a * g) ∧ ArithmeticThetaGeometricNormR0150.fieldNorm φ₃ (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a * g) = (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a * g)) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _ c hc hc6 g hg
  letI := generic_relative_one k h3 M hM s hs
  letI := generic_geometricallyIntegral k h3 M hM
  letI := algebraized_geometric_connectedness k r hr h3 T M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  obtain ⟨ψ₂, hψ₂, _, _, hscalar₂, huniq₂⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 2 (by decide)
  obtain ⟨ψ₃, hψ₃, _, _, hscalar₃, huniq₃⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 3 (by decide)
  have hc2 : Nat.Coprime c 2 := hc6.of_dvd_right (by decide)
  have hc3 : Nat.Coprime c 3 := hc6.of_dvd_right (by decide)
  have hn₂ := coprime_torsion_divisor_norm k r hr h3 T he M hM s hs G hG
    c 2 hc (by decide) hc2 ψ₂ hψ₂ g hg.1 hg.2
  have hn₃ := coprime_torsion_divisor_norm k r hr h3 T he M hM s hs G hG
    c 3 hc (by decide) hc3 ψ₃ hψ₃ g hg.1 hg.2
  obtain ⟨A, hA, hAg⟩ := exists_defect (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
    (fieldNorm ψ₂ g) g hn₂.1 hg.1 (fun x => (hn₂.2 x).trans (hg.2 x).symm)
  obtain ⟨B, hB, hBg⟩ := exists_defect (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
    (fieldNorm ψ₃ g) g hn₃.1 hg.1 (fun x => (hn₃.2 x).trans (hg.2 x).symm)
  have hcomm : fieldNorm ψ₃ (fieldNorm ψ₂ g) = fieldNorm ψ₂ (fieldNorm ψ₃ g) := by
    obtain ⟨hf₂, he₂, hs₂, _⟩ :=
      multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG 2 (by decide)
    obtain ⟨hf₃, he₃, hs₃, _⟩ :=
      multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG 3 (by decide)
    letI := hf₂
    letI := he₂
    letI := hs₂
    letI := hf₃
    letI := he₃
    letI := hs₃
    apply commuting_norms (multiplication k M G 2) (multiplication k M G 3)
      ?_ ψ₂ ψ₃ hψ₂ hψ₃ g
    change G.schemeNsmul 2 ≫ G.schemeNsmul 3 = G.schemeNsmul 3 ≫ G.schemeNsmul 2
    rw [schemeNsmul_comp, schemeNsmul_comp]
  obtain ⟨a, ha, ha₂, ha₃⟩ := explicit_normalization
    (scalarHom (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)) (normHom ψ₂) (normHom ψ₃)
    (fun a => (show fieldNorm ψ₂ (baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) a) =
      baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) (a^4) from hscalar₂ a))
    (fun a => (show fieldNorm ψ₃ (baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) a) =
      baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) (a^9) from hscalar₃ a))
    g hg.1 A B hA hB hAg hBg hcomm
  refine ⟨a, ha, ?_⟩
  intro φ₂ φ₃ hφ₂ hφ₃
  rw [huniq₂ φ₂ hφ₂, huniq₃ φ₃ hφ₃]
  exact ⟨ha₂, ha₃⟩

#print axioms simultaneous_kato_normalization
end ArithmeticThetaKatoExistenceR0151
