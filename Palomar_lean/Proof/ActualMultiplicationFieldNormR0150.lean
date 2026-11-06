module

public import FiniteEtaleLocalNormR0150
public import MultiplicationFiniteEtaleDegreeR0148

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeometricNormR0150
namespace ActualMultiplicationFieldNorm
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

omit [IsIntegral X] [IsIntegral Y] in
lemma exists_stalk_square (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    ∃ φ : Y.presheaf.stalk y →+* X.presheaf.stalk x,
      X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y := by
  subst y
  exact ⟨(f.stalkMap x).hom, (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm⟩

lemma exists_fieldMap (f : X ⟶ Y) [Surjective f] :
    ∃ φ : Y.functionField →+* X.functionField, IsFieldMap f φ := by
  have h : f (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq _ (genericPoint_spec Y)
    simpa only [Set.image_univ, Set.range_eq_univ.mpr f.surjective, closure_univ] using
      (genericPoint_spec X).image f.continuous
  exact exists_stalk_square f _ _ h

lemma fieldMap_unique (f : X ⟶ Y)
    (φ ψ : Y.functionField →+* X.functionField)
    (hφ : IsFieldMap f φ) (hψ : IsFieldMap f ψ) : ψ = φ := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  exact hψ.symm.trans hφ

local instance top_nonempty (Z : Scheme.{u}) [IsIntegral Z] : Nonempty (⊤ : Z.Opens) :=
  ⟨⟨genericPoint Z, trivial⟩⟩

lemma top_square (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField)
    (hφ : IsFieldMap f φ) :
    f.appTop ≫ X.germToFunctionField ⊤ =
      Y.germToFunctionField ⊤ ≫ CommRingCat.ofHom φ := by
  apply Spec.map_injective
  calc
    Spec.map (f.appTop ≫ X.germToFunctionField ⊤) =
        X.fromSpecStalk (genericPoint X) ≫ X.toSpecΓ ≫ Spec.map f.appTop := by
      rw [Spec.map_comp, Scheme.fromSpecStalk_toSpecΓ_assoc]
    _ = X.fromSpecStalk (genericPoint X) ≫ f ≫ Y.toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality]
    _ = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) ≫ Y.toSpecΓ := by
      rw [← Category.assoc, hφ, Category.assoc]
    _ = Spec.map (Y.germToFunctionField ⊤ ≫ CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, Scheme.fromSpecStalk_toSpecΓ]

lemma fieldMap_baseScalar (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) (f : X ⟶ X) (hf : f ≫ p = p)
    (φ : X.functionField →+* X.functionField) (hφ : IsFieldMap f φ) (a : F) :
    φ (baseScalar F p a) = baseScalar F p a := by
  have h := top_square f φ hφ
  have he : p.appTop ≫ f.appTop = p.appTop := by
    rw [← Scheme.Hom.comp_appTop, hf]
  have ha := congrArg (fun q : Γ(X, ⊤) ⟶ X.functionField =>
    q (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a))) h
  change X.germToFunctionField ⊤ (f.appTop (p.appTop _)) =
    φ (baseScalar F p a) at ha
  have hb := congrArg (fun q : Γ(Spec (CommRingCat.of F), ⊤) ⟶ Γ(X, ⊤) =>
    q ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a)) he
  change f.appTop (p.appTop _) = p.appTop _ at hb
  rw [hb] at ha
  exact ha.symm

lemma fieldNorm_image (φ : Y.functionField →+* X.functionField)
    (hfin : FiniteFieldMap φ) (b : Y.functionField) :
    fieldNorm φ (φ b) = b ^ fieldDegree φ := by
  letI := φ.toAlgebra
  letI : FiniteDimensional Y.functionField X.functionField := hfin
  exact Algebra.norm_algebraMap b

lemma fieldNorm_baseScalar (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) (f : X ⟶ X) (hf : f ≫ p = p)
    (φ : X.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (hfin : FiniteFieldMap φ) (a : F) :
    fieldNorm φ (baseScalar F p a) = baseScalar F p (a ^ fieldDegree φ) := by
  calc
    fieldNorm φ (baseScalar F p a) = fieldNorm φ (φ (baseScalar F p a)) := by
      rw [fieldMap_baseScalar F p f hf φ hφ]
    _ = (baseScalar F p a) ^ fieldDegree φ := fieldNorm_image φ hfin _
    _ = baseScalar F p (a ^ fieldDegree φ) := by simp only [baseScalar, map_pow]

end ActualMultiplicationFieldNorm
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ActualMultiplicationFieldNorm

/-- The actual multiplication map determines the finite extension and its scalar norm. -/
theorem actual_multiplication_field_norm :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (n : ℕ), 0 < n → ∃ φ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) φ ∧ ArithmeticThetaGeometricNormR0150.FiniteFieldMap φ ∧ ArithmeticThetaGeometricNormR0150.fieldDegree φ = n^2 ∧ (∀ a : LaurentSeries k, ArithmeticThetaGeometricNormR0150.fieldNorm φ (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) a) = ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) (a^(n^2))) ∧ (∀ ψ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) ψ → ψ = φ) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ n hn
  obtain ⟨hfinite, hetale, hsurj, hrank⟩ :=
    multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG n hn
  letI := hfinite
  letI := hetale
  letI := hsurj
  obtain ⟨φ, hφ⟩ := exists_fieldMap (multiplication k M G n)
  obtain ⟨hfin, hdeg, _⟩ := finite_etale_local_norm _ _ (multiplication k M G n) φ hφ
  have hd : fieldDegree φ = n^2 :=
    (hdeg (_root_.genericPoint (genericScheme k M))).symm.trans (hrank _)
  refine ⟨φ, hφ, hfin, hd, ?_, fun ψ hψ => fieldMap_unique _ φ ψ hφ hψ⟩
  intro a
  rw [fieldNorm_baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
    (multiplication k M G n) (MultiplicationDifferential.multiplication_over k M G n)
    φ hφ hfin a, hd]

#print axioms actual_multiplication_field_norm
end ArithmeticThetaGeometricNormR0150
