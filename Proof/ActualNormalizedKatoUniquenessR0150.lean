module

public import ActualMultiplicationFieldNormR0150
public import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf
public import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeometricNormR0150
namespace ActualNormalizedKatoUniqueness
open CategoryTheory AlgebraicGeometry

open TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

local instance top_nonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨_root_.genericPoint X, trivial⟩⟩

lemma ord_div_eq_zero (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (hord : ∀ x, Scheme.ord f x = Scheme.ord g x) :
    ∀ x, Scheme.ord (f / g) x = 0 := by
  intro x
  have h := Scheme.ord_mul (x := x) (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ _ hg, hord x] at h
  omega

lemma exists_section_of_ord_zero (K : Type u) [Field K]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 p]
    (q : X.functionField) (hq : q ≠ 0) (hord : ∀ x, Scheme.ord q x = 0) :
    ∃ t : Γ(X, ⊤), X.germToFunctionField ⊤ t = q := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨_root_.genericPoint X, trivial⟩⟩
  suffices h : q ∈ (algebraMap Γ(X, ⊤) X.functionField).range from h
  rw [Scheme.Opens.range_algebraMap_functionField_eq_iInf]
  refine Subring.mem_iInf.mpr fun x => Subring.mem_iInf.mpr fun _ => ?_
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set X)) ⟨x, subset_closure (Set.mem_singleton x)⟩
    isClosed_closure.isLocallyClosed
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed p y hyclosed
  have hyco : Order.coheight y = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk y)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hv : Ring.ordFrac (X.presheaf.stalk y) q = 1 := by
    exact
      (Scheme.ord_eq_iff hyco hq).mp (hord y)
  have hm : q ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk y)) := hv
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hm
  obtain ⟨a, _, ha⟩ := hm
  refine ⟨X.presheaf.stalkSpecializes hxy a, ?_⟩
  change (X.presheaf.stalkSpecializes ((_root_.genericPoint_spec X).specializes trivial))
    (X.presheaf.stalkSpecializes hxy a) = q
  rw [← ConcreteCategory.comp_apply, X.presheaf.stalkSpecializes_comp]
  exact ha

lemma exists_baseScalar_of_ord_zero (K : Type u) [Field K]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 p]
    [IsProper p] [GeometricallyReduced p] [GeometricallyConnected p]
    (q : X.functionField) (hq : q ≠ 0) (hord : ∀ x, Scheme.ord q x = 0) :
    ∃ a : K, baseScalar K p a = q := by
  obtain ⟨t, ht⟩ := exists_section_of_ord_zero K p q hq hord
  obtain ⟨b, hb⟩ :=
    (bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected p).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom b, ?_⟩
  simpa only [baseScalar, Iso.hom_inv_id_apply, hb] using ht

omit [IsLocallyNoetherian X] in
lemma norm_quotient_fixed (φ : X.functionField →+* X.functionField)
    (f g : X.functionField) (hg : g ≠ 0)
    (hfN : fieldNorm φ f = f) (hgN : fieldNorm φ g = g) :
    fieldNorm φ (f / g) = f / g := by
  letI := φ.toAlgebra
  apply mul_right_cancel₀ hg
  calc
    fieldNorm φ (f / g) * g =
        fieldNorm φ (f / g) * fieldNorm φ g := by rw [hgN]
    _ = fieldNorm φ ((f / g) * g) := (map_mul (Algebra.norm X.functionField) _ _).symm
    _ = f := by rw [div_mul_cancel₀ _ hg, hfN]
    _ = (f / g) * g := (div_mul_cancel₀ _ hg).symm

lemma eq_one_of_four_nine {F : Type u} [Field F] (q : F) (hq : q ≠ 0)
    (h4 : q^4 = q) (h9 : q^9 = q) : q = 1 := by
  have h3 : q^3 = 1 := by
    apply mul_right_cancel₀ hq
    simpa only [← pow_succ, one_mul] using h4
  calc
    q = q^9 := h9.symm
    _ = (q^3)^3 := by rw [← pow_mul]
    _ = 1 := by rw [h3, one_pow]

end ActualNormalizedKatoUniqueness
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ActualNormalizedKatoUniqueness

/-- Equal divisors and the genuine [2] and [3] norms determine a nonzero
rational function uniquely on the actual generic Tate curve. -/
theorem actual_normalized_kato_uniqueness :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (φ₂ φ₃ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G 2) φ₂ → ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G 3) φ₃ → ∀ (f g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), f ≠ 0 → g ≠ 0 → (∀ x : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M), AlgebraicGeometry.Scheme.ord f x = AlgebraicGeometry.Scheme.ord g x) → ArithmeticThetaGeometricNormR0150.fieldNorm φ₂ f = f → ArithmeticThetaGeometricNormR0150.fieldNorm φ₂ g = g → ArithmeticThetaGeometricNormR0150.fieldNorm φ₃ f = f → ArithmeticThetaGeometricNormR0150.fieldNorm φ₃ g = g → f = g := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _ φ₂ φ₃ hφ₂ hφ₃ f g hf hg hord hf₂ hg₂ hf₃ hg₃
  letI := generic_relative_one k h3 M hM s hs
  letI := generic_geometricallyIntegral k h3 M hM
  letI := algebraized_geometric_connectedness k r hr h3 T M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  obtain ⟨a, ha⟩ := exists_baseScalar_of_ord_zero (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
    (f / g) (div_ne_zero hf hg) (ord_div_eq_zero f g hf hg hord)
  obtain ⟨ψ₂, hψ₂, hfin₂, hdeg₂, hscalar₂, huniq₂⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 2 (by decide)
  obtain ⟨ψ₃, hψ₃, hfin₃, hdeg₃, hscalar₃, huniq₃⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG 3 (by decide)
  have he₂ := huniq₂ φ₂ hφ₂
  have he₃ := huniq₃ φ₃ hφ₃
  have hn₂ := norm_quotient_fixed φ₂ f g hg hf₂ hg₂
  have hn₃ := norm_quotient_fixed φ₃ f g hg hf₃ hg₃
  rw [he₂, ← ha, hscalar₂] at hn₂
  rw [he₃, ← ha, hscalar₃] at hn₃
  have hp4 : (f / g)^4 = f / g := by
    rw [← ha]
    simpa only [baseScalar, map_pow, show (2 : ℕ)^2 = 4 from rfl] using hn₂
  have hp9 : (f / g)^9 = f / g := by
    rw [← ha]
    simpa only [baseScalar, map_pow, show (3 : ℕ)^2 = 9 from rfl] using hn₃
  exact (div_eq_one_iff_eq hg).mp (eq_one_of_four_nine (f / g) (div_ne_zero hf hg) hp4 hp9)

#print axioms actual_normalized_kato_uniqueness
end ArithmeticThetaGeometricNormR0150
