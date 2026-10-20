module

public import SplitDeckExhaustionR0153
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
namespace SplitMultiplicationNorm

/-- A full labelled family of automorphisms computes the determinant norm for μ. -/
lemma norm_of_exhaustion (K L : Type u) [Field K] [Field L] (μ : K →+* L)
    (hfin : letI := μ.toAlgebra; FiniteDimensional K L)
    (I : Type*) [Fintype I] (τ : I → (L ≃+* L))
    (hτ : ∀ i, (τ i).toRingHom.comp μ = μ)
    (hexhaust : ∀ ψ : L →+* L, ψ.comp μ = μ ↔ ∃! i, ψ = (τ i).toRingHom)
    (hcard : Fintype.card I = (letI := μ.toAlgebra; Module.finrank K L))
    (g : L) :
    μ (letI := μ.toAlgebra; Algebra.norm K g) = ∏ i, τ i g := by
  classical
  letI := μ.toAlgebra
  letI : FiniteDimensional K L := hfin
  let f : I → (L ≃ₐ[K] L) := fun i =>
    { τ i with commutes' := fun x => DFunLike.congr_fun (hτ i) x }
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      obtain ⟨a, ha, hu⟩ := (hexhaust (τ i).toRingHom).1 (hτ i)
      exact (hu i rfl).trans (hu j (congrArg (fun e : L ≃ₐ[K] L => e.toRingHom) hij)).symm
    · intro e
      have he : e.toRingHom.comp μ = μ := by
        ext x
        exact e.commutes x
      obtain ⟨i, hi, _⟩ := (hexhaust e.toRingHom).1 he
      refine ⟨i, ?_⟩
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hi.symm x
  let e : I ≃ (L ≃ₐ[K] L) := Equiv.ofBijective f hf
  have hdeg : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, hcard]
  letI : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hdeg
  calc
    μ (Algebra.norm K g) = ∏ a : (L ≃ₐ[K] L), a g :=
      Algebra.norm_eq_prod_automorphisms K g
    _ = ∏ i, τ i g := (e.prod_comp (fun a => a g)).symm

end SplitMultiplicationNorm
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaHodgeFourTorsionR0147
open ActualMultiplicationFieldNorm MarkedFieldAction SplitDeckExhaustion

/-- The pulled-back geometric norm is the product over the actual split translations. -/
theorem split_multiplication_norm :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv) (σ : Fin r → kˣ → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) ≃+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)))) (hσ : ArithmeticThetaSplitNormR0153.IsFieldAction k M rot scal inv ha σ) (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) d) (μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (hμ : ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ), ∀ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), μ (ArithmeticThetaGeometricNormR0150.fieldNorm μ g) = ∏ ab : Fin d × Fin d, σ (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val) g := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ rot scal inv ha σ hσ d hd hdiv ζ hζ μ hμ g
  obtain ⟨ν, hν, hfin, hdeg, _, _⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG d hd
  have hνμ : ν = μ := fieldMap_unique _ _ _ hμ hν
  subst ν
  let τ : Fin d × Fin d → ((genericScheme k M).functionField ≃+* (genericScheme k M).functionField) :=
    fun ab => σ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)
  have hτ : ∀ ab, (τ ab).toRingHom.comp μ = μ := by
    intro ab
    have hh := field_comp (hσ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)) hμ
    rw [translation_deck k h3 he M hM s hs G hG rot scal inv ha d hd hdiv ζ hζ ab] at hh
    exact fieldMap_unique _ _ _ hμ hh
  apply SplitMultiplicationNorm.norm_of_exhaustion
    (genericScheme k M).functionField (genericScheme k M).functionField μ hfin
    (Fin d × Fin d) τ hτ
    (split_deck_exhaustion k r hr h3 T he M hM s hs G hG rot scal inv ha σ hσ d hd hdiv ζ hζ μ hμ)
    _ g
  simpa only [fieldDegree, Fintype.card_prod, Fintype.card_fin, pow_two] using hdeg.symm

#print axioms split_multiplication_norm
end ArithmeticThetaSplitNormR0153
