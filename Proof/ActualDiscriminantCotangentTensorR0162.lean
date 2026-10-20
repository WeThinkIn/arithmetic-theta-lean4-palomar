module

public import CanonicalDifferentialTensorR0162
public import TaylorGradedCoefficientR0162
public import ActualOriginAugmentedTaylorR0162

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The canonical relative cotangent tensor of the actual discriminant initial class. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaConormalInitialR0162
namespace ActualDiscriminantCotangentTensorR0162

private lemma tensor_initial {K A : Type} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] (ε : A →ₐ[K] K) (κ : A →ₐ[K] PowerSeries K)
    (hκ : IsTaylor ε κ) (n : ℕ)
    (e : DifferentialTensor ε n ≃ₗ[K] Grade ε n) (he : IsDifferentialPower ε n e)
    (c : Grade ε n ≃ₗ[K] K) (hc : IsCoefficient ε κ n c)
    (π : ideal ε) (hπ : PowerSeries.coeff 1 (κ π.1) = 1)
    (b : ↥(ideal ε ^ n)) :
    e.symm (gradeClass ε n b) = PowerSeries.coeff n (κ b.1) •
      PiTensorProduct.tprod K (fun _ : Fin n => differentialClass ε π.1) := by
  have hz : PowerSeries.constantCoeff (κ π.1) = 0 := (hκ.1 π.1).trans π.2
  obtain ⟨f, hf⟩ := PowerSeries.X_dvd_iff.mpr hz
  have hf0 : PowerSeries.constantCoeff f = 1 := by
    rw [hf] at hπ
    simpa using hπ
  have hpow : PowerSeries.coeff n (κ (π.1 ^ n)) = 1 := by
    rw [map_pow, hf, mul_pow]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hf0] using
      (PowerSeries.coeff_X_pow_mul (f ^ n) n 0)
  let p : ↥(ideal ε ^ n) := ⟨π.1 ^ n, Ideal.pow_mem_pow π.2 n⟩
  have hep := he (fun _ => π) p (by simp [p])
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, map_smul, hep]
  apply c.injective
  rw [map_smul, hc, hc]
  change PowerSeries.coeff n (κ b.1) = PowerSeries.coeff n (κ b.1) *
    PowerSeries.coeff n (κ (π.1 ^ n))
  rw [hpow, mul_one]

end ActualDiscriminantCotangentTensorR0162
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaKatoExistenceR0151
open ActualDiscriminantCotangentTensorR0162

/-- The actual initial class of 5g is the nonzero discriminant cotangent tensor. -/
theorem actual_discriminant_cotangent_tensor :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g ∧ ArithmeticThetaConormalInitialR0162.DiscriminantTensor k M s hs.1 g := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _
  classical
  obtain ⟨g, hg, _⟩ := geometric_discriminant_initial k r hr h3 he T M hM s hs G hG
  obtain ⟨χ₀, φ₀, σ₀, Ψ₀, κ₀, hχ₀, hφ₀, hσ₀, hΨ₀, hκ₀, hexp₀, b, hb, hm, hnm, hbc⟩ := hg.2
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs.1) :=
    (originScalar k M s hs.1).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs.1) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs.1).toAlgebra
  obtain ⟨ε, κ, ha, hi, hp, hn, ht⟩ :=
    actual_origin_augmented_taylor k r hr h3 he T M hM s hs G hG
  obtain ⟨hε, χ, φ, σ, Ψ, hχ, hφ, hσ, hΨ, hκ⟩ := ha
  have hexp := actual_kato_taylor k r hr h3 he T M hM s hs G hG
    χ hχ φ hφ σ hσ Ψ hΨ g hg.1
  have hsame : κ b = κ₀ b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k)
    have h₁ := hκ.1 b
    have h₀ := hκ₀.1 b
    rw [hb] at h₁ h₀
    simp only [RingHom.comp_apply, map_mul, map_ofNat, hexp, hexp₀] at h₁ h₀
    exact h₁.trans h₀.symm
  have hcoeff : PowerSeries.coeff 24 (κ b) = ArithmeticThetaUnaryKatoPowerR0160.discriminant k r := by
    rw [hsame]
    exact hbc
  obtain ⟨hπ, hc⟩ := taylor_graded_coefficient (LaurentSeries k)
    (OriginStalk k M s hs.1) ε hp hn κ ht
  obtain ⟨π, hπ⟩ := hπ
  obtain ⟨c, hc, _⟩ := hc 24
  obtain ⟨e, he', _⟩ := canonical_differential_tensor (LaurentSeries k)
    (OriginStalk k M s hs.1) ε hp hn 24
  let b' : ↥(ideal ε ^ 24) := ⟨b, by rwa [hi]⟩
  have heq := tensor_initial ε κ ht 24 e he' c hc π hπ b'
  have hne : e.symm (gradeClass ε 24 b') ≠ 0 := by
    intro hz
    have hz' : gradeClass ε 24 b' = 0 := by
      apply e.symm.injective
      simpa only [map_zero] using hz
    have hm' : b ∈ ideal ε ^ (24+1) := (Submodule.Quotient.mk_eq_zero (nextPower ε 24)).mp hz'
    rw [hi] at hm'
    exact hnm hm'
  refine ⟨g, ⟨hg.1, ε, κ, e, b', π,
    ⟨hε, χ, φ, σ, Ψ, hχ, hφ, hσ, hΨ, hκ⟩, he', hb, hπ, ?_, hne⟩, ?_⟩
  · simpa only [b', hcoeff] using heq
  · intro g' hg'
    obtain ⟨g₁, hg₁, hu⟩ := actual_kato_function_existence
      k r hr h3 T he M hM s hs G hG 5 (by decide) (by decide)
    exact (hu g' hg'.1).trans (hu g hg.1).symm

end ArithmeticThetaConormalInitialR0162
#print axioms ArithmeticThetaConormalInitialR0162.actual_discriminant_cotangent_tensor
