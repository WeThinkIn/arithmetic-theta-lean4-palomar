import ConormalInitialDefinitionsR0162

noncomputable section
universe u v
namespace ArithmeticThetaConormalInitialR0162
namespace TaylorGradedCoefficient
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
variable (ε : A →ₐ[K] K) (κ : A →ₐ[K] PowerSeries K)

private theorem normalized [IsDomain A] (hp : (ideal ε).IsPrincipal)
    (hne : ideal ε ≠ ⊥) (hκ : IsTaylor ε κ) :
    ∃ π : ideal ε, PowerSeries.coeff 1 (κ π.1) = 1 := by
  let _ := hp
  let p := Submodule.IsPrincipal.generator (ideal ε)
  have pm : p ∈ ideal ε := Submodule.IsPrincipal.generator_mem _
  have pn : p ≠ 0 := by
    intro h
    exact hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h)
  have pε : ε p = 0 := pm
  have pn2 : p ∉ ideal ε ^ 2 := by
    intro h
    rw [← Ideal.span_singleton_generator (ideal ε), Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    have hc : 1 = p * a := (mul_left_cancel₀ pn) (by simpa [pow_two, mul_assoc] using ha)
    have := congrArg ε hc
    simp [pε] at this
  have pc : PowerSeries.coeff 1 (κ p) ≠ 0 := by
    intro h
    apply pn2
    apply (hκ.2 p 2).mpr
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · simpa [PowerSeries.coeff_zero_eq_constantCoeff] using (hκ.1 p).trans pε
    · exact h
  refine ⟨⟨(PowerSeries.coeff 1 (κ p))⁻¹ • p,
    ((ideal ε).restrictScalars K).smul_mem _ pm⟩, ?_⟩
  simp only [map_smul, PowerSeries.coeff_smul, smul_eq_mul]
  exact inv_mul_cancel₀ pc

private def coefficient (n : ℕ) : ↥(ideal ε ^ n) →ₗ[K] K where
  toFun b := PowerSeries.coeff n (κ b.1)
  map_add' x y := by simp
  map_smul' c x := by simp

private theorem coefficient_kernel (hκ : IsTaylor ε κ) (n : ℕ) :
    (nextPower ε n).restrictScalars K = LinearMap.ker (coefficient ε κ n) := by
  ext b
  change b.1 ∈ ideal ε ^ (n+1) ↔ PowerSeries.coeff n (κ b.1) = 0
  constructor
  · intro h
    exact (hκ.2 b.1 (n+1)).mp h n (by omega)
  · intro h
    apply (hκ.2 b.1 (n+1)).mpr
    intro i hi
    by_cases hin : i < n
    · exact (hκ.2 b.1 n).mp b.2 i hin
    · have : i = n := by omega
      simpa [this] using h

private theorem coeff_power (π : ideal ε) (hπ : PowerSeries.coeff 1 (κ π.1) = 1)
    (hκ : IsTaylor ε κ) (n : ℕ) : PowerSeries.coeff n (κ (π.1 ^ n)) = 1 := by
  have hz : PowerSeries.constantCoeff (κ π.1) = 0 := (hκ.1 π.1).trans π.2
  obtain ⟨f, hf⟩ := PowerSeries.X_dvd_iff.mpr hz
  have hf0 : PowerSeries.constantCoeff f = 1 := by
    rw [hf] at hπ
    simpa using hπ
  rw [map_pow, hf, mul_pow]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff, hf0] using
    (PowerSeries.coeff_X_pow_mul (f ^ n) n 0)

private def quotientCoefficient (hκ : IsTaylor ε κ) (n : ℕ) : Grade ε n →ₗ[K] K :=
  ((nextPower ε n).restrictScalars K).liftQ (coefficient ε κ n)
    (coefficient_kernel ε κ hκ n).le

private theorem quotientCoefficient_bijective (hκ : IsTaylor ε κ)
    (π : ideal ε) (hπ : PowerSeries.coeff 1 (κ π.1) = 1) (n : ℕ) :
    Function.Bijective (quotientCoefficient ε κ hκ n) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot' _ _ (coefficient_kernel ε κ hκ n)
  · intro c
    have hm : π.1 ^ n ∈ ideal ε ^ n := Ideal.pow_mem_pow π.2 n
    refine ⟨gradeClass ε n ⟨c • π.1 ^ n, ((ideal ε ^ n).restrictScalars K).smul_mem c hm⟩, ?_⟩
    change PowerSeries.coeff n (κ (c • π.1 ^ n)) = c
    rw [map_smul, PowerSeries.coeff_smul, coeff_power ε κ π hπ hκ n]
    exact mul_one c

end TaylorGradedCoefficient

/-- A filtration-reflecting Taylor map identifies every graded piece with its coefficient. -/
theorem taylor_graded_coefficient :
    ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [IsDomain A] [Algebra K A]
      (ε : A →ₐ[K] K), (ideal ε).IsPrincipal → ideal ε ≠ ⊥ →
      ∀ (κ : A →ₐ[K] PowerSeries K), IsTaylor ε κ →
      (∃ π : ideal ε, PowerSeries.coeff 1 (κ π.1) = 1) ∧
      ∀ n : ℕ, ∃! e : Grade ε n ≃ₗ[K] K, IsCoefficient ε κ n e := by
  intro K _ A _ _ _ ε hp hne κ hκ
  obtain ⟨π, hπ⟩ := TaylorGradedCoefficient.normalized ε κ hp hne hκ
  refine ⟨⟨π, hπ⟩, ?_⟩
  intro n
  let e : Grade ε n ≃ₗ[K] K := LinearEquiv.ofBijective
    (TaylorGradedCoefficient.quotientCoefficient ε κ hκ n)
    (TaylorGradedCoefficient.quotientCoefficient_bijective ε κ hκ π hπ n)
  refine ⟨e, ?_, ?_⟩
  · intro b
    rfl
  · intro e' he'
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ b => exact he' b

end ArithmeticThetaConormalInitialR0162
