import AugmentedConormalR0162
import CartierGradedTensorR0162

/-! Canonical differential tensor interpretation of the graded augmentation ideal. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace ArithmeticThetaConormalInitialR0162

/-- The differential tensor comparison is characterized on every product of
actual differentials, including the empty product in degree zero. -/
theorem canonical_differential_tensor :
    ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [IsDomain A] [Algebra K A]
      (ε : A →ₐ[K] K), (ideal ε).IsPrincipal → ideal ε ≠ ⊥ →
      ∀ n : ℕ, ∃! e : DifferentialTensor ε n ≃ₗ[K] Grade ε n,
        IsDifferentialPower ε n e := by
  intro K _ A _ _ _ ε hp hn n
  obtain ⟨c, hc, _⟩ := augmented_conormal K A ε
  change ∀ x : ideal ε, c ((ideal ε).toCotangent x) = differentialClass ε x.1 at hc
  obtain ⟨m, hm, hmu⟩ := cartier_graded_tensor K A ε hp hn n
  let t : ConormalTensor ε n ≃ₗ[K] DifferentialTensor ε n :=
    PiTensorProduct.congr (fun _ : Fin n => c)
  have ht (x : Fin n → ideal ε) :
      t (PiTensorProduct.tprod K (fun i => (ideal ε).toCotangent (x i))) =
        PiTensorProduct.tprod K (fun i => differentialClass ε (x i).1) := by
    change PiTensorProduct.congr (fun _ : Fin n => c) _ = _
    rw [PiTensorProduct.congr_tprod]
    simp_rw [hc]
  let e : DifferentialTensor ε n ≃ₗ[K] Grade ε n := t.symm.trans m
  have he : IsDifferentialPower ε n e := by
    intro x b hb
    change m (t.symm (PiTensorProduct.tprod K
      (fun i => differentialClass ε (x i).1))) = _
    rw [← ht x, LinearEquiv.symm_apply_apply]
    exact hm x b hb
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hm' : IsMultiplication ε n (t.trans e') := by
    intro x b hb
    change e' (t (PiTensorProduct.tprod K
      (fun i => (ideal ε).toCotangent (x i)))) = _
    rw [ht]
    exact he' x b hb
  have h := hmu (t.trans e') hm'
  apply LinearEquiv.ext
  intro z
  have hz := DFunLike.congr_fun h (t.symm z)
  simpa only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hz

end ArithmeticThetaConormalInitialR0162
