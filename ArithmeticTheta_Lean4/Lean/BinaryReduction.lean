import BinaryReductionSteps

/-!
Reduction of positive integral binary forms by strong induction on the first
coefficient. The actual unimodular Gram congruence, determinant and entry content
are retained throughout the descent.
-/

namespace ArithmeticThetaBinary

lemma reduced_of_measure (N : ℕ) :
    ∀ a b c : ℤ, a.toNat = N → 0 < a → 0 < 4*a*c-b^2 →
      ∃ a' b' c' : ℤ, 0 < a' ∧ |b'| ≤ a' ∧ a' ≤ c' ∧
        4*a'*c'-b'^2 = 4*a*c-b^2 ∧ gramContent a' b' c' = gramContent a b c ∧
        ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧
          U.transpose * gram a b c * U = gram a' b' c' := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b c hN ha hdisc
    obtain ⟨k, hb, hdet, hgram, hdelta, hcontent⟩ := balanced_shear a b c ha
    let b₁ : ℤ := b+2*a*k
    let c₁ : ℤ := a*k^2+b*k+c
    have hdelta₁ : 4*a*c₁-b₁^2 = 4*a*c-b^2 := hdelta
    have hprod : 0 < a*c₁ := by nlinarith [sq_nonneg b₁]
    have hc₁ : 0 < c₁ := pos_of_mul_pos_right hprod ha.le
    by_cases hac : a ≤ c₁
    · refine ⟨a, b₁, c₁, ha, hb, hac, hdelta₁, hcontent, shear k, ?_, hgram⟩
      rw [hdet]
      exact isUnit_one
    · have hsmall : c₁.toNat < N := by
        have hca : c₁ < a := by omega
        have hna := Int.toNat_of_nonneg ha.le
        have hnc := Int.toNat_of_nonneg hc₁.le
        omega
      have hswapdelta : 4*c₁*a-b₁^2 = 4*a*c-b^2 := by nlinarith [hdelta₁]
      have hswappos : 0 < 4*c₁*a-b₁^2 := by rw [hswapdelta]; exact hdisc
      obtain ⟨a', b', c', ha', hb', hac', hd', hg', V, hV, hcong⟩ :=
        ih c₁.toNat hsmall c₁ b₁ a rfl hc₁ hswappos
      refine ⟨a', b', c', ha', hb', hac', hd'.trans hswapdelta, ?_,
        (shear k * swapVariables) * V, ?_, ?_⟩
      · rw [hg', content_swap]
        exact hcontent
      · rw [Matrix.det_mul, Matrix.det_mul, hdet, swapVariables_det]
        simpa using hV.neg
      · rw [gram_congruence_comp, gram_congruence_comp, hgram, swapVariables_gram]
        exact hcong

theorem reduced_representative (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < 4*a*c-b^2) :
    ∃ a' b' c' : ℤ, 0 < a' ∧ |b'| ≤ a' ∧ a' ≤ c' ∧
      4*a'*c'-b'^2 = 4*a*c-b^2 ∧ gramContent a' b' c' = gramContent a b c ∧
      ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧
        U.transpose * gram a b c * U = gram a' b' c' :=
  reduced_of_measure a.toNat a b c rfl ha hdisc

end ArithmeticThetaBinary
