module

public import CorrectedGammaDefinitionsR0061

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

theorem gamma_finite_factorization :
    ∀ (k : Type u) [Field k] [CharZero k] (r j N : ℕ), 0 < r → j < r → 0 < N →
      fullPartial k r j N = horizontal k r j * tailPartial k r j N := by
  intro k _ _ r j N hr hj hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hleft : leftPartial k r j (n + 1) =
      (if j = 0 then 1 - cx k else 1) *
        (∏ l ∈ Finset.range (n + 1), leftTailFactor k r j l) := by
    by_cases hJ : j = 0
    · subst j
      have htail :
          (∏ l ∈ Finset.range (n + 1), leftTailFactor k r 0 l) =
            ∏ l ∈ Finset.range n, leftFactor k r 0 (l + 1) := by
        rw [Finset.prod_range_succ']
        simp [leftTailFactor]
      rw [leftPartial, Finset.prod_range_succ']
      rw [htail]
      simp [leftTailFactor, leftFactor, leftExponent]
      ring
    · rw [leftPartial]
      simp [leftTailFactor, hJ]
  have hright : rightPartial k r j (n + 1) =
      (if j + 1 = r then 1 - cy k else 1) *
        (∏ l ∈ Finset.range (n + 1), rightTailFactor k r j l) := by
    by_cases hR : j + 1 = r
    · have hexp : rightExponent r j 1 = 0 := by
        simp [rightExponent]
        omega
      have htail :
          (∏ l ∈ Finset.range (n + 1), rightTailFactor k r j l) =
            ∏ l ∈ Finset.range n, rightFactor k r j (l + 1 + 1) := by
        rw [Finset.prod_range_succ']
        simp [rightTailFactor, hR, rightFactor, hexp]
      rw [rightPartial, Finset.prod_range_succ']
      rw [htail]
      simp [rightTailFactor, hR, rightFactor, hexp]
      ring
    · rw [rightPartial]
      simp [rightTailFactor, hR]
  rw [fullPartial, hleft, hright, tailPartial, horizontal]
  ring

end ArithmeticThetaCorrectedGammaR0061
