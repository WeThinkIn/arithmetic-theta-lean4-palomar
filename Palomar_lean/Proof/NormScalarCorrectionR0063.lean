module

public import NormIntegerNormalizationR0063

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

namespace ArithmeticThetaNormFiniteR0063

theorem scalar_correction :
    ∀ (F : Type u) [Field F] (c d : ℕ), 1 < c → Nat.Coprime c 6 → 0 < d →
      Nat.Coprime c d → ∀ (z Q : F), z ≠ 0 → Q ≠ 0 → correction c d z Q = 1 := by
  intro F _ c d hc hc6 hd hcop z Q hz hQ
  obtain ⟨hzexp, hqexp, hsign⟩ := integer_normalization c d hc hc6 hd hcop
  rw [correction, hzexp, hqexp, hsign.neg_one_zpow]
  simp

end ArithmeticThetaNormFiniteR0063
