module

public import ScaledTateCompletionExtensionDefinitions
public import Mathlib.RingTheory.PowerSeries.Order

@[expose] public section

/-! The actual `X`-adic target ideal is separated in the power-series ring. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

open ArithmeticThetaScaledTateBridgeR0046

theorem target_ideal_separated :
    ∀ (k : Type u) [Field k] [CharZero k] (z : PowerSeries k),
      (∀ n : ℕ, z ∈ (targetIdeal k) ^ n) → z = 0 := by
  intro k _ _ z hz
  apply PowerSeries.ext
  intro n
  have hdiv : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ z := by
    simpa [targetIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hz (n + 1)
  exact (PowerSeries.X_pow_dvd_iff.mp hdiv) n (Nat.lt_succ_self n)

end ArithmeticThetaScaledTateCompletionExtensionR0048
