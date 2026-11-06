module

public import SectionOrderDefinitions

@[expose] public section

universe u

namespace ArithmeticThetaSectionOrder

/-- Vanishing through q-degree `B` gives order at least `L * (B + 1)`
after the formal substitution `q = t^L`, for positive `L`. -/
theorem scaled_series_has_q_order {R : Type u} [Semiring R]
    (F : PowerSeries R) (L B : ℕ) (hL : 0 < L)
    (hF : VanishesThrough F B) :
    HasQOrderAtLeast (scaledSeries L F) (L * (B + 1)) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro n hn
  change PowerSeries.coeff n (PowerSeries.mk _) = 0
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · apply hF
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hL).mpr
    simpa only [Nat.mul_comm] using hn
  · rfl

end ArithmeticThetaSectionOrder
