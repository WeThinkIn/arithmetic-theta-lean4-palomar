module

public import ScaledSpecializedCoefficientStabilityR0050
public import ScaledThetaCompletedLimitR0050
public import ScaledThetaFiniteSpecializationR0050

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050

open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaScaledTateCompletionExtensionR0048

theorem theta_limit_exact_specialization :
    ∀ (k : Type u) [Field k] [CharZero k] (r i m d j : ℕ) (nu : ℤ)
      (hr : 0 < r) (hi : i < r) (hm : 0 < m) (he : Even m) (hd : 0 < d)
      (a : k) (ha : a ≠ 0),
      ∃! s : CompletedNode k r,
        ThetaLimit k r m d j nu s ∧
          specialization k r i hr hi a ha s =
            specializedSeries k r i m d j nu a := by
  intro k _ _ r i m d j nu hr hi hm he hd a ha
  obtain ⟨s, hs, hsu⟩ :=
    theta_completed_limit k r m d j nu hr hm he hd
  let phi : CompletedNode k r →+* PowerSeries k :=
    specialization k r i hr hi a ha
  have hfiltered : ∀ (q : ℕ) (z : CompletedNode k r),
      z ∈ completedPower k r q →
        phi z ∈ (targetIdeal k) ^ (r * q) := by
    intro q z hz
    simpa [phi, specialization] using
      (Classical.choose_spec
        (completion_specialization_exists_and_filtered k r i hr hi a ha)).2 q z hz
  have heq : phi s = specializedSeries k r i m d j nu a := by
    apply PowerSeries.ext
    intro n
    let N : ℕ := r * (n + 1) + 2 * (j + r) + 1
    have hNlim : r * (n + 1) + 2 * (j + r) + 1 ≤ N := by
      rfl
    have hmem0 := hfiltered (n + 1) (s - thetaPartial k r m d j nu N)
      (hs (n + 1) N hNlim)
    have hmem : phi s - phi (thetaPartial k r m d j nu N) ∈
        (targetIdeal k) ^ (r * (n + 1)) := by
      simpa only [map_sub] using hmem0
    have hfinite : phi (thetaPartial k r m d j nu N) =
        specializedPartial k r i m d j nu a N := by
      dsimp [phi]
      exact theta_finite_specialization k r i m d j nu hr hi hd a ha N
    have hmem' : phi s - specializedPartial k r i m d j nu a N ∈
        (targetIdeal k) ^ (r * (n + 1)) := by
      rw [← hfinite]
      exact hmem
    have hdiv : (PowerSeries.X : PowerSeries k) ^ (r * (n + 1)) ∣
        phi s - specializedPartial k r i m d j nu a N := by
      simpa [targetIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hmem'
    have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv) n (by
      have hr' : 1 ≤ r := by omega
      nlinarith)
    have hNstab : n + 2 * (j + r) + 1 ≤ N := by
      dsimp [N]
      have hr' : 1 ≤ r := by omega
      nlinarith
    have hstab :=
      (specialized_coefficient_stability k r i m d j nu a hr hi hm he hd ha).2
        n N hNstab
    have hcoeff' : PowerSeries.coeff n (phi s) -
        PowerSeries.coeff n (specializedPartial k r i m d j nu a N) = 0 := by
      simpa using hcoeff
    exact (sub_eq_zero.mp hcoeff').trans hstab
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · exact heq
  · intro z hz
    exact hsu z hz.1

end ArithmeticThetaScaledAnnularR0050
