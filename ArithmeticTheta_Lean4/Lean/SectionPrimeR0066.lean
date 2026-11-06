import LocalOrderDefinitionsR0066
import CompletedSectionKernelsR0053
import Mathlib.RingTheory.Localization.Ideal

/-! Primality of the actual completed section ideal after parameter inversion. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalOrdersR0066

theorem section_prime :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (α : k) (hα : α ≠ 0),
      (sectionIdeal k side α).IsPrime := by
  intro k _ _ side α hα
  obtain ⟨hex, hall⟩ :=
    ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k side α hα
  obtain ⟨σ, hσ, _⟩ := hex
  obtain ⟨_, hker, hprime, _⟩ := hall σ hσ
  have ht : σ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = PowerSeries.X := by
    have hb := DFunLike.congr_fun hσ.1 PowerSeries.X
    simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
      ArithmeticThetaAnnularTorsionPrereqR0053.base,
      ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter] using hb
  have hd : Disjoint
      (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) : Set (Chart k))
      (ArithmeticThetaAnnularTorsionPrereqR0053.sectionIdeal k side α : Set (Chart k)) := by
    apply Set.disjoint_left.mpr
    intro z hz hJ
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    rw [← hker] at hJ
    have hzero : σ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ n) = 0 := hJ
    rw [map_pow, ht] at hzero
    exact (pow_ne_zero n (PowerSeries.X_ne_zero (R := k))) hzero
  have hp := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
    (GenericChart k) (ArithmeticThetaAnnularTorsionPrereqR0053.sectionIdeal k side α)
    hprime hd
  simpa only [ArithmeticThetaAnnularTorsionPrereqR0053.sectionIdeal,
    Ideal.map_span, Set.image_singleton, sectionIdeal, sectionEquation,
    ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric] using hp

end ArithmeticThetaLocalOrdersR0066
