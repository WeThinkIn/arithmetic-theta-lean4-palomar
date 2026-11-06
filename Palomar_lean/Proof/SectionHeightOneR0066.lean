module

public import SectionPrimeR0066
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

@[expose] public section

/-! Height one for the genuine completed sections after parameter inversion. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalOrdersR0066

theorem section_height_one :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (α : k) (hα : α ≠ 0)
      (P : Ideal (GenericChart k)) [P.IsPrime],
      P = sectionIdeal k side α → P.height = 1 := by
  intro k _ _ side α hα P _ hP
  letI : IsNoetherianRing (Chart k) :=
    (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1
  letI : IsNoetherianRing (GenericChart k) := inferInstance
  obtain ⟨hex, hall⟩ :=
    ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels k side α hα
  obtain ⟨σ, hσ, _⟩ := hex
  have hregular := (hall σ hσ).2.2.2
  have hgeneric : sectionEquation k side α ∈ nonZeroDivisors (GenericChart k) :=
    IsLocalization.nonZeroDivisors_le_comap
      (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
      (GenericChart k) hregular
  have hprime := section_prime k side α hα
  rw [hP]
  apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hgeneric
  intro hunit
  exact hprime.ne_top (Ideal.span_singleton_eq_top.mpr hunit)

end ArithmeticThetaLocalOrdersR0066
