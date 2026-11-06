import GenericOverlapDefinitionsR0065

/-! Unique extensions of the specified completed restrictions after inverting t. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaGenericOverlapR0065

variable (k : Type u) [Field k] [CharZero k]

/-- The accepted restriction carries the actual chart parameter to the actual
parameter of the completed coordinate open. -/
theorem restriction_parameter (j : ℕ) (side : Bool) :
    ArithmeticThetaCorrectedGammaR0061.restrict k j side
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = openParameter k j side := by
  have hs : ArithmeticThetaIndexedOverlapsR0058.IsRestriction k j side
      (ArithmeticThetaCorrectedGammaR0061.restrict k j side) :=
    Classical.choose_spec
      (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions k j side).exists
  have h := RingHom.congr_fun hs.1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)
  simpa [openParameter, ArithmeticThetaAnnularTorsionPrereqR0053.tau,
    ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaIndexedOverlapsR0058.ot,
    ArithmeticThetaIndexedOverlapsR0058.openBase,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase] using h

/-- The concrete localization lift of the already specified restriction. -/
def genericRestriction (j : ℕ) (side : Bool) :
    GenericChart k →+* GenericOpen k j side :=
  IsLocalization.Away.lift (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)
    (g := (includeOpen k j side).comp
      (ArithmeticThetaCorrectedGammaR0061.restrict k j side)) (by
        rw [RingHom.comp_apply, restriction_parameter]
        exact IsLocalization.Away.algebraMap_isUnit (openParameter k j side))

theorem genericRestriction_spec (j : ℕ) (side : Bool) :
    IsGenericRestriction k j side (genericRestriction k j side) := by
  exact IsLocalization.Away.lift_comp _ _

theorem generic_restriction_providers :
    ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ) (side : Bool),
      ∃! R : GenericChart k →+* GenericOpen k j side,
        IsGenericRestriction k j side R := by
  intro k _ _ j side
  refine ⟨genericRestriction k j side, genericRestriction_spec k j side, ?_⟩
  intro R hR
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  exact hR.trans (genericRestriction_spec k j side).symm

end ArithmeticThetaGenericOverlapR0065
