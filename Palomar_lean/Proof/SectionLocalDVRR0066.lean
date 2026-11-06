module

public import HeightOneDVRR0066
public import SectionHeightOneR0066

@[expose] public section

/-! Discrete valuation local rings at the genuine completed horizontal sections. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalOrdersR0066

/-- The actual section prime has height one, so its localization is a DVR. -/
theorem section_local_dvr :
    ∀ (k : Type u) [Field k] [CharZero k] (side : Bool) (α : k) (hα : α ≠ 0)
      (P : Ideal (GenericChart k)) [P.IsPrime],
      P = sectionIdeal k side α → IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro k _ _ side α hα P _ hP
  exact height_one_dvr k P (section_height_one k side α hα P hP)

end ArithmeticThetaLocalOrdersR0066
