module

public import RatioRegularityDefinitionsR0067
public import HeightOneDVRR0066
public import FractionRestrictionR0067

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaRatioRegularityR0067

theorem regular_family_descent :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
      (f : Fin r → FunctionField k),
      RationalCompatible k r hr f →
      (∀ (j : Fin r) (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k)),
        P.IsPrime → P.height = 1 →
          ArithmeticThetaLocalOrdersR0066.RegularAt k P (f j)) →
      ∃! v : Fin r → GenericChart k,
        (∀ j, ArithmeticThetaLocalOrdersR0066.toFunctionField k (v j) = f j) ∧
          RegularCompatible k r hr v := by
  intro k _ _ r hr f hrat hregular
  let v : Fin r → GenericChart k := fun j =>
    Classical.choose
      (ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
        (GenericChart k) (FunctionField k) (f j)
        (fun P hP hheight => hregular j P hP hheight))
  have hv (j : Fin r) :
      ArithmeticThetaLocalOrdersR0066.toFunctionField k (v j) = f j := by
    exact Classical.choose_spec
      (ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
        (GenericChart k) (FunctionField k) (f j)
        (fun P hP hheight => hregular j P hP hheight))
  have hmap (j : Fin r) (side : Bool)
      (F : FunctionField k →+* OpenField k j.val side)
      (hF : IsFractionRestriction k j.val side F) :
      F (ArithmeticThetaLocalOrdersR0066.toFunctionField k (v j)) =
        openToField k j.val side
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val side (v j)) := by
    exact RingHom.congr_fun hF (v j)
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · intro j
    let FY : FunctionField k →+* OpenField k j.val false :=
      Classical.choose
        (fraction_restriction k j.val false)
    let FX : FunctionField k →+* OpenField k (nextIndex r hr j).val true :=
      Classical.choose
        (fraction_restriction k (nextIndex r hr j).val true)
    let E : OpenField k j.val false ≃+* OpenField k (nextIndex r hr j).val true :=
      IsFractionRing.ringEquivOfRingEquiv (adjacent k r hr j)
    have hFY : IsFractionRestriction k j.val false FY := by
      exact (Classical.choose_spec (fraction_restriction k j.val false)).1
    have hFX : IsFractionRestriction k (nextIndex r hr j).val true FX := by
      exact (Classical.choose_spec
        (fraction_restriction k (nextIndex r hr j).val true)).1
    have hE : IsFractionAdjacent k r hr j E := by
      apply RingHom.ext
      intro a
      exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (adjacent k r hr j) a
    apply (IsFractionRing.injective (GenericOpen k (nextIndex r hr j).val true)
      (OpenField k (nextIndex r hr j).val true))
    calc
      openToField k (nextIndex r hr j).val true
          (adjacent k r hr j
            (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (v j))) =
          E (openToField k j.val false
            (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (v j))) :=
        (RingHom.congr_fun hE
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (v j))).symm
      _ = E (FY (ArithmeticThetaLocalOrdersR0066.toFunctionField k (v j))) :=
        congrArg E (hmap j false FY hFY).symm
      _ = E (FY (f j)) := congrArg E (congrArg FY (hv j))
      _ = FX (f (nextIndex r hr j)) := hrat j FY FX E hFY hFX hE
      _ = FX (ArithmeticThetaLocalOrdersR0066.toFunctionField k
          (v (nextIndex r hr j))) :=
        congrArg FX (hv (nextIndex r hr j)).symm
      _ = openToField k (nextIndex r hr j).val true
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k
            (nextIndex r hr j).val true (v (nextIndex r hr j))) :=
        hmap (nextIndex r hr j) true FX hFX
  · intro w hw
    apply funext
    intro j
    apply (IsFractionRing.injective (GenericChart k) (FunctionField k))
    exact (hw.1 j).trans (hv j).symm

end ArithmeticThetaRatioRegularityR0067
