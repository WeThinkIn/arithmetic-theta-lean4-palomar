module

public import RatioRegularityDefinitionsR0067

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaRatioRegularityR0067

theorem fraction_restriction :
    ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ) (side : Bool),
      ∃! F : FunctionField k →+* OpenField k j side,
        IsFractionRestriction k j side F := by
  intro k _ _ j side
  let R : GenericChart k →+* GenericOpen k j side :=
    ArithmeticThetaGenericOverlapR0065.genericRestriction k j side
  have hRinj : Function.Injective R := by
    letI : IsDomain (ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :=
      (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
    have ht : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
      have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
        (by omega)).2.2.2.2.1
      simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
        ArithmeticThetaScaledAnnularR0050.tau,
        ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
        ArithmeticThetaScaledTateBridgeR0046.completedParameter,
        ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter] using h
    have hto : Function.Injective
        (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) :=
      IsLocalization.injective (GenericChart k)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
    have hbase : Function.Injective
        ((ArithmeticThetaGenericOverlapR0065.includeOpen k j side).comp
          (ArithmeticThetaCorrectedGammaR0061.restrict k j side)) :=
      (ArithmeticThetaGenericOverlapR0065.generic_open_faithfulness k j side).2
    rw [show R = ArithmeticThetaGenericOverlapR0065.genericRestriction k j side from rfl,
      ArithmeticThetaGenericOverlapR0065.genericRestriction,
      IsLocalization.Away.lift,
      IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have hh := congrArg (fun z => R z) h
      simpa [R, ArithmeticThetaGenericOverlapR0065.genericRestriction,
        IsLocalization.Away.lift_eq, RingHom.comp_apply] using hh
    · intro h
      have hxy : x = y := hbase h
      exact congrArg (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) hxy
  let G0 : GenericChart k →+* OpenField k j side :=
    (openToField k j side).comp R
  have hGinj : Function.Injective G0 := by
    have hopen : Function.Injective (openToField k j side) :=
      IsFractionRing.injective (GenericOpen k j side) (OpenField k j side)
    exact hopen.comp hRinj
  let F : FunctionField k →+* OpenField k j side :=
    IsFractionRing.lift (A := GenericChart k) (K := FunctionField k)
      (L := OpenField k j side) (g := G0) hGinj
  refine ⟨F, ?_, ?_⟩
  · change F.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k) =
      (openToField k j side).comp R
    ext x
    change (IsFractionRing.lift hGinj)
        ((algebraMap (GenericChart k) (FunctionField k)) x) = G0 x
    exact IsFractionRing.lift_algebraMap (A := GenericChart k) (K := FunctionField k)
      (L := OpenField k j side) (g := G0) hGinj x
  · intro H hH
    change H.comp (ArithmeticThetaLocalOrdersR0066.toFunctionField k) =
      (openToField k j side).comp R at hH
    apply IsFractionRing.ringHom_ext (A := GenericChart k) (K := FunctionField k)
      (L := OpenField k j side)
    intro x
    exact (RingHom.congr_fun hH x).trans
      (IsFractionRing.lift_algebraMap (A := GenericChart k) (K := FunctionField k)
        (L := OpenField k j side) (g := G0) hGinj x).symm

end ArithmeticThetaRatioRegularityR0067
