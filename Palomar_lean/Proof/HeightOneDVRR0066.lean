module

public import LocalOrderDefinitionsR0066
public import Mathlib.RingTheory.DedekindDomain.Dvr

@[expose] public section

/-! Height-one local rings of the actual t-inverted completed annular chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066

/-- Noetherianity is supplied by completion of the concrete algebraic node. -/
instance genericNoetherian (k : Type u) [Field k] [CharZero k] :
    IsNoetherianRing (GenericChart k) := by
  let : IsNoetherianRing (Chart k) :=
    (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1
  exact IsLocalization.isNoetherianRing
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) _ inferInstance

/-- Normality is transported along the actual map inverting the parameter. -/
instance genericIntegrallyClosed (k : Type u) [Field k] [CharZero k] :
    IsIntegrallyClosed (GenericChart k) := by
  let : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  let : IsIntegrallyClosed (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).2
  apply isIntegrallyClosed_of_isLocalization (GenericChart k)
    (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau,
    ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

/-- Every height-one prime localization of the generic completed chart is a DVR. -/
theorem height_one_dvr :
    ∀ (k : Type u) [Field k] [CharZero k] (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 → IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro k _ _ P _ hP
  let A := Localization.AtPrime P
  let : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  let : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A, hP]
    rfl
  have hnf : ¬ IsField A := by
    intro hf
    have hz := ringKrullDim_eq_zero_of_isField hf
    rw [hdim] at hz
    exact one_ne_zero hz
  let : Ring.DimensionLEOne A := by
    refine ⟨fun {p} hp0 hp => ?_⟩
    let : p.IsPrime := hp
    have hb : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
    have hh := Ideal.height_add_one_le_of_lt_of_isPrime hb
    rw [Ideal.height_bot, zero_add] at hh
    have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim A :=
      Ideal.height_le_ringKrullDim_of_isPrime
    have hge : (1 : WithBot ℕ∞) ≤ p.height := by exact_mod_cast hh
    exact Ideal.isMaximal_of_height_eq_ringKrullDim
      (le_antisymm hle (by simpa only [hdim] using hge))
  have hded : IsDedekindDomain A := { }
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 1 3).mpr hded

end ArithmeticThetaLocalOrdersR0066
