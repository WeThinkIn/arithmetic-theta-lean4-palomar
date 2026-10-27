import RatioRegularityDefinitionsR0067
import Mathlib.RingTheory.Localization.FractionRing

/-! The unique fraction-field extension of the actual adjacent generic-open map. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaRatioRegularityR0067

theorem fraction_adjacent :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (j : Fin r),
      ∃! E : OpenField k j.val false ≃+* OpenField k (nextIndex r hr j).val true,
        IsFractionAdjacent k r hr j E := by
  intro k _ _ r hr j
  let E : OpenField k j.val false ≃+* OpenField k (nextIndex r hr j).val true :=
    IsFractionRing.ringEquivOfRingEquiv (adjacent k r hr j)
  have hE : IsFractionAdjacent k r hr j E := by
    apply RingHom.ext
    intro a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (adjacent k r hr j) a
  refine ⟨E, hE, ?_⟩
  intro F hF
  have hhom : F.toRingHom = E.toRingHom :=
    IsFractionRing.ringHom_ext (fun a => RingHom.congr_fun (hF.trans hE.symm) a)
  apply RingEquiv.ext
  intro a
  exact RingHom.congr_fun hhom a

end ArithmeticThetaRatioRegularityR0067
