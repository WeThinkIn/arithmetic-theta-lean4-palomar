module

public import GenericOverlapDefinitionsR0065
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaGenericOverlapR0065

open ArithmeticThetaIndexedOverlapsR0058

variable (k : Type u) [Field k] [CharZero k]

/-- The specified completed adjacent equivalence preserves the actual parameter. -/
theorem overlap_openParameter (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj (openParameter k j false) =
      openParameter k (next r j) true := by
  have hE := Classical.choose_spec
    (completed_indexed_adjacent k r j hr hj).exists
  have ht := DFunLike.congr_fun
    (indexed_adjacent_coordinates k r j hr hj).1 PowerSeries.X
  have hcomm := RingHom.congr_fun hE.1 (ot k j false)
  change ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj
    (completeOpen k j false (ot k j false)) =
      completeOpen k (next r j) true (adjacent k r j (ot k j false)) at hcomm
  change adjacent k r j (ot k j false) = ot k (next r j) true at ht
  simpa only [ht, openParameter] using hcomm

theorem generic_adjacent_providers :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ) (hr : 0 < r) (hj : j < r),
      ∃! E : GenericOpen k j false ≃+* GenericOpen k (next r j) true,
        IsGenericAdjacent k r j hr hj E := by
  intro k _ _ r j hr hj
  let e := ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj
  have hM : (Submonoid.powers (openParameter k j false)).map e.toMonoidHom =
      Submonoid.powers (openParameter k (next r j) true) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (overlap_openParameter k r j hr hj)
  let E : GenericOpen k j false ≃+* GenericOpen k (next r j) true :=
    IsLocalization.ringEquivOfRingEquiv _ _ e hM
  have hE : IsGenericAdjacent k r j hr hj E := by
    apply RingHom.ext
    intro a
    exact IsLocalization.ringEquivOfRingEquiv_eq hM a
  refine ⟨E, hE, ?_⟩
  intro F hF
  have hhom : F.toRingHom = E.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (openParameter k j false))
      (hF.trans hE.symm)
  apply RingEquiv.ext
  intro a
  exact RingHom.congr_fun hhom a

end ArithmeticThetaGenericOverlapR0065
