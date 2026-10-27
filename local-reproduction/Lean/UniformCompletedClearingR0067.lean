import RatioRegularityDefinitionsR0067
import GenericRestrictionProvidersR0065
import GenericAdjacentProvidersR0065
import GenericOpenFaithfulnessR0065

/-! Common parameter clearing for a finite family on the accepted completed
annular charts. Compatibility descends through the specified completed open
maps; no global proper model is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067

private lemma generic_localization_representation (k : Type u) [Field k] [CharZero k]
    (z : GenericChart k) :
    ∃ (m : ℕ) (a : Chart k),
      parameter k ^ m * z = ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k a := by
  obtain ⟨m, a, h⟩ := IsLocalization.Away.surj
    (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) z
  refine ⟨m, a, ?_⟩
  change ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ m * z = _
  simpa [parameter, ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric, mul_comm] using h

private lemma includeOpen_injective (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) :
    Function.Injective (ArithmeticThetaGenericOverlapR0065.includeOpen k j side) := by
  letI : IsDomain (GenericOpen k j side) :=
    (ArithmeticThetaGenericOverlapR0065.generic_open_faithfulness k j side).1
  letI : IsDomain (ArithmeticThetaGenericOverlapR0065.OpenHat k j side) :=
    ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.open_hat_domain k j side
  have ht : ArithmeticThetaGenericOverlapR0065.openParameter k j side ≠ 0 := by
    intro hzero
    have hu : IsUnit (ArithmeticThetaGenericOverlapR0065.includeOpen k j side
        (ArithmeticThetaGenericOverlapR0065.openParameter k j side)) :=
      IsLocalization.Away.algebraMap_isUnit
        (ArithmeticThetaGenericOverlapR0065.openParameter k j side)
    apply hu.ne_zero
    simpa [hzero]
  exact IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht)

theorem uniform_completed_clearing :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
      (v : Fin r → GenericChart k),
      RegularCompatible k r hr v →
      ∃ (n : ℕ) (a : Fin r → Chart k),
        (∀ j, ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j) =
          parameter k ^ n * v j) ∧ CompletedCompatible k r hr a := by
  intro k _ _ r hr v hcompatible
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let p : Fin r → ℕ × Chart k := fun j =>
    (Classical.choose (generic_localization_representation k (v j)),
      Classical.choose (Classical.choose_spec
        (generic_localization_representation k (v j))) )
  have hp (j : Fin r) : parameter k ^ (p j).1 * v j =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (p j).2 :=
    Classical.choose_spec (Classical.choose_spec
      (generic_localization_representation k (v j)))
  let n : ℕ := Finset.univ.sup' Finset.univ_nonempty (fun j : Fin r => (p j).1)
  have hn (j : Fin r) : (p j).1 ≤ n :=
    Finset.le_sup' (fun i : Fin r => (p i).1) (Finset.mem_univ j)
  let a : Fin r → Chart k := fun j =>
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (n - (p j).1) * (p j).2
  have hclear (j : Fin r) :
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j) =
        parameter k ^ n * v j := by
    change ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (n - (p j).1) * (p j).2) = _
    rw [map_mul, map_pow, ← parameter]
    calc
      parameter k ^ (n - (p j).1) *
          ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (p j).2 =
          parameter k ^ (n - (p j).1) * (parameter k ^ (p j).1 * v j) := by rw [hp]
      _ = parameter k ^ n * v j := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hn j)]
  refine ⟨n, a, hclear, ?_⟩
  intro j
  let j' := nextIndex r hr j
  let EY := Classical.choose
    (ArithmeticThetaGenericOverlapR0065.generic_adjacent_providers k r j.val hr j.isLt)
  let RY := ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false
  let RX := ArithmeticThetaGenericOverlapR0065.genericRestriction k
    (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
  have hRY (z : Chart k) :
      RY (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k z) =
        ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
          (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false z) := by
    exact RingHom.congr_fun
      (ArithmeticThetaGenericOverlapR0065.genericRestriction_spec k j.val false) z
  have hRX (z : Chart k) :
      RX (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k z) =
        ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaCorrectedGammaR0061.restrict k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true z) := by
    exact RingHom.congr_fun
      (ArithmeticThetaGenericOverlapR0065.genericRestriction_spec k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) z
  have hparamY : RY (parameter k) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
        (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) := by
    rw [show parameter k = ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) by rfl, hRY,
      ArithmeticThetaGenericOverlapR0065.restriction_parameter]
  have hparamX : RX (parameter k) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
        (ArithmeticThetaGenericOverlapR0065.openParameter k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) := by
    rw [show parameter k = ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) by rfl, hRX,
      ArithmeticThetaGenericOverlapR0065.restriction_parameter]
  have hE : ArithmeticThetaGenericOverlapR0065.IsGenericAdjacent k r j.val hr j.isLt EY :=
    (Classical.choose_spec
      (ArithmeticThetaGenericOverlapR0065.generic_adjacent_providers k r j.val hr j.isLt)).1
  have hreg : EY (RY (v j)) = RX (v j') := by
    change (adjacent k r hr j)
        (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (v j)) =
      ArithmeticThetaGenericOverlapR0065.genericRestriction k
        (nextIndex r hr j).val true (v (nextIndex r hr j))
    exact hcompatible j
  have hleft : RY (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j)) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
          (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) ^ n * RY (v j) := by
    rw [hclear j, map_mul, map_pow, hparamY]
  have hright : RX (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j')) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaGenericOverlapR0065.openParameter k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) ^ n * RX (v j') := by
    rw [hclear j', map_mul, map_pow, hparamX]
  have hparamOverlap :
      (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom
        (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) =
      ArithmeticThetaGenericOverlapR0065.openParameter k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true := by
    calc
      (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom
          (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) =
          ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
            (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) :=
        congrFun (RingEquiv.coe_toRingHom
          (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt)) _
      _ = ArithmeticThetaGenericOverlapR0065.openParameter k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true :=
        ArithmeticThetaGenericOverlapR0065.overlap_openParameter k r j.val hr j.isLt
  have hparamE : EY.toRingHom
      (ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
        (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false)) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
        (ArithmeticThetaGenericOverlapR0065.openParameter k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) := by
    calc
      EY.toRingHom (ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
          (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false)) =
          ArithmeticThetaGenericOverlapR0065.includeOpen k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
            ((ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom
              (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false)) :=
          RingHom.congr_fun hE
            (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false)
      _ = ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaGenericOverlapR0065.openParameter k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) :=
          congrArg
            (ArithmeticThetaGenericOverlapR0065.includeOpen k
              (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) hparamOverlap
  have hregHom : EY.toRingHom (RY (v j)) = RX (v j') := by
    exact (congrFun (RingEquiv.coe_toRingHom EY) (RY (v j))).trans hreg
  have hcleared : EY.toRingHom (RY (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j))) =
      RX (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j')) := by
    calc
      EY.toRingHom (RY (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j))) =
          EY.toRingHom (ArithmeticThetaGenericOverlapR0065.includeOpen k j.val false
            (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false) ^ n * RY (v j)) :=
            congrArg EY.toRingHom hleft
      _ = ArithmeticThetaGenericOverlapR0065.includeOpen k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
            (ArithmeticThetaGenericOverlapR0065.openParameter k
              (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) ^ n * RX (v j') := by
            rw [map_mul, map_pow, hparamE, hregHom]
      _ = RX (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j')) :=
            by simpa [j'] using hright.symm
  have hcompleted :
      ArithmeticThetaGenericOverlapR0065.includeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
        (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
          (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))) =
      ArithmeticThetaGenericOverlapR0065.includeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
        (ArithmeticThetaCorrectedGammaR0061.restrict k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true (a j')) := by
    rw [hRY (a j), hRX (a j')] at hcleared
    have hmap := RingHom.congr_fun hE
      (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))
    have hcompleted' :
        ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          ((ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom
            (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))) =
        ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaCorrectedGammaR0061.restrict k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true (a j')) :=
      hmap.symm.trans hcleared
    calc
      ArithmeticThetaGenericOverlapR0065.includeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
            (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))) =
          ArithmeticThetaGenericOverlapR0065.includeOpen k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
            ((ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom
              (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))) :=
            congrArg (ArithmeticThetaGenericOverlapR0065.includeOpen k
              (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true)
              (congrFun (RingEquiv.coe_toRingHom
                (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt)) _).symm
      _ = ArithmeticThetaGenericOverlapR0065.includeOpen k
          (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true
          (ArithmeticThetaCorrectedGammaR0061.restrict k
            (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true (a j')) := hcompleted'
  exact (includeOpen_injective k
    (ArithmeticThetaIndexedOverlapsR0058.next r j.val) true) hcompleted

end ArithmeticThetaRatioRegularityR0067
