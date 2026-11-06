module

public import EqualDivisorUnitR0067
public import FractionAdjacentR0067
public import FractionRestrictionR0067
public import RegularFamilyDescentR0067
public import UniformCompletedClearingR0067
public import LocalFRationalCompatibilityR0065

@[expose] public section

/-! The conditional local comparison theorem for a compatible rational family.
The result is confined to the accepted completed annular charts. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067

open ArithmeticThetaLocalOrdersR0066
open ArithmeticThetaGenericOverlapR0065

theorem local_comparison_family :
    ∀ (k : Type u) [Field k] [CharZero k] (c : ℕ) (ζ : k)
      (hc : 1 < c) (hcop : Nat.Coprime c 6) (hζ : IsPrimitiveRoot ζ c)
      (hr : 0 < 2*c) (g : Fin (2*c) → FunctionField k),
      RationalCompatible k (2*c) hr g →
      (∀ (j : Fin (2*c)) (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k))
        [P.IsPrime], P.height = 1 →
        HasOrder k P (g j) (divisorCoefficient k c j.val ζ P)) →
      ∃ (v : Fin (2*c) → (GenericChart k)ˣ) (n : ℕ)
        (a : Fin (2*c) → Chart k),
        (∀ j, toFunctionField k (v j : GenericChart k) =
          ratio k (g j) (LocalTheta k c ζ hc hcop hζ j)) ∧
        RegularCompatible k (2*c) hr (fun j => (v j : GenericChart k)) ∧
        (∀ j, ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (a j) =
          parameter k ^ n * (v j : GenericChart k)) ∧
        CompletedCompatible k (2*c) hr a := by
  intro k _ _ c ζ hc hcop hζ hr g hgCompatible hdiv
  let ratios : Fin (2*c) → FunctionField k := fun j =>
    ratio k (g j) (LocalTheta k c ζ hc hcop hζ j)
  have hratio_eq (j : Fin (2*c)) :
      ratios j = ratio k (g j) (LocalTheta k c ζ hc hcop hζ j) := rfl
  have horders : ∀ (j : Fin (2*c)) (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 → HasOrder k P (ratios j) 0 := by
    intro j P hPinst hP
    have hg := hdiv j P hP
    have htheta := local_f_divisor k c j.val ζ hc hcop hζ j.isLt P hP
    have hratio := quotient_order k P (g j) (LocalTheta k c ζ hc hcop hζ j)
      (divisorCoefficient k c j.val ζ P) (divisorCoefficient k c j.val ζ P) hP
      hg htheta.1
    have hh : HasOrder k P (ratios j) (0 : ℤ) := by
      simpa [ratios, LocalTheta, ratio] using hratio
    exact hh
  have hregular : ∀ (j : Fin (2*c)) (P : Ideal (GenericChart k)) [P.IsPrime],
      P.height = 1 → RegularAt k P (ratios j) := by
    intro j P hPinst hP
    exact (order_regularity k P (ratios j) 0 hP (horders j P hP)).mpr (by omega)
  have hratiosCompatible : RationalCompatible k (2*c) hr ratios := by
    intro j FY FX E hFY hFX hE
    let j' : Fin (2*c) := nextIndex (2*c) hr j
    have hj' : j'.val < 2*c := j'.isLt
    have hlocal := ArithmeticThetaGenericOverlapR0065.local_f_rational_compatibility
      k c j.val ζ hc hcop hζ hr j.isLt hj'
    rcases hlocal with ⟨RX, RY, E0, hRX, hRY, hE0, hdenX, hdenEY, hnum⟩
    have hFYeq : FY = Classical.choose (fraction_restriction k j.val false) := by
      apply (Classical.choose_spec (fraction_restriction k j.val false)).2
      exact hFY
    have hFXeq : FX = Classical.choose (fraction_restriction k j'.val true) := by
      apply (Classical.choose_spec (fraction_restriction k j'.val true)).2
      exact hFX
    have hEeq : E = Classical.choose (fraction_adjacent k (2*c) hr j) := by
      apply (Classical.choose_spec (fraction_adjacent k (2*c) hr j)).2
      exact hE
    subst FY
    subst FX
    subst E
    let F0 : FunctionField k →+* OpenField k j.val false :=
      Classical.choose (fraction_restriction k j.val false)
    let G0 : FunctionField k →+* OpenField k j'.val true :=
      Classical.choose (fraction_restriction k j'.val true)
    let E1 : OpenField k j.val false ≃+* OpenField k j'.val true :=
      Classical.choose (fraction_adjacent k (2*c) hr j)
    have hF0 : IsFractionRestriction k j.val false F0 :=
      (Classical.choose_spec (fraction_restriction k j.val false)).1
    have hG0 : IsFractionRestriction k j'.val true G0 :=
      (Classical.choose_spec (fraction_restriction k j'.val true)).1
    have hE1 : IsFractionAdjacent k (2*c) hr j E1 :=
      (Classical.choose_spec (fraction_adjacent k (2*c) hr j)).1
    let FY0 : GenericChart k →+* ArithmeticThetaGenericOverlapR0065.GenericOpen k j.val false :=
      ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false
    let FX0 : GenericChart k →+* ArithmeticThetaGenericOverlapR0065.GenericOpen k j'.val true :=
      ArithmeticThetaGenericOverlapR0065.genericRestriction k j'.val true
    let Ebase : ArithmeticThetaGenericOverlapR0065.GenericOpen k j.val false ≃+*
        ArithmeticThetaGenericOverlapR0065.GenericOpen k j'.val true :=
      ArithmeticThetaRatioRegularityR0067.adjacent k (2*c) hr j
    have hRXeq : RX = FX0 := by
      dsimp [FX0]
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
      exact hRX.trans
        (ArithmeticThetaGenericOverlapR0065.genericRestriction_spec k j'.val true).symm
    have hRYeq : RY = FY0 := by
      dsimp [FY0]
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
      exact hRY.trans
        (ArithmeticThetaGenericOverlapR0065.genericRestriction_spec k j.val false).symm
    have hEeq : E0 = Ebase := by
      have hEbase : ArithmeticThetaGenericOverlapR0065.IsGenericAdjacent k (2*c) j.val hr j.isLt Ebase := by
        exact (Classical.choose_spec
          (ArithmeticThetaGenericOverlapR0065.generic_adjacent_providers k (2*c) j.val hr j.isLt)).1
      apply RingEquiv.ext
      intro x
      have hhom : E0.toRingHom = Ebase.toRingHom := by
        apply IsLocalization.ringHom_ext
          (Submonoid.powers
            (ArithmeticThetaGenericOverlapR0065.openParameter k j.val false))
        exact hE0.trans hEbase.symm
      exact RingHom.congr_fun hhom x
    rw [hRXeq] at hnum hdenX
    rw [hRYeq, hEeq] at hnum hdenEY
    have hF0_spec : F0.comp (toFunctionField k) =
        (openToField k j.val false).comp FY0 := hF0
    have hG0_spec : G0.comp (toFunctionField k) =
        (openToField k j'.val true).comp FX0 := hG0
    have hE1_spec : E1.toRingHom.comp (openToField k j.val false) =
        (openToField k j'.val true).comp Ebase.toRingHom := hE1
    have hF0eval (x : GenericChart k) :
        F0 (toFunctionField k x) = openToField k j.val false (FY0 x) :=
      RingHom.congr_fun hF0_spec x
    have hG0eval (x : GenericChart k) :
        G0 (toFunctionField k x) = openToField k j'.val true (FX0 x) :=
      RingHom.congr_fun hG0_spec x
    have hE1eval (x : ArithmeticThetaGenericOverlapR0065.GenericOpen k j.val false) :
        E1 (openToField k j.val false x) =
          openToField k j'.val true (Ebase x) := RingHom.congr_fun hE1_spec x
    have hnumField :
        E1 (F0 (toFunctionField k (numerator k c j.val ζ hc hcop hζ j.isLt))) *
            G0 (toFunctionField k (denominator k c j'.val ζ hc hcop hζ j'.isLt)) =
            G0 (toFunctionField k (numerator k c j'.val ζ hc hcop hζ j'.isLt)) *
            E1 (F0 (toFunctionField k (denominator k c j.val ζ hc hcop hζ j.isLt))) := by
      have hmapped := congrArg (openToField k j'.val true) hnum
      change E1 (F0 (toFunctionField k (numerator k c j.val ζ hc hcop hζ j.isLt))) *
          G0 (toFunctionField k (denominator k c
            (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val) ζ hc hcop hζ hj')) =
        G0 (toFunctionField k (numerator k c
            (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val) ζ hc hcop hζ hj')) *
          E1 (F0 (toFunctionField k (denominator k c j.val ζ hc hcop hζ j.isLt)))
      calc
        _ = openToField k j'.val true (Ebase (FY0
              (numerator k c j.val ζ hc hcop hζ j.isLt))) *
            openToField k j'.val true (FX0
              (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
                ζ hc hcop hζ hj')) := by
              rw [hF0eval, hG0eval, hE1eval]
        _ = openToField k j'.val true
              (Ebase (FY0 (numerator k c j.val ζ hc hcop hζ j.isLt)) *
                FX0 (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
                  ζ hc hcop hζ hj')) := (map_mul _ _ _).symm
        _ = openToField k j'.val true
              (FX0 (numerator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
                ζ hc hcop hζ hj') *
                Ebase (FY0 (denominator k c j.val ζ hc hcop hζ j.isLt))) :=
              congrArg (openToField k j'.val true) hnum
        _ = _ := by
          rw [map_mul, ← hE1eval, ← hF0eval, ← hG0eval]
    have hden0 : G0 (toFunctionField k (denominator k c j'.val ζ hc hcop hζ j'.isLt)) ≠ 0 := by
      change G0 (toFunctionField k
          (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
            ζ hc hcop hζ hj')) ≠ 0
      intro hz
      have hz' : openToField k j'.val true
          (FX0 (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
            ζ hc hcop hζ hj')) = 0 := by
        rw [← hG0eval (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
          ζ hc hcop hζ hj'), hz]
      apply mem_nonZeroDivisors_iff_ne_zero.mp hdenX
      apply (IsFractionRing.injective (GenericOpen k j'.val true)
        (OpenField k j'.val true))
      change openToField k j'.val true
          (FX0 (denominator k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j.val)
            ζ hc hcop hζ hj')) = openToField k j'.val true 0
      simpa only [map_zero] using hz'
    have hden1 : E1 (F0 (toFunctionField k (denominator k c j.val ζ hc hcop hζ j.isLt))) ≠ 0 := by
      intro hz
      have h := hdenEY
      have hz' : E1 (openToField k j.val false
          (FY0 (denominator k c j.val ζ hc hcop hζ j.isLt))) = 0 := by
        rw [← hF0eval, hz]
      have hz'' : openToField k j'.val true
          (Ebase (FY0 (denominator k c j.val ζ hc hcop hζ j.isLt))) = 0 := by
        exact (hE1eval _).symm.trans hz'
      apply mem_nonZeroDivisors_iff_ne_zero.mp hdenEY
      apply (IsFractionRing.injective (GenericOpen k j'.val true)
        (OpenField k j'.val true))
      change openToField k j'.val true
          (Ebase (FY0 (denominator k c j.val ζ hc hcop hζ j.isLt))) =
        openToField k j'.val true 0
      simpa only [map_zero] using hz''
    have hquot :
        E1 (F0 (toFunctionField k (numerator k c j.val ζ hc hcop hζ j.isLt))) /
            E1 (F0 (toFunctionField k (denominator k c j.val ζ hc hcop hζ j.isLt))) =
          G0 (toFunctionField k (numerator k c j'.val ζ hc hcop hζ j'.isLt)) /
            G0 (toFunctionField k (denominator k c j'.val ζ hc hcop hζ j'.isLt)) :=
      (div_eq_div_iff hden1 hden0).2 hnumField
    have hratio_g := hgCompatible j F0 G0 E1 hF0 hG0 hE1
    calc
      E1 (F0 (ratios j)) =
          E1 (F0 (g j)) /
            (E1 (F0 (toFunctionField k
              (numerator k c j.val ζ hc hcop hζ j.isLt))) /
              E1 (F0 (toFunctionField k
                (denominator k c j.val ζ hc hcop hζ j.isLt)))) := by
            change E1 (F0
                (g j /
                  (toFunctionField k (numerator k c j.val ζ hc hcop hζ j.isLt) /
                    toFunctionField k (denominator k c j.val ζ hc hcop hζ j.isLt)))) = _
            simp only [map_div₀]
      _ = G0 (g j') /
            (G0 (toFunctionField k
              (numerator k c j'.val ζ hc hcop hζ j'.isLt)) /
              G0 (toFunctionField k
                (denominator k c j'.val ζ hc hcop hζ j'.isLt))) := by
            rw [hratio_g, hquot]
      _ = G0 (ratios j') := by
            change G0 (g j') /
                (G0 (toFunctionField k
                  (numerator k c j'.val ζ hc hcop hζ j'.isLt)) /
                  G0 (toFunctionField k
                    (denominator k c j'.val ζ hc hcop hζ j'.isLt))) =
              G0 (g j' /
                (toFunctionField k (numerator k c j'.val ζ hc hcop hζ j'.isLt) /
                  toFunctionField k (denominator k c j'.val ζ hc hcop hζ j'.isLt)))
            rw [map_div₀, map_div₀]
  obtain ⟨units0, ⟨hunitval0, hunitsCompat⟩, _⟩ :=
    regular_family_descent k (2*c) hr ratios hratiosCompatible hregular
  let u : Fin (2*c) → (GenericChart k)ˣ := fun j =>
    Classical.choose (equal_divisor_unit k c j.val ζ hc hcop hζ j.isLt (g j)
      (fun P hP hheight => hdiv j P hheight))
  have huval : ∀ j, toFunctionField k (u j : GenericChart k) = ratios j := by
    intro j
    have hu := Classical.choose_spec (equal_divisor_unit k c j.val ζ hc hcop hζ j.isLt
      (g j) (fun P hP hheight => hdiv j P hheight))
    simpa [ratios, LocalTheta] using hu.1
  have hucompat : RegularCompatible k (2*c) hr (fun j => (u j : GenericChart k)) := by
    intro j
    let FY : FunctionField k →+* OpenField k j.val false :=
      Classical.choose (fraction_restriction k j.val false)
    let FX : FunctionField k →+* OpenField k (nextIndex (2*c) hr j).val true :=
      Classical.choose (fraction_restriction k (nextIndex (2*c) hr j).val true)
    let E : OpenField k j.val false ≃+* OpenField k (nextIndex (2*c) hr j).val true :=
      Classical.choose (fraction_adjacent k (2*c) hr j)
    have hFY : IsFractionRestriction k j.val false FY :=
      (Classical.choose_spec (fraction_restriction k j.val false)).1
    have hFX : IsFractionRestriction k (nextIndex (2*c) hr j).val true FX :=
      (Classical.choose_spec (fraction_restriction k (nextIndex (2*c) hr j).val true)).1
    have hE : IsFractionAdjacent k (2*c) hr j E :=
      (Classical.choose_spec (fraction_adjacent k (2*c) hr j)).1
    have hrat := hratiosCompatible j FY FX E hFY hFX hE
    have hvleft := huval j
    have hvright := huval (nextIndex (2*c) hr j)
    have hcomm : E (FY (toFunctionField k (u j : GenericChart k))) =
        FX (toFunctionField k (u (nextIndex (2*c) hr j) : GenericChart k)) := by
      rw [hvleft, hvright]
      exact hrat
    apply (IsFractionRing.injective (GenericOpen k (nextIndex (2*c) hr j).val true)
      (OpenField k (nextIndex (2*c) hr j).val true))
    change openToField k (nextIndex (2*c) hr j).val true
        (adjacent k (2*c) hr j
          (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (u j : GenericChart k))) = _
    calc
      _ = E (FY (toFunctionField k (u j : GenericChart k))) := by
        calc
          _ = E (openToField k j.val false
              (ArithmeticThetaGenericOverlapR0065.genericRestriction k j.val false (u j : GenericChart k))) := by
                exact (RingHom.congr_fun hE _).symm
          _ = _ := by
            exact congrArg E (RingHom.congr_fun hFY (u j)).symm
      _ = FX (toFunctionField k (u (nextIndex (2*c) hr j) : GenericChart k)) := hcomm
      _ = _ := by
        exact RingHom.congr_fun hFX (u (nextIndex (2*c) hr j))
  obtain ⟨n, a, ha, hacompat⟩ :=
    uniform_completed_clearing k (2*c) hr (fun j => (u j : GenericChart k)) hucompat
  refine ⟨u, n, a, ?_, hucompat, ha, hacompat⟩
  intro j
  simpa [ratios, LocalTheta] using huval j

end ArithmeticThetaRatioRegularityR0067
