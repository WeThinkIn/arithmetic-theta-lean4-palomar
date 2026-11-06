import TateMarkedPointDoubling
import TateBasicFourthIdentity
import TateSeriesSubstitution
import FourTorsionRoot

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaTateSeries
open ArithmeticThetaTateIdentities ArithmeticThetaFourTorsion

theorem marked_root_expansion :
    ∀ {k : Type u} [Field k] [CharZero k],
      yR k ≠ 0 ∧ 2 * rootExpression (toLaurent k (e₁ k)) (toLaurent k (e₂ k))
        (toLaurent k (e₃ k)) (toLaurent k (xR k)) (toLaurent k (yR k)) =
          toLaurent k (PowerSeries.expand 2 (by norm_num) (theta k) ^ 2) := by
  intro k _ _
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : DecidableEq (LaurentSeries k) := Classical.decEq _
  let j := toLaurent k
  let E₁ := j (e₁ k)
  let E₂ := j (e₂ k)
  let E₃ := j (e₃ k)
  let X := j (xR k)
  let Y := j (yR k)
  let B := j (PowerSeries.expand 2 (by norm_num) (theta k) ^ 2)
  have hy : yR k ≠ 0 := by
    intro h
    have hc := marked_cusp_terms (k := k) 1 (by decide)
    have hcoeff := congrArg (PowerSeries.coeff 1) h
    have hlead : PowerSeries.coeff 1 (yR k) = (2 : k)⁻¹ := by
      simpa [yR] using hc.2.2.2.2.1
    rw [hlead] at hcoeff
    simpa using hcoeff
  have hyL : Y ≠ 0 := by
    intro h
    apply hy
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
    change (HahnSeries.ofPowerSeries ℤ k) (yR k) = 0 at h
    simpa using h
  have hsplit : (splitCurve E₁ E₂ E₃).Nonsingular E₂ 0 ∧
      (splitCurve E₁ E₂ E₃).Nonsingular X Y := by
    have h := literal_doubling (k := k)
    rcases h with ⟨hP, hR, hd⟩
    simpa [E₁, E₂, E₃, X, Y, j] using ⟨hP, hR⟩
  have hrootSq : rootExpression E₁ E₂ E₃ X Y ^ 2 = E₂ - E₁ := by
    have h := literal_doubling (k := k)
    rcases h with ⟨hP, hR, hd⟩
    have hdist12 : E₁ ≠ E₂ := by
      exact fun hh => (literal_split_cubic (k := k)).2.1
        (HahnSeries.ofPowerSeries_injective hh)
    have hdist13 : E₁ ≠ E₃ := by
      exact fun hh => (literal_split_cubic (k := k)).2.2.1
        (HahnSeries.ofPowerSeries_injective hh)
    have hdist23 : E₂ ≠ E₃ := by
      exact fun hh => (literal_split_cubic (k := k)).2.2.2
        (HahnSeries.ofPowerSeries_injective hh)
    let R : (splitCurve E₁ E₂ E₃).Point := .some X Y hR
    have hd' : 2 • R = .some E₂ 0 hP := by
      rw [two_nsmul]
      change (R.add R) = .some E₂ 0 hP
      simpa [R, E₁, E₂, E₃, X, Y, j] using hd
    have hhalf := actual_half_root (LaurentSeries k) E₁ E₂ E₃ hP R
      hdist12 hdist13 hdist23 hd'
    rcases hhalf with ⟨x, y, hxy, hRxy, _hy, hs, _⟩
    have hcoord : x = X ∧ y = Y := by
      change (.some X Y hR : (splitCurve E₁ E₂ E₃).Point) = .some x y hxy at hRxy
      have hi := WeierstrassCurve.Affine.Point.some.inj hRxy
      exact ⟨hi.1.symm, hi.2.symm⟩
    simpa [hcoord.1, hcoord.2] using hs
  have hsubstX : tateX 4 2 (1 : k) = PowerSeries.expand 2 (by norm_num) (tateX 2 1 (1 : k)) := by
    exact (ramified_substitution 2 2 1 (1 : k) (by decide)
      (by norm_num [Admissible])).1
  have hsubstE : tateX 4 0 (-1 : k) = PowerSeries.expand 2 (by norm_num) (tateX 2 0 (-1 : k)) := by
    exact (ramified_substitution 2 2 0 (-1 : k) (by decide)
      (by norm_num [Admissible])).1
  have hD : E₂ - E₁ = B ^ 2 / 4 := by
    have hfour := basic_fourth (k := k)
    have hex := congrArg (PowerSeries.expand 2 (by norm_num)) hfour
    rw [map_pow, map_mul, map_sub] at hex
    rw [← hsubstX, ← hsubstE] at hex
    apply (eq_div_iff (show (4 : LaurentSeries k) ≠ 0 by norm_num)).2
    have hexL := congrArg j hex
    rw [map_pow, map_mul, map_sub] at hexL
    have hconst : j (PowerSeries.expand 2 (by norm_num) (4 : PowerSeries k)) =
        (4 : LaurentSeries k) := by
      rw [show PowerSeries.expand 2 (by norm_num) (4 : PowerSeries k) = 4 by
        change PowerSeries.expand 2 (by norm_num) ((algebraMap k (PowerSeries k)) (4 : k)) = _
        rw [AlgHom.commutes]
        exact map_ofNat (algebraMap k (PowerSeries k)) 4]
      rw [map_ofNat]
    rw [hconst] at hexL
    calc
      (E₂ - E₁) * (4 : LaurentSeries k) = j (PowerSeries.expand 2 (by norm_num) (theta k)) ^ 4 := by
        simpa [E₁, E₂, e₁, e₂, j, mul_comm] using hexL.symm
      _ = B ^ 2 := by
        simp only [B, map_pow]
        ring
  have hsq : (2 * rootExpression E₁ E₂ E₃ X Y) ^ 2 = B ^ 2 := by
    rw [mul_pow, hrootSq, hD]
    ring
  have hsign : 2 * rootExpression E₁ E₂ E₃ X Y + B ≠ 0 := by
    intro hneg
    have hmul := congrArg (fun z : LaurentSeries k => z * (2 * Y)) hneg
    simp only [rootExpression] at hmul
    field_simp [hyL] at hmul
    have hmulPS :
        (xR k - e₁ k) ^ 2 - (e₁ k - e₂ k) * (e₁ k - e₃ k) +
            yR k * (PowerSeries.expand 2 (by norm_num) (theta k) ^ 2) = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
      simpa [E₁, E₂, E₃, X, Y, B, j, toLaurent] using hmul
    have hv := marked_cusp_vanishing (k := k) 1 (by decide)
    have hx0 : PowerSeries.coeff 0 (xR k) = 0 := hv.2.2.1 0 (by decide)
    have hy0 : PowerSeries.coeff 0 (yR k) = 0 := hv.2.2.2 0 (by decide)
    have he20 : PowerSeries.coeff 0 (e₂ k) = 0 := hv.1 0 (by decide)
    have he30 : PowerSeries.coeff 0 (e₃ k) = 0 := hv.2.1 0 (by decide)
    have hx1 : PowerSeries.coeff 1 (xR k) = 1 := (marked_cusp_terms (k := k) 1 (by decide)).2.2.2.1
    have hy1 : PowerSeries.coeff 1 (yR k) = (2 : k)⁻¹ := (marked_cusp_terms (k := k) 1 (by decide)).2.2.2.2.1
    have he10 : PowerSeries.coeff 0 (e₁ k) = -(4 : k)⁻¹ := (marked_cusp_terms (k := k) 1 (by decide)).1
    have he11 : PowerSeries.coeff 1 (e₁ k) = 0 := by
      rw [show e₁ k = PowerSeries.expand 2 (by norm_num) (tateX 2 0 (-1 : k)) by
        exact hsubstE]
      rw [PowerSeries.coeff_expand]
      simp
    have he21 : PowerSeries.coeff 1 (e₂ k) = 0 := by
      rw [show e₂ k = PowerSeries.expand 2 (by norm_num) (tateX 2 1 (1 : k)) by
        exact hsubstX]
      rw [PowerSeries.coeff_expand]
      simp
    have he31 : PowerSeries.coeff 1 (e₃ k) = 0 := by
      rw [show e₃ k = PowerSeries.expand 2 (by norm_num) (tateX 2 1 (-1 : k)) by
        exact (ramified_substitution 2 2 1 (-1 : k) (by decide)
          (by norm_num [Admissible])).1]
      rw [PowerSeries.coeff_expand]
      simp
    have hB0 : PowerSeries.coeff 0 (PowerSeries.expand 2 (by norm_num) (theta k) ^ 2) = 1 := by
      simp [PowerSeries.coeff_mul, theta]
    have hc := congrArg (PowerSeries.coeff 1) hmulPS
    simp only [map_add, map_sub, map_zero, PowerSeries.coeff_one_pow,
      PowerSeries.coeff_one_mul, PowerSeries.coeff_zero_eq_constantCoeff] at hc
    have hcx0 : PowerSeries.constantCoeff (xR k) = 0 := by simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hx0
    have hcy0 : PowerSeries.constantCoeff (yR k) = 0 := by simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hy0
    have he1c0 : PowerSeries.constantCoeff (e₁ k) = -(4 : k)⁻¹ := by simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using he10
    have he2c0 : PowerSeries.constantCoeff (e₂ k) = 0 := by simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using he20
    have he3c0 : PowerSeries.constantCoeff (e₃ k) = 0 := by simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using he30
    have hBc0 : PowerSeries.constantCoeff (PowerSeries.expand 2 (by norm_num) (theta k) ^ 2) = 1 := by
      simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hB0
    rw [hx1, hy1, he11, he21, he31, hcx0, hcy0, he1c0, he2c0, he3c0, hBc0] at hc
    norm_num at hc
  have heq : 2 * rootExpression E₁ E₂ E₃ X Y = B := by
    have hz : (2 * rootExpression E₁ E₂ E₃ X Y - B) *
        (2 * rootExpression E₁ E₂ E₃ X Y + B) = 0 := by
      calc
        _ = (2 * rootExpression E₁ E₂ E₃ X Y) ^ 2 - B ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hsign)
  exact ⟨hy, by simpa [B, E₁, E₂, E₃, X, Y, j] using heq⟩

end ArithmeticThetaTateSeries

#print axioms ArithmeticThetaTateSeries.marked_root_expansion
