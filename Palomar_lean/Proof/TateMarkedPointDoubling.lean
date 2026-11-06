module

public import TateGeneralSplitCubic
public import TateMarkedCuspOrders
public import SplitCubicGeometry
public import Theorems.Thm_TateCurve_symAdd_sum_regional
public import TateSeriesCuspTerms

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaTateSeries
open ArithmeticThetaTateIdentities ArithmeticThetaFourTorsion

/-- The literal marked coordinates lie on the smooth split cubic. -/
theorem literal_split_cubic :
    ∀ {k : Type u} [Field k] [CharZero k],
      (splitCurve (e₁ k) (e₂ k) (e₃ k)).Equation (xR k) (yR k) ∧
      e₁ k ≠ e₂ k ∧ e₁ k ≠ e₃ k ∧ e₂ k ≠ e₃ k := by
  intro k _ _
  have h := general_annular_split_cubic (k := k) 2 1 1
    (by norm_num [Admissible])
  refine ⟨?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [splitCurve, zero_mul, add_zero]
    change (yR k)^2 = (xR k-e₁ k)*(xR k-e₂ k)*(xR k-e₃ k) at h
    rw [h]
    ring
  · exact general_two_torsion_distinct (k := k) 2 (by decide)

open scoped LaurentSeries.XAdic
local instance {k : Type u} [Field k] [CharZero k] : CharZero (LaurentSeries k) :=
  LaurentSeries.XAdic.charZero k

variable {k : Type u} [Field k] [CharZero k]

private def t : LaurentSeries k := HahnSeries.single 1 1

private lemma mono_one (n : ℕ) : toLaurent k (monomial 1 n) = (t : LaurentSeries k)^n := by
  simp [monomial, toLaurent, t]

private lemma t_off (r : ℕ) (hr : 0 < r) (hr4 : r < 4) :
    TateCurve.OffLattice ((t : LaurentSeries k)^4) (t^r) := by
  intro n hn
  have ht : (t : LaurentSeries k) ≠ 0 := LaurentSeries.XAdic.single_one_one_ne_zero k
  have he : ((t : LaurentSeries k)^4)^n * t^r = t^(4*n+(r : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast t r, ← zpow_add₀ ht]
    norm_num
  rw [he] at hn
  have hnorm := congrArg norm hn
  rw [norm_zpow, norm_one] at hnorm
  have hp : 0 < ‖(t : LaurentSeries k)‖ := norm_pos_iff.mpr ht
  have hlt : ‖(t : LaurentSeries k)‖ < 1 := LaurentSeries.XAdic.norm_X_lt_one k
  have hz : 4*n+(r : ℤ) = 0 := by
    exact (zpow_right_injective₀ hp (ne_of_lt hlt)) (by simpa using hnorm)
  omega

private lemma marked_sym_sum :
    let j := toLaurent k
    let q := (t : LaurentSeries k)^4
    2*j (xR k)*(j (xR k)-j (e₂ k))^2 =
      TateCurve.symSumNum q (j (xR k)) (j (e₂ k)) := by
  dsimp only
  have ht0 : (t : LaurentSeries k) ≠ 0 := LaurentSeries.XAdic.single_one_one_ne_zero k
  have hq0 := pow_ne_zero 4 ht0
  have htn : 0 < ‖(t : LaurentSeries k)‖ := norm_pos_iff.mpr ht0
  have htn1 : ‖(t : LaurentSeries k)‖ < 1 := LaurentSeries.XAdic.norm_X_lt_one k
  have hq : ‖(t : LaurentSeries k)^4‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ htn.le htn1 (by decide)
  have hprod : (t : LaurentSeries k)*t^2 = t^3 := by ring
  have hdiv : (t : LaurentSeries k)*(t^2)⁻¹ = t⁻¹ := by field_simp
  have hti : TateCurve.OffLattice ((t : LaurentSeries k)^4) t := by simpa using t_off (k := k) 1 (by decide) (by decide)
  have ht2 := t_off (k := k) 2 (by decide) (by decide)
  have ht3 := t_off (k := k) 3 (by decide) (by decide)
  have hti' : TateCurve.OffLattice ((t : LaurentSeries k)^4) t⁻¹ :=
    TateCurve.OffLattice.inv hq0 hti
  have hp : TateCurve.AddParams ((t : LaurentSeries k)^4) t (t^2) :=
    ⟨hq0, ht0, pow_ne_zero 2 ht0, hti, ht2, hprod ▸ ht3, hdiv ▸ hti'⟩
  have hregion : TateCurve.ExpansionRegion ((t : LaurentSeries k)^4) t (t^2) := by
    refine ⟨hp, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [hprod, hdiv, norm_pow, norm_inv]
    · simpa using pow_lt_pow_right_of_lt_one₀ htn htn1 (by decide : 1 < 4)
    · simpa only [← pow_succ] using pow_lt_one₀ htn.le htn1 (by decide : 5 ≠ 0)
    · exact pow_lt_pow_right_of_lt_one₀ htn htn1 (by decide : 2 < 4)
    · rw [← pow_add]; exact pow_lt_one₀ htn.le htn1 (by decide)
    · exact pow_lt_pow_right_of_lt_one₀ htn htn1 (by decide : 3 < 4)
    · rw [← pow_add]; exact pow_lt_one₀ htn.le htn1 (by decide)
    · have : 1 < ‖(t : LaurentSeries k)‖⁻¹ := (one_lt_inv₀ htn).mpr htn1
      exact lt_trans (by simpa [norm_pow] using hq) this
    · rw [pow_succ, mul_assoc, mul_inv_cancel₀ htn.ne', mul_one]
      exact pow_lt_one₀ htn.le htn1 (by decide)
  have hs := TateCurve.symAdd_sum_regional hq0 hq t (t^2) hregion
  have hx1 : toLaurent k (xR k) = TateCurve.pointX (t^4) t := by
    simpa only [xR, mono_one, pow_one] using tateX_eq_pointX (k := k) 4 1 1 (by norm_num [Admissible])
  have hx2 : toLaurent k (e₂ k) = TateCurve.pointX (t^4) (t^2) := by
    simpa only [e₂, mono_one] using tateX_eq_pointX (k := k) 4 2 1 (by norm_num [Admissible])
  have hx3 : TateCurve.pointX ((t : LaurentSeries k)^4) (t^3) = TateCurve.pointX (t^4) t := by
    have he : (t : LaurentSeries k)^3 = t^4*t⁻¹ := by field_simp
    rw [he, TateCurve.pointX_q_mul hq0, TateCurve.pointX_inv hq0 ht0 hti]
  rw [hprod, hdiv, hx3, TateCurve.pointX_inv hq0 ht0 hti, ← hx1, ← hx2, ← two_mul] at hs
  exact hs


private theorem coefficients_of_roots {F : Type*} [Field F]
    (B C D e₁ e₂ e₃ : F) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (h1 : e₁^3+B*e₁^2+C*e₁+D=0) (h2 : e₂^3+B*e₂^2+C*e₂+D=0)
    (h3 : e₃^3+B*e₃^2+C*e₃+D=0) :
    B = -(e₁+e₂+e₃) ∧ C = e₁*e₂+e₁*e₃+e₂*e₃ ∧ D = -(e₁*e₂*e₃) := by
  have h12' : e₁^2+e₁*e₂+e₂^2+B*(e₁+e₂)+C = 0 := by
    apply (mul_eq_zero.mp (show (e₁-e₂)*(e₁^2+e₁*e₂+e₂^2+B*(e₁+e₂)+C)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h12)
    linear_combination h1-h2
  have h13' : e₁^2+e₁*e₃+e₃^2+B*(e₁+e₃)+C = 0 := by
    apply (mul_eq_zero.mp (show (e₁-e₃)*(e₁^2+e₁*e₃+e₃^2+B*(e₁+e₃)+C)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h13)
    linear_combination h1-h3
  have hsum : e₁+e₂+e₃+B = 0 := by
    apply (mul_eq_zero.mp (show (e₂-e₃)*(e₁+e₂+e₃+B)=0 from ?_)).resolve_left
      (sub_ne_zero.mpr h23)
    linear_combination h12'-h13'
  have hpair : C-(e₁*e₂+e₁*e₃+e₂*e₃)=0 := by
    linear_combination h12'-(e₁+e₂)*hsum
  have hprod : D+e₁*e₂*e₃=0 := by
    linear_combination h1-e₁^2*hsum-e₁*hpair
  exact ⟨by linear_combination hsum, by linear_combination hpair, by linear_combination hprod⟩


private lemma marked_coefficients :
    let j := toLaurent k
    (1/4 : LaurentSeries k) = -(j (e₁ k)+j (e₂ k)+j (e₃ k)) ∧
    TateCurve.a₄ ((t : LaurentSeries k)^4) = j (e₁ k)*j (e₂ k)+j (e₁ k)*j (e₃ k)+j (e₂ k)*j (e₃ k) ∧
    TateCurve.a₆ ((t : LaurentSeries k)^4) = -(j (e₁ k)*j (e₂ k)*j (e₃ k)) := by
  dsimp only
  have hinj : Function.Injective (toLaurent k) := HahnSeries.ofPowerSeries_injective
  rcases (literal_split_cubic (k := k)).2 with ⟨h12,h13,h23⟩
  apply coefficients_of_roots _ _ _ _ _ _
    (fun h => h12 (hinj h)) (fun h => h13 (hinj h)) (fun h => h23 (hinj h))
  · have h := literal_tate_equation (k := k) 4 0 (-1) (by norm_num [Admissible])
    simpa only [mono_one, tateY_boundary_neg_one, map_zero, zero_pow (by decide : 2 ≠ 0), e₁] using h.symm
  · have h := literal_tate_equation (k := k) 4 2 1 (by norm_num [Admissible])
    simpa only [mono_one, show 4 = 2*2 from rfl, tateY_midpoint_one 2 (by decide), map_zero,
      zero_pow (by decide : 2 ≠ 0), e₂] using h.symm
  · have h := literal_tate_equation (k := k) 4 2 (-1) (by norm_num [Admissible])
    simpa only [mono_one, show 4 = 2*2 from rfl, tateY_midpoint_neg_one 2 (by decide), map_zero,
      zero_pow (by decide : 2 ≠ 0), e₃] using h.symm

private lemma marked_nonzero : toLaurent k (yR k) ≠ 0 ∧
    toLaurent k (xR k) ≠ toLaurent k (e₂ k) := by
  have hinj : Function.Injective (toLaurent k) := HahnSeries.ofPowerSeries_injective
  have hc := marked_cusp_terms (k := k) 1 (by decide)
  have hv := marked_cusp_vanishing (k := k) 1 (by decide)
  constructor
  · intro h
    have h0 : yR k = 0 := hinj (by simpa using h)
    have h1 := congrArg (PowerSeries.coeff 1) h0
    have hlead : PowerSeries.coeff 1 (yR k) = (2:k)⁻¹ := hc.2.2.2.2.1
    rw [hlead] at h1
    simpa using h1
  · intro h
    have h1 := congrArg (PowerSeries.coeff 1) (hinj h)
    have hx : PowerSeries.coeff 1 (xR k) = 1 := hc.2.2.2.1
    have he : PowerSeries.coeff 1 (e₂ k) = 0 := by
      simpa only [map_zero, e₂, Nat.mul_one] using hv.1 1 (by decide)
    rw [hx, he] at h1
    exact one_ne_zero h1

private lemma marked_half_relation :
    let j := toLaurent k
    (j (xR k)-j (e₂ k))^2 = (j (e₂ k)-j (e₁ k))*(j (e₂ k)-j (e₃ k)) := by
  dsimp only
  rcases marked_coefficients (k := k) with ⟨hB,hC,hD⟩
  have hs := marked_sym_sum (k := k)
  dsimp only [TateCurve.symSumNum] at hs
  rw [hC,hD] at hs
  have hh : 2*(toLaurent k (xR k)-toLaurent k (e₂ k))*
      ((toLaurent k (xR k)-toLaurent k (e₂ k))^2-
        (toLaurent k (e₂ k)-toLaurent k (e₁ k))*(toLaurent k (e₂ k)-toLaurent k (e₃ k))) = 0 := by
    linear_combination hs + 4 * toLaurent k (xR k) * toLaurent k (e₂ k) * hB
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (marked_nonzero (k := k)).2)))


private lemma split_double_of_half {F : Type*} [Field F] [CharZero F]
    (a b c x y : F) (hy : y ≠ 0) (hx : x ≠ b)
    (heq : y^2 = (x-a)*(x-b)*(x-c))
    (hhalf : (x-b)^2 = (b-a)*(b-c))
    (hR : (splitCurve a b c).Nonsingular x y)
    (hP : (splitCurve a b c).Nonsingular b 0) :
    @WeierstrassCurve.Affine.Point.add F _ _ (Classical.decEq _)
      (.some x y hR) (.some x y hR) = .some b 0 hP := by
  classical
  have hn : y ≠ (splitCurve a b c).negY x y := by
    simp only [WeierstrassCurve.Affine.negY, splitCurve, zero_mul, sub_zero]
    intro h
    apply hy
    have hh : (2:F)*y = 0 := by linear_combination h
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hxb : x-b ≠ 0 := sub_ne_zero.mpr hx
  have hslope : (splitCurve a b c).slope x x y y = y/(x-b) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn]
    simp only [splitCurve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
    field_simp
    linear_combination (x-b)*hhalf - 2*heq
  have haddX : (splitCurve a b c).addX x x (y/(x-b)) = b := by
    simp only [WeierstrassCurve.Affine.addX, splitCurve, zero_mul, add_zero]
    field_simp
    linear_combination heq - (x-b)*hhalf
  have haddY : (splitCurve a b c).addY x x y (y/(x-b)) = 0 := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [haddX]
    simp only [WeierstrassCurve.Affine.negY, splitCurve, zero_mul, sub_zero]
    field_simp
    <;> ring
  change WeierstrassCurve.Affine.Point.some x y hR + .some x y hR = .some b 0 hP
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn]
  simp only [hslope, haddX, haddY]

/-- Actual elliptic-curve doubling of the literal marked point over k((t)). -/
theorem literal_doubling :
    ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (hP : (splitCurve (toLaurent k (e₁ k)) (toLaurent k (e₂ k))
      (toLaurent k (e₃ k))).Nonsingular (toLaurent k (e₂ k)) 0)
      (hR : (splitCurve (toLaurent k (e₁ k)) (toLaurent k (e₂ k))
      (toLaurent k (e₃ k))).Nonsingular (toLaurent k (xR k)) (toLaurent k (yR k))),
      @WeierstrassCurve.Affine.Point.add (LaurentSeries k) _ _ (Classical.decEq _)
        (.some (toLaurent k (xR k)) (toLaurent k (yR k)) hR)
        (.some (toLaurent k (xR k)) (toLaurent k (yR k)) hR) =
          .some (toLaurent k (e₂ k)) 0 hP := by
  intro k _ _
  have hinj : Function.Injective (toLaurent k) := HahnSeries.ofPowerSeries_injective
  rcases literal_split_cubic (k := k) with ⟨heq,h12,h13,h23⟩
  have hsm := split_smooth (toLaurent k (e₁ k)) (toLaurent k (e₂ k)) (toLaurent k (e₃ k))
    (fun h => h12 (hinj h)) (fun h => h13 (hinj h)) (fun h => h23 (hinj h))
  have heq' : (toLaurent k (yR k))^2 =
      (toLaurent k (xR k)-toLaurent k (e₁ k))*
      (toLaurent k (xR k)-toLaurent k (e₂ k))*
      (toLaurent k (xR k)-toLaurent k (e₃ k)) := by
    have h := general_annular_split_cubic (k := k) 2 1 1 (by norm_num [Admissible])
    have hj := congrArg (toLaurent k) h
    simpa only [map_pow,map_mul,map_sub, xR, yR, e₁, e₂, e₃, show 2*2 = 4 from rfl] using hj
  have hR : (splitCurve (toLaurent k (e₁ k)) (toLaurent k (e₂ k))
      (toLaurent k (e₃ k))).Nonsingular (toLaurent k (xR k)) (toLaurent k (yR k)) := by
    rw [WeierstrassCurve.Affine.Nonsingular]
    refine ⟨(split_equation _ _ _ _ _).mpr heq', Or.inr ?_⟩
    rw [WeierstrassCurve.Affine.evalEval_polynomialY]
    simp only [splitCurve, zero_mul, add_zero]
    exact mul_ne_zero (by norm_num) (marked_nonzero (k := k)).1
  exact ⟨hsm.2.2.1, hR, split_double_of_half _ _ _ _ _
    (marked_nonzero (k := k)).1 (marked_nonzero (k := k)).2 heq'
    (marked_half_relation (k := k)) hR hsm.2.2.1⟩

end ArithmeticThetaTateSeries
