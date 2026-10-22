module

public import TateCuspDefinitionsR0181
public import CompactifiedCoordinateIsomorphismR0145

@[expose] public section

/-! The normalized pole of the invariant of the fixed literal Tate cubic. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaTateCuspsR0181
namespace JPole
open ArithmeticThetaTateSeries ArithmeticThetaTateIdentities
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145

variable {k : Type u} [Field k]

private lemma xTerm_coeff_below (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (xTerm (monomial a r)) = 0 := by
  rw [ArithmeticThetaTateBridges.x_term_coeff a r n (by omega)]
  split_ifs with hd
  · have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt hd h
    simp [hn]
  · rfl

/-- The midpoint coordinates have no terms below the half-period. -/
lemma midpoint_divisible (m : ℕ) (a : k) :
    (PowerSeries.X : PowerSeries k)^m ∣ tateX (2*m) m a := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  have hx : PowerSeries.coeff n
      (∑ j ∈ Finset.range (n+1),
        (xTerm (monomial a (2*m*(j+1)+m)) +
         xTerm (monomial a⁻¹ (2*m*(j+1)-m)))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_add, xTerm_coeff_below a (by nlinarith),
      xTerm_coeff_below a⁻¹ (by
        have : 2*m ≤ 2*m*(j+1) := by nlinarith
        omega), add_zero]
  have hc : PowerSeries.coeff n
      (∑ j ∈ Finset.range (n+1),
        PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (2*m*(j+1)) *
          (1-monomial 1 (2*m*(j+1)))⁻¹) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [monomial, map_one, one_mul]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp [show ¬ 2*m*(j+1) ≤ n by nlinarith]
  simp only [tateX, PowerSeries.coeff_mk, partialX]
  rw [map_sub, map_add, xTerm_coeff_below a hn, hx, two_mul, map_add, hc]
  simp

variable [CharZero k]

/-- The difference of the two colliding roots is t^m times a series starting at 4. -/
lemma root_difference (m : ℕ) (hm : 0 < m) :
    ∃ w : PowerSeries k, rootSeries k (2*m) 1 - rootSeries k (2*m) 2 =
      PowerSeries.X ^ m * w ∧ PowerSeries.constantCoeff w = 4 := by
  have hr1 : rootSeries k (2*m) 1 = tateX (2*m) m (1 : k) := by
    simp [rootSeries, show 2*m/2 = m by omega]
  have hr2 : rootSeries k (2*m) 2 = tateX (2*m) m (-1 : k) := by
    simp [rootSeries, show 2*m/2 = m by omega]
  obtain ⟨w, hw⟩ := dvd_sub (midpoint_divisible m (1 : k))
    (midpoint_divisible m (-1 : k))
  refine ⟨w, ?_, ?_⟩
  · simpa [hr1, hr2] using hw
  · have hh := congrArg (PowerSeries.coeff m) hw
    rw [map_sub, tateX_midpoint_leading m hm, tateX_midpoint_leading m hm] at hh
    have hc : PowerSeries.coeff m (PowerSeries.X ^ m * w) =
        PowerSeries.constantCoeff w := by
      simpa using PowerSeries.coeff_X_pow_mul w m 0
    rw [hc] at hh
    norm_num at hh ⊢
    exact hh.symm

lemma root_constants (m : ℕ) (hm : 0 < m) :
    PowerSeries.constantCoeff (rootSeries k (2*m) 0) = -(1/4 : k) ∧
    PowerSeries.constantCoeff (rootSeries k (2*m) 1) = 0 ∧
    PowerSeries.constantCoeff (rootSeries k (2*m) 2) = 0 := by
  simp only [rootSeries]
  change PowerSeries.constantCoeff (tateX (2*m) 0 (-1 : k)) = _ ∧
    PowerSeries.constantCoeff (tateX (2*m) ((2*m)/2) (1 : k)) = 0 ∧
    PowerSeries.constantCoeff (tateX (2*m) ((2*m)/2) (-1 : k)) = 0
  rw [show 2*m/2 = m by omega, ← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [tateX_boundary_constant (2*m) (by omega),
    tateX_interior_constant (2*m) m 1 hm (by omega),
    tateX_interior_constant (2*m) m (-1) hm (by omega)]
  norm_num

/-- The two invariants descend to series c and t^(2m)d with c(0)=d(0)=1. -/
lemma invariant_series (m : ℕ) (hm : 0 < m) :
    ∃ c d : PowerSeries k,
      PowerSeries.constantCoeff c = 1 ∧ PowerSeries.constantCoeff d = 1 ∧
      (TateCurve k (2*m)).c₄ = algebraMap (PowerSeries k) (LaurentSeries k) c ∧
      (TateCurve k (2*m)).Δ =
        algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^(2*m) * d) := by
  obtain ⟨w, hw, hw0⟩ := root_difference (k := k) m hm
  obtain ⟨h0, h1, h2⟩ := root_constants (k := k) m hm
  let a := rootSeries k (2*m) 0
  let b := rootSeries k (2*m) 1
  let e := rootSeries k (2*m) 2
  let c : PowerSeries k := 16 * (a+b+e)^2 - 48 * (a*b+a*e+b*e)
  let d : PowerSeries k := 16 * (a-b)^2 * (a-e)^2 * w^2
  refine ⟨c, d, ?_, ?_, ?_, ?_⟩
  · simp only [c, a, b, e, map_sub, map_mul, map_add, map_pow, map_ofNat, h0, h1, h2]
    norm_num
  · simp only [d, a, b, e, map_sub, map_mul, map_pow, map_ofNat, h0, h1, h2, hw0]
    norm_num
  · simp only [TateCurve, curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, root, c, a, b, e, map_sub, map_add, map_mul, map_pow,
      map_ofNat]
    ring
  · have hd : (TateCurve k (2*m)).Δ = algebraMap (PowerSeries k) (LaurentSeries k)
        (16 * (a-b)^2 * (a-e)^2 * (b-e)^2) := by
      simp only [TateCurve, curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
        root, a, b, e, map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [hd]
    apply congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
    change 16 * (a-b)^2 * (a-e)^2 *
      (rootSeries k (2*m) 1 - rootSeries k (2*m) 2)^2 = _
    rw [hw]
    dsimp [d]
    rw [show 2*m = m*2 by omega, pow_mul]
    ring

/-- Division by the discriminant is reduced to a power-series inverse identity. -/
lemma normalized_quotient (n : ℕ) (c d : PowerSeries k)
    (hc : PowerSeries.constantCoeff c = 1) (hd : PowerSeries.constantCoeff d = 1)
    (A B : LaurentSeries k) (hA : A = algebraMap (PowerSeries k) (LaurentSeries k) c)
    (hB : B = algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^n * d))
    (hB0 : B ≠ 0) :
    ∃ v : PowerSeries k, IsUnit v ∧ PowerSeries.constantCoeff v = 1 ∧
      A^3 / B * (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^n =
        algebraMap (PowerSeries k) (LaurentSeries k) v := by
  let v : PowerSeries k := c^3 * d⁻¹
  have hv : PowerSeries.constantCoeff v = 1 := by
    simp [v, map_mul, map_pow, PowerSeries.constantCoeff_inv, hc, hd]
  have hu : IsUnit v := PowerSeries.isUnit_iff_constantCoeff.mpr (hv ▸ isUnit_one)
  refine ⟨v, hu, hv, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hB0).mpr
  rw [hA, hB, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
  apply congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
  dsimp [v]
  calc
    c^3 * PowerSeries.X^n = (c^3 * PowerSeries.X^n) * (d⁻¹ * d) := by
      rw [PowerSeries.inv_mul_cancel d (by rw [hd]; exact one_ne_zero), mul_one]
    _ = c^3 * d⁻¹ * (PowerSeries.X^n * d) := by ring

end JPole

/-- The actual cubic has precisely the normalized j-pole prescribed by q=t^L. -/
theorem tate_j_pole :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L),
      (TateCurve k L).IsElliptic ∧ ∃ v : PowerSeries k, IsUnit v ∧
        PowerSeries.constantCoeff v = 1 ∧ tateJ k L *
          (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^L =
            algebraMap (PowerSeries k) (LaurentSeries k) v := by
  intro k _ _ L hL heven
  have hell := ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.curve_elliptic
    k hL heven
  refine ⟨hell, ?_⟩
  obtain ⟨m, hm⟩ := heven
  have hLm : L = 2*m := by omega
  clear hm
  subst L
  obtain ⟨c, d, hc, hd, hc4, hdelta⟩ := JPole.invariant_series (k := k) m (by omega)
  exact JPole.normalized_quotient (2*m) c d hc hd
    (TateCurve k (2*m)).c₄ (TateCurve k (2*m)).Δ hc4 hdelta
    (isUnit_iff_ne_zero.mp hell.isUnit)

end ArithmeticThetaTateCuspsR0181
