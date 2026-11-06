import MillerGeometryDefinitionsR0114
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.Ring

/-!
# The complete branch at infinity

For every characteristic-zero field and every three labelled coefficients, construct
and uniquely characterize the full power series satisfying `branchEquation`.
Existence uses formal compositional inversion; uniqueness uses a polynomial
factorization with a nonzero constant coefficient. No distinctness is needed.
-/

noncomputable section
universe u
namespace ArithmeticThetaMillerR0114

open PowerSeries

/-- The reciprocal-coordinate cubic, whose constant coefficient is one. -/
def branchD (k : Type u) [Field k] (e : Fin 3 → k) : PowerSeries k :=
  ∏ i : Fin 3, (1 - C (e i) * X)

/-- The series with linear coefficient one to be inverted under composition. -/
def branchP (k : Type u) [Field k] (e : Fin 3 → k) : PowerSeries k :=
  X * (branchD k e)⁻¹

/-- The unique full branch in the parameter `z = -X/Y`. -/
theorem infinity_branch :
    ∀ (k : Type u) [Field k] [CharZero k] (e : Fin 3 → k),
      ∃! h : PowerSeries k, branchEquation k e h := by
  intro k _ _ e
  let D : PowerSeries k := branchD k e
  let P : PowerSeries k := branchP k e
  have hD0 : PowerSeries.constantCoeff D = 1 := by
    simp [D, branchD]
  have hP0 : PowerSeries.constantCoeff P = 0 := by
    simp [P, branchP]
  have hP1 : PowerSeries.coeff 1 P = 1 := by
    simp [P, branchP, branchD]
  have hPunit : IsUnit (PowerSeries.coeff 1 P) := by simp [hP1]
  let q : PowerSeries k := P.substInvOfIsUnit hPunit
  have hq0 : PowerSeries.constantCoeff q = 0 := by
    simp [q, PowerSeries.constantCoeff_substInvOfIsUnit]
  have hqsub : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero' hq0
  have hq : P.subst q = X := by
    exact PowerSeries.subst_substInvOfIsUnit_right P hP0 hPunit
  have hqrel : q = X * D.subst q := by
    have hm : (D⁻¹).subst q * D.subst q = 1 := by
      rw [← PowerSeries.subst_mul hqsub]
      simp [D, hD0]
      rw [← PowerSeries.coe_substAlgHom hqsub]
      exact map_one _
    have heq : q * (D⁻¹).subst q = X := by
      change PowerSeries.subst q (X * D⁻¹) = X at hq
      rw [PowerSeries.subst_mul hqsub, PowerSeries.subst_X hqsub] at hq
      exact hq
    calc
      q = q * 1 := by rw [mul_one]
      _ = q * ((D⁻¹).subst q * D.subst q) := by rw [hm]
      _ = (q * (D⁻¹).subst q) * D.subst q := by ring
      _ = X * D.subst q := by rw [heq]
  let q₂ : PowerSeries k := q.subst (X ^ 2)
  have hq₂0 : PowerSeries.constantCoeff q₂ = 0 := by
    simp [q₂, hq0]
  have hq₂rel : q₂ = X ^ 2 * D.subst q₂ := by
    have := congrArg (fun r : PowerSeries k =>
      PowerSeries.subst (X ^ 2 : PowerSeries k) r) hqrel
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow (by decide : 2 ≠ 0)),
      PowerSeries.subst_X (PowerSeries.HasSubst.X_pow (by decide : 2 ≠ 0)),
      PowerSeries.subst_comp_subst_apply hqsub
        (PowerSeries.HasSubst.X_pow (by decide : 2 ≠ 0))] at this
    simpa [q₂] using this
  let g : PowerSeries k := PowerSeries.divXPowOrder q
  have hq1 : PowerSeries.coeff 1 q = 1 := by
    simp [q, hP1]
  have hqorder : q.order = 1 := by
    apply (PowerSeries.order_eq_nat).2
    refine ⟨(by rw [hq1]; exact one_ne_zero), ?_⟩
    intro i hi
    have : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
    subst i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hq0
  have hqfactor : q = X * g := by
    simpa [g, hqorder] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := q)).symm
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    simp [g, PowerSeries.constantCoeff_divXPowOrder, hqorder, hq1]
  let g₂ : PowerSeries k := PowerSeries.subst (X ^ 2 : PowerSeries k) g
  have hg₂0 : PowerSeries.constantCoeff g₂ = 1 := by
    simp [g₂, hg0]
  let h : PowerSeries k := g₂⁻¹
  have hh0 : PowerSeries.constantCoeff h = 1 := by
    dsimp [h]
    rw [PowerSeries.constantCoeff_inv]
    rw [hg₂0]
    simp
  have hDq₂ : D.subst q₂ = g₂ := by
    have hqfactor₂ : q₂ = X ^ 2 * g₂ := by
      let hs := congrArg (fun r : PowerSeries k =>
        PowerSeries.subst (X ^ 2 : PowerSeries k) r) hqfactor
      have hXsub : PowerSeries.HasSubst (X ^ 2 : PowerSeries k) :=
        PowerSeries.HasSubst.X_pow (by decide : 2 ≠ 0)
      rw [PowerSeries.subst_mul hXsub, PowerSeries.subst_X hXsub] at hs
      simpa [q₂, g₂] using hs
    have hcancel : (X ^ 2) * D.subst q₂ = (X ^ 2) * g₂ := by
      rw [← hq₂rel, hqfactor₂]
    exact (mul_left_cancel₀ (pow_ne_zero 2 PowerSeries.X_ne_zero) hcancel)
  have hbranch : branchEquation k e h := by
    refine ⟨hh0, ?_⟩
    have hq₂h : q₂ * h = X ^ 2 := by
      rw [hq₂rel, hDq₂]
      dsimp [h]
      rw [mul_assoc, PowerSeries.mul_inv_cancel, mul_one]
      · exact by rw [hg₂0]; exact one_ne_zero
    have hq₂sub : PowerSeries.HasSubst q₂ :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hq₂0
    have hDexpand : D.subst q₂ = ∏ i : Fin 3, (1 - C (e i) * q₂) := by
      change PowerSeries.subst q₂ (∏ i : Fin 3, (1 - C (e i) * X)) = _
      rw [← PowerSeries.coe_substAlgHom hq₂sub, map_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [PowerSeries.coe_substAlgHom hq₂sub]
      rw [PowerSeries.subst_sub hq₂sub, PowerSeries.subst_mul hq₂sub,
        PowerSeries.subst_C, PowerSeries.subst_X hq₂sub]
      have hone : PowerSeries.subst q₂ (1 : PowerSeries k) = 1 := by
        rw [← PowerSeries.coe_substAlgHom hq₂sub]
        exact map_one _
      rw [hone]
      rfl
    have hprod : (∏ i : Fin 3, (h - C (e i) * X ^ 2)) =
        h ^ 3 * D.subst q₂ := by
      have hi : ∀ i : Fin 3,
          h - C (e i) * X ^ 2 = h * (1 - C (e i) * q₂) := by
        intro i
        rw [← hq₂h]
        ring
      rw [Finset.prod_congr rfl (fun i _ => hi i)]
      have hmul : (∏ i : Fin 3, h * (1 - C (e i) * q₂)) =
          (∏ i : Fin 3, h) * (∏ i : Fin 3, (1 - C (e i) * q₂)) := by
        simpa using (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin 3)))
          (f := fun _ : Fin 3 => h) (g := fun i => 1 - C (e i) * q₂))
      rw [hmul, hDexpand]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hprod, hDq₂]
    dsimp [h]
    calc
      g₂⁻¹ ^ 2 = g₂⁻¹ ^ 2 * 1 := by rw [mul_one]
      _ = g₂⁻¹ ^ 2 * (g₂ * g₂⁻¹) := by
        rw [PowerSeries.mul_inv_cancel g₂ (by rw [hg₂0]; exact one_ne_zero)]
      _ = g₂⁻¹ ^ 3 * g₂ := by ring
  refine ⟨h, hbranch, ?_⟩
  intro h' hh'
  rcases hh' with ⟨hh'0, hh'eq⟩
  let a : PowerSeries k := C (e 0) * X ^ 2
  let b : PowerSeries k := C (e 1) * X ^ 2
  let c : PowerSeries k := C (e 2) * X ^ 2
  let v : PowerSeries k := h'^2 + h'*h + h^2 - (1 + a + b + c) * (h' + h) +
    (a*b + a*c + b*c)
  have hv0 : constantCoeff v = 1 := by
    simp [v, a, b, c, hh'0, hh0]
  have hvne : v ≠ 0 := by
    intro hz
    have := congrArg constantCoeff hz
    rw [hv0, map_zero] at this
    exact one_ne_zero this
  have he : h^2 = (h-a)*(h-b)*(h-c) := by
    simpa [a, b, c, Fin.prod_univ_succ, mul_assoc] using hbranch.2
  have he' : h'^2 = (h'-a)*(h'-b)*(h'-c) := by
    simpa [a, b, c, Fin.prod_univ_succ, mul_assoc] using hh'eq
  have hf : (h' - h) * v = 0 := by
    dsimp [v]
    linear_combination he - he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hvne)

end ArithmeticThetaMillerR0114
