import MillerGeometryDefinitionsR0114
import Mathlib.Tactic.FinCases

/-! Nonvanishing of evaluations between actual halves of distinct labelled points. -/
namespace ArithmeticThetaMillerR0114

universe u
open WeierstrassCurve.Affine
open ArithmeticThetaFourTorsion

private lemma half_tangent_data {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    {e : Fin 3 → k} {i : Fin 3} {x y : k} (h : IsHalf k e i x y) :
    (Curve k e).Equation x y ∧ y ≠ 0 ∧
    y ≠ (Curve k e).negY x y ∧
    (Curve k e).addX x x (tangentSlope k e x y) = e i := by
  obtain ⟨hR, hP, hd⟩ := h
  have hn : y ≠ (Curve k e).negY x y := by
    intro heq
    have hz : 2 • Point.some x y hR = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq heq]
    exact Point.some_ne_zero hP (hd.symm.trans hz)
  refine ⟨hR.1, ?_, hn, ?_⟩
  · intro hy
    apply hn
    simp [Curve, splitCurve, negY, hy]
  · rw [two_nsmul, Point.add_self_of_Y_ne hn] at hd
    exact (Point.some.inj hd).1

private lemma half_avoids_roots {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    {e : Fin 3 → k} {i : Fin 3} {x y : k} (h : IsHalf k e i x y) :
    ∀ j : Fin 3, x ≠ e j := by
  obtain ⟨heq, hy, _⟩ := half_tangent_data h
  have heq' := (split_equation (e 0) (e 1) (e 2) x y).mp heq
  intro j hx
  apply pow_ne_zero 2 hy
  fin_cases j <;> simp [hx] at heq' ⊢ <;> exact heq'

/-- A tangent at an actual half cannot contain a half with a different double. -/
private lemma cross_tangent_nonzero {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    {e : Fin 3 → k} {i j : Fin 3} {x y a b : k}
    (hij : e i ≠ e j) (h : IsHalf k e i x y) (h' : IsHalf k e j a b) :
    tangentValue k e x y a b ≠ 0 := by
  obtain ⟨heq, _hy, hn, hx⟩ := half_tangent_data h
  obtain ⟨heq', _hb, _hn', _ha⟩ := half_tangent_data h'
  intro hz
  have hline : b = tangentSlope k e x y * (a - x) + y := by
    dsimp [tangentValue] at hz
    linear_combination hz
  have hpoly := (Curve k e).addPolynomial_slope heq heq (by
    intro hc
    exact hn hc.2)
  have heval := congrArg (Polynomial.eval a) hpoly
  change (Curve k e).addX x x ((Curve k e).slope x x y y) = e i at hx
  rw [hx] at heval
  have hzpoly : ((Curve k e).addPolynomial x y ((Curve k e).slope x x y y)).eval a = 0 := by
    rw [addPolynomial, linePolynomial, WeierstrassCurve.Affine.polynomial]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    dsimp [tangentSlope] at hline
    rw [← hline]
    rw [equation_iff] at heq'
    linear_combination heq'
  rw [hzpoly] at heval
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at heval
  have hprod : (a - x) * (a - x) * (a - e i) = 0 := neg_eq_zero.mp heval.symm
  have hax : a = x := by
    have hroot := half_avoids_roots h' i
    have hs : (a - x) * (a - x) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hroot)
    rcases mul_eq_zero.mp hs with hs | hs <;> exact sub_eq_zero.mp hs
  have hby : b = y := by simpa [hax] using hline
  obtain ⟨hR, hP, hd⟩ := h
  obtain ⟨hS, hQ, hd'⟩ := h'
  subst a
  subst b
  have hpq : Point.some (e i) 0 hP = Point.some (e j) 0 hQ := hd.symm.trans hd'
  exact hij (Point.some.inj hpq).1

/-- Denominators and cross-tangent values are nonzero for halves of the two labelled points. -/
theorem half_tangent_evaluation_nonzero :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Distinct k e → ∀ (x₁ y₁ x₂ y₂ : k),
      IsHalf k e 0 x₁ y₁ → IsHalf k e 1 x₂ y₂ →
      y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ (∀ i : Fin 3, x₁ ≠ e i ∧ x₂ ≠ e i) ∧
      tangentValue k e x₁ y₁ x₂ y₂ ≠ 0 ∧
      tangentValue k e x₂ y₂ x₁ y₁ ≠ 0 := by
  intro k _ _ _ e hd x₁ y₁ x₂ y₂ h₁ h₂
  have he : e 0 ≠ e 1 := fun hh => (by decide : (0 : Fin 3) ≠ 1) (hd hh)
  exact ⟨(half_tangent_data h₁).2.1, (half_tangent_data h₂).2.1,
    fun i => ⟨half_avoids_roots h₁ i, half_avoids_roots h₂ i⟩,
    cross_tangent_nonzero he h₁ h₂, cross_tangent_nonzero he.symm h₂ h₁⟩

end ArithmeticThetaMillerR0114
