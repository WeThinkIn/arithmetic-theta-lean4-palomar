module

public import SplitCubicGeometry
public import SplitCubicDuplication

@[expose] public section

/-! Actual halves of the labelled two-torsion points on the split cubic. -/
namespace ArithmeticThetaFourTorsion

universe u
open WeierstrassCurve.Affine

private lemma split_negY {k : Type u} [Field k] (e₁ e₂ e₃ x y : k) :
    (splitCurve e₁ e₂ e₃).negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, splitCurve]

/-- A genuine half of the second labelled point has exact order four. -/
theorem actual_half_order_four :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e₁ e₂ e₃ : k)
      (hP : (splitCurve e₁ e₂ e₃).Nonsingular e₂ 0)
      (R : (splitCurve e₁ e₂ e₃).Point),
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      2 • R = Point.some e₂ 0 hP → addOrderOf R = 4 := by
  intro k _ _ _ e₁ e₂ e₃ hP R _h12 _h13 _h23 hdouble
  have hPtwo : 2 • Point.some e₂ 0 hP = 0 := by
    rw [two_nsmul]
    exact Point.add_self_of_Y_eq (by simp only [split_negY, neg_zero])
  have hfour : 4 • R = 0 := by
    calc
      4 • R = 2 • (2 • R) := by rw [← mul_nsmul]
      _ = 0 := by rw [hdouble, hPtwo]
  have htwo : 2 • R ≠ 0 := by rw [hdouble]; exact Point.some_ne_zero hP
  exact addOrderOf_eq_prime_pow (p := 2) (n := 1) htwo hfour

/-- Doubling to a finite point forces a nonvertical tangent and identifies addX. -/
private lemma half_coordinates {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e₁ e₂ e₃ x y t : k)
    (hR : (splitCurve e₁ e₂ e₃).Nonsingular x y)
    (hP : (splitCurve e₁ e₂ e₃).Nonsingular t 0)
    (hd : 2 • Point.some x y hR = Point.some t 0 hP) :
    y ≠ 0 ∧ (splitCurve e₁ e₂ e₃).addX x x
      ((splitCurve e₁ e₂ e₃).slope x x y y) = t := by
  have hn : y ≠ (splitCurve e₁ e₂ e₃).negY x y := by
    intro heq
    have hz : 2 • Point.some x y hR = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq heq]
    exact Point.some_ne_zero hP (hd.symm.trans hz)
  have hy : y ≠ 0 := by
    intro hz
    apply hn
    simp only [split_negY, hz, neg_zero]
  refine ⟨hy, ?_⟩
  rw [two_nsmul, Point.add_self_of_Y_ne hn] at hd
  exact (Point.some.inj hd).1

private lemma first_relation_of_addX {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e₁ e₂ e₃ x y : k) (hEq : (splitCurve e₁ e₂ e₃).Equation x y)
    (hy : y ≠ 0)
    (hx : (splitCurve e₁ e₂ e₃).addX x x
      ((splitCurve e₁ e₂ e₃).slope x x y y) = e₁) :
    (x-e₁)^2 = (e₁-e₂)*(e₁-e₃) := by
  have hdup := duplication_coordinate k e₁ e₂ e₃ x y hEq hy
  rw [hx, sub_self] at hdup
  have hg : rootExpression e₁ e₂ e₃ x y = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hdup.symm
  have hden : (2 : k) * y ≠ 0 := mul_ne_zero (by norm_num) hy
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp hg).resolve_right hden)

private lemma split_swap {k : Type u} [Field k] (e₁ e₂ e₃ : k) :
    splitCurve e₂ e₁ e₃ = splitCurve e₁ e₂ e₃ := by
  ext <;> simp only [splitCurve] <;> ring

/-- The square-root formula and quadratic relation for a half of the second point. -/
theorem actual_half_root :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e₁ e₂ e₃ : k)
      (hP : (splitCurve e₁ e₂ e₃).Nonsingular e₂ 0)
      (R : (splitCurve e₁ e₂ e₃).Point),
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      2 • R = Point.some e₂ 0 hP →
      ∃ (x y : k) (hR : (splitCurve e₁ e₂ e₃).Nonsingular x y),
        R = Point.some x y hR ∧ y ≠ 0 ∧
        (rootExpression e₁ e₂ e₃ x y)^2 = e₂-e₁ ∧
        (x-e₁)^2+2*(e₁-e₂)*(x-e₁)+(e₁-e₂)*(e₁-e₃) = 0 := by
  intro k _ _ _ e₁ e₂ e₃ hP R h12 h13 h23 hd
  have hord := actual_half_order_four k e₁ e₂ e₃ hP R h12 h13 h23 hd
  cases R with
  | zero =>
    change addOrderOf (0 : (splitCurve e₁ e₂ e₃).Point) = 4 at hord
    norm_num at hord
  | some x y hR =>
    obtain ⟨hy, hx⟩ := half_coordinates e₁ e₂ e₃ x y e₂ hR hP hd
    refine ⟨x, y, hR, rfl, hy, ?_, ?_⟩
    · have hdup := duplication_coordinate k e₁ e₂ e₃ x y hR.1 hy
      rw [hx] at hdup
      exact hdup.symm
    · have hEq : (splitCurve e₂ e₁ e₃).Equation x y := by
        rw [split_swap]; exact hR.1
      have hx' : (splitCurve e₂ e₁ e₃).addX x x
          ((splitCurve e₂ e₁ e₃).slope x x y y) = e₂ := by
        rw [split_swap]; exact hx
      have hr := first_relation_of_addX e₂ e₁ e₃ x y hEq hy hx'
      linear_combination hr

/-- The other half-point equation, derived from actual group doubling. -/
theorem actual_half_first_relation :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e₁ e₂ e₃ x y : k)
      (hP : (splitCurve e₁ e₂ e₃).Nonsingular e₁ 0)
      (hR : (splitCurve e₁ e₂ e₃).Nonsingular x y),
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      2 • (Point.some x y hR) = Point.some e₁ 0 hP →
      y ≠ 0 ∧ (x-e₁)^2 = (e₁-e₂)*(e₁-e₃) := by
  intro k _ _ _ e₁ e₂ e₃ x y hP hR _h12 _h13 _h23 hd
  obtain ⟨hy, hx⟩ := half_coordinates e₁ e₂ e₃ x y e₁ hR hP hd
  exact ⟨hy, first_relation_of_addX e₁ e₂ e₃ x y hR.1 hy hx⟩

/-- Explicit provider-to-consumer application: smoothness supplies the labelled point. -/
theorem actual_half_order_four_from_smooth {k : Type u} [Field k] [CharZero k]
    [DecidableEq k] (e₁ e₂ e₃ : k) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃)
    (h23 : e₂ ≠ e₃) (R : (splitCurve e₁ e₂ e₃).Point)
    (hd : 2 • R = Point.some e₂ 0 (split_smooth e₁ e₂ e₃ h12 h13 h23).2.2.1) :
    addOrderOf R = 4 :=
  actual_half_order_four k e₁ e₂ e₃
    (split_smooth e₁ e₂ e₃ h12 h13 h23).2.2.1 R h12 h13 h23 hd

end ArithmeticThetaFourTorsion
