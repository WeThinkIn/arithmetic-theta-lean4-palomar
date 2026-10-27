import HalfTangentEvaluationNonzeroR0114
import MillerOpenEvaluationR0114

/-! The algebraic Miller phase for actual independent halves. -/
namespace ArithmeticThetaMillerR0114
universe u
open ArithmeticThetaFourTorsion WeierstrassCurve.Affine

private lemma half_slope {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    {e : Fin 3 → k} {i : Fin 3} {x y : k} (h : IsHalf k e i x y)
    (hx : x ≠ e i) : tangentSlope k e x y = y / (x - e i) := by
  obtain ⟨hR, hP, hd⟩ := h
  have hn : y ≠ (Curve k e).negY x y := by
    intro heq
    have hz : 2 • Point.some x y hR = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq heq]
    exact Point.some_ne_zero hP (hd.symm.trans hz)
  rw [two_nsmul, Point.add_self_of_Y_ne hn] at hd
  obtain ⟨hX, hY⟩ := Point.some.inj hd
  simp only [addY, negAddY, negY, hX] at hY
  change -(tangentSlope k e x y * (e i - x) + y) - 0 * e i - 0 = 0 at hY
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  linear_combination hY

private lemma scalar_phase {k : Type u} [Field k] [CharZero k]
    (a b u v y₁ y₂ : k) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hv : v^2 = a*b) (hu : u^2+2*a*u+a*b = 0)
    (hy₁ : y₁^2 = v*(v+a)*(v+b)) (hy₂ : y₂^2 = u*(u+a)*(u+b))
    (_h₁ : y₁ ≠ 0) (h₂ : y₂ ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hua : u+a ≠ 0) (hvb : v+b ≠ 0)
    (hL : y₁-y₂*(v+a)/(u+a) ≠ 0) :
    ((y₂-y₁*u/v)^2/u) / ((y₁-y₂*(v+a)/(u+a))^2/(v+a)) =
      (u+b)*(y₁/y₂)/(v+b) := by
  let t := y₁ / y₂
  have ht : t^2*u*(u+a)*(u+b) = v*(v+a)*(v+b) := by
    dsimp [t]
    field_simp
    linear_combination hy₁ * (u*(u+a)*(u+b)) - hy₂ * (v*(v+a)*(v+b))
  have hLt : (u+a)*t-v-a ≠ 0 := by
    intro hz
    apply hL
    dsimp [t] at hz
    have hz' := (div_eq_zero_iff).mp (show ((u+a)*y₁-y₂*(v+a))/y₂ = 0 by
      calc
        _ = (u+a)*(y₁/y₂)-v-a := by field_simp; ring
        _ = 0 := hz)
    have hn := hz'.resolve_right h₂
    apply (sub_eq_zero.mpr ((eq_div_iff hua).mpr ?_))
    linear_combination hn
  have hm := miller_rational_identity k a b u v t ha hb hab hv hu ht hu0 hv0 hvb hLt
  calc
    _ = (v+a)*(u+a)^2*(v-t*u)^2 / (u*v^2*((u+a)*t-v-a)^2) := by
      dsimp [t] at *
      field_simp
      ring
    _ = _ := hm

/-- The phase formula, with all scalar divisions justified by actual point geometry. -/
theorem actual_miller_phase :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Distinct k e → ∀ (x₁ y₁ x₂ y₂ : k),
    IsHalf k e 0 x₁ y₁ → IsHalf k e 1 x₂ y₂ →
    millerRatio k e x₁ y₁ x₂ y₂ =
      rootExpression (e 0) (e 1) (e 2) x₂ y₂ /
        rootExpression (e 1) (e 0) (e 2) x₁ (-y₁) ∧
    IsPrimitiveRoot (millerRatio k e x₁ y₁ x₂ y₂) 4 := by
  intro k _ _ _ e hd x₁ y₁ x₂ y₂ h₁ h₂
  obtain ⟨hy₁, hy₂, hx, hL₁, hL₂⟩ :=
    half_tangent_evaluation_nonzero k e hd x₁ y₁ x₂ y₂ h₁ h₂
  have h12 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hd h)
  have h13 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hd h)
  have h23 : e 1 ≠ e 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hd h)
  obtain ⟨hR₁, hP₁, hd₁⟩ := h₁
  obtain ⟨hR₂, hP₂, hd₂⟩ := h₂
  -- The mandatory localization providers witness that these are evaluations of the sections.
  obtain ⟨J₁, hJ₁, hC₁, hf₁, V₁, hV₁, _⟩ :=
    miller_open_evaluation k e hd 0 x₁ y₁ x₂ y₂ hR₂.1 (hx 0).2
  obtain ⟨J₂, hJ₂, hC₂, hf₂, V₂, hV₂, _⟩ :=
    miller_open_evaluation k e hd 1 x₂ y₂ x₁ y₁ hR₁.1 (hx 1).1
  have heval : millerRatio k e x₁ y₁ x₂ y₂ =
      V₁ (localMiller k e 0 x₁ y₁) / V₂ (localMiller k e 1 x₂ y₂) := by
    rw [hV₁.2.2, hV₂.2.2]; rfl
  have hs₁ := half_slope (show IsHalf k e 0 x₁ y₁ from ⟨hR₁,hP₁,hd₁⟩) (hx 0).1
  have hs₂ := half_slope (show IsHalf k e 1 x₂ y₂ from ⟨hR₂,hP₂,hd₂⟩) (hx 1).2
  let a := e 0 - e 1
  let b := e 0 - e 2
  let u := x₂ - e 0
  let v := x₁ - e 0
  have ha : a ≠ 0 := sub_ne_zero.mpr h12
  have hb : b ≠ 0 := sub_ne_zero.mpr h13
  have hab : a ≠ b := by dsimp [a,b]; intro h; apply h23; linear_combination -h
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (hx 0).2
  have hv0 : v ≠ 0 := sub_ne_zero.mpr (hx 0).1
  have hua : u+a ≠ 0 := by convert sub_ne_zero.mpr (hx 1).2 using 1 <;> dsimp [u,a] <;> ring
  have hvb : v+b ≠ 0 := by convert sub_ne_zero.mpr (hx 2).1 using 1 <;> dsimp [v,b] <;> ring
  have hv := (actual_half_first_relation k (e 0) (e 1) (e 2) x₁ y₁
    hP₁ hR₁ h12 h13 h23 hd₁).2
  change v^2 = a*b at hv
  obtain ⟨x',y',hR',he',_,hg,hu⟩ := actual_half_root k (e 0) (e 1) (e 2)
    hP₂ (Point.some x₂ y₂ hR₂) h12 h13 h23 hd₂
  obtain ⟨rfl,rfl⟩ := Point.some.inj he'
  change u^2+2*a*u+a*b = 0 at hu
  have heq₁ : y₁^2 = v*(v+a)*(v+b) := by
    convert (split_equation (e 0) (e 1) (e 2) x₁ y₁).mp hR₁.1 using 1 <;>
      dsimp [v,a,b] <;> ring
  have heq₂ : y₂^2 = u*(u+a)*(u+b) := by
    convert (split_equation (e 0) (e 1) (e 2) x₂ y₂).mp hR₂.1 using 1 <;>
      dsimp [u,a,b] <;> ring
  have ht₁ : tangentValue k e x₁ y₁ x₂ y₂ = y₂-y₁*u/v := by
    rw [tangentValue, hs₁]; dsimp [u,v]; field_simp [sub_ne_zero.mpr (hx 0).1]; ring
  have ht₂ : tangentValue k e x₂ y₂ x₁ y₁ = y₁-y₂*(v+a)/(u+a) := by
    rw [tangentValue, hs₂]; dsimp [u,v,a]; field_simp [sub_ne_zero.mpr (hx 1).2]; ring
  have hphase : millerRatio k e x₁ y₁ x₂ y₂ = (u+b)*(y₁/y₂)/(v+b) := by
    rw [heval, hV₁.2.2, hV₂.2.2]
    simp only [millerValue, ht₁, ht₂]
    have hxv : x₁-e 1 = v+a := by dsimp [v,a]; ring
    rw [hxv]
    exact scalar_phase a b u v y₁ y₂ ha hb hab hv hu heq₁ heq₂ hy₁ hy₂
      hu0 hv0 hua hvb (ht₂ ▸ hL₂)
  have hg₂ : rootExpression (e 0) (e 1) (e 2) x₂ y₂ = -a*(u+b)/y₂ := by
    unfold rootExpression
    change (u^2-a*b)/(2*y₂) = _
    field_simp
    linear_combination hu
  have hg₁ : rootExpression (e 1) (e 0) (e 2) x₁ (-y₁) = -a*(v+b)/y₁ := by
    unfold rootExpression
    have hn : (x₁-e 1)^2-(e 1-e 0)*(e 1-e 2) = 2*a*(v+b) := by
      dsimp [a,b,v] at *
      linear_combination hv
    rw [hn]
    field_simp
  have hroot : rootExpression (e 0) (e 1) (e 2) x₂ y₂ /
      rootExpression (e 1) (e 0) (e 2) x₁ (-y₁) = (u+b)*(y₁/y₂)/(v+b) := by
    rw [hg₁, hg₂]; field_simp
  refine ⟨hphase.trans hroot.symm, ?_⟩
  have hsquare : (millerRatio k e x₁ y₁ x₂ y₂)^2 = -1 := by
    rw [hphase]
    field_simp
    linear_combination
      (u+b)^2 * heq₁ + (v+b)^2 * heq₂ +
      (u+b)*(v+b)*(u+b)*hv + (u+b)*(v+b)*(v+b)*hu
  have hfour : (millerRatio k e x₁ y₁ x₂ y₂)^4 = 1 := by
    calc
      _ = ((millerRatio k e x₁ y₁ x₂ y₂)^2)^2 := by ring
      _ = 1 := by rw [hsquare]; ring
  have hord : orderOf (millerRatio k e x₁ y₁ x₂ y₂) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [show (2:ℕ)^1 = 2 by decide, hsquare]; norm_num) hfour
  rw [← hord]
  exact IsPrimitiveRoot.orderOf _

end ArithmeticThetaMillerR0114
