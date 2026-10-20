module

public import MarkingCharacterDefinitionsR0115

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Coordinate covariance on the actual nonsingular point group. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine
open ArithmeticThetaFourTorsion
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k]
variable (e : Fin 3 → k) (a : kˣ) (r : k)

private lemma changed_injective (he : Function.Injective e) :
    Function.Injective (changedLabels k e a r) := by
  intro i j h
  apply he
  exact (mul_left_cancel₀ (pow_ne_zero 2 a.ne_zero)) (add_right_cancel h)

private lemma curve_elliptic (he : Function.Injective e) : (Curve k e).IsElliptic :=
  split_elliptic _ _ _ (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))

private lemma changed_equation (x y : k) :
    (Curve k (changedLabels k e a r)).Equation ((a:k)^2*x+r) ((a:k)^3*y) ↔
      (Curve k e).Equation x y := by
  rw [split_equation, split_equation]
  have h : ((a:k)^3*y)^2 -
      (((a:k)^2*x+r) - changedLabels k e a r 0) *
      (((a:k)^2*x+r) - changedLabels k e a r 1) *
      (((a:k)^2*x+r) - changedLabels k e a r 2) =
      (a:k)^6 * (y^2 - (x-e 0)*(x-e 1)*(x-e 2)) := by
    simp only [changedLabels]; ring
  rw [← sub_eq_zero, h, mul_eq_zero]
  simp [a.ne_zero, sub_eq_zero]

private lemma changed_nonsingular (he : Function.Injective e) (x y : k)
    (h : (Curve k e).Nonsingular x y) :
    (Curve k (changedLabels k e a r)).Nonsingular ((a:k)^2*x+r) ((a:k)^3*y) := by
  let := curve_elliptic k (changedLabels k e a r) (changed_injective k e a r he)
  apply (Curve k (changedLabels k e a r)).equation_iff_nonsingular.mp
  exact (changed_equation k e a r x y).mpr h.1

private lemma changed_slope (x z y w : k) :
    (Curve k (changedLabels k e a r)).slope
      ((a:k)^2*x+r) ((a:k)^2*z+r) ((a:k)^3*y) ((a:k)^3*w) =
      (a:k) * (Curve k e).slope x z y w := by
  have hx : ((a:k)^2*x+r = (a:k)^2*z+r) ↔ x=z := by
    simp [a.ne_zero]
  have hy : ((a:k)^3*y = -((a:k)^3*w)) ↔ y = -w := by
    rw [← mul_neg]; exact mul_right_inj' (pow_ne_zero 3 a.ne_zero)
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY,
    Curve, ArithmeticThetaMillerR0114.Curve, splitCurve, zero_mul, sub_zero, hx, hy]
  split_ifs
  · simp
  · have hn : 3*((a:k)^2*x+r)^2 + 2*(-(changedLabels k e a r 0 +
        changedLabels k e a r 1 + changedLabels k e a r 2))*((a:k)^2*x+r) +
        (changedLabels k e a r 0 * changedLabels k e a r 1 +
        changedLabels k e a r 0 * changedLabels k e a r 2 +
        changedLabels k e a r 1 * changedLabels k e a r 2) =
        (a:k)^4 * (3*x^2 + 2*(-(e 0+e 1+e 2))*x +
        (e 0*e 1+e 0*e 2+e 1*e 2)) := by simp only [changedLabels]; ring
    rw [hn, show (a:k)^3*y - -((a:k)^3*y) = (a:k)^3*(y - -y) by ring,
      mul_div_mul_comm]
    congr 1
    field_simp
  · rw [show (a:k)^3*y - (a:k)^3*w = (a:k)^3*(y-w) by ring,
      show (a:k)^2*x+r - ((a:k)^2*z+r) = (a:k)^2*(x-z) by ring,
      mul_div_mul_comm]
    congr 1
    field_simp

def changePoint (he : Function.Injective e) :
    (Curve k e).Point → (Curve k (changedLabels k e a r)).Point
  | .zero => .zero
  | .some x y h => .some _ _ (changed_nonsingular k e a r he x y h)

lemma changePoint_add (he : Function.Injective e) (P Q : (Curve k e).Point) :
    changePoint k e a r he (P+Q) = changePoint k e a r he P + changePoint k e a r he Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some z w hq =>
      have hn : ∀ t v, (Curve k e).negY t v = -v := by intros; simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, splitCurve]
      have hn' : ∀ t v, (Curve k (changedLabels k e a r)).negY t v = -v := by intros; simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, splitCurve]
      by_cases hxy : x=z ∧ y=(Curve k e).negY z w
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        change 0 = Point.some _ _ _ + Point.some _ _ _
        rw [Point.add_of_Y_eq (by rw [hxy.1]) (by rw [hn', hxy.2, hn]; ring)]
      · have hxy' : ¬((a:k)^2*x+r = (a:k)^2*z+r ∧
            (a:k)^3*y = (Curve k (changedLabels k e a r)).negY ((a:k)^2*z+r) ((a:k)^3*w)) := by
          intro h
          apply hxy
          refine ⟨mul_left_cancel₀ (pow_ne_zero 2 a.ne_zero) (add_right_cancel h.1), ?_⟩
          rw [hn', ← mul_neg] at h
          rw [hn]
          exact mul_left_cancel₀ (pow_ne_zero 3 a.ne_zero) h.2
        rw [Point.add_some hxy]
        change Point.some _ _ _ = Point.some _ _ _ + Point.some _ _ _
        rw [Point.add_some hxy', Point.some.injEq, changed_slope]
        simp only [addX, addY, negAddY, negY, Curve, ArithmeticThetaMillerR0114.Curve,
          splitCurve, changedLabels]
        constructor <;> ring

lemma changePoint_bijective (he : Function.Injective e) :
    Function.Bijective (changePoint k e a r he) := by
  constructor
  · intro P Q h
    cases P with
    | zero => cases Q <;> simp_all [changePoint]
    | some x y hp =>
      cases Q with
      | zero => simp_all [changePoint]
      | some z w hq =>
        simp only [changePoint, Point.some.injEq] at h ⊢
        exact ⟨mul_left_cancel₀ (pow_ne_zero 2 a.ne_zero) (add_right_cancel h.1),
          mul_left_cancel₀ (pow_ne_zero 3 a.ne_zero) h.2⟩
  · intro Q
    cases Q with
    | zero => exact ⟨0, rfl⟩
    | some x y hq =>
      have hx : (a:k)^2*((x-r)/(a:k)^2)+r = x := by field_simp; ring
      have hy : (a:k)^3*(y/(a:k)^3) = y := by field_simp
      have hp : (Curve k e).Nonsingular ((x-r)/(a:k)^2) (y/(a:k)^3) := by
        let := curve_elliptic k e he
        apply (Curve k e).equation_iff_nonsingular.mp
        apply (changed_equation k e a r _ _).mp
        simpa only [hx, hy] using hq.1
      refine ⟨Point.some _ _ hp, ?_⟩
      simp only [changePoint, Point.some.injEq, hx, hy, and_self]

/-- The coordinate map is constructed from the affine point formulas and their group law. -/
def coordinateChangeEquiv (he : Function.Injective e) :
    (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point :=
  AddEquiv.ofBijective
    ({ toFun := changePoint k e a r he
       map_zero' := rfl
       map_add' := changePoint_add k e a r he } : (Curve k e).Point →+ (Curve k (changedLabels k e a r)).Point)
    (changePoint_bijective k e a r he)

private lemma coordinateChange_spec (he : Function.Injective e) :
    IsCoordinateChange k e a r (coordinateChangeEquiv k e a r he) := by
  intro P hp
  cases P with
  | zero => exact (hp rfl).elim
  | some x y h => exact ⟨rfl, rfl⟩

private lemma basis_transport (d : Fin 3 → k)
    (F : (Curve k e).Point ≃+ (Curve k d).Point)
    (b : Marking k e) (hb : IsBasis k e b) : IsBasis k d (F ∘ b) := by
  have hc : ∀ z, coordinates k d (F ∘ b) z = F (coordinates k e b z) := by
    intro z; simp [coordinates]
  refine ⟨?_, ?_, ?_⟩
  · intro i; simpa using congrArg F (hb.1 i)
  · intro z w h
    exact hb.2.1 (F.injective (by simpa only [hc] using h))
  · intro T ht
    obtain ⟨z, hz⟩ := hb.2.2 (F.symm T) (by simpa using congrArg F.symm ht)
    exact ⟨z, by rw [hc, hz, F.apply_symm_apply]⟩

private lemma basis_affine (b : Marking k e) (hb : IsBasis k e b) :
    2 • b 0 ≠ 0 ∧ 2 • b 1 ≠ 0 ∧ 2 • b 0 + 2 • b 1 ≠ 0 ∧ b 0 ≠ 0 ∧ b 1 ≠ 0 := by
  have h0 : 2 • b 0 ≠ 0 := by
    intro h
    have hh := hb.2.1 (a₁ := ![2,0]) (a₂ := ![0,0]) (by simpa [coordinates, ZMod.val_two_eq_two_mod] using h)
    have := congrFun hh 0
    exact (by decide : (2 : ZMod 4) ≠ 0) this
  have h1 : 2 • b 1 ≠ 0 := by
    intro h
    have hh := hb.2.1 (a₁ := ![0,2]) (a₂ := ![0,0]) (by simpa [coordinates, ZMod.val_two_eq_two_mod] using h)
    have := congrFun hh 1
    exact (by decide : (2 : ZMod 4) ≠ 0) this
  refine ⟨h0, h1, ?_, ?_, ?_⟩
  · intro h
    have hh := hb.2.1 (a₁ := ![2,2]) (a₂ := ![0,0]) (by simpa [coordinates, ZMod.val_two_eq_two_mod] using h)
    have := congrFun hh 0
    exact (by decide : (2 : ZMod 4) ≠ 0) this
  · intro h; apply h0; simp [h]
  · intro h; apply h1; simp [h]

private lemma y_ne_of_double_ne (P : (Curve k e).Point) (hP : 2 • P ≠ 0) :
    pointY k e P ≠ 0 := by
  cases P with
  | zero => exact (hP (by simp [← Point.zero_def])).elim
  | some x y hp =>
    intro hy
    apply hP
    rw [two_nsmul, Point.add_self_of_Y_eq]
    change y = 0 at hy
    simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, splitCurve, hy]

private lemma x_ne_of_orders (P T : (Curve k e).Point)
    (hP : 2 • P ≠ 0) (hT : T ≠ 0) (ht : 2 • T = 0) :
    pointX k e P ≠ pointX k e T := by
  cases P with
  | zero => exact (hP (by simp [← Point.zero_def])).elim
  | some x y hp =>
    cases T with
    | zero => exact (hT rfl).elim
    | some z w hq =>
      intro hx
      have hh := (Point.X_eq_iff (h₁ := hp) (h₂ := hq)).mp hx
      rcases hh with hh | hh
      · exact hP (by rw [hh, ht])
      · exact hP (by rw [hh, smul_neg, ht, neg_zero])

private lemma tangent_ne_of_orders (P Q : (Curve k e).Point)
    (hP : 2 • P ≠ 0) (hQ : 2 • Q ≠ 0) (h4 : 4 • P = 0)
    (hd : 2 • P ≠ 2 • Q) : tangent k e P Q ≠ 0 := by
  have hxT := x_ne_of_orders k e Q (2 • P) hQ hP (by simpa [← mul_nsmul] using h4)
  cases P with
  | zero => exact (hP (by simp [← Point.zero_def])).elim
  | some x y hp =>
    cases Q with
    | zero => exact (hQ (by simp [← Point.zero_def])).elim
    | some z w hq =>
      have hn : y ≠ (Curve k e).negY x y := by
        intro h; apply hP; rw [two_nsmul, Point.add_self_of_Y_eq h]
      have hpoly := (Curve k e).addPolynomial_slope hp.1 hp.1 (by
        intro hc; exact hn hc.2)
      have heval := congrArg (Polynomial.eval z) hpoly
      intro hz
      have hline : w = (Curve k e).slope x x y y * (z-x) + y := by
        change w-y-(Curve k e).slope x x y y*(z-x) = 0 at hz
        linear_combination hz
      have hzpoly : ((Curve k e).addPolynomial x y ((Curve k e).slope x x y y)).eval z = 0 := by
        rw [addPolynomial, linePolynomial, WeierstrassCurve.Affine.polynomial]
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        rw [← hline]
        have heq := (equation_iff ..).mp hq.1
        linear_combination heq
      rw [hzpoly] at heval
      simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at heval
      rw [two_nsmul, Point.add_self_of_Y_ne hn] at hxT
      change z ≠ (Curve k e).addX x x ((Curve k e).slope x x y y) at hxT
      have hprod := (mul_eq_zero.mp (neg_eq_zero.mp heval.symm)).resolve_right
        (sub_ne_zero.mpr hxT)
      have hx : z=x := by
        rcases mul_eq_zero.mp hprod with h | h <;> exact sub_eq_zero.mp h
      have hy : w=y := by simpa [hx] using hline
      apply hd
      congr 1
      simpa only [Point.some.injEq] using And.intro hx.symm hy.symm

/-- All scalar denominators and cross-tangent evaluations used in the basis formulas are nonzero. -/
theorem coordinate_basis_regular (b : Marking k e) (hb : IsBasis k e b) :
    pointY k e (b 0) ≠ 0 ∧ pointY k e (b 1) ≠ 0 ∧
    pointX k e (b 1) - labels k e b 0 ≠ 0 ∧
    pointX k e (b 0) - labels k e b 1 ≠ 0 ∧
    tangent k e (b 0) (b 1) ≠ 0 ∧ tangent k e (b 1) (b 0) ≠ 0 := by
  obtain ⟨h0,h1,_,_,_⟩ := basis_affine k e b hb
  have hd : 2 • b 0 ≠ 2 • b 1 := by
    intro hh
    have h := hb.2.1 (a₁ := ![2,0]) (a₂ := ![0,2])
      (by simpa [coordinates, ZMod.val_two_eq_two_mod] using hh)
    exact (by decide : (2 : ZMod 4) ≠ 0) (congrFun h 0)
  refine ⟨y_ne_of_double_ne k e _ h0, y_ne_of_double_ne k e _ h1, ?_, ?_,
    tangent_ne_of_orders k e _ _ h0 h1 (hb.1 0) hd,
    tangent_ne_of_orders k e _ _ h1 h0 (hb.1 1) hd.symm⟩
  · apply sub_ne_zero.mpr
    exact x_ne_of_orders k e _ _ h1 h0 (by simpa [← mul_nsmul] using hb.1 0)
  · apply sub_ne_zero.mpr
    exact x_ne_of_orders k e _ _ h0 h1 (by simpa [← mul_nsmul] using hb.1 1)

private lemma change_labels
    (F : (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point)
    (hF : IsCoordinateChange k e a r F) (b : Marking k e) (hb : IsBasis k e b) :
    ∀ i, labels k (changedLabels k e a r) (F ∘ b) i = (a:k)^2 * labels k e b i + r := by
  obtain ⟨h0,h1,h2,_,_⟩ := basis_affine k e b hb
  intro i
  fin_cases i
  · simpa [labels, ← map_nsmul] using (hF (2 • b 0) h0).1
  · simpa [labels, ← map_nsmul] using (hF (2 • b 1) h1).1
  · simpa [labels, ← map_nsmul, ← map_add] using (hF (2 • b 0 + 2 • b 1) h2).1

private lemma root_scaled (l₀ l₁ l₂ x y : k) :
    rootExpression ((a:k)^2*l₀+r) ((a:k)^2*l₁+r) ((a:k)^2*l₂+r)
      ((a:k)^2*x+r) ((a:k)^3*y) = (a:k) * rootExpression l₀ l₁ l₂ x y := by
  unfold rootExpression
  rw [show ((a:k)^2*x+r - ((a:k)^2*l₀+r))^2 -
      ((a:k)^2*l₀+r - ((a:k)^2*l₁+r))*((a:k)^2*l₀+r - ((a:k)^2*l₂+r)) =
      (a:k)^4*((x-l₀)^2-(l₀-l₁)*(l₀-l₂)) by ring,
    show 2*((a:k)^3*y) = (a:k)^3*(2*y) by ring, mul_div_mul_comm]
  congr 1
  field_simp

private lemma tangent_scaled (x y z w : k) :
    ArithmeticThetaMillerR0114.tangentValue k (changedLabels k e a r)
      ((a:k)^2*x+r) ((a:k)^3*y) ((a:k)^2*z+r) ((a:k)^3*w) =
      (a:k)^3 * ArithmeticThetaMillerR0114.tangentValue k e x y z w := by
  simp only [ArithmeticThetaMillerR0114.tangentValue, ArithmeticThetaMillerR0114.tangentSlope,
    changed_slope]
  ring

private lemma evaluation_scaled (t x l : k) :
    ((a:k)^3*t)^2 / ((a:k)^2*x+r - ((a:k)^2*l+r)) =
      (a:k)^4*(t^2/(x-l)) := by
  rw [show ((a:k)^3*t)^2 = (a:k)^6*t^2 by ring,
    show (a:k)^2*x+r - ((a:k)^2*l+r) = (a:k)^2*(x-l) by ring, mul_div_mul_comm]
  congr 1
  field_simp

private lemma coordinate_invariants
    (F : (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point)
    (hF : IsCoordinateChange k e a r F) (b : Marking k e) (hb : IsBasis k e b) :
    root k (changedLabels k e a r) (F ∘ b) = (a:k) * root k e b ∧
      phase k (changedLabels k e a r) (F ∘ b) = phase k e b := by
  obtain ⟨_,_,_,h0,h1⟩ := basis_affine k e b hb
  have hP := hF (b 0) h0
  have hQ := hF (b 1) h1
  have hl := change_labels k e a r F hF b hb
  constructor
  · simp only [root, hl, Function.comp_apply, hQ.1, hQ.2]
    exact root_scaled k a r _ _ _ _ _
  · have ht₀ : tangent k (changedLabels k e a r) (F (b 0)) (F (b 1)) =
        (a:k)^3 * tangent k e (b 0) (b 1) := by
      unfold tangent
      rw [hP.1,hP.2,hQ.1,hQ.2]
      exact tangent_scaled k e a r _ _ _ _
    have ht₁ : tangent k (changedLabels k e a r) (F (b 1)) (F (b 0)) =
        (a:k)^3 * tangent k e (b 1) (b 0) := by
      unfold tangent
      rw [hP.1,hP.2,hQ.1,hQ.2]
      exact tangent_scaled k e a r _ _ _ _
    simp only [phase, Function.comp_apply, ht₀, ht₁, hl, hP.1, hQ.1,
      evaluation_scaled, mul_div_mul_left _ _ (pow_ne_zero 4 a.ne_zero)]

private lemma coordinateChange_unique
    (F G : (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point)
    (hF : IsCoordinateChange k e a r F) (hG : IsCoordinateChange k e a r G) : F = G := by
  ext P
  by_cases hp : P = 0
  · simp [hp]
  · have hf : F P ≠ 0 := by simpa using hp
    have hg : G P ≠ 0 := by simpa using hp
    have hx : pointX k (changedLabels k e a r) (F P) =
        pointX k (changedLabels k e a r) (G P) := (hF P hp).1.trans (hG P hp).1.symm
    have hy : pointY k (changedLabels k e a r) (F P) =
        pointY k (changedLabels k e a r) (G P) := (hF P hp).2.trans (hG P hp).2.symm
    generalize F P = U at *
    generalize G P = V at *
    cases U with
    | zero => exact (hf rfl).elim
    | some x y hu =>
      cases V with
      | zero => exact (hg rfl).elim
      | some z w hv => simpa only [Point.some.injEq, pointX, pointY] using And.intro hx hy

/-- Unique affine coordinate equivalence, basis transport, weight-one root and invariant phase. -/
theorem coordinate_change_covariance :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ (a : kˣ) (r : k),
    ∃! F : (Curve k e).Point ≃+ (Curve k (changedLabels k e a r)).Point,
      IsCoordinateChange k e a r F ∧
      (∀ b : Marking k e, IsBasis k e b →
        IsBasis k (changedLabels k e a r) (F ∘ b) ∧
        root k (changedLabels k e a r) (F ∘ b) = (a:k) * root k e b ∧
        phase k (changedLabels k e a r) (F ∘ b) = phase k e b) := by
  intro k _ _ _ e he a r
  refine ⟨coordinateChangeEquiv k e a r he, ⟨coordinateChange_spec k e a r he, ?_⟩, ?_⟩
  · intro b hb
    exact ⟨basis_transport k e _ _ b hb,
      coordinate_invariants k e a r _ (coordinateChange_spec k e a r he) b hb⟩
  · intro F hF
    exact coordinateChange_unique k e a r F _ hF.1 (coordinateChange_spec k e a r he)

end ArithmeticThetaMarkingR0115
