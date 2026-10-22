module

public import MarkingCharacterDefinitionsR0115
public import Mathlib.Tactic.FinCases
public import FourTorsionRoot

@[expose] public section

/-! Recover the actual affine two-torsion labels from a full four-torsion basis. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

private lemma finite_two_torsion {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (T : (Curve k e).Point) (hT : 2 • T = 0) (hn : T ≠ 0) :
    ∃ (i : Fin 3) (hi : (Curve k e).Nonsingular (e i) 0),
      T = Point.some (e i) 0 hi := by
  cases T with
  | zero => exact False.elim (hn rfl)
  | some x y h =>
    have hn' : Point.some x y h = -Point.some x y h := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [two_nsmul] using hT
    have hy : y = 0 := by
      have hh := (Point.some.inj hn').2
      simp only [WeierstrassCurve.Affine.negY, Curve,
        ArithmeticThetaMillerR0114.Curve, splitCurve, zero_mul, sub_zero] at hh
      have hz : (2 : k) * y = 0 := by linear_combination hh
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
    subst y
    have hx := (split_equation (e 0) (e 1) (e 2) x 0).mp h.1
    simp only [zero_pow (by decide : 2 ≠ 0), eq_comm (a := (0 : k)),
      mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (hx | hx) | hx
    · subst x; exact ⟨0, h, rfl⟩
    · subst x; exact ⟨1, h, rfl⟩
    · subst x; exact ⟨2, h, rfl⟩

private lemma curve_perm {k : Type u} [Field k] (e : Fin 3 → k)
    (σ : Equiv.Perm (Fin 3)) : Curve k e = Curve k (e ∘ σ) := by
  have h01 := σ.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := σ.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := σ.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  generalize h0 : σ 0 = a at *
  generalize h1 : σ 1 = b at *
  generalize h2 : σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> try contradiction
  all_goals
    ext <;> simp only [Curve, ArithmeticThetaMillerR0114.Curve,
      splitCurve, Function.comp_apply, h0, h1, h2] <;> ring!

private lemma half_root_on_equal_curve {k : Type u} [Field k] [CharZero k]
    [DecidableEq k] (W : WeierstrassCurve.Affine k) (a b c : k)
    (hW : W = splitCurve a b c) (P : W.Point)
    (h : W.Nonsingular b 0) (hd : 2 • P = Point.some b 0 h)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ (x y : k) (hP : W.Nonsingular x y), P = Point.some x y hP ∧
      rootExpression a b c x y ^ 2 = b - a := by
  subst W
  obtain ⟨x, y, hP, hp, _, hr, _⟩ := actual_half_root k a b c h P hab hac hbc hd
  exact ⟨x, y, hP, hp, hr⟩

/-- All coordinate and nonvanishing providers are recovered from the actual basis. -/
theorem basis_coordinate_geometry :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Function.Injective e → ∀ b : Marking k e, IsBasis k e b →
      (∀ i : Fin 2, b i ≠ 0 ∧ pointY k e (b i) ≠ 0) ∧
      (∃ σ : Equiv.Perm (Fin 3), labels k e b = e ∘ σ) ∧
      Curve k e = Curve k (labels k e b) ∧
      (∀ i : Fin 2, ∃ h : (Curve k e).Nonsingular (labels k e b i.castSucc) 0,
        2 • b i = Point.some (labels k e b i.castSucc) 0 h) ∧
      root k e b ≠ 0 ∧ root k e b ^ 2 = labels k e b 1 - labels k e b 0 := by
  intro k _ _ _ e he b hb
  let z : Fin 3 → Fin 2 → ZMod 4 := ![![2,0], ![0,2], ![2,2]]
  let D : Fin 3 → (Curve k e).Point :=
    ![2 • b 0, 2 • b 1, 2 • b 0 + 2 • b 1]
  have hzD : ∀ j, coordinates k e b (z j) = D j := by
    intro j
    have hv2 : (2 : ZMod 4).val = 2 := by decide
    fin_cases j <;> simp [coordinates, z, D, hv2]
  have hz : Function.Injective z := by decide
  have hD : Function.Injective D := by
    intro i j hij
    apply hz
    apply hb.2.1
    simpa only [hzD] using hij
  have hDn : ∀ j, D j ≠ 0 := by
    intro j hj
    have hh : z j = 0 := hb.2.1 (by rw [hzD, hj]; simp [coordinates])
    have hne : z j ≠ 0 := by fin_cases j <;> decide
    exact hne hh
  have hDt : ∀ j, 2 • D j = 0 := by
    intro j
    fin_cases j <;> simp [D, ← mul_nsmul, hb.1]
  have hrepr : ∀ j, ∃ (i : Fin 3) (hi : (Curve k e).Nonsingular (e i) 0),
      D j = Point.some (e i) 0 hi := fun j => finite_two_torsion e (D j) (hDt j) (hDn j)
  choose s hs hsD using hrepr
  have hsInj : Function.Injective s := by
    intro i j hij
    apply hD
    rw [hsD i, hsD j]
    rw [Point.some.injEq]
    exact ⟨congrArg e hij, rfl⟩
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective s
    ⟨hsInj, (Finite.injective_iff_surjective).mp hsInj⟩
  have hlabels : labels k e b = e ∘ σ := by
    funext j
    change labels k e b j = e (s j)
    have hcoord := congrArg (pointX k e) (hsD j)
    fin_cases j <;> simpa [labels, D, pointX] using hcoord
  have hlinj : Function.Injective (labels k e b) := by
    rw [hlabels]
    exact he.comp σ.injective
  have hcurve : Curve k e = Curve k (labels k e b) := by
    rw [hlabels]
    exact curve_perm e σ
  have hd : ∀ i : Fin 2, ∃ h : (Curve k e).Nonsingular (labels k e b i.castSucc) 0,
      2 • b i = Point.some (labels k e b i.castSucc) 0 h := by
    intro i
    have hli : labels k e b i.castSucc = e (s i.castSucc) := congrFun hlabels i.castSucc
    rw [hli]
    refine ⟨hs i.castSucc, ?_⟩
    have hh := hsD i.castSucc
    fin_cases i <;> simpa [D] using hh
  have hbn : ∀ i : Fin 2, 2 • b i ≠ 0 := by
    intro i
    obtain ⟨h, hh⟩ := hd i
    rw [hh]
    exact Point.some_ne_zero h
  have hfinite : ∀ i : Fin 2, b i ≠ 0 ∧ pointY k e (b i) ≠ 0 := by
    intro i
    refine ⟨fun hh => hbn i (by simp [hh]), ?_⟩
    have hn := hbn i
    cases hp : b i with
    | zero => exact False.elim (hn (by rw [hp]; exact nsmul_zero 2))
    | some x y h =>
      change y ≠ 0
      intro hy
      apply hn
      rw [hp, two_nsmul]
      apply Point.add_self_of_Y_eq
      simp [WeierstrassCurve.Affine.negY, Curve,
        ArithmeticThetaMillerR0114.Curve, splitCurve, hy]
  have hl01 : labels k e b 0 ≠ labels k e b 1 := hlinj.ne (by decide)
  have hl02 : labels k e b 0 ≠ labels k e b 2 := hlinj.ne (by decide)
  have hl12 : labels k e b 1 ≠ labels k e b 2 := hlinj.ne (by decide)
  obtain ⟨h1, hd1⟩ := hd 1
  obtain ⟨x, y, hP, hp, hr⟩ := half_root_on_equal_curve (Curve k e)
    (labels k e b 0) (labels k e b 1) (labels k e b 2) hcurve (b 1) h1 hd1 hl01 hl02 hl12
  have hroot : root k e b ^ 2 = labels k e b 1 - labels k e b 0 := by
    simpa [root, hp, pointX, pointY] using hr
  refine ⟨hfinite, ⟨σ, hlabels⟩, hcurve, hd, ?_, hroot⟩
  intro hz
  have hh : labels k e b 1 - labels k e b 0 = 0 := by simpa [hz] using hroot.symm
  exact hl01 (sub_eq_zero.mp hh).symm

end ArithmeticThetaMarkingR0115
