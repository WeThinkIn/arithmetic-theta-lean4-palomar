module

public import MillerGeometryDefinitionsR0114
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Full rational four-torsion coordinates from two actual independent halves. -/
noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

private lemma split_two_torsion {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (T : (Curve k e).Point) (hT : 2 • T = 0) :
    T = 0 ∨ ∃ (i : Fin 3) (hi : (Curve k e).Nonsingular (e i) 0),
      T = Point.some (e i) 0 hi := by
  cases T with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have hn : Point.some x y h = -Point.some x y h := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [two_nsmul] using hT
    have hy : y = 0 := by
      have hh := (Point.some.inj hn).2
      simp only [WeierstrassCurve.Affine.negY, Curve, splitCurve, zero_mul, sub_zero] at hh
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

private lemma labelled_add {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (he : Distinct k e)
    (h0 : (Curve k e).Nonsingular (e 0) 0)
    (h1 : (Curve k e).Nonsingular (e 1) 0)
    (h2 : (Curve k e).Nonsingular (e 2) 0) :
    Point.some (e 0) 0 h0 + Point.some (e 1) 0 h1 = Point.some (e 2) 0 h2 := by
  have h01 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (he h)
  rw [Point.add_of_X_ne h01]
  rw [Point.some.injEq]
  simp only [addX, addY, negAddY, negY, Curve, splitCurve]
  simp [WeierstrassCurve.Affine.slope_of_X_ne h01]
  ring

private def fourCoordinates {G : Type*} [AddCommGroup G]
    (P Q : G) (hP : 4 • P = 0) (hQ : 4 • Q = 0) :
    ZMod 4 × ZMod 4 →+ G where
  toFun z := z.1.val • P + z.2.val • Q
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← nsmul_eq_mod_nsmul _ hP, ← nsmul_eq_mod_nsmul _ hQ]
    simp only [add_nsmul]
    abel

private lemma fourCoordinates_injective {G : Type*} [AddCommGroup G]
    (P Q : G) (hP : 4 • P = 0) (hQ : 4 • Q = 0)
    (hA : 2 • P ≠ 0) (hB : 2 • Q ≠ 0) (hAB : 2 • P + 2 • Q ≠ 0) :
    Function.Injective (fourCoordinates P Q hP hQ) := by
  have hk : ∀ z, fourCoordinates P Q hP hQ z = 0 → z = 0 := by
    rintro ⟨a,b⟩ h
    change a.val • P + b.val • Q = 0 at h
    have hd := congrArg (fun t : G => 2 • t) h
    simp only [nsmul_add, smul_smul, nsmul_zero] at hd
    rw [nsmul_eq_mod_nsmul (2 * a.val) hP,
      nsmul_eq_mod_nsmul (2 * b.val) hQ] at hd
    -- Doubling excludes odd coordinates; the original relation excludes
    -- the three nonzero even pairs. This exhausts all sixteen pairs.
    fin_cases a <;> fin_cases b <;>
      norm_num [ZMod.val] at h hd ⊢ <;> simp_all
    rfl
  intro a b hab
  have hz : fourCoordinates P Q hP hQ (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (hk _ hz)

private lemma fourCoordinates_surjective_torsion {G : Type*} [AddCommGroup G]
    (P Q : G) (hP : 4 • P = 0) (hQ : 4 • Q = 0)
    (hc : ∀ U : G, 2 • U = 0 → U = 0 ∨ U = 2 • P ∨ U = 2 • Q ∨
      U = 2 • P + 2 • Q) (T : G) (hT : 4 • T = 0) :
    ∃ z, fourCoordinates P Q hP hQ z = T := by
  let f := fourCoordinates P Q hP hQ
  have hlift : ∃ z, 2 • f z = 2 • T := by
    have hv1 : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by decide)
    have h := hc (2 • T) (by simpa only [← mul_nsmul] using hT)
    rcases h with h | h | h | h
    · exact ⟨(0,0), by simpa [f, fourCoordinates] using h.symm⟩
    · exact ⟨(1,0), by simpa [f, fourCoordinates, hv1] using h.symm⟩
    · exact ⟨(0,1), by simpa [f, fourCoordinates, hv1] using h.symm⟩
    · exact ⟨(1,1), by simpa [f, fourCoordinates, hv1, nsmul_add] using h.symm⟩
  obtain ⟨z, hz⟩ := hlift
  have hU : 2 • (T - f z) = 0 := by rw [nsmul_sub, hz, sub_self]
  have hres : ∃ w, f w = T - f z := by
    have hv2 : (2 : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by decide)
    rcases hc (T - f z) hU with h | h | h | h
    · exact ⟨(0,0), by simpa [f, fourCoordinates] using h.symm⟩
    · exact ⟨(2,0), by simpa [f, fourCoordinates, hv2] using h.symm⟩
    · exact ⟨(0,2), by simpa [f, fourCoordinates, hv2] using h.symm⟩
    · exact ⟨(2,2), by simpa [f, fourCoordinates, hv2, nsmul_add] using h.symm⟩
  obtain ⟨w, hw⟩ := hres
  refine ⟨w + z, ?_⟩
  change f (w + z) = T
  rw [map_add, hw, sub_add_cancel]


/-- Two actual independent halves give unique ordered coordinates on rational four-torsion. -/
theorem independent_halves_four_basis :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Distinct k e → ∀ (P Q : (Curve k e).Point),
      IsHalfPoint k e 0 P → IsHalfPoint k e 1 Q →
      ∀ T : (Curve k e).Point, 4 • T = 0 ↔
        ∃! z : Fin 2 → ZMod 4, (z 0).val • P + (z 1).val • Q = T := by
  intro k _ _ _ e he P Q hP hQ T
  have h01 : e 0 ≠ e 1 := by intro h; exact (by decide : (0 : Fin 3) ≠ 1) (he h)
  have h02 : e 0 ≠ e 2 := by intro h; exact (by decide : (0 : Fin 3) ≠ 2) (he h)
  have h12 : e 1 ≠ e 2 := by intro h; exact (by decide : (1 : Fin 3) ≠ 2) (he h)
  rcases hP with ⟨hP0, hdP⟩
  rcases hQ with ⟨hQ1, hdQ⟩
  have hP4 : 4 • P = 0 := by
    have ht : 2 • WeierstrassCurve.Affine.Point.some (e 0) 0 hP0 = 0 := by
      rw [two_nsmul]
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [WeierstrassCurve.Affine.negY, Curve, ArithmeticThetaFourTorsion.splitCurve]
    calc
      4 • P = 2 • (2 • P) := by rw [← mul_nsmul]
      _ = 0 := by rw [hdP, ht]
  have hQ4 : 4 • Q = 0 := by
    have ho := ArithmeticThetaFourTorsion.actual_half_order_four k (e 0) (e 1) (e 2)
      hQ1 Q h01 h02 h12 hdQ
    simpa only [ho] using addOrderOf_nsmul_eq_zero Q
  have hP2 : 2 • P ≠ 0 := by rw [hdP]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQ2 : 2 • Q ≠ 0 := by rw [hdQ]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have h2 := (ArithmeticThetaFourTorsion.split_smooth (e 0) (e 1) (e 2) h01 h02 h12).2.2.2
  have hadd := labelled_add e he hP0 hQ1 h2
  have hsum : 2 • P + 2 • Q ≠ 0 := by
    rw [hdP, hdQ, hadd]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hc : ∀ U : (Curve k e).Point, 2 • U = 0 → U = 0 ∨ U = 2 • P ∨ U = 2 • Q ∨ U = 2 • P + 2 • Q := by
    intro U hU
    rcases split_two_torsion e U hU with h | ⟨i, hi, hU⟩
    · exact Or.inl h
    · fin_cases i
      · exact Or.inr (Or.inl (by rw [hU, hdP]; rfl))
      · exact Or.inr (Or.inr (Or.inl (by rw [hU, hdQ]; rfl)))
      · exact Or.inr (Or.inr (Or.inr (by rw [hU, hdP, hdQ, hadd]; rfl)))
  constructor
  · intro hT
    have hex := fourCoordinates_surjective_torsion P Q hP4 hQ4 hc T hT
    obtain ⟨z, hz⟩ := hex
    refine ⟨fun j => if j = 0 then z.1 else z.2, ?_, ?_⟩
    · simpa [fourCoordinates] using hz
    · intro w hw
      have hh : fourCoordinates P Q hP4 hQ4 (w 0, w 1) =
          fourCoordinates P Q hP4 hQ4 z := hw.trans hz.symm
      have hzw := fourCoordinates_injective P Q hP4 hQ4 hP2 hQ2 hsum hh
      funext j
      fin_cases j
      · simpa using congrArg Prod.fst hzw
      · simpa using congrArg Prod.snd hzw
  · rintro ⟨z, hz, _⟩
    rw [← hz, nsmul_add, smul_comm 4, smul_comm 4, hP4, hQ4]
    simp

end ArithmeticThetaMillerR0114
