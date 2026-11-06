module

public import AnnularTorsionPrerequisiteDefinitionsR0053
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

open ArithmeticThetaAnnularTorsionPrereqR0053

private lemma even_index_left (c a : ℕ) :
    2 * c ∣ c * (2 * a) := by
  refine ⟨a, ?_⟩
  ring

private lemma odd_index_right_not_dvd {c a : ℕ} (hc : 0 < c) :
    ¬ 2 * c ∣ c * (2 * a + 1) := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hmul : c * (2 * a + 1) = c * (2 * q) := by
    calc
      c * (2 * a + 1) = (2 * c) * q := hq
      _ = c * (2 * q) := by ring
  have heq : 2 * a + 1 = 2 * q := Nat.eq_of_mul_eq_mul_left hc hmul
  omega

private lemma odd_index_left_not_dvd {c a : ℕ} (hc : 0 < c) :
    ¬ 2 * c ∣ c * (2 * a + 1) := by
  exact odd_index_right_not_dvd hc

private lemma preceding_index (c : ℕ) (a : Fin c) (hc : 1 < c) :
    (2 * a.val + 2 * c - 1) % (2 * c) =
      if a.val = 0 then 2 * c - 1 else 2 * a.val - 1 := by
  by_cases ha : a.val = 0
  · simp [ha, Nat.mod_eq_of_lt (by omega : 2 * c - 1 < 2 * c)]
  · have ha_pos : 0 < a.val := Nat.pos_of_ne_zero ha
    have hlt : 2 * a.val - 1 < 2 * c := by omega
    have hrewrite : 2 * a.val + 2 * c - 1 =
        (2 * a.val - 1) + 2 * c := by omega
    rw [hrewrite]
    calc
      ((2 * a.val - 1) + 2 * c) % (2 * c) =
          ((2 * a.val - 1) % (2 * c) + (2 * c) % (2 * c)) % (2 * c) :=
        Nat.add_mod _ _ _
      _ = 2 * a.val - 1 := by
        rw [Nat.mod_eq_of_lt hlt]
        simp
        exact Nat.mod_eq_of_lt hlt
      _ = (if a.val = 0 then 2 * c - 1 else 2 * a.val - 1) := by simp [ha]

theorem powered_chart_placement :
    ∀ (k : Type u) [Field k] [CharZero k] (c : ℕ), 1 < c →
      (∀ a : Fin c,
        horizontal k (2 * c) c (2 * a.val) = horizontalEquation k true c) ∧
      (∀ a : Fin c,
        horizontal k (2 * c) c ((2 * a.val + 2 * c - 1) % (2 * c)) =
          horizontalEquation k false c) := by
  intro k _ _ c hc
  have hcpos : 0 < c := by omega
  constructor
  · intro a
    have hleft : 2 * c ∣ c * (2 * a.val) := even_index_left c a.val
    have hright : ¬ 2 * c ∣ c * (2 * a.val + 1) :=
      odd_index_right_not_dvd hcpos
    simp [horizontal, hleft, hright]
  · intro a
    rw [preceding_index c a hc]
    by_cases ha : a.val = 0
    · have hleft : ¬ 2 * c ∣ c * (2 * c - 1) := by
        have h := odd_index_left_not_dvd (c := c) (a := c - 1) hcpos
        simpa [show 2 * (c - 1) + 1 = 2 * c - 1 by omega] using h
      have hright : 2 * c ∣ c * ((2 * c - 1) + 1) := by
        have heq : (2 * c - 1) + 1 = 2 * c := by omega
        rw [heq]
        refine ⟨c, ?_⟩
        ring
      simp [horizontal, ha, hleft, hright]
    · have ha_pos : 0 < a.val := Nat.pos_of_ne_zero ha
      have hleft : ¬ 2 * c ∣ c * (2 * a.val - 1) := by
        have h := odd_index_left_not_dvd (c := c) (a := a.val - 1) hcpos
        simpa [show 2 * (a.val - 1) + 1 = 2 * a.val - 1 by omega] using h
      have hright : 2 * c ∣ c * ((2 * a.val - 1) + 1) := by
        have heq : (2 * a.val - 1) + 1 = 2 * a.val := by omega
        rw [heq]
        exact even_index_left c a.val
      simp [horizontal, ha, hleft, hright]

end ArithmeticThetaLocalNormR0054
