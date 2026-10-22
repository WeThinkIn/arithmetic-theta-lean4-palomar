module

public import CorrectedGammaDefinitionsR0061
public import ScaledGammaUnitProductR0050

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

open ArithmeticThetaScaledAnnularR0050
open ArithmeticThetaAnnularTorsionPrereqR0053

lemma tailPartial_eq_scaledGammaTailPartial
    (k : Type u) [Field k] [CharZero k] (r j N : ℕ)
    (hr : 0 < r) (hj : j < r) :
    tailPartial k r j N =
      ArithmeticThetaScaledAnnularR0050.gammaTailPartial k 1 r j N := by
  classical
  rw [tailPartial, ArithmeticThetaScaledAnnularR0050.gammaTailPartial,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  have hLiff : r * l + j = 0 ↔ j = 0 ∧ l = 0 := by
    constructor
    · intro h
      have hsum : r * l = 0 ∧ j = 0 := Nat.add_eq_zero.mp h
      have hl0 : l = 0 := (Nat.mul_eq_zero.mp hsum.1).resolve_left (by omega)
      exact ⟨hsum.2, hl0⟩
    · rintro ⟨rfl, rfl⟩
      simp
  have hRiff : r * (l + 1) - j - 1 = 0 ↔ j + 1 = r ∧ l = 0 := by
    constructor
    · intro h
      have hmul : r ≤ r * (l + 1) := by
        exact Nat.le_mul_of_pos_right r (by omega : 0 < l + 1)
      have hle : j ≤ r * (l + 1) := by omega
      have hsub : r * (l + 1) - j = 1 := by omega
      have hEq : r * (l + 1) = 1 + j :=
        (Nat.sub_eq_iff_eq_add hle).mp hsub
      have hjr : j + 1 = r := by omega
      have hprod_le : r * (l + 1) ≤ r * 1 := by
        calc
          r * (l + 1) = 1 + j := hEq
          _ = r := by omega
          _ ≤ r * 1 := by simp
      have hl1 : l + 1 ≤ 1 := Nat.le_of_mul_le_mul_left hprod_le hr
      exact ⟨hjr, by omega⟩
    · rintro ⟨hjr, rfl⟩
      omega
  have hLcond : ((r = 0 ∨ l = 0) ∧ j = 0) ↔ (j = 0 ∧ l = 0) := by
    constructor
    · rintro ⟨hr0 | rfl, rfl⟩
      · omega
      · simp
    · rintro ⟨rfl, rfl⟩
      simp [hr.ne']
  simp [leftTailFactor, rightTailFactor, leftFactor, rightFactor,
    leftExponent, rightExponent, tau, cx, cy,
    ArithmeticThetaScaledAnnularR0050.gammaTailFactor,
    ArithmeticThetaScaledAnnularR0050.gammaLeftExponent,
    ArithmeticThetaScaledAnnularR0050.gammaRightExponent,
    ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledAnnularR0050.cx,
    ArithmeticThetaScaledAnnularR0050.cy, hLiff, hRiff, hLcond]

theorem gamma_tail_exists :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ), 0 < r → j < r →
      ∃ v : Chart k, IsUnit v ∧
        Converges k r j (tailPartial k r j) v := by
  intro k _ _ r j hr hj
  have hj' : j + 1 ≤ r := by omega
  obtain ⟨v, hv, _⟩ :=
    ArithmeticThetaScaledAnnularR0050.gamma_unit_product k 1 r j
      (by simpa using hr) hj'
  refine ⟨v, hv.1, ?_⟩
  intro n
  obtain ⟨N₀, hN₀⟩ := hv.2.1 n
  refine ⟨N₀, ?_⟩
  intro N hN
  simpa [tailPartial_eq_scaledGammaTailPartial k r j N hr hj,
    ArithmeticThetaAnnularTorsionPrereqR0053.filtration] using hN₀ N hN

end ArithmeticThetaCorrectedGammaR0061
