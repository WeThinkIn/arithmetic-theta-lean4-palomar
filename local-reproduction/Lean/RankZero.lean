import Mathlib

namespace ArithmeticThetaElementary

theorem rank_zero_coefficients :
    ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ,
      Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0 := by
  intro Q hQ n
  have hx (x : Fin 0 → ℤ) : x = 0 := Subsingleton.elim _ _
  by_cases hn : n = 0
  · subst n
    have : Nonempty {x : Fin 0 → ℤ // Q x = 0} := ⟨⟨0, hQ⟩⟩
    rw [if_pos rfl]
    exact Nat.card_unique
  · have : IsEmpty {x : Fin 0 → ℤ // Q x = n} :=
      ⟨fun x => hn (x.property.symm.trans ((congrArg Q (hx x.val)).trans hQ))⟩
    simp [hn]

theorem sum_smul_one (h : ℕ) (c : Fin h → ℂ) :
    (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = PowerSeries.C (∑ i : Fin h, c i) := by
  simp [PowerSeries.smul_eq_C_mul, map_sum]

theorem rank_zero_kernel :
    ∀ (h : ℕ) (c : Fin h → ℂ),
      (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = 0 ↔ (∑ i : Fin h, c i) = 0 := by
  intro h c
  rw [sum_smul_one]
  exact map_eq_zero_iff _ PowerSeries.C_injective

theorem rank_zero_image :
    ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ,
      (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔
        ∃ z : ℂ, f = PowerSeries.C z := by
  intro h hh f
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨∑ i : Fin h, c i, hc.symm.trans (sum_smul_one h c)⟩
  · rintro ⟨z, rfl⟩
    let j : Fin h := ⟨0, hh⟩
    refine ⟨fun i => if i = j then z else 0, ?_⟩
    rw [sum_smul_one]
    simp

end ArithmeticThetaElementary
