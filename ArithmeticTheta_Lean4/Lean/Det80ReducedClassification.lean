import Mathlib

open scoped BigOperators

namespace ArithmeticThetaDet80

private lemma abs_bounds {a b : ℤ} (h : |b| ≤ a) : -a ≤ b ∧ b ≤ a := by
  exact (abs_le.mp h)

theorem reduced_bounds :
    ∀ a b c : ℤ,
      (0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80) →
        1 ≤ a ∧ a ≤ 5 ∧ -5 ≤ b ∧ b ≤ 5 ∧ 1 ≤ c ∧ c ≤ 26 := by
  intro a b c h
  rcases h with ⟨ha, habs, hac, hdet⟩
  have hab := abs_bounds habs
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have hac0 : 0 ≤ a * (c - a) := by nlinarith
  have ha2 : 3 * a ^ 2 ≤ 80 := by nlinarith
  have ha5 : a ≤ 5 := by nlinarith
  have hamin : 1 ≤ a := by omega
  have hb5 : -5 ≤ b ∧ b ≤ 5 := by omega
  have hcmin : 1 ≤ c := by omega
  have hc26 : c ≤ 26 := by nlinarith [sq_nonneg b]
  exact ⟨hamin, ha5, hb5.1, hb5.2, hcmin, hc26⟩

private lemma reduced_cases (a b c : ℤ)
    (h : 0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80) :
    (a = 1 ∧ b = 0 ∧ c = 20) ∨
    (a = 3 ∧ b = -2 ∧ c = 7) ∨
    (a = 3 ∧ b = 2 ∧ c = 7) ∨
    (a = 4 ∧ b = 0 ∧ c = 5) ∨
    (a = 2 ∧ b = 0 ∧ c = 10) ∨
    (a = 4 ∧ b = -4 ∧ c = 6) ∨
    (a = 4 ∧ b = 4 ∧ c = 6) := by
  have bd := reduced_bounds a b c h
  rcases h with ⟨ha, habs, hac, hdet⟩
  rcases bd with ⟨ha1, ha5, hb5n, hb5p, hc1, hc26⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at *

theorem all_reduced_triples :
    ∀ a b c : ℤ,
      (0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80) ↔
        ((a = 1 ∧ b = 0 ∧ c = 20) ∨
         (a = 3 ∧ b = -2 ∧ c = 7) ∨
         (a = 3 ∧ b = 2 ∧ c = 7) ∨
         (a = 4 ∧ b = 0 ∧ c = 5) ∨
         (a = 2 ∧ b = 0 ∧ c = 10) ∨
         (a = 4 ∧ b = -4 ∧ c = 6) ∨
         (a = 4 ∧ b = 4 ∧ c = 6)) := by
  intro a b c
  constructor
  · exact reduced_cases a b c
  · intro h
    rcases h with h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl, rfl⟩ <;> norm_num

theorem smith_gcd_classification :
    ∀ a b c : ℤ,
      (0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80 ∧
        Nat.gcd (Int.gcd (2 * a) b) (Int.natAbs (2 * c)) = 2) ↔
        ((a = 1 ∧ b = 0 ∧ c = 20) ∨
         (a = 3 ∧ b = -2 ∧ c = 7) ∨
         (a = 3 ∧ b = 2 ∧ c = 7) ∨
         (a = 4 ∧ b = 0 ∧ c = 5)) := by
  intro a b c
  constructor
  · rintro ⟨ha, habs, hac, hdet, hg⟩
    have hbase : 0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80 := ⟨ha, habs, hac, hdet⟩
    rcases (all_reduced_triples a b c).mp hbase with h | h | h | h | h | h | h
    all_goals
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num at hg <;> norm_num
  · intro h
    rcases h with h | h | h | h <;>
      rcases h with ⟨rfl, rfl, rfl⟩ <;> norm_num

private def U₁ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![0, 1]]
private def V₁ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![0, 1]]
private def U₂ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![7, -1]]
private def V₂ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![0, 1], ![1, -3]]
private def U₃ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![7, 1]]
private def V₃ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![0, 1], ![-1, 3]]
private def U₄ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![-1, 1], ![-5, 4]]
private def V₄ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, -5], ![1, -4]]

theorem explicit_smith_witnesses :
    ∀ a b c : ℤ,
      (0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = 80 ∧
        Nat.gcd (Int.gcd (2 * a) b) (Int.natAbs (2 * c)) = 2) →
      ∃ U V : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit U.det ∧ IsUnit V.det ∧ U * Matrix.of ![![2 * a, b], ![b, 2 * c]] * V =
          Matrix.of ![![2, 0], ![0, 40]] := by
  intro a b c h
  rcases (smith_gcd_classification a b c).mp h with h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨U₁, V₁, ?_, ?_, ?_⟩ <;> decide
  · rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨U₃, V₃, ?_, ?_, ?_⟩ <;> decide
  · rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨U₂, V₂, ?_, ?_, ?_⟩ <;> decide
  · rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨U₄, V₄, ?_, ?_, ?_⟩ <;> decide

end ArithmeticThetaDet80
