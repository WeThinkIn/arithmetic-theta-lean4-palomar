module

public import Mathlib

@[expose] public section

open Polynomial

namespace ArithmeticThetaKummer

universe u v

theorem single_root_degree (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E] (x : E) (a : K)
    (N : ℕ) (hN : 0 < N) (hx : x ^ N = algebraMap K E a) :
    FiniteDimensional K (IntermediateField.adjoin K {x}) ∧
      Module.finrank K (IntermediateField.adjoin K {x}) ≤ N := by
  have hm : (X ^ N - C a : K[X]).Monic := monic_X_pow_sub_C a (by omega)
  have he : aeval x (X ^ N - C a : K[X]) = 0 := by simp [hx]
  have hi : IsIntegral K x := ⟨_, hm, he⟩
  refine ⟨IntermediateField.adjoin.finiteDimensional hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have hd := Polynomial.natDegree_le_natDegree (minpoly.min K x hm he)
  simpa using hd

theorem finite_root_degree (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E] (N : ℕ) (hN : 0 < N)
    (S : Finset E) (hS : ∀ x ∈ S, ∃ a : K, x ^ N = algebraMap K E a) :
    FiniteDimensional K (IntermediateField.adjoin K (S : Set E)) ∧
      Module.finrank K (IntermediateField.adjoin K (S : Set E)) ≤ N ^ S.card := by
  classical
  have hi : ∀ x ∈ (S : Set E), IsIntegral K x := by
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨X ^ N - C a, monic_X_pow_sub_C a (by omega), by simp [ha]⟩
  refine ⟨IntermediateField.finiteDimensional_adjoin hi, ?_⟩
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot,
      Finset.card_empty, pow_zero]
  | @insert x S hx ih =>
    have hs : ∀ y ∈ S, ∃ a : K, y ^ N = algebraMap K E a := by
      intro y hy
      exact hS y (Finset.mem_insert_of_mem hy)
    obtain ⟨a, ha⟩ := hS x (Finset.mem_insert_self x S)
    have hsingle := (single_root_degree K E x a N hN ha).2
    rw [Finset.card_insert_of_notMem hx, pow_succ]
    rw [Finset.coe_insert, ← Set.singleton_union, IntermediateField.adjoin_union]
    calc
      Module.finrank K ↥(IntermediateField.adjoin K {x} ⊔
          IntermediateField.adjoin K (S : Set E)) ≤
        Module.finrank K (IntermediateField.adjoin K {x}) *
          Module.finrank K (IntermediateField.adjoin K (S : Set E)) :=
        IntermediateField.finrank_sup_le _ _
      _ ≤ N * N ^ S.card := Nat.mul_le_mul hsingle
        (ih hs (fun y hy => hi y (Finset.mem_insert_of_mem hy)))
      _ = N ^ S.card * N := Nat.mul_comm _ _

/-- Adjoining a prescribed indexed family allows repeated roots. -/
theorem family_root_degree (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E] (N s : ℕ) (hN : 0 < N)
    (r : Fin s → E) (a : Fin s → K)
    (hr : ∀ j, r j ^ N = algebraMap K E (a j)) :
    FiniteDimensional K (IntermediateField.adjoin K (Set.range r)) ∧
      Module.finrank K (IntermediateField.adjoin K (Set.range r)) ≤ N ^ s := by
  classical
  let S : Finset E := Finset.univ.image r
  have hS : (S : Set E) = Set.range r := by
    ext x
    simp [S]
  have hroots : ∀ x ∈ S, ∃ b : K, x ^ N = algebraMap K E b := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a j, hr j⟩
  obtain ⟨hfinite, hdegree⟩ := finite_root_degree K E N hN S hroots
  rw [hS] at hfinite hdegree
  refine ⟨hfinite, hdegree.trans ?_⟩
  have hcard : S.card ≤ s := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f := r))
  exact Nat.pow_le_pow_right hN hcard

/-- All roots can be selected in one algebraic closure with the same degree bound. -/
theorem exists_closure_roots_degree (K : Type u) [Field K]
    (N s : ℕ) (hN : 0 < N) (a : Fin s → K) :
    ∃ r : Fin s → AlgebraicClosure K,
      (∀ j, r j ^ N = algebraMap K (AlgebraicClosure K) (a j)) ∧
      FiniteDimensional K (IntermediateField.adjoin K (Set.range r)) ∧
      Module.finrank K (IntermediateField.adjoin K (Set.range r)) ≤ N ^ s := by
  classical
  have hroot : ∀ j : Fin s, ∃ x : AlgebraicClosure K,
      x ^ N = algebraMap K (AlgebraicClosure K) (a j) :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ hN
  choose r hr using hroot
  exact ⟨r, hr, family_root_degree K (AlgebraicClosure K) N s hN r a hr⟩

end ArithmeticThetaKummer

