module

public import LatticeShellFinite
public import IntegralGramOrthogonalization

@[expose] public section

open scoped BigOperators

namespace ArithmeticThetaCore

lemma gram_eval (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm'))
      (fun k => (x k : ℚ)) =
      (1 / 2 : ℚ) * ∑ i : Fin n, ∑ j : Fin n, (x i : ℚ) * (A i j : ℚ) * (x j : ℚ) := by
  change (1 / 2 : ℚ) *
      ((((Matrix.toLinearMap₂' ℚ) (A.map (Int.castRingHom ℚ)))
        (fun k => (x k : ℚ))) (fun k => (x k : ℚ))) = _
  rw [Matrix.toLinearMap₂'_apply]
  simp [smul_eq_mul, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem even_gram_natural_values :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) →
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef →
      (∀ x : Fin n → ℤ, ∃ m : ℕ,
        (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm'))
          (fun k => (x k : ℚ)) = (m : ℚ)) := by
  intro n A hsym hdiag hpos x
  let f : Fin n → Fin n → ℤ := fun i j => x i * A i j * x j
  have hfsym : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M i j) hsym
    have hs' : A j i = A i j := by simpa only [Matrix.transpose_apply] using hs
    rw [hs']
    ring
  have hfdiag : ∀ i, Even (f i i) := by
    intro i
    dsimp [f]
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hdiag i).mul_left (x i * x i)
  have heven : Even (∑ i : Fin n, ∑ j : Fin n, f i j) :=
    ArithmeticThetaLattice.even_symmetric_sum (Finset.univ : Finset (Fin n)) f hfsym hfdiag
  let S : ℤ := ∑ i : Fin n, ∑ j : Fin n, f i j
  have hevenS : Even S := by simpa [S] using heven
  obtain ⟨z, hz⟩ := hevenS
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, (x i : ℚ) * (A i j : ℚ) * (x j : ℚ)) = (S : ℚ) := by
    simp only [S, f, Int.cast_sum, Int.cast_mul]
  have hnonneg : (0 : ℚ) ≤
      (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm'))
        (fun k => (x k : ℚ)) := hpos.nonneg _
  have hnonneg' : (0 : ℚ) ≤ (1 / 2 : ℚ) * (S : ℚ) := by
    rw [← hsum]
    rw [gram_eval] at hnonneg
    exact hnonneg
  have hzq : (0 : ℚ) ≤ (z : ℚ) := by
    have hhalf : (1 / 2 : ℚ) * (S : ℚ) = (z : ℚ) := by
      rw [hz]
      push_cast
      ring
    rw [← hhalf]
    exact hnonneg'
  have hzint : (0 : ℤ) ≤ z := by exact_mod_cast hzq
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hzint
  refine ⟨m, ?_⟩
  rw [gram_eval, hsum, hz]
  rw [hm]
  push_cast
  ring

theorem finite_integer_coefficients :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      (∀ x : Fin n → ℤ, ∃ m : ℕ, (Q) (fun k => (x k : ℚ)) = (m : ℚ)) →
      ∀ m : ℕ, Set.Finite {x : Fin n → ℤ | (Q) (fun k => (x k : ℚ)) = (m : ℚ)} ∧
        PowerSeries.coeff m
          (PowerSeries.mk (fun m : ℕ =>
            (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ) =
          (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ) := by
  intro n Q hQ hnat m
  refine ⟨ArithmeticThetaLattice.exact_shell_finite n Q hQ (m : ℚ), ?_⟩
  rw [PowerSeries.coeff_mk]

theorem complex_coefficients :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      (∀ x : Fin n → ℤ, ∃ m : ℕ, (Q) (fun k => (x k : ℚ)) = (m : ℚ)) →
      ∀ m : ℕ, PowerSeries.coeff m
        (PowerSeries.map (Int.castRingHom ℂ)
          (PowerSeries.mk (fun m : ℕ =>
            (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ)) =
        (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℂ) := by
  intro n Q hQ hnat m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  norm_num

theorem constant_one :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      (∀ x : Fin n → ℤ, ∃ m : ℕ, (Q) (fun k => (x k : ℚ)) = (m : ℚ)) →
      PowerSeries.coeff 0
          (PowerSeries.mk (fun m : ℕ =>
            (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ) = 1 ∧
      PowerSeries.coeff 0
          (PowerSeries.map (Int.castRingHom ℂ)
            (PowerSeries.mk (fun m : ℕ =>
              (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ)) = 1 := by
  intro n Q hQ hnat
  let S : Set (Fin n → ℤ) := {x | Q (fun k => (x k : ℚ)) = (0 : ℚ)}
  have hS : S = ({0} : Set (Fin n → ℤ)) := by
    ext x
    constructor
    · intro hx
      have hxQ : Q (fun k => (x k : ℚ)) = 0 := by simpa [S] using hx
      have hv : (fun k => (x k : ℚ)) = 0 := hQ.anisotropic _ hxQ
      have hx0 : x = 0 := by
        funext k
        have hk : (x k : ℚ) = 0 := by simpa using congrFun hv k
        exact_mod_cast hk
      simpa [hx0]
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      change Q (0 : Fin n → ℚ) = 0
      exact Q.map_zero
  have hcard : Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (0 : ℚ)} = 1 := by
    change Nat.card {x : Fin n → ℤ // x ∈ S} = 1
    rw [hS]
    simp
  constructor
  · rw [PowerSeries.coeff_mk]
    norm_num [hcard]
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    norm_num [hcard]

end ArithmeticThetaCore
