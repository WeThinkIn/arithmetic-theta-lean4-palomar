module

public import ThetaSeriesConstruction

@[expose] public section

open scoped BigOperators Matrix

namespace ArithmeticThetaCore

theorem norm_preserving_equivalence :
    ∀ (n r : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)) (R : QuadraticForm ℚ (Fin r → ℚ)), Q.PosDef →
      R.PosDef → (∀ x : Fin n → ℤ, ∃ m : ℕ, (Q) (fun k => (x k : ℚ)) = (m : ℚ)) → (∀ x : Fin r → ℤ,
      ∃ m : ℕ, (R) (fun k => (x k : ℚ)) = (m : ℚ)) → ∀ e : (Fin n → ℤ) ≃ (Fin r → ℤ), (∀ x : Fin n →
      ℤ, (R) (fun k => ((e x) k : ℚ)) = (Q) (fun k => (x k : ℚ))) → (PowerSeries.mk (fun m : ℕ =>
      (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ) =
      (PowerSeries.mk (fun m : ℕ => (Nat.card {x : Fin r → ℤ // (R) (fun k => (x k : ℚ)) = (m : ℚ)}
      : ℤ)) : PowerSeries ℤ) ∧ (PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk (fun m : ℕ =>
      (Nat.card {x : Fin n → ℤ // (Q) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ)) =
      (PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk (fun m : ℕ => (Nat.card {x : Fin r → ℤ //
      (R) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ)) := by
  intro n r Q R hQ hR hnatQ hnatR e he
  have hcard (m : ℕ) :
      Nat.card {x : Fin n → ℤ // Q (fun k => (x k : ℚ)) = (m : ℚ)} =
      Nat.card {y : Fin r → ℤ // R (fun k => (y k : ℚ)) = (m : ℚ)} := by
    have hfinQ := (finite_integer_coefficients n Q hQ hnatQ m).1
    have hfinR := (finite_integer_coefficients r R hR hnatR m).1
    let : Fintype {x : Fin n → ℤ // Q (fun k => (x k : ℚ)) = (m : ℚ)} := hfinQ.fintype
    let : Fintype {y : Fin r → ℤ // R (fun k => (y k : ℚ)) = (m : ℚ)} := hfinR.fintype
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    exact
      { toFun := fun x => ⟨e x, (he x).trans x.property⟩
        invFun := fun y => ⟨e.symm y, by rw [← he, e.apply_symm_apply]; exact y.property⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
        right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  have hz :
      (PowerSeries.mk (fun m : ℕ =>
        (Nat.card {x : Fin n → ℤ // Q (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ) =
      PowerSeries.mk (fun m : ℕ =>
        (Nat.card {x : Fin r → ℤ // R (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) := by
    ext m
    simpa only [PowerSeries.coeff_mk] using congrArg (fun a : ℕ => (a : ℤ)) (hcard m)
  refine ⟨hz, ?_⟩
  ext m
  rw [complex_coefficients n Q hQ hnatQ, complex_coefficients r R hR hnatR, hcard]

private lemma gram_eval_dot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm'))
      (fun k => (x k : ℚ)) =
      (1 / 2 : ℚ) * ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
  rw [gram_eval]
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem integral_basis_change :
    ∀ (n : ℕ) (A A' P : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → A'.IsSymm → (∀ i, Even (A i i)) →
      (∀ i, Even (A' i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef →
      ((1 / 2 : ℚ) • (A'.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → IsUnit P.det →
      P.transpose * A * P = A' → (PowerSeries.mk (fun m : ℕ => (Nat.card {x : Fin n → ℤ // (((1 / 2
      : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) :
      PowerSeries ℤ) = (PowerSeries.mk (fun m : ℕ => (Nat.card {x : Fin n → ℤ // (((1 / 2 : ℚ) •
      (A'.map (Int.castRingHom ℚ)).toQuadraticForm')) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) :
      PowerSeries ℤ) ∧ (PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk (fun m : ℕ => (Nat.card
      {x : Fin n → ℤ // (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')) (fun k => (x
      k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries ℤ)) = (PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.mk (fun m : ℕ => (Nat.card {x : Fin n → ℤ // (((1 / 2 : ℚ) • (A'.map
      (Int.castRingHom ℚ)).toQuadraticForm')) (fun k => (x k : ℚ)) = (m : ℚ)} : ℤ)) : PowerSeries
      ℤ)) := by
  intro n A A' P hsym hsym' heven heven' hpos hpos' hunit hconj
  let e : (Fin n → ℤ) ≃ (Fin n → ℤ) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => P⁻¹ *ᵥ x
      left_inv := fun x => by
        change P⁻¹ *ᵥ (P *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hunit, Matrix.one_mulVec]
      right_inv := fun x => by
        change P *ᵥ (P⁻¹ *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hunit, Matrix.one_mulVec] }
  have hn (x : Fin n → ℤ) :
      (((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm'))
          (fun k => ((e x) k : ℚ)) =
      (((1 / 2 : ℚ) • (A'.map (Int.castRingHom ℚ)).toQuadraticForm'))
          (fun k => (x k : ℚ)) := by
    rw [gram_eval_dot, gram_eval_dot]
    change (1 / 2 : ℚ) * (((P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) : ℤ) : ℚ) = _
    have hid : (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) = x ⬝ᵥ (A' *ᵥ x) := by
      rw [← hconj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec x P.transpose, Matrix.vecMul_transpose]
    rw [hid]
  have h := norm_preserving_equivalence n n
    ((1 / 2 : ℚ) • (A'.map (Int.castRingHom ℚ)).toQuadraticForm')
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
    hpos' hpos
    (even_gram_natural_values n A' hsym' heven' hpos')
    (even_gram_natural_values n A hsym heven hpos) e hn
  exact ⟨h.1.symm, h.2.symm⟩

end ArithmeticThetaCore
