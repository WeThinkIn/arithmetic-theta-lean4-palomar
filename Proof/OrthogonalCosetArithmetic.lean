module

public import IntegralGramOrthogonalization

@[expose] public section

open scoped BigOperators
namespace ArithmeticThetaCosets

private lemma cast_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (fun j => ((A.mulVec x) j : ℚ)) =
      (A.map (Int.castRingHom ℚ)).mulVec (fun j => (x j : ℚ)) := by
  ext j
  simp [Matrix.mulVec, dotProduct]

private lemma rational_gram {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℕ) (h : B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ))) :
    (B.map (Int.castRingHom ℚ)).transpose * A.map (Int.castRingHom ℚ) *
      B.map (Int.castRingHom ℚ) = Matrix.diagonal (fun j => (m j : ℚ)) := by
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map (Int.castRingHom ℚ)) h
  rw [Matrix.map_mul, Matrix.map_mul] at hh
  have ht : B.transpose.map (Int.castRingHom ℚ) =
      (B.map (Int.castRingHom ℚ)).transpose := rfl
  rw [ht] at hh
  simpa using hh

private lemma rational_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (h : B.det ≠ 0) :
    IsUnit (B.map (Int.castRingHom ℚ)).det := by
  apply isUnit_iff_ne_zero.mpr
  change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
  rw [← RingHom.map_det]
  change (B.det : ℚ) ≠ 0
  exact_mod_cast h

private lemma quadratic_change {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (m : Fin n → ℚ) (h : B.transpose * A * B = Matrix.diagonal m) (y : Fin n → ℚ) :
    ((1 / 2 : ℚ) • A.toQuadraticForm') (B.mulVec y) =
      ∑ j, (1 / 2 : ℚ) * (y j * (m j * y j)) := by
  change (1 / 2 : ℚ) * A.toBilin' (B.mulVec y) (B.mulVec y) = _
  rw [Matrix.toBilin'_apply']
  have he : dotProduct (B.mulVec y) (A.mulVec (B.mulVec y)) =
      dotProduct y ((B.transpose * A * B).mulVec y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [he, h]
  simp [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]

theorem orthogonal_residue_formula : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), A.IsSymm → B.det ≠ 0 → (∀ j, 0 < m j) → B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ)) → ∀ v k : (Fin n → ℤ), (∀ j : Fin n, (((B.transpose * A).mulVec v) j : ℚ) = (m j : ℚ) * (((B.map (Int.castRingHom ℚ))⁻¹).mulVec (fun l => (v l : ℚ))) j) ∧ ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') (fun j => ((v + B.mulVec k) j : ℚ)) = ∑ j : Fin n, (((((B.transpose * A).mulVec v) j + (m j : ℤ) * k j : ℤ) : ℚ) ^ 2) / (2 * (m j : ℚ)) := by
  intro n A B m _hsym hdet hm hgram v k
  let C := B.map (Int.castRingHom ℚ)
  let M := A.map (Int.castRingHom ℚ)
  let w : Fin n → ℚ := fun j => (v j : ℚ)
  let y := C⁻¹.mulVec w
  have hC : IsUnit C.det := rational_det B hdet
  have hCy : C.mulVec y = w := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
  have hg : C.transpose * M * C = Matrix.diagonal (fun j => (m j : ℚ)) :=
    rational_gram A B m hgram
  have hnu : (fun j => (((B.transpose * A).mulVec v) j : ℚ)) =
      fun j => (m j : ℚ) * y j := by
    rw [cast_mulVec]
    have hmap : (B.transpose * A).map (Int.castRingHom ℚ) = C.transpose * M := by
      rw [Matrix.map_mul]
      rfl
    rw [hmap]
    change (C.transpose * M).mulVec w = _
    rw [← hCy, Matrix.mulVec_mulVec, hg]
    ext j
    simp [Matrix.mulVec_diagonal]
  refine ⟨fun j => congrFun hnu j, ?_⟩
  have hx : (fun j => ((v + B.mulVec k) j : ℚ)) =
      C.mulVec (y + fun j => (k j : ℚ)) := by
    rw [Matrix.mulVec_add, hCy]
    have hc := cast_mulVec B k
    ext j
    simp only [Pi.add_apply, Int.cast_add]
    exact congrArg ((v j : ℚ) + ·) (congrFun hc j)
  rw [hx, quadratic_change M C _ hg]
  apply Finset.sum_congr rfl
  intro j _
  have hmj : (m j : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hm j))
  simp only [Pi.add_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [congrFun hnu j]
  field_simp [hmj]

/-- Parity of a symmetric even integral Gram matrix gives integral half-norms. -/
private lemma natural_half_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsym : A.IsSymm) (heven : ∀ j, Even (A j j))
    (hpos : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (x : Fin n → ℤ) :
    ∃ a : ℕ, ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a : ℚ) := by
  have he : Even (∑ i, ∑ j, x i * A i j * x j) := by
    apply ArithmeticThetaLattice.even_symmetric_sum
    · intro i j
      rw [hsym.apply i j]
      ring
    · intro i
      exact ((heven i).mul_left (x i)).mul_right (x i)
  obtain ⟨z, hz⟩ := he
  have hq : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (z : ℚ) := by
    change (1 / 2 : ℚ) * (A.map (Int.castRingHom ℚ)).toBilin'
      (fun j => (x j : ℚ)) (fun j => (x j : ℚ)) = _
    rw [Matrix.toBilin'_apply]
    have hzq : (∑ i, ∑ j, (x i : ℚ) * (A i j : ℚ) * (x j : ℚ)) =
        (z : ℚ) + z := by exact_mod_cast hz
    simpa only [Matrix.map_apply, Int.coe_castRingHom] using
      (show (1 / 2 : ℚ) * (∑ i, ∑ j, (x i : ℚ) * (A i j : ℚ) * (x j : ℚ)) = z by
        rw [hzq]; ring)
  have hzpos : 0 ≤ z := by
    have hh := hpos.nonneg (fun j => (x j : ℚ))
    rw [hq] at hh
    exact_mod_cast hh
  refine ⟨z.toNat, ?_⟩
  rw [hq]
  exact_mod_cast (Int.toNat_of_nonneg hzpos).symm

theorem total_exponent_integrality : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), A.IsSymm → (∀ j, Even (A j j)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → B.det ≠ 0 → (∀ j, 0 < m j ∧ Even (m j)) → B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ)) → ∀ v r : (Fin n → ℤ), (∀ j : Fin n, Int.ModEq (m j : ℤ) (r j) (((B.transpose * A).mulVec v) j)) → ∃ a : ℕ, (∑ j : Fin n, (r j : ℚ) ^ 2 / (2 * (m j : ℚ))) = (a : ℚ) := by
  intro n A B m hsym heven hpos hdet hm hgram v r hres
  have hk : ∀ j, ∃ k : ℤ, r j - ((B.transpose * A).mulVec v) j = (m j : ℤ) * k := by
    intro j
    exact (hres j).symm.dvd
  choose k hk using hk
  have hr : ∀ j, ((B.transpose * A).mulVec v) j + (m j : ℤ) * k j = r j := by
    intro j
    rw [← hk j]
    ring
  obtain ⟨a, ha⟩ := natural_half_norm A hsym heven hpos (v + B.mulVec k)
  refine ⟨a, ?_⟩
  have hformula := (orthogonal_residue_formula n A B m hsym hdet
    (fun j => (hm j).1) hgram v k).2
  rw [hformula] at ha
  simpa only [hr] using ha

end ArithmeticThetaCosets
