module

public import RationalOrthogonalBasis
public import MatrixDenominator

@[expose] public section

open scoped BigOperators

namespace ArithmeticThetaLattice

theorem integral_orthogonalization : ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef → ∃ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 ∧ (∀ i j, i ≠ j → QuadraticMap.associated Q (fun k => (B k i : ℚ)) (fun k => (B k j : ℚ)) = 0) ∧ ∀ i, 0 < Q (fun k => (B k i : ℚ)) := by
  intro n Q hQ
  obtain ⟨b, hb, hpos, _⟩ := rational_orthogonal_basis n Q hQ
  let P : Matrix (Fin n) (Fin n) ℚ := fun k i => b i k
  obtain ⟨D, hD, B, hB⟩ := matrix_common_denominator n n P
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hcol (i : Fin n) : (fun k => (B k i : ℚ)) = (D : ℚ) • b i := by
    funext k
    exact hB k i
  have hmap : B.map (Int.castRingHom ℚ) = (D : ℚ) • P := by
    ext k i
    exact hB k i
  have hP : P.det ≠ 0 := by
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det P).mp
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    exact b.linearIndependent
  have hdet : B.det ≠ 0 := by
    intro hz
    have hzq : (B.map (Int.castRingHom ℚ)).det = 0 := by
      change ((Int.castRingHom ℚ).mapMatrix B).det = 0
      rw [← RingHom.map_det, hz]
      rfl
    rw [hmap, Matrix.det_smul] at hzq
    exact (mul_ne_zero (pow_ne_zero _ hDq) hP) hzq
  refine ⟨B, hdet, ?_, ?_⟩
  · intro i j hij
    rw [hcol i, hcol j]
    have hij' : QuadraticMap.associated Q (b i) (b j) = 0 := hb hij
    simp [hij']
  · intro i
    rw [hcol i, QuadraticMap.map_smul]
    simpa [pow_two] using mul_pos (sq_pos_of_ne_zero hDq) (hpos i)

/-- A symmetric finite double sum is even when its diagonal is even. -/
lemma even_symmetric_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ι → ℤ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, Even (f i i)) : Even (∑ i ∈ s, ∑ j ∈ s, f i j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have heq : (∑ i ∈ s, (f i a + ∑ j ∈ s, f i j)) =
        (∑ i ∈ s, f a i) + ∑ i ∈ s, ∑ j ∈ s, f i j := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hs i a)
    rw [heq]
    have htw : Even ((∑ j ∈ s, f a j) + ∑ j ∈ s, f a j) := ⟨_, rfl⟩
    simpa only [add_assoc, add_left_comm, add_comm] using ((hd a).add htw).add ih

lemma gram_entry {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (u v : Fin n) :
    (B.transpose * A * B) u v = ∑ i, ∑ j, B i u * A i j * B j v := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem even_integral_gram_orthogonalization : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → ∃ (B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ), B.det ≠ 0 ∧ (∀ i, 0 < m i ∧ Even (m i)) ∧ B.transpose * A * B = Matrix.diagonal m := by
  intro n A hsym heven hpos
  let M := A.map (Int.castRingHom ℚ)
  let Q : QuadraticForm ℚ (Fin n → ℚ) := (1 / 2 : ℚ) • M.toQuadraticForm'
  obtain ⟨B, hdet, hortho, hnorm⟩ := integral_orthogonalization n Q hpos
  let G := B.transpose * A * B
  let m : Fin n → ℤ := fun i => G i i
  have hsymM : M.toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr (hsym.map _)
  have hassoc : QuadraticMap.associated Q = (1 / 2 : ℚ) • M.toBilin' := by
    change QuadraticMap.associated ((1 / 2 : ℚ) • M.toBilin'.toQuadraticMap) = _
    rw [map_smul]
    congr 1
    exact QuadraticMap.associated_left_inverse ℚ (fun x y => hsymM.eq x y)
  have hentry (i j : Fin n) :
      M.toBilin' (fun k => (B k i : ℚ)) (fun k => (B k j : ℚ)) = (G i j : ℚ) := by
    rw [Matrix.toBilin'_apply]
    dsimp [G]
    rw [gram_entry]
    simp [M, Int.cast_sum, Int.cast_mul]
  have hq (i : Fin n) : Q (fun k => (B k i : ℚ)) = (1 / 2 : ℚ) * (m i : ℚ) := by
    change (1 / 2 : ℚ) * M.toBilin' (fun k => (B k i : ℚ)) (fun k => (B k i : ℚ)) = _
    rw [hentry]
  refine ⟨B, m, hdet, ?_, ?_⟩
  · intro i
    constructor
    · have hp := hnorm i
      rw [hq] at hp
      have hm : (0 : ℚ) < (m i : ℚ) := by linarith
      exact_mod_cast hm
    · change Even ((B.transpose * A * B) i i)
      rw [gram_entry]
      apply even_symmetric_sum
      · intro j k
        rw [hsym.apply j k]
        ring
      · intro j
        exact ((heven j).mul_left (B j i)).mul_right (B j i)
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [m, G]
    · rw [Matrix.diagonal_apply_ne _ hij]
      have ho := hortho i j hij
      rw [hassoc] at ho
      change (1 / 2 : ℚ) * M.toBilin' (fun k => (B k i : ℚ)) (fun k => (B k j : ℚ)) = 0 at ho
      rw [hentry] at ho
      have hz : (G i j : ℚ) = 0 := by linarith
      exact_mod_cast hz

end ArithmeticThetaLattice
