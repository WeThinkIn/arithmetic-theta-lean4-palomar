import OrthogonalAlgorithm

namespace ArithmeticThetaOrthogonalAlgorithm

lemma pairing_gram {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (C.transpose * A * C) i j = pairing A (fun a => C a i) (fun a => C a j) := by
  simp only [pairing, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma pairing_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (pairing A x x : ℚ) / 2 := by
  change (1 / 2 : ℚ) * (A.map (Int.castRingHom ℚ)).toBilin'
    (fun i => (x i : ℚ)) (fun i => (x i : ℚ)) = _
  rw [Matrix.toBilin'_apply]
  simp [pairing, Int.cast_sum, Int.cast_mul, div_eq_mul_inv, mul_comm]

lemma pairing_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hs : A.IsSymm)
    (x y : Fin n → ℤ) : pairing A x y = pairing A y x := by
  unfold pairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs.apply j i]
  ring

theorem pairing_identities (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    (∀ (C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n),
      (C.transpose * A * C) i j = pairing A (fun a => C a i) (fun a => C a j)) ∧
    (∀ x : Fin n → ℤ, ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (pairing A x x : ℚ) / 2) ∧
    (A.IsSymm → ∀ x y : Fin n → ℤ, pairing A x y = pairing A y x) :=
  ⟨pairing_gram A, pairing_quadratic A, pairing_symm A⟩

lemma pairing_combination {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x y z : Fin n → ℤ) (s t : ℤ) :
    pairing A x (fun i => s * y i - t * z i) = s * pairing A x y - t * pairing A x z := by
  simp only [pairing, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem projection_identities (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (b v z : Fin n → ℤ) :
    pairing A z (project A b v) = pairing A b b * pairing A z v - pairing A b v * pairing A z b ∧
    pairing A b (project A b v) = 0 := by
  constructor
  · exact pairing_combination A z v b _ _
  · rw [show project A b v = (fun i => pairing A b b * v i - pairing A b v * b i) from rfl,
      pairing_combination]
    ring

-- Proof adapted verbatim from the accepted batch-2 general parity lemma:
-- workspace/deliveries/arithmetic-theta-foundations-1/Lean/IntegralGramOrthogonalization.lean:43
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

lemma pairing_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (x : Fin n → ℤ) (hx : x ≠ 0) : 0 < pairing A x x := by
  have hcast : (fun i => (x i : ℚ)) ≠ 0 := by
    intro h
    apply hx
    ext i
    have hi := congrFun h i
    change (x i : ℚ) = 0 at hi
    change x i = 0
    exact_mod_cast hi
  have h := hp _ hcast
  rw [(pairing_identities n A).2.1 x] at h
  have hq : (0 : ℚ) < (pairing A x x : ℚ) := by linarith
  exact_mod_cast hq

theorem positive_even_pairing (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (he : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    (∀ x : Fin n → ℤ, x ≠ 0 → 0 < pairing A x x) ∧
    (∀ x : Fin n → ℤ, Even (pairing A x x)) := by
  refine ⟨pairing_positive A hp, ?_⟩
  intro x
  unfold pairing
  apply even_symmetric_sum
  · intro i j
    rw [hs.apply i j]
    ring
  · intro i
    exact ((he i).mul_left (x i)).mul_right (x i)

end ArithmeticThetaOrthogonalAlgorithm
