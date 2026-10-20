module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarFoundations269Orthogonal


def pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j

def project {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => pairing A b b * v i - pairing A b v * b i

def step {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun i j => if k < j then project A (fun a => C a k) (fun a => C a j) i
    else C i j)

def runPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).take k).foldl (step A) 1

def basisMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := runPrefix A n

def norms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  pairing A (fun i => basisMatrix A i j) (fun i => basisMatrix A i j)

def naturalNorms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
  (norms A j).toNat

def indexValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (basisMatrix A).det.natAbs


/-- Independent exact target: accepted-003. -/
theorem even_integral_gram_orthogonalization :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → ∃ (B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ), B.det ≠ 0 ∧ (∀ i, 0 < m i ∧ Even (m i)) ∧ B.transpose * A * B = Matrix.diagonal m := by
  sorry

/-- Independent exact target: accepted-008. -/
theorem computed_natural_data :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → (∀ i, 0 < (naturalNorms A) i ∧ Even ((naturalNorms A) i) ∧ ((naturalNorms A) i : ℤ) = (norms A) i) ∧ indexValue A = ∏ i : Fin n, ((basisMatrix A) i i).toNat ∧ 0 < indexValue A := by
  sorry

/-- Independent exact target: support-computed-orthogonalization. -/
theorem computed_orthogonalization :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → 0 < (basisMatrix A).det ∧ (∀ i, 0 < norms A i ∧ Even (norms A i)) ∧ (basisMatrix A).transpose * A * basisMatrix A = Matrix.diagonal (norms A) := by
  sorry

end ArithmeticThetaPalomarFoundations269Orthogonal
