module

public import Mathlib

@[expose] public section

namespace ArithmeticThetaOrthogonalAlgorithm

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

def normSet {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : Finset ℕ :=
  Finset.univ.image (fun p : Fin h × Fin n => naturalNorms (A p.1) p.2)

def commonModulus {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (normSet A).lcm id

def level {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  24 * commonModulus A ^ 2

def normExponent {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (1 + 12 * commonModulus A) ^ 2 - 1

def distinctNormCount {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (normSet A).card

def Invariant {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Prop :=
  k ≤ n ∧ (∀ i j : Fin n, j < i → C i j = 0) ∧
    (∀ i : Fin n, 0 < C i i) ∧
    ∀ i j : Fin n, i.val < k → i ≠ j →
      pairing A (fun a => C a i) (fun a => C a j) = 0

end ArithmeticThetaOrthogonalAlgorithm
