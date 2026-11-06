import Mathlib

namespace ArithmeticThetaRank16

def latticeBasis (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if j.val = 0 then 1/2
  else if j.val = n-1 then (if i.val = n-1 then 2 else 0)
  else if i = j then 1 else if i.val = n-1 then -1 else 0

def doubledBasis (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if j.val = 0 then 1
  else if j.val = n-1 then (if i.val = n-1 then 4 else 0)
  else if i = j then 2 else if i.val = n-1 then -2 else 0

def latticeGram (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.val = 0 then
    (if j.val = 0 then (n/4 : ℕ) else if j.val = n-1 then 1 else 0)
  else if j.val = 0 then (if i.val = n-1 then 1 else 0)
  else if i.val = n-1 then (if j.val = n-1 then 4 else -2)
  else if j.val = n-1 then -2
  else if i = j then 2 else 1

def sumBasis : Matrix (Fin 16) (Fin 16) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (latticeBasis 8) 0 0 (latticeBasis 8))

def sumGram : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (latticeGram 8) 0 0 (latticeGram 8))

def originalDPlus (n : ℕ) (v : Fin n → ℚ) : Prop :=
  (∃ x : Fin n → ℤ, (∑ i, x i) % 2 = 0 ∧ ∀ i, v i = x i) ∨
  (∃ x : Fin n → ℤ, (∑ i, x i) % 2 = 0 ∧ ∀ i, v i = x i + 1/2)

def doubledRealization (n : ℕ) (y : Fin n → ℤ) : Fin n → ℚ :=
  fun i => (y i : ℚ)/2

def basisCoordinates (n : ℕ) (y : Fin n → ℤ) : Fin n → ℤ := fun j =>
  if hj : j.val = 0 then y j
  else if j.val = n-1 then
    ((∑ i, y i) - (n : ℤ) * y ⟨0, by omega⟩) / 4
  else (y j - y ⟨0, by omega⟩) / 2

end ArithmeticThetaRank16
