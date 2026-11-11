import OrthogonalAlgorithm

/-!
# Arithmetic parameters used by the review statements

This interface has no geometric input. The diagonal norms are the actual output
of the original integral orthogonalization algorithm. The bridge theorems in
`ReviewArithmeticBridges` identify these parameters with both historical APIs.

The sharp cutoff below is a natural quotient, hence an exact nonnegative floor.
It is not the different conservative cutoff appearing in the original theorem.
-/
set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaReview.Arithmetic

/-- A finite family of integral Gram matrices of one fixed rank. -/
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ

/-- The distinct diagonal norms produced by integral orthogonalization. -/
def norms {n h : ℕ} (A : Matrices n h) : Finset ℕ :=
  Finset.univ.image (fun ij : Fin h × Fin n =>
    ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A ij.1) ij.2)

/-- Number of distinct norms, denoted by `r` in the sharp bound. -/
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (norms A).card

/-- Their least common multiple, denoted by `N` in the paper. -/
def commonNorm {n h : ℕ} (A : Matrices n h) : ℕ := (norms A).lcm id

/-- The level `L = 24 N²`. -/
def level {n h : ℕ} (A : Matrices n h) : ℕ := 24 * commonNorm A ^ 2

/-- The exponent used in the conservative construction, `K = (1+12N)²−1`. -/
def exponent {n h : ℕ} (A : Matrices n h) : ℕ := (1 + 12 * commonNorm A) ^ 2 - 1

/-- The rational arithmetic formula `I(L) = L³ ∏_{p∣L}(1−p⁻²)`. -/
def index (L : ℕ) : ℚ :=
  (L : ℚ) ^ 3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹ ^ 2)

/-- The exact sharp coefficient bound. Agreement with the rational floor and
the executable bound is proved for valid Gram families in the bridge module. -/
def sharpCutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2 ^ (normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level A))) / (48 * level A)

end ArithmeticThetaReview.Arithmetic
