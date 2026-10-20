module

public import Mathlib

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarMain172

/-- Symmetric integral Gram matrix, even diagonal, positive-definite half norm. -/
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef

/-- Full theta series whose coefficients are actual integral lattice shell counts. -/
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))

/-- Complex linear map taking a coefficient vector to its full theta combination. -/
noncomputable def thetaMap {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))

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

def castVec (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℚ) where
  toFun x := fun j => (x j : ℚ)
  map_zero' := by ext j; simp
  map_add' := by intro x y; ext j; simp

def integerVectors (n : ℕ) : AddSubgroup (Fin n → ℚ) := (castVec n).range

def preimageLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    AddSubgroup (Fin n → ℚ) :=
  (integerVectors n).comap (B.map (Int.castRingHom ℚ)).mulVecLin.toAddMonoidHom

def periods {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    AddSubgroup (preimageLattice B) :=
  (integerVectors n).comap (preimageLattice B).subtype

abbrev RationalCosets {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :=
  (preimageLattice B) ⧸ periods B

def cosetClass {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : preimageLattice B) : RationalCosets B := QuotientAddGroup.mk t

def Representatives {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Fin B.det.natAbs → preimageLattice B) : Prop :=
  Function.Bijective (fun i => cosetClass B (t i))

abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
abbrev Cosets {n h : ℕ} (A : Matrices n h) (i : Fin h) :=
  Fin (basisMatrix (A i)).det.natAbs

def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)

def centered (m : ℕ) (a : Fin m) : ℤ :=
  if 2 * a.val < m then (a.val : ℤ) else (a.val : ℤ) - (m : ℤ)

/-- Enumerate the distinct pairs actually used by the chosen preimage cosets. -/
structure Indexing {n h : ℕ} (A : Matrices n h) where
  representatives : (i : Fin h) → Cosets A i → preimageLattice (basisMatrix (A i))
  residue : (i : Fin h) → Cosets A i → (j : Fin n) → Fin (naturalNorms (A i) j)
  count : ℕ
  pair : Fin count → ℕ × ℤ
  index : (i : Fin h) → Cosets A i → Fin n → Fin count

def Indexed {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
  (∀ i, Representatives (basisMatrix (A i)) (U.representatives i)) ∧
  (∀ i a j, ∃ z : ℤ,
    (naturalNorms (A i) j : ℚ) * (U.representatives i a).val j =
      ((U.residue i a j).val : ℚ) + (naturalNorms (A i) j : ℚ) * (z : ℚ)) ∧
  Function.Injective U.pair ∧
  (∀ i a j, U.pair (U.index i a j) =
    (naturalNorms (A i) j, centered (naturalNorms (A i) j) (U.residue i a j))) ∧
  (∀ z : Fin U.count, ∃ i a j, U.index i a j = z)

/-- The displayed product I(L), not an assumed group-cardinality identity. -/
def levelIndex (L : ℕ) : ℚ :=
  (L : ℚ)^3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹^2)

def level (N : ℕ) : ℕ := 24 * N^2

def exponent (N : ℕ) : ℕ := (1 + 12 * N)^2 - 1

/-- The integer cutoff; its exact rational product formula is a conclusion. -/
def cutoff {n h : ℕ} (A : Matrices n h) (U : Indexing A) : ℕ :=
  n * (exponent (commonN A))^U.count *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) / 48

/-- Actual integer-shell counts, cast to Q; rows include both 0 and B. -/
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)


end ArithmeticThetaPalomarMain172
