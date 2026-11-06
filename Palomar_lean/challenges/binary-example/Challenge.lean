module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarExamples258Binary

def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef


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

def OrthogonalData {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℕ) : Prop :=
  B.det ≠ 0 ∧ (∀ j, 0 < m j ∧ Even (m j)) ∧
    B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ))

def thetaZ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (castVec n x) = (a : ℚ)} : ℤ)

def cosetSeries {n : ℕ} (m : Fin n → ℕ) (t : Fin n → ℚ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {x : Fin n → ℤ //
    (∑ j, (m j : ℚ) / 2 * (t j + (x j : ℚ))^2) = (a : ℚ)} : ℤ)

def scaledUnary (m w : ℕ) (ν : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {r : ℤ //
    Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r^2 = (a : ℤ)} : ℤ)


def binaryGram : Matrix (Fin 2) (Fin 2) ℤ := ![![2, 1], ![1, 12]]
def binaryBasis : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![0, 2]]
def binaryNorms : Fin 2 → ℕ := ![2, 46]
def binaryRepresentatives : Fin 2 → Fin 2 → ℚ := ![![0, 0], ![1/2, 1/2]]
def binaryResidues : Fin 2 → Fin 2 → ℤ := ![![0, 0], ![1, 23]]


/-- Independent exact target: binary-orthogonal-example. -/
theorem binary_orthogonal_example :
  validGram binaryGram ∧ binaryBasis.det = 2 ∧ OrthogonalData binaryGram binaryBasis binaryNorms ∧ ∃ t : Fin 2 → preimageLattice binaryBasis, (∀ i, (t i).val = binaryRepresentatives i) ∧ Function.Bijective (fun i => cosetClass binaryBasis (t i)) ∧ (∀ i j, ((binaryResidues i j : ℤ) : ℚ) = (binaryNorms j : ℚ) * (t i).val j) ∧ thetaZ binaryGram = cosetSeries binaryNorms (binaryRepresentatives 0) + cosetSeries binaryNorms (binaryRepresentatives 1) ∧ (∀ (D : ℕ) (hD : D ≠ 0), 92 ∣ D → PowerSeries.expand D hD (thetaZ binaryGram) = scaledUnary 2 (D / 4) 0 * scaledUnary 46 (D / 92) 0 + scaledUnary 2 (D / 4) 1 * scaledUnary 46 (D / 92) 23) := by
  sorry

end ArithmeticThetaPalomarExamples258Binary
