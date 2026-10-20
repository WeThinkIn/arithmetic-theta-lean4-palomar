module
public import Mathlib
public import RationalPreimageCosetsR0127
public import UnaryParameterIdentificationR0127
public import IndividualCosetIntegralProductR0127
public import SourceOrthogonalFactorizationR0127
public import ComputedFamilyFormalUnaryConsumerR0127

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarOrthogonal254


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

def unary (k : Type u) [Field k] (m : ℕ) (ν : Fin m) : PowerSeries k :=
  PowerSeries.mk fun n => (Nat.card {r : ℤ // Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2 = (n : ℤ)} : k)


/-- Exact independent target for accepted-023. -/
theorem rational_preimage_cosets :
  ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 → ∃ E : RationalCosets B ≃+ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)), (∀ (t : preimageLattice B) (x : Fin n → ℤ), (B.map (Int.castRingHom ℚ)).mulVec t.val = castVec n x → E (cosetClass B t) = (LinearMap.range (Matrix.mulVecLin B)).mkQ x) ∧ Finite (RationalCosets B) ∧ Nat.card (RationalCosets B) = B.det.natAbs ∧ ∃ t : Fin B.det.natAbs → preimageLattice B, Representatives B t := by
  exact ArithmeticThetaOrthogonalConsumerR0127.rational_preimage_cosets

/-- Exact independent target for accepted-024. -/
theorem unary_parameter_identification :
  ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (w : ℕ) (hw : w ≠ 0) (ν : ℤ) (a : Fin m), Int.ModEq (m : ℤ) ν (a.val : ℤ) → PowerSeries.map (Int.castRingHom k) (scaledUnary m w ν) = PowerSeries.expand w hw (unary k m a) := by
  exact ArithmeticThetaOrthogonalConsumerR0127.unary_parameter_identification

/-- Exact independent target for accepted-025. -/
theorem individual_coset_integral_product :
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), validGram A → OrthogonalData A B m → ∀ (t : preimageLattice B) (ν : Fin n → ℤ), (∀ j, (ν j : ℚ) = (m j : ℚ) * t.val j) → (∀ r : Fin n → ℤ, (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) → ∃ a : ℕ, (∑ j : Fin n, (r j : ℚ)^2 / (2 * (m j : ℚ))) = (a : ℚ)) ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (cosetSeries m t.val) = ∏ j : Fin n, scaledUnary (m j) (D / (2 * m j)) (ν j)) := by
  exact ArithmeticThetaOrthogonalConsumerR0127.individual_coset_integral_product

/-- Exact independent target for accepted-026. -/
theorem source_orthogonal_factorization :
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), validGram A → OrthogonalData A B m → ∀ t : Fin B.det.natAbs → preimageLattice B, Representatives B t → ∃ ν : Fin B.det.natAbs → Fin n → ℤ, (∀ i j, (ν i j : ℚ) = (m j : ℚ) * (t i).val j) ∧ thetaZ A = ∑ i : Fin B.det.natAbs, cosetSeries m (t i).val ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (thetaZ A) = ∑ i : Fin B.det.natAbs, ∏ j : Fin n, scaledUnary (m j) (D / (2 * m j)) (ν i j)) := by
  exact ArithmeticThetaOrthogonalConsumerR0127.source_orthogonal_factorization

/-- Exact independent target for accepted-027. -/
theorem computed_family_formal_unary_consumer :
  ∀ (n h : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, validGram (A i)) → ∀ (D : ℕ) (hD : D ≠ 0), (∀ (i : Fin h) (j : Fin n), 2 * (naturalNorms (A i) j) ∣ D) → ∃ (t : (i : Fin h) → Fin (basisMatrix (A i)).det.natAbs → preimageLattice (basisMatrix (A i))) (ν : (i : Fin h) → Fin (basisMatrix (A i)).det.natAbs → (j : Fin n) → Fin (naturalNorms (A i) j)) (hw : ∀ (i : Fin h) (j : Fin n), D / (2 * (naturalNorms (A i) j)) ≠ 0), (∀ i, Representatives (basisMatrix (A i)) (t i)) ∧ (∀ (i : Fin h) (a : Fin (basisMatrix (A i)).det.natAbs) (j : Fin n), ∃ z : ℤ, ((naturalNorms (A i) j) : ℚ) * (t i a).val j = ((ν i a j).val : ℚ) + ((naturalNorms (A i) j) : ℚ) * (z : ℚ)) ∧ (∀ c : Fin h → ℂ, PowerSeries.expand D hD (thetaMap A c) = ∑ i : Fin h, c i • (∑ a : Fin (basisMatrix (A i)).det.natAbs, ∏ j : Fin n, PowerSeries.expand (D / (2 * (naturalNorms (A i) j))) (hw i j) (unary ℂ (naturalNorms (A i) j) (ν i a j)))) := by
  exact ArithmeticThetaOrthogonalConsumerR0127.computed_family_formal_unary_consumer

end ArithmeticThetaPalomarOrthogonal254
#print axioms ArithmeticThetaPalomarOrthogonal254.rational_preimage_cosets
#print axioms ArithmeticThetaPalomarOrthogonal254.unary_parameter_identification
#print axioms ArithmeticThetaPalomarOrthogonal254.individual_coset_integral_product
#print axioms ArithmeticThetaPalomarOrthogonal254.source_orthogonal_factorization
#print axioms ArithmeticThetaPalomarOrthogonal254.computed_family_formal_unary_consumer
