module
public import ActualEarlierCertificate
public import LatticeShellFinite
public import Mathlib
public import RationalPreimageCosetsR0127
public import UnaryParameterIdentificationR0127
public import IndividualCosetIntegralProductR0127
public import SourceOrthogonalFactorizationR0127
public import ComputedFamilyFormalUnaryConsumerR0127
public import ShiftedIntegerIntervalR0229
public import RationalSchurCompletionR0229
public import ComputedRationalLDLR0229
public import RecursiveEllipsoidEnumerationR0229
public import LDLThetaPrefixR0229
public import BinaryOrthogonalExampleR0268
public import Det80CoefficientMinor
public import Det80ThetaIndependence
public import Det80CompleteClassification
public import Det80Similarity
public import Det80LocalRealization
public import Det80OrderClassification
public import Rank16Nonisometry
public import Rank16Theta
public import GeneralDPlusEvenUnimodularR0242
public import GeneralDPlusDualR0242
public import GeneralDPlusThetaRealizationR0242
public import FiniteEtaleNormFamilyR0251
public import FormalJacobiTripleProduct
public import HadamardJacobi
public import TateBasicFourthIdentity
public import TateGeneralAddition
public import LaurentPoweredNormR0064
public import RankZero
public import NormExponentAlgebra
public import IntegralGramOrthogonalization
public import ComputedOrthogonalization
public import OrthogonalConsumerDefinitionsR0127
public import ComputedCoefficientMatrix
public import GlobalizationDefinitions
public import ComputedBoundParameters
public import FiniteFullLevelCount
public import LatticeGlobalSectionsDefinitionsR0188
public import ConservativeMatrixKernelR0189
@[expose] public section
section Package00
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarEarly205
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
/-- Actual integer-shell counts, cast to Q; rows include both 0 and B. -/
def coefficientMatrix {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
/-- The actual shell matrix agrees over Q with the executable enumeration.
This uses enumeration correctness; these definitions are not identified by rfl. -/
lemma coefficientMatrix_eq_computed {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i, validGram (A i)) (B : ℕ) :
    coefficientMatrix A B = ArithmeticThetaComputed.coefficientMatrix A B := by
  ext a i
  have hc := ArithmeticThetaComputed.computed_coefficient_matrix n h B A hA a i
  simp only [ArithmeticThetaComputed.theta, PowerSeries.coeff_mk] at hc
  change (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ) = _
  exact_mod_cast hc.symm
/-- A certificate for actual full theta relations, including zero-sized inputs.
No stabilized rank or unproved geometric cutoff is a sufficient certificate. -/
theorem earlierCertificate (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    LinearMap.ker (thetaMap A) ≤
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin) ∧
    ((coefficientMatrix A B).rank = h → LinearMap.ker (thetaMap A) = ⊥) ∧
    (∀ W : Submodule ℂ (Fin h → ℂ),
      (∀ c ∈ W, thetaMap A c = 0) →
      Module.finrank ℂ W = h - (coefficientMatrix A B).rank →
      W = LinearMap.ker (thetaMap A) ∧
      LinearMap.ker (thetaMap A) =
        LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) := by
  refine ⟨?_, ?_⟩
  · intro i a
    exact (ArithmeticThetaLattice.exact_shell_finite n _ (hA i).2.2 (a : ℚ)).to_subtype
  · rw [coefficientMatrix_eq_computed A hA B]
    exact ArithmeticThetaEarlyAssembly.actual_earlier_certificate n h B A hA
end ArithmeticThetaPalomarEarly205
#print axioms ArithmeticThetaPalomarEarly205.coefficientMatrix_eq_computed
#print axioms ArithmeticThetaPalomarEarly205.earlierCertificate
end
end Package00
section Package01
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
end
end Package01
section Package02
set_option autoImplicit false
namespace ArithmeticThetaPalomarAlgorithm257.Enumeration
def normNumerator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
def coordinateRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (j : Fin n) : ℕ :=
  Nat.sqrt (2 * m * (A.adjugate j j).natAbs / A.det.natAbs)
def integerInterval (R : ℕ) : Finset ℤ :=
  (Finset.range (2 * R + 1)).image (fun k : ℕ => (k : ℤ) - (R : ℤ))
def searchBox {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun j => integerInterval (coordinateRadius A m j))
def shellVectors {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : Finset (Fin n → ℤ) :=
  (searchBox A m).filter (fun x => normNumerator A x = 2 * (m : ℤ))
def representationCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : ℕ :=
  (shellVectors A m).card
def coefficientsUpTo {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : List ℕ :=
  let box := searchBox A B
  List.ofFn (fun m : Fin (B + 1) =>
    (box.filter (fun x => normNumerator A x = 2 * (m.val : ℤ))).card)
end ArithmeticThetaPalomarAlgorithm257.Enumeration
namespace ArithmeticThetaPalomarAlgorithm257.Elimination
def findPivot {m h : ℕ} (M : Matrix (Fin m) (Fin h) ℚ) (r : ℕ) (c : Fin h) :
    Option (Fin m) :=
  (List.finRange m).find? (fun i => r ≤ i.val && M i c != 0)
def swapRows {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) :
    Matrix (Fin m) (Fin k) ℚ :=
  Matrix.of (fun i j => if i = r then M s j else if i = s then M r j else M i j)
def pivotOperation {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
    (N : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) (c : Fin h) :
    Matrix (Fin m) (Fin k) ℚ :=
  let S := swapRows M r s
  let T := swapRows N r s
  Matrix.of (fun i j => if i = r then T r j / S r c
    else T i j - S i c * (T r j / S r c))
structure State (m h : ℕ) where
  reduced : Matrix (Fin m) (Fin h) ℚ
  transform : Matrix (Fin m) (Fin m) ℚ
  nextRow : ℕ
  pivots : List (Fin m × Fin h)
def initial {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) : State m h :=
  ⟨A, 1, 0, []⟩
def step {m h : ℕ} (s : State m h) (c : Fin h) : State m h :=
  if hr : s.nextRow < m then
    match findPivot s.reduced s.nextRow c with
    | none => s
    | some t =>
      { reduced := pivotOperation s.reduced s.reduced ⟨s.nextRow, hr⟩ t c
        transform := pivotOperation s.reduced s.transform ⟨s.nextRow, hr⟩ t c
        nextRow := s.nextRow + 1
        pivots := s.pivots ++ [(⟨s.nextRow, hr⟩, c)] }
  else s
def run {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) : State m h :=
  (List.finRange h).foldl step (initial A)
def pivotMap {m h : ℕ} (s : State m h) (i : Fin m) : WithTop (Fin h) :=
  match s.pivots.find? (fun p => p.1 == i) with
  | none => ⊤
  | some p => p.2
def pivotRow {m h : ℕ} (s : State m h) (j : Fin h) : Option (Fin m) :=
  (s.pivots.find? (fun p => p.2 == j)).map Prod.fst
def pivotColumns {m h : ℕ} (s : State m h) : List (Fin h) :=
  s.pivots.map Prod.snd
def freeColumns {m h : ℕ} (s : State m h) : List (Fin h) :=
  (List.finRange h).filter (fun j => !(pivotColumns s).contains j)
def nullVector {m h : ℕ} (s : State m h) (f : Fin h) (j : Fin h) : ℚ :=
  if j = f then 1 else
    match pivotRow s j with
    | none => 0
    | some i => -s.reduced i f
def nullBasis {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Fin (freeColumns (run A)).length → (Fin h → ℚ) :=
  fun f => nullVector (run A) ((freeColumns (run A)).get f)
def pivotColumn {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Fin (run A).pivots.length → (Fin m → ℚ) :=
  fun t i => A i (((run A).pivots.get t).2)
def columnCoordinates {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (j : Fin h) :
    Fin (run A).pivots.length → ℚ :=
  fun t => (run A).reduced (((run A).pivots.get t).1) j
end ArithmeticThetaPalomarAlgorithm257.Elimination
namespace ArithmeticThetaPalomarAlgorithm257.Computed
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
def coefficientMatrix {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ)
    (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((ArithmeticThetaPalomarAlgorithm257.Enumeration.coefficientsUpTo (A i) B).getD a.val 0 : ℚ)
noncomputable def thetaMap {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
noncomputable def prefixMap (B : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin (B+1) → ℂ) :=
  LinearMap.pi (fun a => PowerSeries.coeff a.val)
def selectedIndex {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (t : Fin (ArithmeticThetaPalomarAlgorithm257.Elimination.run (coefficientMatrix A B)).pivots.length) : Fin h :=
  ((ArithmeticThetaPalomarAlgorithm257.Elimination.run (coefficientMatrix A B)).pivots.get t).2
end ArithmeticThetaPalomarAlgorithm257.Computed
namespace ArithmeticThetaPalomarAlgorithm257.LDL
abbrev QMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
def energy {n : ℕ} (A : QMatrix n) (x : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * A i j * x j
def schur {n : ℕ} (A : QMatrix (n+1)) : QMatrix n :=
  fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
def shift {n : ℕ} (A : QMatrix (n+1)) (y : Fin n → ℤ) : ℚ :=
  -(∑ j, A 0 j.succ * (y j : ℚ)) / A 0 0
def remainder {n : ℕ} (A : QMatrix (n+1)) (B : ℚ) (y : Fin n → ℤ) : ℚ :=
  (B - energy (schur A) (fun i => (y i : ℚ))) / A 0 0
def intervalRadius (c R : ℚ) : ℕ :=
  Nat.sqrt (Int.toNat ⌊R * (c.den : ℚ)^2⌋)
def lowerEndpoint (c R : ℚ) : ℤ :=
  ⌈((c.num : ℚ) - (intervalRadius c R : ℚ)) / (c.den : ℚ)⌉
def upperEndpoint (c R : ℚ) : ℤ :=
  ⌊((c.num : ℚ) + (intervalRadius c R : ℚ)) / (c.den : ℚ)⌋
def shiftedInterval (c R : ℚ) : Finset ℤ :=
  if R < 0 then ∅ else
    (Finset.range (upperEndpoint c R - lowerEndpoint c R + 1).toNat).image
      fun i : ℕ => lowerEndpoint c R + (i : ℤ)
/-- Head-first rational LDL, recorded as A = Uᵀ diag(d) U with U upper unitriangular.
Thus L = Uᵀ is the lower factor in the source's LDLᵀ convention. -/
def ldl : (n : ℕ) → QMatrix n → (Fin n → ℚ) × QMatrix n
  | 0, _ => (Fin.elim0, fun i => Fin.elim0 i)
  | n+1, A =>
    let p := ldl n (schur A)
    (Fin.cons (A 0 0) p.1,
      Fin.cases (Fin.cons 1 (fun j => A 0 j.succ / A 0 0))
        (fun i => Fin.cons 0 (p.2 i)))
/-- Recursion is structurally decreasing in dimension, with a finite exact
integer interval above every tail. No search radius oracle is supplied. -/
def enumerate : (n : ℕ) → QMatrix n → ℚ → Finset (Fin n → ℤ)
  | 0, _, B => if 0 ≤ B then {Fin.elim0} else ∅
  | n+1, A, B =>
    if 0 < A 0 0 then
      (enumerate n (schur A) B).biUnion fun y =>
        (shiftedInterval (shift A y) (remainder A B y)).image fun z => Fin.cons z y
    else ∅
def gramHalf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : QMatrix n :=
  fun i j => (A i j : ℚ) / 2
def shell {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : Finset (Fin n → ℤ) :=
  (enumerate n (gramHalf A) m).filter fun x =>
    ArithmeticThetaPalomarAlgorithm257.Enumeration.normNumerator A x = 2 * (m : ℤ)
def coefficients {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : List ℕ :=
  let vectors := enumerate n (gramHalf A) B
  List.ofFn fun a : Fin (B+1) =>
    (vectors.filter fun x => ArithmeticThetaPalomarAlgorithm257.Enumeration.normNumerator A x = 2 * (a.val : ℤ)).card
def coefficientMatrix {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((coefficients (A i) B).getD a.val 0 : ℚ)
end ArithmeticThetaPalomarAlgorithm257.LDL
namespace ArithmeticThetaPalomarAlgorithm257
private theorem ldl_bridge (n : ℕ) (A : LDL.QMatrix n) :
    LDL.ldl n A = ArithmeticThetaLDLEnumerationR0229.ldl n A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LDL.ldl, ArithmeticThetaLDLEnumerationR0229.ldl, ih]
    rfl
private theorem enumerate_bridge (n : ℕ) (A : LDL.QMatrix n) (B : ℚ) :
    LDL.enumerate n A B = ArithmeticThetaLDLEnumerationR0229.enumerate n A B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LDL.enumerate, ArithmeticThetaLDLEnumerationR0229.enumerate, ih]
    rfl
private theorem shell_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) :
    LDL.shell A m = ArithmeticThetaLDLEnumerationR0229.shell A m := by
  simp only [LDL.shell, ArithmeticThetaLDLEnumerationR0229.shell, enumerate_bridge]
  rfl
private theorem coefficients_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    LDL.coefficients A B = ArithmeticThetaLDLEnumerationR0229.coefficients A B := by
  simp only [LDL.coefficients, ArithmeticThetaLDLEnumerationR0229.coefficients, enumerate_bridge]
  rfl
private theorem coefficientMatrix_bridge {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    LDL.coefficientMatrix A B = ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B := by
  funext a i
  simp only [LDL.coefficientMatrix, ArithmeticThetaLDLEnumerationR0229.coefficientMatrix,
    coefficients_bridge]
/-- Exact scope accepted-058; all hypotheses, dimensions and bounds retained. -/
theorem shifted_integer_interval :
  ∀ (c R : ℚ) (z : ℤ), z ∈ ArithmeticThetaPalomarAlgorithm257.LDL.shiftedInterval c R ↔ ((z : ℚ) - c)^2 ≤ R := by
  exact ArithmeticThetaLDLEnumerationR0229.shifted_integer_interval
/-- Exact scope accepted-059; all hypotheses, dimensions and bounds retained. -/
theorem rational_schur_completion :
  ∀ (n : ℕ) (A : ArithmeticThetaPalomarAlgorithm257.LDL.QMatrix (n+1)), A.IsSymm → A.toQuadraticForm'.PosDef → 0 < A 0 0 ∧ (ArithmeticThetaPalomarAlgorithm257.LDL.schur A).IsSymm ∧ (ArithmeticThetaPalomarAlgorithm257.LDL.schur A).toQuadraticForm'.PosDef ∧ ∀ (z : ℚ) (y : Fin n → ℚ), ArithmeticThetaPalomarAlgorithm257.LDL.energy A (Fin.cons z y) = A 0 0 * (z + (∑ j : Fin n, A 0 j.succ * y j) / A 0 0)^2 + ArithmeticThetaPalomarAlgorithm257.LDL.energy (ArithmeticThetaPalomarAlgorithm257.LDL.schur A) y := by
  exact ArithmeticThetaLDLEnumerationR0229.rational_schur_completion
/-- Exact scope accepted-060; all hypotheses, dimensions and bounds retained. -/
theorem computed_rational_ldl :
  ∀ (n : ℕ) (A : ArithmeticThetaPalomarAlgorithm257.LDL.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → (∀ i : Fin n, 0 < (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).1 i) ∧ (∀ i : Fin n, (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).2 i i = 1) ∧ (∀ i j : Fin n, j < i → (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).2 i j = 0) ∧ A = (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).2.transpose * Matrix.diagonal (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).1 * (ArithmeticThetaPalomarAlgorithm257.LDL.ldl n A).2 := by
  simpa only [ldl_bridge] using ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl
/-- Exact scope accepted-061; all hypotheses, dimensions and bounds retained. -/
theorem recursive_ellipsoid_enumeration :
  ∀ (n : ℕ) (A : ArithmeticThetaPalomarAlgorithm257.LDL.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → ∀ (B : ℚ) (x : Fin n → ℤ), x ∈ ArithmeticThetaPalomarAlgorithm257.LDL.enumerate n A B ↔ ArithmeticThetaPalomarAlgorithm257.LDL.energy A (fun i => (x i : ℚ)) ≤ B := by
  intro n A hs hp B x
  rw [enumerate_bridge]
  exact ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration n A hs hp B x
/-- Exact scope accepted-062; all hypotheses, dimensions and bounds retained. -/
theorem ldl_theta_prefix :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ArithmeticThetaPalomarAlgorithm257.Computed.validGram A → (∀ m : ℕ, ArithmeticThetaPalomarAlgorithm257.LDL.shell A m = ArithmeticThetaPalomarAlgorithm257.Enumeration.shellVectors A m) ∧ ∀ B : ℕ, ArithmeticThetaPalomarAlgorithm257.LDL.coefficients A B = ArithmeticThetaPalomarAlgorithm257.Enumeration.coefficientsUpTo A B ∧ (ArithmeticThetaPalomarAlgorithm257.LDL.coefficients A B).length = B + 1 ∧ ∀ a : Fin (B+1), ((ArithmeticThetaPalomarAlgorithm257.LDL.coefficients A B).getD a.val 0 : ℂ) = PowerSeries.coeff a.val (ArithmeticThetaPalomarAlgorithm257.Computed.theta A) := by
  intro n A hv
  simp only [shell_bridge, coefficients_bridge]
  exact ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix n A hv
/-- Exact scope accepted-063; all hypotheses, dimensions and bounds retained. -/
theorem ldl_coefficient_matrix :
  ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaPalomarAlgorithm257.Computed.validGram (A i)) → ArithmeticThetaPalomarAlgorithm257.LDL.coefficientMatrix A B = ArithmeticThetaPalomarAlgorithm257.Computed.coefficientMatrix A B ∧ ArithmeticThetaPalomarAlgorithm257.Elimination.run (ArithmeticThetaPalomarAlgorithm257.LDL.coefficientMatrix A B) = ArithmeticThetaPalomarAlgorithm257.Elimination.run (ArithmeticThetaPalomarAlgorithm257.Computed.coefficientMatrix A B) ∧ (ArithmeticThetaPalomarAlgorithm257.Computed.prefixMap B).comp (ArithmeticThetaPalomarAlgorithm257.Computed.thetaMap A) = ((ArithmeticThetaPalomarAlgorithm257.LDL.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  intro n h B A hv
  have h := ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix n h B A hv
  rw [coefficientMatrix_bridge]
  exact ⟨h.1, congrArg Elimination.run h.1, h.2.2⟩
end ArithmeticThetaPalomarAlgorithm257
#print axioms ArithmeticThetaPalomarAlgorithm257.shifted_integer_interval
#print axioms ArithmeticThetaPalomarAlgorithm257.rational_schur_completion
#print axioms ArithmeticThetaPalomarAlgorithm257.computed_rational_ldl
#print axioms ArithmeticThetaPalomarAlgorithm257.recursive_ellipsoid_enumeration
#print axioms ArithmeticThetaPalomarAlgorithm257.ldl_theta_prefix
#print axioms ArithmeticThetaPalomarAlgorithm257.ldl_coefficient_matrix
end Package02
section Package03
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
  exact ArithmeticThetaFullSourceR0268.binary_orthogonal_example
end ArithmeticThetaPalomarExamples258Binary
#print axioms ArithmeticThetaPalomarExamples258Binary.binary_orthogonal_example
end
end Package03
section Package04
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarExamples258Det80
def gram (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2*a, b; b, 2*c]
def gramContent (a b c : ℤ) : ℕ := Nat.gcd (Int.gcd (2*a) b) (Int.natAbs (2*c))
def shear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, k; 0, 1]
def forms : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![gram 1 0 20, gram 3 2 7, gram 4 0 5]
def value (j : Fin 3) (x : Fin 2 → ℤ) : ℤ :=
  (![x 0 ^ 2 + 20*x 1 ^ 2, 3*x 0 ^ 2 + 2*x 0*x 1 + 7*x 1 ^ 2,
    4*x 0 ^ 2 + 5*x 1 ^ 2] : Fin 3 → ℤ) j
def embeddings : Fin 3 → Matrix (Fin 2) (Fin 2) ℚ :=
  ![1, !![3, 1; 0, 1], !![2, 0; 0, 1/2]]
def sameLocalSmith (a b c : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ U V : Matrix (Fin 2) (Fin 2) (PadicInt p),
    IsUnit U.det ∧ IsUnit V.det ∧
      U * (gram a b c).map (Int.castRingHom (PadicInt p)) * V =
        (gram 1 0 20).map (Int.castRingHom (PadicInt p))
/-- Independent exact target: accepted-004. -/
theorem actual_coefficient_matrix :
  ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = ![![1, 1, 1], ![2, 0, 0], ![0, 2, 0]] := by
  exact ArithmeticThetaDet80.actual_coefficient_matrix
/-- Independent exact target: accepted-005. -/
theorem actual_minor_determinant :
  Matrix.det ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 4 := by
  exact ArithmeticThetaDet80.actual_minor_determinant
/-- Independent exact target: accepted-006. -/
theorem actual_theta_kernel_zero :
  LinearMap.ker (∑ j : Fin 3, (LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight (PowerSeries.mk (fun m : ℕ => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} : ℂ)) : PowerSeries ℂ)) = ⊥ := by
  exact ArithmeticThetaDet80.actual_theta_kernel_zero
/-- Independent exact target: accepted-010. -/
theorem all_positive_classes :
  ∀ a b c : ℤ, 0 < a → 4*a*c-b^2 = 80 → gramContent a b c = 2 → ∃ (j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ), IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  exact ArithmeticThetaBinary.all_positive_classes
/-- Independent exact target: accepted-011. -/
theorem similarity_distinct :
  ∀ (i j : Fin 3), i ≠ j → ¬ ∃ (s : ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (forms j).map (Int.castRingHom ℚ) := by
  exact ArithmeticThetaBinary.similarity_distinct
/-- Independent exact target: accepted-012. -/
theorem ambient_realization :
  ∀ j : Fin 3, (embeddings j).det ≠ 0 ∧ (embeddings j).transpose * (forms 0).map (Int.castRingHom ℚ) * embeddings j = (![1,3,1] : Fin 3 → ℚ) j • (forms j).map (Int.castRingHom ℚ) := by
  exact ArithmeticThetaBinary.ambient_realization
/-- Independent exact target: accepted-013. -/
theorem same_order_classes :
  ∀ a b c : ℤ, 0 < a → 0 < 4*a*c-b^2 → sameLocalSmith a b c → ∃! j : Fin 3, ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  exact ArithmeticThetaBinary.same_order_classes
/-- Independent exact target: support-representation-finiteness. -/
theorem representation_finiteness :
  ∀ (j : Fin 3) (m : ℕ), Set.Finite {v : ℤ × ℤ |
      (![v.1 ^ 2 + 20 * v.2 ^ 2,
        3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2,
        4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} := by
  exact ArithmeticThetaDet80.representation_finiteness
end ArithmeticThetaPalomarExamples258Det80
#print axioms ArithmeticThetaPalomarExamples258Det80.actual_coefficient_matrix
#print axioms ArithmeticThetaPalomarExamples258Det80.actual_minor_determinant
#print axioms ArithmeticThetaPalomarExamples258Det80.actual_theta_kernel_zero
#print axioms ArithmeticThetaPalomarExamples258Det80.all_positive_classes
#print axioms ArithmeticThetaPalomarExamples258Det80.similarity_distinct
#print axioms ArithmeticThetaPalomarExamples258Det80.ambient_realization
#print axioms ArithmeticThetaPalomarExamples258Det80.same_order_classes
#print axioms ArithmeticThetaPalomarExamples258Det80.representation_finiteness
end
end Package04
section Package05
set_option autoImplicit false
namespace ArithmeticThetaPalomarRank16_260.Rank16
abbrev Vec (n : ℕ) := Fin n → ℤ
def DPlusDoubled (n : ℕ) (y : Vec n) : Prop :=
  ((∀ i, y i % 2 = 0) ∨ (∀ i, y i % 2 = 1)) ∧ (∑ i, y i) % 4 = 0
def normNumerator (n : ℕ) (y : Vec n) : ℤ := ∑ i, y i ^ 2
abbrev NormShell (n m : ℕ) :=
  {y : Vec n // DPlusDoubled n y ∧ normNumerator n y = (m : ℤ)}
abbrev SumNormShell (m : ℕ) :=
  {y : Vec 8 × Vec 8 // DPlusDoubled 8 y.1 ∧ DPlusDoubled 8 y.2 ∧
    normNumerator 8 y.1 + normNumerator 8 y.2 = (m : ℤ)}
noncomputable def normSeries (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (NormShell n m) : ℤ))
noncomputable def sumNormSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (SumNormShell m) : ℤ))
noncomputable def theta (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (NormShell n (8*m)) : ℤ))
noncomputable def sumTheta : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (SumNormShell (8*m)) : ℤ))
noncomputable def columns : Fin 2 → PowerSeries ℂ :=
  ![PowerSeries.map (Int.castRingHom ℂ) sumTheta,
    PowerSeries.map (Int.castRingHom ℂ) (theta 16)]
end ArithmeticThetaPalomarRank16_260.Rank16
namespace ArithmeticThetaPalomarRank16_260.Rank16
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
end ArithmeticThetaPalomarRank16_260.Rank16
namespace ArithmeticThetaPalomarRank16_260.GeneralDPlus
def lattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range (fun j : Fin n =>
    fun i : Fin n => ArithmeticThetaPalomarRank16_260.Rank16.latticeBasis n i j))
def dualMember (n : ℕ) (v : Fin n → ℚ) : Prop :=
  ∀ w : lattice n, ∃ z : ℤ, (∑ i, v i * w.val i) = (z : ℚ)
abbrev OriginalShell (n m : ℕ) :=
  {v : Fin n → ℚ // ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v ∧
    (∑ i, v i ^ 2) / 2 = (m : ℚ)}
noncomputable def originalTheta (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (OriginalShell n m) : ℤ))
end ArithmeticThetaPalomarRank16_260.GeneralDPlus
namespace ArithmeticThetaPalomarRank16_260.Computed
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
end ArithmeticThetaPalomarRank16_260.Computed
namespace ArithmeticThetaPalomarRank16_260.Hadamard
noncomputable def a : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ)} : ℤ))
noncomputable def b : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 0} : ℤ) -
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 1} : ℤ))
noncomputable def c : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // (2 * r + 1) ^ 2 = (m : ℤ)} : ℤ))
end ArithmeticThetaPalomarRank16_260.Hadamard
namespace ArithmeticThetaPalomarRank16_260
/-- Exact independent target for accepted-014. -/
theorem no_similarity :
  ¬ ∃ (s : ℚ) (U : Matrix (Fin 16) (Fin 16) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (ArithmeticThetaPalomarRank16_260.Rank16.sumGram).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram 16).map (Int.castRingHom ℚ) := by
  exact ArithmeticThetaRank16.no_similarity
/-- Exact independent target for accepted-015. -/
theorem integral_identity :
  ArithmeticThetaPalomarRank16_260.Rank16.sumTheta = ArithmeticThetaPalomarRank16_260.Rank16.theta 16 := by
  exact ArithmeticThetaRank16.integral_identity
/-- Exact independent target for accepted-016. -/
theorem two_column_kernel :
  ∀ v : Fin 2 → ℂ, (∑ i, v i • ArithmeticThetaPalomarRank16_260.Rank16.columns i) = 0 ↔ ∃ t : ℂ, v = ![t, -t] := by
  exact ArithmeticThetaRank16.two_column_kernel
/-- Exact independent target for accepted-077. -/
theorem general_dplus_even_unimodular :
  ∀ n : ℕ, 8 ∣ n → ArithmeticThetaPalomarRank16_260.Computed.validGram (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n) ∧ (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n).det = 1 ∧ (∀ v : Fin n → ℚ, v ∈ ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n ↔ ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v) ∧ (∃ b : Module.Basis (Fin n) ℤ (ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n), ∀ (j i : Fin n), (b j).val i = ArithmeticThetaPalomarRank16_260.Rank16.latticeBasis n i j) ∧ (∀ v : Fin n → ℚ, ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v → ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ)) := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular
/-- Exact independent target for accepted-078. -/
theorem general_dplus_dual :
  ∀ n : ℕ, 8 ∣ n → ∀ v : Fin n → ℚ, ArithmeticThetaPalomarRank16_260.GeneralDPlus.dualMember n v ↔ v ∈ ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_dual
/-- Exact independent target for accepted-079. -/
theorem general_dplus_theta_realization :
  ∀ n : ℕ, 8 ∣ n → (∀ m : ℕ, ∃ e : ArithmeticThetaPalomarRank16_260.GeneralDPlus.OriginalShell n m ≃ ArithmeticThetaPalomarRank16_260.Rank16.NormShell n (8 * m), ∀ v, ArithmeticThetaPalomarRank16_260.Rank16.doubledRealization n (e v).val = v.val) ∧ ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n = ArithmeticThetaPalomarRank16_260.Rank16.theta n ∧ ArithmeticThetaPalomarRank16_260.Computed.theta (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n) = PowerSeries.map (Int.castRingHom ℂ) (ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n) ∧ (0 < n → (2 : PowerSeries ℤ) * PowerSeries.expand 8 (by decide) (ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n) = ArithmeticThetaPalomarRank16_260.Hadamard.a ^ n + ArithmeticThetaPalomarRank16_260.Hadamard.b ^ n + ArithmeticThetaPalomarRank16_260.Hadamard.c ^ n) := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization
end ArithmeticThetaPalomarRank16_260
#print axioms ArithmeticThetaPalomarRank16_260.no_similarity
#print axioms ArithmeticThetaPalomarRank16_260.integral_identity
#print axioms ArithmeticThetaPalomarRank16_260.two_column_kernel
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_even_unimodular
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_dual
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_theta_realization
end Package05
section Package06
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarEtaleNorm259
open CategoryTheory AlgebraicGeometry
abbrev Sections (X : Scheme.{u}) (U : X.Opens) :=
  X.presheaf.obj (Opposite.op U)
def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : Sections X U) : Sections X V :=
  X.presheaf.map (homOfLE h).op a
/-- Determinant with scalar algebra given by the actual morphism on sections. -/
def affineNorm {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) : Sections Y U :=
  letI := (f.app U).hom.toAlgebra
  Algebra.norm (Sections Y U) a
def AffineFree {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : Prop :=
  letI := (f.app U).hom.toAlgebra
  Module.Free (Sections Y U) (Sections X (f ⁻¹ᵁ U))
/-- The norm section agrees with the actual determinant on every free affine test. -/
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U), AffineFree f V.1 →
    affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) = restrict U V.1 e b
abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U
/-- All sections, including zero, with determinant normalization and restriction. -/
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)
/-- Exact accepted-098 scope: existence and uniqueness on arbitrary schemes. -/
theorem finite_etale_norm_family
    (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f] :
    ∃! N : NormFamily f, IsNormFamily f N := by
  exact ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family X Y f
end ArithmeticThetaPalomarEtaleNorm259
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaPalomarEtaleNorm259
 theorem sections_bridge (X : Scheme.{u}) (U : X.Opens) :
    Sections X U = ArithmeticThetaSchemeKatoNormR0251.Sections X U := rfl
 theorem restrict_bridge {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : Sections X U) :
    restrict U V h a = ArithmeticThetaSchemeKatoNormR0251.restrict U V h a := rfl
 theorem affineNorm_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) :
    affineNorm f U a = ArithmeticThetaGeometricNormR0150.affineNorm f U a := rfl
 theorem affineFree_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    AffineFree f U = ArithmeticThetaGeometricNormR0150.AffineFree f U := rfl
 theorem isNormSection_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) :
    IsNormSection f U a b = ArithmeticThetaSchemeKatoNormR0251.IsNormSection f U a b := rfl
 theorem normFamily_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NormFamily f = ArithmeticThetaSchemeKatoNormR0251.NormFamily f := rfl
 theorem isNormFamily_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) :
    IsNormFamily f N = ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N := rfl
end ArithmeticThetaPalomarEtaleNorm259
#print axioms ArithmeticThetaPalomarEtaleNorm259.finite_etale_norm_family
#print axioms ArithmeticThetaPalomarEtaleNorm259.sections_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.restrict_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.affineNorm_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.affineFree_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.isNormSection_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.normFamily_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.isNormFamily_bridge
end
end Package06
section Package07
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Jacobi
namespace Hadamard
noncomputable def a : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ)} : ℤ))
noncomputable def b : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 0} : ℤ) -
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 1} : ℤ))
noncomputable def c : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // (2 * r + 1) ^ 2 = (m : ℤ)} : ℤ))
end Hadamard
namespace Durfee
noncomputable def normalizedFiniteProduct (N : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  (1 + PowerSeries.C (LaurentPolynomial.T 1)) *
    ∏ j ∈ Finset.range N,
      (1 - PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j+1))
end Durfee
/-- Exact independent target: accepted-007. -/
theorem formal_jacobi_triple_product :
  (PowerSeries.mk (fun e => PowerSeries.coeff e ((1 + PowerSeries.C (LaurentPolynomial.T 1)) * ∏ j ∈ Finset.range e, (1 - PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j + 1)) : PowerSeries (LaurentPolynomial ℤ)))) = PowerSeries.mk (fun d => ∑ k ∈ Finset.Icc (-(d : ℤ)) ((d : ℤ) + 1), if k * (k - 1) = 2 * (d : ℤ) then (LaurentPolynomial.T k : LaurentPolynomial ℤ) else 0) := by
  exact ArithmeticThetaDurfee.formal_jacobi_triple_product
/-- Exact independent target: accepted-009. -/
theorem jacobi_formal :
  ArithmeticThetaPalomarFormal261Jacobi.Hadamard.a ^ 4 = ArithmeticThetaPalomarFormal261Jacobi.Hadamard.b ^ 4 + ArithmeticThetaPalomarFormal261Jacobi.Hadamard.c ^ 4 := by
  exact ArithmeticThetaHadamard.jacobi_formal
/-- Exact independent target: support-normalized-product-stability. -/
theorem normalized_partial_stable :
  ∀ (d N : ℕ), d ≤ N → PowerSeries.coeff d (ArithmeticThetaPalomarFormal261Jacobi.Durfee.normalizedFiniteProduct N) = PowerSeries.coeff d (ArithmeticThetaPalomarFormal261Jacobi.Durfee.normalizedFiniteProduct d) := by
  exact ArithmeticThetaDurfee.normalized_partial_stable
end ArithmeticThetaPalomarFormal261Jacobi
#print axioms ArithmeticThetaPalomarFormal261Jacobi.formal_jacobi_triple_product
#print axioms ArithmeticThetaPalomarFormal261Jacobi.jacobi_formal
#print axioms ArithmeticThetaPalomarFormal261Jacobi.normalized_partial_stable
end
end Package07
section Package08
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Tate
namespace Tate
variable {k : Type u} [Field k]
/-- a*t^n in the actual power series ring. -/
def monomial (a : k) (n : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ n
/-- v/(1-v)^2, using the formal power-series inverse. -/
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2
/-- z*d/dz of xTerm(z); evaluated at the annular monomial. -/
def yTerm (v : PowerSeries k) : PowerSeries k := v * (1+v) * ((1-v)⁻¹)^3
/-- r=0 plus the two tails for 1≤r≤N, including the normalization correction. -/
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  xTerm (monomial a i) +
  (∑ j ∈ Finset.range N,
    (xTerm (monomial a (d*(j+1)+i)) +
     xTerm (monomial a⁻¹ (d*(j+1)-i)))) -
  2 * ∑ j ∈ Finset.range N,
    PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1 - monomial 1 (d*(j+1)))⁻¹
/-- One half the logarithmic z-derivative; the negative tail has a minus sign. -/
def partialY (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  PowerSeries.C (2 : k)⁻¹ *
    (yTerm (monomial a i) + ∑ j ∈ Finset.range N,
      (yTerm (monomial a (d*(j+1)+i)) -
       yTerm (monomial a⁻¹ (d*(j+1)-i))))
/-- Stable coefficient candidates; stabilization is a new theorem obligation. -/
def tateX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
def tateY (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialY d i a (n+1))
/-- Q=t^d, z=a*t^i avoiding the identity representative. -/
def Admissible (d i : ℕ) (a : k) : Prop :=
  0 < d ∧ i < d ∧ a ≠ 0 ∧ (i = 0 → a ≠ 1)
/-- The actual series ∑_{r∈ℤ} t^(r²), with the zero index counted once. -/
def theta (k : Type u) [Field k] : PowerSeries k :=
  PowerSeries.mk fun n => (if n = 0 then 1 else 0) +
    2 * ((Finset.filter (fun j : ℕ => j^2 = n) (Finset.Icc 1 n)).card : k)
/-- Exact equality of all coefficients below N; O(t^N) has no analytic meaning here. -/
def AgreeBelow (N : ℕ) (f g : PowerSeries k) : Prop :=
  ∀ n : ℕ, n < N → PowerSeries.coeff n f = PowerSeries.coeff n g
/-- The specified q=s², Q=s⁴ marking, so s is the source's q^(1/2). -/
def e₁ (k : Type u) [Field k] : PowerSeries k := tateX 4 0 (-1)
def e₂ (k : Type u) [Field k] : PowerSeries k := tateX 4 2 1
def e₃ (k : Type u) [Field k] : PowerSeries k := tateX 4 2 (-1)
def xR (k : Type u) [Field k] : PowerSeries k := tateX 4 1 1
def yR (k : Type u) [Field k] : PowerSeries k := tateY 4 1 1
/-- Genuine power-series inclusion into its Laurent-series fraction field. -/
def toLaurent (k : Type u) [Field k] : PowerSeries k →+* LaurentSeries k :=
  HahnSeries.ofPowerSeries ℤ k
/-- Literal source rational expression; division takes place in k((s)). -/
def markedRoot (k : Type u) [Field k] : LaurentSeries k :=
  let j := toLaurent k
  ((j (xR k) - j (e₁ k))^2 -
    (j (e₁ k) - j (e₂ k)) * (j (e₁ k) - j (e₃ k))) / (2*j (yR k))
end Tate
namespace Gamma
noncomputable def partialGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) (N : ℕ) : PowerSeries R :=
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (d * r + i))) *
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C b * PowerSeries.X ^ (d * (r + 1) - i)))
noncomputable def fullGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) : PowerSeries R :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (partialGamma d i a b (n + 1)))
end Gamma
namespace UnaryProduct
noncomputable def etaPartial (D N : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range N, (1-PowerSeries.X^(D*(j+1)))
noncomputable def etaProduct (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (etaPartial D d))
end UnaryProduct
namespace Identities
variable {k : Type u} [Field k]
def gammaLaurent (d : ℕ) (i : ℤ) (a : k) : LaurentSeries k :=
  let h := i / (d : ℤ)
  let r := i % (d : ℤ)
  HahnSeries.single (-r*h - (d : ℤ)*(h*(h-1)/2)) ((-a)^(-h)) *
    ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k
      (ArithmeticThetaPalomarFormal261Tate.Gamma.fullGamma d r.toNat a a⁻¹)
end Identities
/-- Exact independent target: accepted-018. -/
theorem basic_fourth :
  ∀ {k : Type u} [Field k] [CharZero k], ArithmeticThetaPalomarFormal261Tate.Tate.theta k ^ 4 = 4 * (ArithmeticThetaPalomarFormal261Tate.Tate.tateX 2 1 (1:k) - ArithmeticThetaPalomarFormal261Tate.Tate.tateX 2 0 (-1:k)) := by
  exact ArithmeticThetaTateSeries.basic_fourth
/-- Exact independent target: accepted-089. -/
theorem general_annular_addition :
  ∀ {k : Type u} [Field k] [CharZero k], ∀ (d i j : ℕ) (a b : k), ArithmeticThetaPalomarFormal261Tate.Tate.Admissible d i a → ArithmeticThetaPalomarFormal261Tate.Tate.Admissible d j b → (ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (ArithmeticThetaPalomarFormal261Tate.Tate.tateX d i (a : k)) - ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (ArithmeticThetaPalomarFormal261Tate.Tate.tateX d j (b : k))) * (ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d (i:ℤ) a)^2 * (ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d (j:ℤ) b)^2 = -HahnSeries.single (j:ℤ) b * (ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaPalomarFormal261Tate.UnaryProduct.etaProduct d)))^4 * ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d ((i:ℤ)-(j:ℤ)) (a/b) * ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d ((i:ℤ)+(j:ℤ)) (a*b) := by
  exact ArithmeticThetaTateIdentities.general_annular_addition
end ArithmeticThetaPalomarFormal261Tate
#print axioms ArithmeticThetaPalomarFormal261Tate.basic_fourth
#print axioms ArithmeticThetaPalomarFormal261Tate.general_annular_addition
end
end Package08
section Package09
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Norm
namespace Quotients
def quotient (c d i : ℕ) : ℕ := c * i / d
def residue (c d i : ℕ) : ℕ := c * i % d
end Quotients
namespace FiniteNorm
def triangle (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) - 1) / 2
def p (c : ℕ) : ℤ := -triangle c
def K (c : ℕ) : ℤ := (c : ℤ) ^ 2 - 1
def S (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i : ℤ)
def E (c d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d,
    ((ArithmeticThetaPalomarFormal261Norm.Quotients.residue c d i : ℤ) *
      (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i : ℤ) +
    (d : ℤ) * triangle (ArithmeticThetaPalomarFormal261Norm.Quotients.quotient c d i))
end FiniteNorm
namespace LaurentNorm
def Partial (F : Type) [Field F] (d m : ℕ) (a : F) (N : ℕ) : LaurentSeries F :=
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a * HahnSeries.single ((d : ℤ) * l + m) (1 : F))) *
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a⁻¹ * HahnSeries.single ((d : ℤ) * (l + 1) - m) (1 : F)))
def IsGamma (F : Type) [Field F] (d m : ℕ) (a : F) (g : LaurentSeries F) : Prop :=
  ∀ n : ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ e : ℤ, e ≤ n →
    (Partial F d m a N).coeff e = g.coeff e
def t (F : Type) [Field F] : LaurentSeries F := HahnSeries.single 1 1
abbrev Coeff (K : Type) [Field K] := FractionRing (LaurentPolynomial K)
abbrev Series (K : Type) [Field K] := LaurentSeries (Coeff K)
def w (K : Type) [Field K] : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.T 1)
def scalar (K : Type) [Field K] (a : K) : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.C a)
def a (K : Type) [Field K] (ζ : K) (j c : ℕ) : Coeff K :=
  scalar K ζ ^ (c * j) * w K ^ c
def point (K : Type) [Field K] (ζ : K) (i j : ℕ) : Series K :=
  HahnSeries.C (a K ζ j 1) * t (Coeff K) ^ i
def z (K : Type) [Field K] (d : ℕ) : Series K :=
  HahnSeries.C (w K ^ d)
def Q (K : Type) [Field K] (d : ℕ) : Series K := t (Coeff K) ^ d
end LaurentNorm
/-- Exact independent target: accepted-092. -/
theorem powered_gamma_norm :
  ∀ (K : Type) [Field K] [CharZero K] (c d : ℕ) (ζ : K), 1 < c → 0 < d → Nat.Coprime c d → IsPrimitiveRoot ζ d → ∀ (H : Fin d → Fin d → ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K) (b : ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K), (∀ i j : Fin d, ArithmeticThetaPalomarFormal261Norm.LaurentNorm.IsGamma (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Coeff K) d (c * i.val) (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.a K ζ j.val c) (H i j)) → ArithmeticThetaPalomarFormal261Norm.LaurentNorm.IsGamma (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Coeff K) d 0 (ArithmeticThetaPalomarFormal261Norm.LaurentNorm.w K ^ (c * d)) b → (∏ i : Fin d, ∏ j : Fin d, H i j) = (-1 : ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Series K) ^ (-ArithmeticThetaPalomarFormal261Norm.FiniteNorm.S c d) * ArithmeticThetaPalomarFormal261Norm.LaurentNorm.z K d ^ (-(c : ℤ) * ArithmeticThetaPalomarFormal261Norm.FiniteNorm.S c d) * ArithmeticThetaPalomarFormal261Norm.LaurentNorm.Q K d ^ (-ArithmeticThetaPalomarFormal261Norm.FiniteNorm.E c d) * b := by
  exact ArithmeticThetaLaurentNormR0064.powered_gamma_norm
end ArithmeticThetaPalomarFormal261Norm
#print axioms ArithmeticThetaPalomarFormal261Norm.powered_gamma_norm
end
end Package09
section Package10
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarFoundations269Elementary
/-- Independent exact target: accepted-000. -/
theorem rank_zero_coefficients :
  ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ, Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0 := by
  exact ArithmeticThetaElementary.rank_zero_coefficients
/-- Independent exact target: accepted-001. -/
theorem rank_zero_kernel :
  ∀ (h : ℕ) (c : Fin h → ℂ), (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = 0 ↔ (∑ i : Fin h, c i) = 0 := by
  exact ArithmeticThetaElementary.rank_zero_kernel
/-- Independent exact target: accepted-002. -/
theorem rank_zero_image :
  ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ, (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔ ∃ z : ℂ, f = PowerSeries.C z := by
  exact ArithmeticThetaElementary.rank_zero_image
/-- Independent exact target: accepted-090. -/
theorem norm_exponent_identities :
  ∀ (c d : ℚ), (d - 1) * (-c * (c - 1) / 2) + c * ((c - 1) * (d - 1) / 2) = 0 ∧ (d ^ 2 - 1) * (c ^ 2 - 1) / 12 + (-c * (c - 1) / 2) * d * (d - 1) / 2 + ((c ^ 2 - 1) * (d - 1) * (2 * d - 1) / 12 - d * (c - 1) * (d - 1) / 4) = 0 ∧ (d ^ 2 - 1) * (-c * (c - 1) / 2) + (c - 1) * (d - 1) / 2 = (c - 1) * (d - 1) * (1 - c * (d + 1)) / 2 := by
  exact ArithmeticThetaElementary.norm_exponent_identities
/-- Independent exact target: accepted-091. -/
theorem norm_sign_exponent_even :
  ∀ (c d : ℤ), Odd c → Even ((c - 1) * (d - 1) * (1 - c * (d + 1)) / 2) := by
  exact ArithmeticThetaElementary.norm_sign_exponent_even
end ArithmeticThetaPalomarFoundations269Elementary
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_coefficients
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_kernel
#print axioms ArithmeticThetaPalomarFoundations269Elementary.rank_zero_image
#print axioms ArithmeticThetaPalomarFoundations269Elementary.norm_exponent_identities
#print axioms ArithmeticThetaPalomarFoundations269Elementary.norm_sign_exponent_even
end
end Package10
section Package11
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
  exact ArithmeticThetaLattice.even_integral_gram_orthogonalization
/-- Independent exact target: accepted-008. -/
theorem computed_natural_data :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → (∀ i, 0 < (naturalNorms A) i ∧ Even ((naturalNorms A) i) ∧ ((naturalNorms A) i : ℤ) = (norms A) i) ∧ indexValue A = ∏ i : Fin n, ((basisMatrix A) i i).toNat ∧ 0 < indexValue A := by
  exact ArithmeticThetaOrthogonalAlgorithm.computed_natural_data
/-- Independent exact target: support-computed-orthogonalization. -/
theorem computed_orthogonalization :
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → 0 < (basisMatrix A).det ∧ (∀ i, 0 < norms A i ∧ Even (norms A i)) ∧ (basisMatrix A).transpose * A * basisMatrix A = Matrix.diagonal (norms A) := by
  exact ArithmeticThetaOrthogonalAlgorithm.computed_orthogonalization
end ArithmeticThetaPalomarFoundations269Orthogonal
#print axioms ArithmeticThetaPalomarFoundations269Orthogonal.even_integral_gram_orthogonalization
#print axioms ArithmeticThetaPalomarFoundations269Orthogonal.computed_natural_data
#print axioms ArithmeticThetaPalomarFoundations269Orthogonal.computed_orthogonalization
end
end Package11
section Package12
/-! Independent main finite-determination CHALLENGE SPECIFICATION.
This Solution consumes the actual original conservative kernel theorem.
Only Mathlib is imported. This package is a strict subset of the 103 original
endpoints and 13 requirements: geometric constructions, sharper bound,
algorithms, image coordinates and examples remain separately required.
-/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarMainFormal295
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
/-- Literal finite integer-shell coefficient definition used by the real unary provider. -/
def clearedUnaryTheta (m : ℕ) (ν : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun a => ∑ k ∈ Finset.Icc (-(a : ℤ)) ((a : ℤ)+1),
    if 12*((m : ℤ)*k+ν)^2=(a : ℤ) then (1 : ℤ) else 0)
/-- Actual integral unary series at the same common denominator N. -/
def unarySeries (N m : ℕ) (ν : ℤ) : PowerSeries ℂ :=
  PowerSeries.map (Int.castRingHom ℂ)
    (PowerSeries.subst (PowerSeries.X ^ (N^2/m)) (clearedUnaryTheta m ν))
/-- Literal q=t^(24*N^2), with N computed from the given Gram family. -/
def expanded {n h : ℕ} (A : Matrices n h) (c : Fin h → ℂ) : PowerSeries ℂ :=
  PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (thetaMap A c)
/-- The SAME indexing witness used by the cutoff supplies every pair in this full series identity. -/
def FormalIdentity {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
  ∀ c : Fin h → ℂ, expanded A c =
    ∑ i : Fin h, c i • (∑ a : Cosets A i, ∏ j : Fin n,
      unarySeries (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2)
end ArithmeticThetaPalomarMainFormal295
namespace ArithmeticThetaPalomarMainFormal295.Bridges198
open ArithmeticThetaPalomarMainFormal295
variable {n h : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ)
lemma validGram_eq : validGram A = ArithmeticThetaComputed.validGram A := rfl
lemma theta_eq : theta A = ArithmeticThetaComputed.theta A := rfl
lemma thetaMap_eq (As : Matrices n h) : thetaMap As = ArithmeticThetaComputed.thetaMap As := rfl
lemma pairing_eq (x y : Fin n → ℤ) : pairing A x y = ArithmeticThetaOrthogonalAlgorithm.pairing A x y := rfl
lemma project_eq (b v : Fin n → ℤ) : project A b v = ArithmeticThetaOrthogonalAlgorithm.project A b v := rfl
lemma step_eq (k : Fin n) : step A C k = ArithmeticThetaOrthogonalAlgorithm.step A C k := rfl
lemma runPrefix_eq (k : ℕ) : runPrefix A k = ArithmeticThetaOrthogonalAlgorithm.runPrefix A k := rfl
lemma basisMatrix_eq : basisMatrix A = ArithmeticThetaOrthogonalAlgorithm.basisMatrix A := rfl
lemma norms_eq (j : Fin n) : norms A j = ArithmeticThetaOrthogonalAlgorithm.norms A j := rfl
lemma naturalNorms_eq (j : Fin n) : naturalNorms A j = ArithmeticThetaOrthogonalAlgorithm.naturalNorms A j := rfl
lemma castVec_eq (n : ℕ) : castVec n = ArithmeticThetaOrthogonalConsumerR0127.castVec n := rfl
lemma integerVectors_eq (n : ℕ) : integerVectors n = ArithmeticThetaOrthogonalConsumerR0127.integerVectors n := rfl
lemma preimageLattice_eq : preimageLattice A = ArithmeticThetaOrthogonalConsumerR0127.preimageLattice A := rfl
lemma periods_eq : periods A = ArithmeticThetaOrthogonalConsumerR0127.periods A := rfl
lemma RationalCosets_eq : RationalCosets A = ArithmeticThetaOrthogonalConsumerR0127.RationalCosets A := rfl
lemma cosetClass_eq (t : preimageLattice A) : cosetClass A t = ArithmeticThetaOrthogonalConsumerR0127.cosetClass A t := rfl
lemma Representatives_eq (t : Fin A.det.natAbs → preimageLattice A) :
    Representatives A t = ArithmeticThetaOrthogonalConsumerR0127.Representatives A t := rfl
lemma levelIndex_eq (L : ℕ) : levelIndex L = ArithmeticThetaLevelCount.levelIndex L := rfl
lemma shell_finite (hA : validGram A) (a : ℕ) : Finite {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a : ℚ)} :=
  (ArithmeticThetaLattice.exact_shell_finite n _ hA.2.2 (a : ℚ)).to_subtype
lemma coefficientMatrix_complex_eq (As : Matrices n h) (hAs : ∀ i, validGram (As i)) (B : ℕ) :
    (coefficientMatrix As B).map (algebraMap ℚ ℂ) =
      (ArithmeticThetaComputed.coefficientMatrix As B).map (algebraMap ℚ ℂ) := by
  ext a i
  change ((coefficientMatrix As B a i : ℚ) : ℂ) =
    ((ArithmeticThetaComputed.coefficientMatrix As B a i : ℚ) : ℂ)
  rw [ArithmeticThetaComputed.computed_coefficient_matrix n h B As hAs a i]
  simp [coefficientMatrix, ArithmeticThetaComputed.theta]
end ArithmeticThetaPalomarMainFormal295.Bridges198
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.thetaMap_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.Representatives_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.shell_finite
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.coefficientMatrix_complex_eq
namespace ArithmeticThetaPalomarMainFormal295.Bridges198
open ArithmeticThetaPalomarMainFormal295
variable {n h : ℕ} (A : Matrices n h)
lemma commonN_eq : commonN A = ArithmeticThetaLatticeSectionsR0188.commonN A := rfl
lemma centered_eq (m : ℕ) (a : Fin m) :
    centered m a = ArithmeticThetaLatticeSectionsR0188.centered m a := rfl
/-- Copy the actual fields; no new choice of representatives, pairs or count. -/
def fromOriginal (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) : Indexing A where
  representatives := U.representatives
  residue := U.residue
  count := U.count
  pair := U.pair
  index := U.index
/-- Reverse fieldwise conversion, useful for checking that no data were omitted. -/
def toOriginal (U : Indexing A) : ArithmeticThetaLatticeSectionsR0188.Indexing A where
  representatives := U.representatives
  residue := U.residue
  count := U.count
  pair := U.pair
  index := U.index
lemma fromOriginal_count (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    (fromOriginal A U).count = U.count := rfl
lemma fromOriginal_indexed (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    Indexed A (fromOriginal A U) ↔ ArithmeticThetaLatticeSectionsR0188.Indexed A U := Iff.rfl
lemma toOriginal_indexed (U : Indexing A) :
    ArithmeticThetaLatticeSectionsR0188.Indexed A (toOriginal A U) ↔ Indexed A U := Iff.rfl
lemma to_fromOriginal (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    toOriginal A (fromOriginal A U) = U := by cases U; rfl
lemma from_toOriginal (U : Indexing A) :
    fromOriginal A (toOriginal A U) = U := by cases U; rfl
end ArithmeticThetaPalomarMainFormal295.Bridges198
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.fromOriginal_indexed
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges198.to_fromOriginal
namespace ArithmeticThetaPalomarMainFormal295.Bridges250
open ArithmeticThetaPalomarMainFormal295
variable {n h : ℕ} (A : Matrices n h)
lemma commonN_computed : commonN A = ArithmeticThetaOrthogonalAlgorithm.commonModulus A := by
  exact Finset.lcm_eq_lcm_image
lemma level_computed : level (commonN A) = ArithmeticThetaOrthogonalAlgorithm.level A := by
  unfold level ArithmeticThetaOrthogonalAlgorithm.level
  rw [commonN_computed]
lemma exponent_computed : exponent (commonN A) = ArithmeticThetaOrthogonalAlgorithm.normExponent A := by
  unfold exponent ArithmeticThetaOrthogonalAlgorithm.normExponent
  rw [commonN_computed]
lemma commonN_pos (hA : ∀ i, validGram (A i)) : 0 < commonN A := by
  rw [commonN_computed]
  exact (ArithmeticThetaOrthogonalAlgorithm.computed_bound_parameters n h A
    (fun i => (hA i).1) (fun i => (hA i).2.1) (fun i => (hA i).2.2)).2.2.1
/-- The integer division in the Challenge equals its rational product formula,
with no geometric existence premise and no assumption on padded pair counts. -/
lemma cutoff_rational (U : Indexing A) (hN : 0 < commonN A) :
    (cutoff A U : ℚ) = (n : ℚ) * (exponent (commonN A) : ℚ)^U.count *
      levelIndex (level (commonN A)) / 48 := by
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  obtain ⟨hcard, hsigned⟩ := ArithmeticThetaGlobalization.finite_full_level_count _ hL
  have hnat : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) =
      2 * level (commonN A) *
        Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair (level (commonN A))) := by
    exact_mod_cast hcard.trans hsigned.symm
  have hd : 48 ∣ n * exponent (commonN A) ^ U.count *
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) := by
    rw [hnat]
    refine ⟨n * exponent (commonN A) ^ U.count * (commonN A)^2 *
      Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair (level (commonN A))), ?_⟩
    dsimp [level]
    ring
  unfold cutoff
  rw [Nat.cast_div hd (by decide : (48 : ℚ) ≠ 0)]
  push_cast
  rw [hcard]
  rfl
lemma prefix_map_eq (hA : ∀ i, validGram (A i)) (B : ℕ) :
    (ArithmeticThetaComputed.prefixMap B).comp (thetaMap A) =
      ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  rw [Bridges198.coefficientMatrix_complex_eq A hA B]
  exact ArithmeticThetaComputed.computed_prefix_map n h B A hA
lemma matrix_zero_iff_coefficients (hA : ∀ i, validGram (A i)) (B : ℕ) (c : Fin h → ℂ) :
    ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin c = 0 ↔
      ∀ a : ℕ, a ≤ B → PowerSeries.coeff a (thetaMap A c) = 0 := by
  rw [← prefix_map_eq A hA B]
  constructor
  · intro hc a ha
    exact congrFun hc (⟨a, by omega⟩ : Fin (B+1))
  · intro hc
    funext a
    exact hc a.val (by omega)
/-- This transports a previously proved kernel equality; it does not assume
or assert that such an equality exists at the explicit conservative bound. -/
lemma coefficients_iff_of_kernel (hA : ∀ i, validGram (A i)) (B : ℕ)
    (hk : LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin))
    (c : Fin h → ℂ) :
    thetaMap A c = 0 ↔ ∀ a : ℕ, a ≤ B → PowerSeries.coeff a (thetaMap A c) = 0 := by
  rw [← LinearMap.mem_ker, hk, LinearMap.mem_ker]
  exact matrix_zero_iff_coefficients A hA B c
end ArithmeticThetaPalomarMainFormal295.Bridges250
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.commonN_computed
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.level_computed
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.exponent_computed
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.commonN_pos
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.cutoff_rational
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.prefix_map_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.matrix_zero_iff_coefficients
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges250.coefficients_iff_of_kernel
namespace ArithmeticThetaPalomarMainFormal295.Bridges265
open ArithmeticThetaPalomarMainFormal295
lemma level_original (N : ℕ) : level N = ArithmeticThetaCompactUnaryR0183.level N := rfl
lemma exponent_original (N : ℕ) : exponent N = ArithmeticThetaCompactUnaryR0183.exponent N := rfl
lemma cutoff_original {n h : ℕ} (A : Matrices n h)
    (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    cutoff A (Bridges198.fromOriginal A U) = ArithmeticThetaConservativeKernelR0189.cutoff A U := rfl
end ArithmeticThetaPalomarMainFormal295.Bridges265
namespace ArithmeticThetaPalomarMainFormal295.Bridges295
open ArithmeticThetaPalomarMainFormal295
lemma clearedUnaryTheta_eq (m : ℕ) (ν : ℤ) :
    clearedUnaryTheta m ν = ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν := rfl
lemma unarySeries_eq (N m : ℕ) (ν : ℤ) :
    unarySeries N m ν = ArithmeticThetaSimultaneousUnaryR0187.unarySeries ℂ N m ν := rfl
lemma expanded_eq {n h : ℕ} (A : Matrices n h) (c : Fin h → ℂ) :
    expanded A c = ArithmeticThetaLatticeSectionsR0188.expanded A c := rfl
lemma fromOriginal_formal {n h : ℕ} (A : Matrices n h)
    (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    FormalIdentity A (Bridges198.fromOriginal A U) ↔
      ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U := Iff.rfl
lemma toOriginal_formal {n h : ℕ} (A : Matrices n h) (U : Indexing A) :
    ArithmeticThetaLatticeSectionsR0188.FormalIdentity A (Bridges198.toOriginal A U) ↔
      FormalIdentity A U := Iff.rfl
end ArithmeticThetaPalomarMainFormal295.Bridges295
namespace ArithmeticThetaPalomarMainFormal295
/-- Full main kernel statement. No cutoff or geometric existence premise.
The witnesses enumerate precisely the actual preimage cosets and occurring
centered unary pairs; thus s cannot be an arbitrary padding count. -/
theorem explicitFiniteDeterminationWithFormalIdentity (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    ∃ B : ℕ,
      (if n = 0 then B = 0 else
        ∃ U : Indexing A, Indexed A U ∧ FormalIdentity A U ∧ B = cutoff A U ∧
          (B : ℚ) = (n : ℚ) * (exponent (commonN A) : ℚ)^U.count *
            levelIndex (level (commonN A)) / 48) ∧
      (∀ B' : ℕ, B ≤ B' →
        LinearMap.ker (thetaMap A) =
          LinearMap.ker (((coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧
      (∀ B' : ℕ, B ≤ B' → ∀ c : Fin h → ℂ,
        thetaMap A c = 0 ↔ ∀ a : ℕ, a ≤ B' →
          PowerSeries.coeff a (thetaMap A c) = 0) ∧
      (n = 0 → ∀ c : Fin h → ℂ,
        thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  refine ⟨fun i a => Bridges198.shell_finite (A i) (hA i) a, ?_⟩
  obtain ⟨B, hB, hkernel, hzero⟩ :=
    ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel n h hh A hA
  have hk : ∀ B' : ℕ, B ≤ B' → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin) := by
    intro B' hBB
    rw [Bridges198.thetaMap_eq A, Bridges198.coefficientMatrix_complex_eq A hA B']
    exact hkernel B' hBB
  refine ⟨B, ?_, hk, ?_, ?_⟩
  · by_cases hn : n = 0
    · simpa only [if_pos hn] using hB
    · rw [if_neg hn] at hB ⊢
      obtain ⟨U, hU, hformal, hcut, _hformula⟩ := hB
      refine ⟨Bridges198.fromOriginal A U, (Bridges198.fromOriginal_indexed A U).mpr hU,
        (Bridges295.fromOriginal_formal A U).mpr hformal, ?_, ?_⟩
      · rw [Bridges265.cutoff_original]
        exact hcut
      · rw [← Bridges265.cutoff_original A U] at hcut
        rw [hcut]
        exact Bridges250.cutoff_rational A (Bridges198.fromOriginal A U)
          (Bridges250.commonN_pos A hA)
  · intro B' hBB c
    exact Bridges250.coefficients_iff_of_kernel A hA B' (hk B' hBB) c
  · intro hn c
    rw [Bridges198.thetaMap_eq A]
    exact hzero hn c
end ArithmeticThetaPalomarMainFormal295
#print axioms ArithmeticThetaPalomarMainFormal295.explicitFiniteDeterminationWithFormalIdentity
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges295.clearedUnaryTheta_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges295.unarySeries_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges295.expanded_eq
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges295.fromOriginal_formal
#print axioms ArithmeticThetaPalomarMainFormal295.Bridges295.toOriginal_formal
end
end Package12
