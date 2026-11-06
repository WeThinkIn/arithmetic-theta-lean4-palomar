import SharpExactImageDataR0195
import DistinctNormSharpArithmeticR0195
import LDLThetaPrefixR0229
import ComputedBoundParameters
import ComputedEarlyCertificate
import ThetaBasisChange

/-! Executable source algorithm and its correctness predicates.
The correctness assertions are separate proof-worker obligations. -/
set_option autoImplicit false
namespace ArithmeticThetaAdaptiveSolverR0230

abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ

def indexValue (L : ℕ) : ℚ :=
  (L : ℚ)^3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹^2)

/-- Exact rational floor computed from the actual orthogonalization output. -/
def bound {n h : ℕ} (A : Matrices n h) : ℕ :=
  Int.toNat ⌊(n : ℚ) * 2^(ArithmeticThetaOrthogonalAlgorithm.distinctNormCount A - 1) *
    indexValue (ArithmeticThetaOrthogonalAlgorithm.level A) /
      (48 * (ArithmeticThetaOrthogonalAlgorithm.level A : ℚ))⌋

def next (cap b : ℕ) : ℕ := min cap (max 1 (2*b))

def scheduleAux (cap : ℕ) : ℕ → ℕ → List ℕ
  | 0, b => [b]
  | fuel+1, b => if cap ≤ b then [cap] else b :: scheduleAux cap fuel (next cap b)

def schedule (cap : ℕ) : List ℕ := scheduleAux cap (cap+1) 0

/-- Columns are already established full-series relations. This predicate
never accepts finite-prefix agreement as evidence of a relation. -/
def Relations {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) : Prop :=
  ∀ j : Fin d, ArithmeticThetaComputed.thetaMap A (fun i => (R i j : ℂ)) = 0

def early {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) (B : ℕ) : Bool :=
  let rank := (ArithmeticThetaElimination.run
    (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B)).pivots.length
  rank == h || (ArithmeticThetaElimination.run R).pivots.length + rank == h

structure Result (h : ℕ) where
  cutoff : ℕ
  matrix : Matrix (Fin (cutoff+1)) (Fin h) ℚ

def assemble {n h : ℕ} (A : Matrices n h) (B : ℕ) : Result h :=
  ⟨B, ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B⟩

def certify {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ)
    (B : ℕ) : Option (Result h) :=
  if early A R B then some (assemble A B) else none

/-- This entrypoint derives the cap internally. Its caller supplies no bound. -/
def solve {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) : Option (Result h) :=
  ((schedule (bound A)).find? (fun B => early A R B || B == bound A)).map (assemble A)

def nullVectors {h : ℕ} (o : Result h) := ArithmeticThetaElimination.nullBasis o.matrix

def pivotIndices {h : ℕ} (o : Result h) :
    Fin (ArithmeticThetaElimination.run o.matrix).pivots.length → Fin h :=
  fun t => ((ArithmeticThetaElimination.run o.matrix).pivots.get t).2

def coordinates {h : ℕ} (o : Result h) := ArithmeticThetaElimination.columnCoordinates o.matrix

/-- Complete facts about the actual returned matrix, null vectors, pivot
indices and coordinates, rather than a merely equal prefix's abstract rank. -/
def Correct {n h : ℕ} (A : Matrices n h) (o : Result h) : Prop :=
  o.matrix = ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A o.cutoff ∧
  LinearMap.ker (ArithmeticThetaComputed.thetaMap A) =
    LinearMap.ker ((o.matrix.map (algebraMap ℚ ℂ)).mulVecLin) ∧
  (LinearIndependent ℂ (fun t => fun j => (nullVectors o t j : ℂ)) ∧
    Submodule.span ℂ (Set.range (fun t => fun j => (nullVectors o t j : ℂ))) =
      LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧
  (LinearIndependent ℂ (fun t => ArithmeticThetaComputed.theta (A (pivotIndices o t))) ∧
    Submodule.span ℂ (Set.range (fun t => ArithmeticThetaComputed.theta (A (pivotIndices o t)))) =
      LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧
  ∀ j : Fin h,
    ArithmeticThetaComputed.theta (A j) = ∑ t,
      (coordinates o j t : ℂ) • ArithmeticThetaComputed.theta (A (pivotIndices o t)) ∧
    ∀ c : Fin (ArithmeticThetaElimination.run o.matrix).pivots.length → ℚ,
      ArithmeticThetaComputed.theta (A j) = ∑ t,
        (c t : ℂ) • ArithmeticThetaComputed.theta (A (pivotIndices o t)) →
      c = coordinates o j

structure Change (n h : ℕ) where
  left : Fin h
  right : Fin h
  matrix : Matrix (Fin n) (Fin n) ℤ

/-- Invalid candidates contribute a zero relation, never an unverified claim. -/
def checkChange {n h : ℕ} (A : Matrices n h) (c : Change n h) : Bool :=
  decide ((c.matrix.det = 1 ∨ c.matrix.det = -1) ∧
    c.matrix.transpose * A c.left * c.matrix = A c.right)

def changeRelations {n h : ℕ} (A : Matrices n h) (cs : List (Change n h)) :
    Matrix (Fin h) (Fin cs.length) ℚ :=
  fun i j => let c := cs.get j
    if checkChange A c then
      (if i = c.left then 1 else 0) - (if i = c.right then 1 else 0) else 0

def solveChanges {n h : ℕ} (A : Matrices n h) (cs : List (Change n h)) : Option (Result h) :=
  solve A (changeRelations A cs)

end ArithmeticThetaAdaptiveSolverR0230
