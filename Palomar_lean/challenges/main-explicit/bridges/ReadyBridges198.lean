module
public import MainIndependentDefinitions198
public import OrthogonalConsumerDefinitionsR0127
public import ComputedCoefficientMatrix
public import LatticeShellFinite
public import GlobalizationDefinitions
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarMain172.Bridges198
open ArithmeticThetaPalomarMain172
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
end ArithmeticThetaPalomarMain172.Bridges198
#print axioms ArithmeticThetaPalomarMain172.Bridges198.thetaMap_eq
#print axioms ArithmeticThetaPalomarMain172.Bridges198.Representatives_eq
#print axioms ArithmeticThetaPalomarMain172.Bridges198.shell_finite
#print axioms ArithmeticThetaPalomarMain172.Bridges198.coefficientMatrix_complex_eq
