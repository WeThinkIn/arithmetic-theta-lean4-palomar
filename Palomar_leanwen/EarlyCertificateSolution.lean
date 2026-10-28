module
public import ActualEarlierCertificate
public import LatticeShellFinite

@[expose] public section
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
