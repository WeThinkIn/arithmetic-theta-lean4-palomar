module
public import AmbientPrescribedRootsR0228
public import SmoothPointSimultaneousRootsR0228
public import Mathlib
public import SharpMatrixKernelR0195
public import ComputedCoefficientMatrix
public import LatticeShellFinite
@[expose] public section
section Package00
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaPalomarAmbient355
theorem ambient_prescribed_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space), CategoryTheory.CategoryStruct.comp f X.map = ArithmeticThetaTateCuspsR0181.diskStructure (ArithmeticThetaConstantExtensionR0225.Omega k) → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion (ArithmeticThetaConstantExtensionR0225.Omega k)) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by
  exact ArithmeticThetaAmbientCompletedRootsR0227.ambient_prescribed_roots
#print axioms ambient_prescribed_roots
theorem smooth_point_simultaneous_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ x : X.space, IsClosed ({x} : Set X.space) → ∃ f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space, ArithmeticThetaAmbientCompletedRootsR0227.IsCompletedDisk (ArithmeticThetaConstantExtensionR0225.Omega k) X x f ∧ (∃ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h) ∧ ∀ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by
  exact ArithmeticThetaAmbientCompletedRootsR0227.smooth_point_simultaneous_roots
#print axioms smooth_point_simultaneous_roots
end ArithmeticThetaPalomarAmbient355
end
end Package00
section Package01
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarSharp360
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
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
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def distinctNorms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (distinctNorms A).card
def level (N : ℕ) : ℕ := 24 * N^2
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
end ArithmeticThetaPalomarSharp360
namespace ArithmeticThetaPalomarSharp360.Bridges
open ArithmeticThetaPalomarSharp360
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
end ArithmeticThetaPalomarSharp360.Bridges
namespace ArithmeticThetaPalomarSharp360
/-- Full original sharp kernel conclusion plus actual shell finiteness. -/
theorem sharpFiniteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    (∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧
    (n = 0 → cutoff A = 0 ∧ ∀ c : Fin h → ℂ,
      thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  obtain ⟨hk, hz⟩ := ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel n h hh A hA
  refine ⟨fun i a => Bridges.shell_finite (A i) (hA i) a, ?_, hz⟩
  intro B hB
  rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B]
  exact hk B hB
theorem original049Correspondence :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧ ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro n h hh A hA
  have hs := sharpFiniteDetermination n h hh A hA
  refine ⟨?_, hs.2.2⟩
  intro B hB
  have hk := hs.2.1 B hB
  rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B] at hk
  exact hk
end ArithmeticThetaPalomarSharp360
end
end Package01
