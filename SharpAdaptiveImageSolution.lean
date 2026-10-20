module
public import Mathlib
public import OrthogonalConsumerDefinitionsR0127
public import ComputedCoefficientMatrix
public import LatticeShellFinite
public import DistinctNormSharpArithmeticR0195
public import SharpMatrixKernelR0195
public import AdaptiveUniversalSolverR0230
public import EarlyCertificateAssembly
@[expose] public section
section Package00
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarSharp349
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
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
/-- Distinct computed diagonal norms; repeated norms contribute only once. -/
def distinctNorms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (distinctNorms A).card
structure NormIndex {n h : ℕ} (A : Matrices n h) where
  norm : Fin (normCount A) → ℕ
  index : Fin h × Fin n → Fin (normCount A)
def IndexesNorms {n h : ℕ} (A : Matrices n h) (I : NormIndex A) : Prop :=
  Function.Injective I.norm ∧ Function.Surjective I.index ∧
  ∀ ij, I.norm (I.index ij) = naturalNorms (A ij.1) ij.2
/-- The displayed product I(L), not an assumed group-cardinality identity. -/
def levelIndex (L : ℕ) : ℚ :=
  (L : ℚ)^3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹^2)
def level (N : ℕ) : ℕ := 24 * N^2
/-- Exact natural floor cutoff, using the actual full-level group cardinality. -/
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))
/-- Actual integer-shell counts, cast to Q; rows include both 0 and B. -/
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
end ArithmeticThetaPalomarSharp349
namespace ArithmeticThetaPalomarSharp349.Bridges
open ArithmeticThetaPalomarSharp349
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
lemma commonN_eq (As : Matrices n h) :
    commonN As = ArithmeticThetaLatticeSectionsR0188.commonN As := rfl
lemma normCount_eq (As : Matrices n h) :
    normCount As = ArithmeticThetaSharpKernelR0195.normCount As := rfl
lemma distinctNorms_eq (As : Matrices n h) :
    distinctNorms As = ArithmeticThetaSharpKernelR0195.norms As := rfl
lemma cutoff_eq (As : Matrices n h) :
    cutoff As = ArithmeticThetaSharpKernelR0195.cutoff As := rfl
lemma level_eq (N : ℕ) : level N = ArithmeticThetaCompactUnaryR0183.level N := rfl
lemma levelIndex_eq (L : ℕ) : levelIndex L = ArithmeticThetaLevelCount.levelIndex L := rfl
def fromOriginal (As : Matrices n h) (I : ArithmeticThetaSharpKernelR0195.NormIndex As) :
    NormIndex As where
  norm := I.norm
  index := I.index
def toOriginal (As : Matrices n h) (I : NormIndex As) :
    ArithmeticThetaSharpKernelR0195.NormIndex As where
  norm := I.norm
  index := I.index
lemma fromOriginal_indexed (As : Matrices n h) (I : ArithmeticThetaSharpKernelR0195.NormIndex As) :
    IndexesNorms As (fromOriginal As I) ↔ ArithmeticThetaSharpKernelR0195.IndexesNorms As I := Iff.rfl
lemma toOriginal_indexed (As : Matrices n h) (I : NormIndex As) :
    ArithmeticThetaSharpKernelR0195.IndexesNorms As (toOriginal As I) ↔ IndexesNorms As I := Iff.rfl
lemma to_fromOriginal (As : Matrices n h) (I : ArithmeticThetaSharpKernelR0195.NormIndex As) :
    toOriginal As (fromOriginal As I) = I := by cases I; rfl
lemma from_toOriginal (As : Matrices n h) (I : NormIndex As) :
    fromOriginal As (toOriginal As I) = I := by cases I; rfl
end ArithmeticThetaPalomarSharp349.Bridges
namespace ArithmeticThetaPalomarSharp349.Bridges
open ArithmeticThetaPalomarSharp349
variable {n h : ℕ} (A : Matrices n h)
lemma prefix_map_eq (hA : ∀ i, validGram (A i)) (B : ℕ) :
    (ArithmeticThetaComputed.prefixMap B).comp (thetaMap A) =
      ((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by
  rw [coefficientMatrix_complex_eq A hA B]
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
end ArithmeticThetaPalomarSharp349.Bridges
namespace ArithmeticThetaPalomarSharp349
/-- Exact sharp norm arithmetic and complete complex theta kernel, including
rank zero and every larger prefix, with no geometric existence assumption. -/
theorem explicitSharpFiniteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    (0 < n → 0 < normCount A ∧ ∃ I : NormIndex A, IndexesNorms A I ∧
      (∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ commonN A ∧
        8*I.norm i ∣ level (commonN A)) ∧
      (cutoff A : ℚ) ≤ (n : ℚ) * 2^(normCount A-1) *
        levelIndex (level (commonN A)) / (48*(level (commonN A) : ℚ)) ∧
      (n : ℚ) * 2^(normCount A-1) * levelIndex (level (commonN A)) /
        (48*(level (commonN A) : ℚ)) < (cutoff A : ℚ)+1) ∧
    (∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧
    (∀ B : ℕ, cutoff A ≤ B → ∀ c : Fin h → ℂ,
      thetaMap A c = 0 ↔ ∀ a : ℕ, a ≤ B → PowerSeries.coeff a (thetaMap A c) = 0) ∧
    (n = 0 → cutoff A = 0 ∧ ∀ c : Fin h → ℂ,
      thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  obtain ⟨hk, hz⟩ := ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel n h hh A hA
  have hkernel : ∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin) := by
    intro B hB
    rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B]
    exact hk B hB
  refine ⟨fun i a => Bridges.shell_finite (A i) (hA i) a, ?_, hkernel, ?_, ?_⟩
  · intro hn
    obtain ⟨hr, I, hI, hprops, hlo, hhi⟩ :=
      ArithmeticThetaSharpKernelR0195.distinct_norm_sharp_arithmetic n h hn hh A hA
    exact ⟨hr, Bridges.fromOriginal A I, (Bridges.fromOriginal_indexed A I).mpr hI,
      hprops, hlo, hhi⟩
  · intro B hB c
    exact Bridges.coefficients_iff_of_kernel A hA B (hkernel B hB) c
  · exact hz
end ArithmeticThetaPalomarSharp349
#print axioms ArithmeticThetaPalomarSharp349.explicitSharpFiniteDetermination
namespace ArithmeticThetaPalomarSharp349
theorem original046Correspondence :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → 0 < ArithmeticThetaSharpKernelR0195.normCount A ∧ ∃ I : ArithmeticThetaSharpKernelR0195.NormIndex A, ArithmeticThetaSharpKernelR0195.IndexesNorms A I ∧ (∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ ArithmeticThetaLatticeSectionsR0188.commonN A ∧ 8*I.norm i ∣ ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ∧ ((ArithmeticThetaSharpKernelR0195.cutoff A : ℕ) : ℚ) ≤ (n : ℚ) * 2^(ArithmeticThetaSharpKernelR0195.normCount A-1) * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / (48*(ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℚ)) ∧ (n : ℚ) * 2^(ArithmeticThetaSharpKernelR0195.normCount A-1) * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / (48*(ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℚ)) < (ArithmeticThetaSharpKernelR0195.cutoff A : ℚ)+1 := by
  intro n h hn hh A hA
  obtain ⟨hr, I, hI, hp, hlo, hhi⟩ :=
    (explicitSharpFiniteDetermination n h hh A hA).2.1 hn
  exact ⟨hr, Bridges.toOriginal A I, (Bridges.toOriginal_indexed A I).mpr hI,
    hp, hlo, hhi⟩
end ArithmeticThetaPalomarSharp349
#print axioms ArithmeticThetaPalomarSharp349.original046Correspondence
namespace ArithmeticThetaPalomarSharp349
theorem original049Correspondence :
∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧ ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  intro n h hh A hA
  have hs := explicitSharpFiniteDetermination n h hh A hA
  refine ⟨?_, hs.2.2.2.2⟩
  intro B hB
  have hk := hs.2.2.1 B hB
  rw [Bridges.thetaMap_eq A, Bridges.coefficientMatrix_complex_eq A hA B] at hk
  exact hk
end ArithmeticThetaPalomarSharp349
#print axioms ArithmeticThetaPalomarSharp349.original049Correspondence
end
end Package00
section Package01
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace ArithmeticThetaPalomarAdaptive348.Enumeration
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
end ArithmeticThetaPalomarAdaptive348.Enumeration
namespace ArithmeticThetaPalomarAdaptive348.Elimination
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
end ArithmeticThetaPalomarAdaptive348.Elimination
namespace ArithmeticThetaPalomarAdaptive348.Computed
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
def coefficientMatrix {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ)
    (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((ArithmeticThetaPalomarAdaptive348.Enumeration.coefficientsUpTo (A i) B).getD a.val 0 : ℚ)
noncomputable def thetaMap {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
noncomputable def prefixMap (B : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin (B+1) → ℂ) :=
  LinearMap.pi (fun a => PowerSeries.coeff a.val)
def selectedIndex {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (t : Fin (ArithmeticThetaPalomarAdaptive348.Elimination.run (coefficientMatrix A B)).pivots.length) : Fin h :=
  ((ArithmeticThetaPalomarAdaptive348.Elimination.run (coefficientMatrix A B)).pivots.get t).2
end ArithmeticThetaPalomarAdaptive348.Computed
namespace ArithmeticThetaPalomarAdaptive348.Orthogonal
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
def normSet {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : Finset ℕ :=
  Finset.univ.image (fun p : Fin h × Fin n => naturalNorms (A p.1) p.2)
def commonModulus {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (normSet A).lcm id
def level {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  24 * commonModulus A ^ 2
def normExponent {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (1 + 12 * commonModulus A) ^ 2 - 1
def distinctNormCount {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (normSet A).card
def Invariant {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Prop :=
  k ≤ n ∧ (∀ i j : Fin n, j < i → C i j = 0) ∧
    (∀ i : Fin n, 0 < C i i) ∧
    ∀ i j : Fin n, i.val < k → i ≠ j →
      pairing A (fun a => C a i) (fun a => C a j) = 0
end ArithmeticThetaPalomarAdaptive348.Orthogonal
namespace ArithmeticThetaPalomarAdaptive348.LDL
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
    ArithmeticThetaPalomarAdaptive348.Enumeration.normNumerator A x = 2 * (m : ℤ)
def coefficients {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : List ℕ :=
  let vectors := enumerate n (gramHalf A) B
  List.ofFn fun a : Fin (B+1) =>
    (vectors.filter fun x => ArithmeticThetaPalomarAdaptive348.Enumeration.normNumerator A x = 2 * (a.val : ℤ)).card
def coefficientMatrix {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((coefficients (A i) B).getD a.val 0 : ℚ)
end ArithmeticThetaPalomarAdaptive348.LDL
namespace ArithmeticThetaPalomarAdaptive348
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def indexValue (L : ℕ) : ℚ :=
  (L : ℚ)^3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹^2)
/-- Exact rational floor computed from the actual orthogonalization output. -/
def bound {n h : ℕ} (A : Matrices n h) : ℕ :=
  Int.toNat ⌊(n : ℚ) * 2^(ArithmeticThetaPalomarAdaptive348.Orthogonal.distinctNormCount A - 1) *
    indexValue (ArithmeticThetaPalomarAdaptive348.Orthogonal.level A) /
      (48 * (ArithmeticThetaPalomarAdaptive348.Orthogonal.level A : ℚ))⌋
def next (cap b : ℕ) : ℕ := min cap (max 1 (2*b))
def scheduleAux (cap : ℕ) : ℕ → ℕ → List ℕ
  | 0, b => [b]
  | fuel+1, b => if cap ≤ b then [cap] else b :: scheduleAux cap fuel (next cap b)
def schedule (cap : ℕ) : List ℕ := scheduleAux cap (cap+1) 0
/-- Columns are already established full-series relations. This predicate
never accepts finite-prefix agreement as evidence of a relation. -/
def Relations {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) : Prop :=
  ∀ j : Fin d, ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A (fun i => (R i j : ℂ)) = 0
def early {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) (B : ℕ) : Bool :=
  let rank := (ArithmeticThetaPalomarAdaptive348.Elimination.run
    (ArithmeticThetaPalomarAdaptive348.LDL.coefficientMatrix A B)).pivots.length
  rank == h || (ArithmeticThetaPalomarAdaptive348.Elimination.run R).pivots.length + rank == h
structure Result (h : ℕ) where
  cutoff : ℕ
  matrix : Matrix (Fin (cutoff+1)) (Fin h) ℚ
def assemble {n h : ℕ} (A : Matrices n h) (B : ℕ) : Result h :=
  ⟨B, ArithmeticThetaPalomarAdaptive348.LDL.coefficientMatrix A B⟩
def certify {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ)
    (B : ℕ) : Option (Result h) :=
  if early A R B then some (assemble A B) else none
/-- This entrypoint derives the cap internally. Its caller supplies no bound. -/
def solve {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) : Option (Result h) :=
  ((schedule (bound A)).find? (fun B => early A R B || B == bound A)).map (assemble A)
def nullVectors {h : ℕ} (o : Result h) := ArithmeticThetaPalomarAdaptive348.Elimination.nullBasis o.matrix
def pivotIndices {h : ℕ} (o : Result h) :
    Fin (ArithmeticThetaPalomarAdaptive348.Elimination.run o.matrix).pivots.length → Fin h :=
  fun t => ((ArithmeticThetaPalomarAdaptive348.Elimination.run o.matrix).pivots.get t).2
def coordinates {h : ℕ} (o : Result h) := ArithmeticThetaPalomarAdaptive348.Elimination.columnCoordinates o.matrix
/-- Complete facts about the actual returned matrix, null vectors, pivot
indices and coordinates, rather than a merely equal prefix's abstract rank. -/
def Correct {n h : ℕ} (A : Matrices n h) (o : Result h) : Prop :=
  o.matrix = ArithmeticThetaPalomarAdaptive348.LDL.coefficientMatrix A o.cutoff ∧
  LinearMap.ker (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A) =
    LinearMap.ker ((o.matrix.map (algebraMap ℚ ℂ)).mulVecLin) ∧
  (LinearIndependent ℂ (fun t => fun j => (nullVectors o t j : ℂ)) ∧
    Submodule.span ℂ (Set.range (fun t => fun j => (nullVectors o t j : ℂ))) =
      LinearMap.ker (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A)) ∧
  (LinearIndependent ℂ (fun t => ArithmeticThetaPalomarAdaptive348.Computed.theta (A (pivotIndices o t))) ∧
    Submodule.span ℂ (Set.range (fun t => ArithmeticThetaPalomarAdaptive348.Computed.theta (A (pivotIndices o t)))) =
      LinearMap.range (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A)) ∧
  ∀ j : Fin h,
    ArithmeticThetaPalomarAdaptive348.Computed.theta (A j) = ∑ t,
      (coordinates o j t : ℂ) • ArithmeticThetaPalomarAdaptive348.Computed.theta (A (pivotIndices o t)) ∧
    ∀ c : Fin (ArithmeticThetaPalomarAdaptive348.Elimination.run o.matrix).pivots.length → ℚ,
      ArithmeticThetaPalomarAdaptive348.Computed.theta (A j) = ∑ t,
        (c t : ℂ) • ArithmeticThetaPalomarAdaptive348.Computed.theta (A (pivotIndices o t)) →
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
end ArithmeticThetaPalomarAdaptive348
namespace ArithmeticThetaPalomarAdaptive348
namespace Bridges
abbrev O := ArithmeticThetaAdaptiveSolverR0230.Result
def fromState {m h : ℕ} (s : ArithmeticThetaElimination.State m h) : Elimination.State m h :=
  ⟨s.reduced, s.transform, s.nextRow, s.pivots⟩
lemma step_from {m h : ℕ} (s : ArithmeticThetaElimination.State m h) (c : Fin h) :
    Elimination.step (fromState s) c = fromState (ArithmeticThetaElimination.step s c) := by
  by_cases hr : s.nextRow < m
  · cases hp : ArithmeticThetaElimination.findPivot s.reduced s.nextRow c with
    | none => simp [Elimination.step, ArithmeticThetaElimination.step, fromState, hr,
        show Elimination.findPivot s.reduced s.nextRow c = none from hp, hp]
    | some t =>
      simp only [Elimination.step, ArithmeticThetaElimination.step, fromState, hr, dite_eq_left,
        show Elimination.findPivot s.reduced s.nextRow c = some t from hp, hp]
      rfl
  · simp [Elimination.step, ArithmeticThetaElimination.step, fromState, hr]
lemma fold_from {m h : ℕ} (xs : List (Fin h)) (s : ArithmeticThetaElimination.State m h) :
    xs.foldl Elimination.step (fromState s) =
      fromState (xs.foldl ArithmeticThetaElimination.step s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih => simp only [List.foldl_cons, step_from, ih]
lemma run_bridge {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
    Elimination.run A = fromState (ArithmeticThetaElimination.run A) := by
  exact fold_from (List.finRange h) (ArithmeticThetaElimination.initial A)
lemma enumerate_bridge (n : ℕ) (A : LDL.QMatrix n) (B : ℚ) :
    LDL.enumerate n A B = ArithmeticThetaLDLEnumerationR0229.enumerate n A B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LDL.enumerate, ArithmeticThetaLDLEnumerationR0229.enumerate, ih]
    rfl
lemma coefficients_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    LDL.coefficients A B = ArithmeticThetaLDLEnumerationR0229.coefficients A B := by
  simp only [LDL.coefficients, ArithmeticThetaLDLEnumerationR0229.coefficients, enumerate_bridge]
  rfl
lemma matrix_bridge {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    LDL.coefficientMatrix A B = ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B := by
  funext a i
  simp only [LDL.coefficientMatrix, ArithmeticThetaLDLEnumerationR0229.coefficientMatrix,
    coefficients_bridge]
lemma valid_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Computed.validGram A ↔ ArithmeticThetaComputed.validGram A := Iff.rfl
lemma theta_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Computed.theta A = ArithmeticThetaComputed.theta A := rfl
lemma thetaMap_bridge {n h : ℕ} (A : Matrices n h) :
    Computed.thetaMap A = ArithmeticThetaComputed.thetaMap A := rfl
lemma bound_bridge {n h : ℕ} (A : Matrices n h) :
    bound A = ArithmeticThetaAdaptiveSolverR0230.bound A := rfl
lemma relations_bridge {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) :
    Relations A R ↔ ArithmeticThetaAdaptiveSolverR0230.Relations A R := Iff.rfl
lemma scheduleAux_bridge (cap fuel b : ℕ) :
    scheduleAux cap fuel b = ArithmeticThetaAdaptiveSolverR0230.scheduleAux cap fuel b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
    simp only [scheduleAux, ArithmeticThetaAdaptiveSolverR0230.scheduleAux, ih]
    rfl
lemma schedule_bridge (cap : ℕ) :
    schedule cap = ArithmeticThetaAdaptiveSolverR0230.schedule cap := scheduleAux_bridge _ _ _
lemma early_bridge {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) (B : ℕ) :
    early A R B = ArithmeticThetaAdaptiveSolverR0230.early A R B := by
  simp only [early, ArithmeticThetaAdaptiveSolverR0230.early, matrix_bridge, run_bridge, fromState]
def fromResult {h : ℕ} (o : O h) : Result h := ⟨o.cutoff, o.matrix⟩
def toResult {h : ℕ} (o : Result h) : O h := ⟨o.cutoff, o.matrix⟩
lemma result_left {h : ℕ} (o : Result h) : fromResult (toResult o) = o := by cases o; rfl
lemma result_right {h : ℕ} (o : O h) : toResult (fromResult o) = o := by cases o; rfl
lemma assemble_bridge {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    assemble A B = fromResult (ArithmeticThetaAdaptiveSolverR0230.assemble A B) := by
  simp only [assemble, ArithmeticThetaAdaptiveSolverR0230.assemble, fromResult, matrix_bridge]
lemma solve_bridge {n h d : ℕ} (A : Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ) :
    solve A R = (ArithmeticThetaAdaptiveSolverR0230.solve A R).map fromResult := by
  simp only [solve, ArithmeticThetaAdaptiveSolverR0230.solve, schedule_bridge, bound_bridge,
    early_bridge, Option.map_map]
  congr 1
  funext B
  exact assemble_bridge A B
def correctWithState {n h : ℕ} (A : Matrices n h) (o : Result h)
    (s : Elimination.State (o.cutoff+1) h) : Prop :=
  o.matrix = ArithmeticThetaPalomarAdaptive348.LDL.coefficientMatrix A o.cutoff ∧
  LinearMap.ker (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A) =
    LinearMap.ker ((o.matrix.map (algebraMap ℚ ℂ)).mulVecLin) ∧
  (LinearIndependent ℂ (fun t => fun j => (Elimination.nullVector s ((Elimination.freeColumns s).get t) j : ℂ)) ∧
    Submodule.span ℂ (Set.range (fun t => fun j => (Elimination.nullVector s ((Elimination.freeColumns s).get t) j : ℂ))) =
      LinearMap.ker (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A)) ∧
  (LinearIndependent ℂ (fun t => ArithmeticThetaPalomarAdaptive348.Computed.theta (A ((s.pivots.get t).2))) ∧
    Submodule.span ℂ (Set.range (fun t => ArithmeticThetaPalomarAdaptive348.Computed.theta (A ((s.pivots.get t).2)))) =
      LinearMap.range (ArithmeticThetaPalomarAdaptive348.Computed.thetaMap A)) ∧
  ∀ j : Fin h,
    ArithmeticThetaPalomarAdaptive348.Computed.theta (A j) = ∑ t,
      (s.reduced (s.pivots.get t).1 j : ℂ) • ArithmeticThetaPalomarAdaptive348.Computed.theta (A ((s.pivots.get t).2)) ∧
    ∀ c : Fin (s).pivots.length → ℚ,
      ArithmeticThetaPalomarAdaptive348.Computed.theta (A j) = ∑ t,
        (c t : ℂ) • ArithmeticThetaPalomarAdaptive348.Computed.theta (A ((s.pivots.get t).2)) →
      c = (fun t => s.reduced (s.pivots.get t).1 j)
lemma correct_bridge {n h : ℕ} (A : Matrices n h) (o : O h) :
    Correct A (fromResult o) ↔ ArithmeticThetaAdaptiveSolverR0230.Correct A o := by
  rcases o with ⟨b, M⟩
  change correctWithState A ⟨b, M⟩ (Elimination.run M) ↔ _
  rw [run_bridge]
  simp only [correctWithState, ArithmeticThetaAdaptiveSolverR0230.Correct,
    fromResult, fromState, matrix_bridge, thetaMap_bridge, theta_bridge]
  rfl
def toChange {n h : ℕ} (c : Change n h) : ArithmeticThetaAdaptiveSolverR0230.Change n h :=
  ⟨c.left, c.right, c.matrix⟩
def fromChange {n h : ℕ} (c : ArithmeticThetaAdaptiveSolverR0230.Change n h) : Change n h :=
  ⟨c.left, c.right, c.matrix⟩
lemma change_left {n h : ℕ} (c : Change n h) : fromChange (toChange c) = c := by cases c; rfl
lemma change_right {n h : ℕ} (c : ArithmeticThetaAdaptiveSolverR0230.Change n h) :
    toChange (fromChange c) = c := by cases c; rfl
lemma checkChange_bridge {n h : ℕ} (A : Matrices n h) (c : Change n h) :
    checkChange A c = ArithmeticThetaAdaptiveSolverR0230.checkChange A (toChange c) := rfl
lemma changeRelations_heq {n h : ℕ} (A : Matrices n h) (cs : List (Change n h)) :
    HEq (changeRelations A cs)
      (ArithmeticThetaAdaptiveSolverR0230.changeRelations A (cs.map toChange)) := by
  apply (Fin.heq_fun₂_iff rfl (List.length_map (f := toChange)).symm).2
  intro i j
  simp only [changeRelations, ArithmeticThetaAdaptiveSolverR0230.changeRelations,
    List.get_eq_getElem, List.getElem_map]
  rfl
lemma relations_heq {n h d e : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (S : Matrix (Fin h) (Fin e) ℚ)
    (hd : d = e) (hr : HEq R S) :
    Relations A R ↔ ArithmeticThetaAdaptiveSolverR0230.Relations A S := by
  subst e
  cases eq_of_heq hr
  exact relations_bridge A R
lemma solve_heq {n h d e : ℕ} (A : Matrices n h)
    (R : Matrix (Fin h) (Fin d) ℚ) (S : Matrix (Fin h) (Fin e) ℚ)
    (hd : d = e) (hr : HEq R S) :
    solve A R = (ArithmeticThetaAdaptiveSolverR0230.solve A S).map fromResult := by
  subst e
  cases eq_of_heq hr
  exact solve_bridge A R
lemma solveChanges_bridge {n h : ℕ} (A : Matrices n h) (cs : List (Change n h)) :
    solveChanges A cs =
      (ArithmeticThetaAdaptiveSolverR0230.solveChanges A (cs.map toChange)).map fromResult := by
  exact solve_heq A _ _ (List.length_map (f := toChange)).symm (changeRelations_heq A cs)
end Bridges
end ArithmeticThetaPalomarAdaptive348
namespace ArithmeticThetaPalomarAdaptive348
theorem checked_basis_change_relations :
  ∀ (n h : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n h), ArithmeticThetaPalomarAdaptive348.Relations A (ArithmeticThetaPalomarAdaptive348.changeRelations A cs) := by
  intro n h A hv cs
  exact (Bridges.relations_heq A _ _ (List.length_map (f := Bridges.toChange)).symm
    (Bridges.changeRelations_heq A cs)).mpr
      (ArithmeticThetaAdaptiveSolverR0230.checked_basis_change_relations n h A hv
        (cs.map Bridges.toChange))
theorem adaptive_universal_solver :
  ∀ (n h d : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ArithmeticThetaPalomarAdaptive348.Relations A R → 0 < h → ∃ o : ArithmeticThetaPalomarAdaptive348.Result h, ArithmeticThetaPalomarAdaptive348.solve A R = some o ∧ o.cutoff ≤ ArithmeticThetaPalomarAdaptive348.bound A ∧ ArithmeticThetaPalomarAdaptive348.Correct A o ∧ o.cutoff ∈ ArithmeticThetaPalomarAdaptive348.schedule (ArithmeticThetaPalomarAdaptive348.bound A) ∧ (o.cutoff = ArithmeticThetaPalomarAdaptive348.bound A ∨ ArithmeticThetaPalomarAdaptive348.early A R o.cutoff = true) ∧ ∀ b ∈ ArithmeticThetaPalomarAdaptive348.schedule (ArithmeticThetaPalomarAdaptive348.bound A), b < o.cutoff → ArithmeticThetaPalomarAdaptive348.early A R b = false := by
  intro n h d A R hv hR hh
  obtain ⟨o, ho, hb, hc, hm, he, hf⟩ :=
    ArithmeticThetaAdaptiveSolverR0230.adaptive_universal_solver n h d A R hv hR hh
  refine ⟨Bridges.fromResult o, ?_, ?_, (Bridges.correct_bridge A o).mpr hc, ?_, ?_, ?_⟩
  · rw [Bridges.solve_bridge, ho]
    rfl
  · simpa only [Bridges.fromResult, Bridges.bound_bridge] using hb
  · simpa only [Bridges.fromResult, Bridges.schedule_bridge, Bridges.bound_bridge] using hm
  · simpa only [Bridges.fromResult, Bridges.early_bridge, Bridges.bound_bridge] using he
  · simpa only [Bridges.fromResult, Bridges.schedule_bridge, Bridges.bound_bridge,
      Bridges.early_bridge] using hf
theorem adaptive_checked_input :
  ∀ (n h : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → 0 < h → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n h), ∃ o : ArithmeticThetaPalomarAdaptive348.Result h, ArithmeticThetaPalomarAdaptive348.solveChanges A cs = some o ∧ o.cutoff ≤ ArithmeticThetaPalomarAdaptive348.bound A ∧ ArithmeticThetaPalomarAdaptive348.Correct A o := by
  intro n h A hv hh cs
  obtain ⟨o, ho, hb, hc⟩ :=
    ArithmeticThetaAdaptiveSolverR0230.adaptive_checked_input n h A hv hh (cs.map Bridges.toChange)
  refine ⟨Bridges.fromResult o, ?_, ?_, (Bridges.correct_bridge A o).mpr hc⟩
  · rw [Bridges.solveChanges_bridge, ho]
    rfl
  · simpa only [Bridges.fromResult, Bridges.bound_bridge] using hb
theorem adaptive_singleton_zero :
  ∀ (n : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n 1), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n 1), ArithmeticThetaPalomarAdaptive348.solveChanges A cs = some (ArithmeticThetaPalomarAdaptive348.assemble A 0) ∧ ArithmeticThetaPalomarAdaptive348.Correct A (ArithmeticThetaPalomarAdaptive348.assemble A 0) := by
  intro n A hv cs
  obtain ⟨hs, hc⟩ := ArithmeticThetaAdaptiveSolverR0230.adaptive_singleton_zero
    n A hv (cs.map Bridges.toChange)
  constructor
  · rw [Bridges.solveChanges_bridge, hs, Bridges.assemble_bridge]
    rfl
  · rw [Bridges.assemble_bridge]
    exact (Bridges.correct_bridge A _).mpr hc
end ArithmeticThetaPalomarAdaptive348
end Package01
section Package02
set_option autoImplicit false
namespace ArithmeticThetaPalomarImage350
/-- Exact original certificate consequence: null basis, image basis and unique rational coordinates. -/
theorem certifiedImage :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ W : Submodule ℂ (Fin h → ℂ), W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j := by
  exact ArithmeticThetaDegreeAssembly.certified_theta_image_data
theorem shellFinite (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ArithmeticThetaComputed.validGram A) (a : ℕ) :
    Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (a : ℚ)} := by
  exact (ArithmeticThetaLattice.exact_shell_finite n _ hA.2.2 (a : ℚ)).to_subtype
end ArithmeticThetaPalomarImage350
end Package02
