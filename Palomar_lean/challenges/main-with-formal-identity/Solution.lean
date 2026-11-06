module

public import Mathlib
public import OrthogonalConsumerDefinitionsR0127
public import ComputedCoefficientMatrix
public import LatticeShellFinite
public import GlobalizationDefinitions
public import ComputedBoundParameters
public import FiniteFullLevelCount
public import LatticeGlobalSectionsDefinitionsR0188
public import ConservativeMatrixKernelR0189

@[expose] public section

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
