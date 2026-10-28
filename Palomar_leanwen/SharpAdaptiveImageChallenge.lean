module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
section Package00
set_option autoImplicit false
noncomputable section
/-! Mathlib-only sharp-bound challenge covering original accepted-046 and
accepted-049. The single sorry is the challenge placeholder. Geometric outputs
accepted-047/048 are separate requirements and are not claimed by this package.
Neither covered original endpoint has a FormalIdentity output. -/
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
  sorry
end ArithmeticThetaPalomarSharp349
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
theorem checked_basis_change_relations :
  ∀ (n h : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n h), ArithmeticThetaPalomarAdaptive348.Relations A (ArithmeticThetaPalomarAdaptive348.changeRelations A cs) := by
  sorry
theorem adaptive_universal_solver :
  ∀ (n h d : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ArithmeticThetaPalomarAdaptive348.Relations A R → 0 < h → ∃ o : ArithmeticThetaPalomarAdaptive348.Result h, ArithmeticThetaPalomarAdaptive348.solve A R = some o ∧ o.cutoff ≤ ArithmeticThetaPalomarAdaptive348.bound A ∧ ArithmeticThetaPalomarAdaptive348.Correct A o ∧ o.cutoff ∈ ArithmeticThetaPalomarAdaptive348.schedule (ArithmeticThetaPalomarAdaptive348.bound A) ∧ (o.cutoff = ArithmeticThetaPalomarAdaptive348.bound A ∨ ArithmeticThetaPalomarAdaptive348.early A R o.cutoff = true) ∧ ∀ b ∈ ArithmeticThetaPalomarAdaptive348.schedule (ArithmeticThetaPalomarAdaptive348.bound A), b < o.cutoff → ArithmeticThetaPalomarAdaptive348.early A R b = false := by
  sorry
theorem adaptive_checked_input :
  ∀ (n h : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n h), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → 0 < h → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n h), ∃ o : ArithmeticThetaPalomarAdaptive348.Result h, ArithmeticThetaPalomarAdaptive348.solveChanges A cs = some o ∧ o.cutoff ≤ ArithmeticThetaPalomarAdaptive348.bound A ∧ ArithmeticThetaPalomarAdaptive348.Correct A o := by
  sorry
theorem adaptive_singleton_zero :
  ∀ (n : ℕ) (A : ArithmeticThetaPalomarAdaptive348.Matrices n 1), (∀ i, ArithmeticThetaPalomarAdaptive348.Computed.validGram (A i)) → ∀ cs : List (ArithmeticThetaPalomarAdaptive348.Change n 1), ArithmeticThetaPalomarAdaptive348.solveChanges A cs = some (ArithmeticThetaPalomarAdaptive348.assemble A 0) ∧ ArithmeticThetaPalomarAdaptive348.Correct A (ArithmeticThetaPalomarAdaptive348.assemble A 0) := by
  sorry
end ArithmeticThetaPalomarAdaptive348
end Package01
section Package02
set_option autoImplicit false
namespace ArithmeticThetaEnumeration
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
end ArithmeticThetaEnumeration
namespace ArithmeticThetaElimination
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
end ArithmeticThetaElimination
namespace ArithmeticThetaComputed
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
def coefficientMatrix {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ)
    (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((ArithmeticThetaEnumeration.coefficientsUpTo (A i) B).getD a.val 0 : ℚ)
noncomputable def thetaMap {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
noncomputable def prefixMap (B : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin (B+1) → ℂ) :=
  LinearMap.pi (fun a => PowerSeries.coeff a.val)
def selectedIndex {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (t : Fin (ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.length) : Fin h :=
  ((ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.get t).2
end ArithmeticThetaComputed
namespace ArithmeticThetaPalomarImage350
/-- Exact original certificate consequence: null basis, image basis and unique rational coordinates. -/
theorem certifiedImage :
    ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ W : Submodule ℂ (Fin h → ℂ), W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j := by
  sorry
theorem shellFinite (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ArithmeticThetaComputed.validGram A) (a : ℕ) :
    Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (a : ℚ)} := by
  sorry
end ArithmeticThetaPalomarImage350
end Package02
