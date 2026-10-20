module
public import Mathlib
public import ShiftedIntegerIntervalR0229
public import RationalSchurCompletionR0229
public import ComputedRationalLDLR0229
public import RecursiveEllipsoidEnumerationR0229
public import LDLThetaPrefixR0229

@[expose] public section
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
