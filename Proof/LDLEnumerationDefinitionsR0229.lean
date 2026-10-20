module

public import ComputedCoefficientMatrix

@[expose] public section

/-! Exact rational completion-of-squares enumeration. All correctness claims
are separate worker obligations. These definitions use only executable rational,
integer, finite-set and matrix operations. -/
set_option autoImplicit false
namespace ArithmeticThetaLDLEnumerationR0229

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
    ArithmeticThetaEnumeration.normNumerator A x = 2 * (m : ℤ)

def coefficients {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : List ℕ :=
  let vectors := enumerate n (gramHalf A) B
  List.ofFn fun a : Fin (B+1) =>
    (vectors.filter fun x => ArithmeticThetaEnumeration.normNumerator A x = 2 * (a.val : ℤ)).card

def coefficientMatrix {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => ((coefficients (A i) B).getD a.val 0 : ℚ)

end ArithmeticThetaLDLEnumerationR0229
