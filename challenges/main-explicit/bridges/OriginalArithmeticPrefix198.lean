module
public import OrthogonalConsumerDefinitionsR0127
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaOrthogonalAlgorithm ArithmeticThetaOrthogonalConsumerR0127
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


end ArithmeticThetaLatticeSectionsR0188
