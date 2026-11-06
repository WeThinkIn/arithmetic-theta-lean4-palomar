module

public import Rank16Theta
public import Rank16Basis
public import Rank16Coordinates
public import Rank16Unimodular
public import GramThetaShells
public import IntegrationDefinitions
public import Rank16LatticeDefinitions
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

set_option autoImplicit false

namespace ArithmeticThetaGeneralDPlusR0242

def lattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range (fun j : Fin n =>
    fun i : Fin n => ArithmeticThetaRank16.latticeBasis n i j))

def dualMember (n : ℕ) (v : Fin n → ℚ) : Prop :=
  ∀ w : lattice n, ∃ z : ℤ, (∑ i, v i * w.val i) = (z : ℚ)

abbrev OriginalShell (n m : ℕ) :=
  {v : Fin n → ℚ // ArithmeticThetaRank16.originalDPlus n v ∧
    (∑ i, v i ^ 2) / 2 = (m : ℚ)}

noncomputable def originalTheta (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (OriginalShell n m) : ℤ))

end ArithmeticThetaGeneralDPlusR0242
