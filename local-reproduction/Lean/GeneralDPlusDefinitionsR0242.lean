import Rank16Theta
import Rank16Basis
import Rank16Coordinates
import Rank16Unimodular
import GramThetaShells
import IntegrationDefinitions

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
