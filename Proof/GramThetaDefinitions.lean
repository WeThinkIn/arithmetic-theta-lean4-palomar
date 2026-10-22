module

public import Rank16Definitions
public import Rank16LatticeDefinitions
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace ArithmeticThetaRank16Gram

abbrev GramShell (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) :=
  {z : Fin n → ℤ // z ⬝ᵥ G.mulVec z = 2*(m : ℤ)}

noncomputable def gramTheta (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (GramShell n G m) : ℤ))

def split (z : Fin 16 → ℤ) : (Fin 8 → ℤ) × (Fin 8 → ℤ) :=
  (fun i => z (i.castAdd 8), fun i => z (Fin.natAdd 8 i))

def join (p : (Fin 8 → ℤ) × (Fin 8 → ℤ)) : Fin 16 → ℤ :=
  fun i => Fin.addCases (m := 8) (n := 8) p.1 p.2 i

def sumDoubled (z : Fin 16 → ℤ) : (Fin 8 → ℤ) × (Fin 8 → ℤ) :=
  ((ArithmeticThetaRank16.doubledBasis 8).mulVec (split z).1,
    (ArithmeticThetaRank16.doubledBasis 8).mulVec (split z).2)

def sumCoordinates (p : (Fin 8 → ℤ) × (Fin 8 → ℤ)) : Fin 16 → ℤ :=
  join (ArithmeticThetaRank16.basisCoordinates 8 p.1,
    ArithmeticThetaRank16.basisCoordinates 8 p.2)

def actualForms : Fin 2 → Matrix (Fin 16) (Fin 16) ℤ :=
  ![ArithmeticThetaRank16.sumGram, ArithmeticThetaRank16.latticeGram 16]

noncomputable def actualColumns : Fin 2 → PowerSeries ℂ :=
  fun i => PowerSeries.map (Int.castRingHom ℂ) (gramTheta 16 (actualForms i))

noncomputable def thetaMap : (Fin 2 → ℂ) →ₗ[ℂ] PowerSeries ℂ where
  toFun v := ∑ i, v i • actualColumns i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [smul_smul]

end ArithmeticThetaRank16Gram
