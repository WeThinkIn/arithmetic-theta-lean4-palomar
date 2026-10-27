import Mathlib

namespace ArithmeticThetaRank16

abbrev Vec (n : ℕ) := Fin n → ℤ

def DPlusDoubled (n : ℕ) (y : Vec n) : Prop :=
  ((∀ i, y i % 2 = 0) ∨ (∀ i, y i % 2 = 1)) ∧ (∑ i, y i) % 4 = 0

def normNumerator (n : ℕ) (y : Vec n) : ℤ := ∑ i, y i ^ 2

abbrev NormShell (n m : ℕ) :=
  {y : Vec n // DPlusDoubled n y ∧ normNumerator n y = (m : ℤ)}

abbrev SumNormShell (m : ℕ) :=
  {y : Vec 8 × Vec 8 // DPlusDoubled 8 y.1 ∧ DPlusDoubled 8 y.2 ∧
    normNumerator 8 y.1 + normNumerator 8 y.2 = (m : ℤ)}

noncomputable def normSeries (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (NormShell n m) : ℤ))

noncomputable def sumNormSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (SumNormShell m) : ℤ))

noncomputable def theta (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (NormShell n (8*m)) : ℤ))

noncomputable def sumTheta : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (SumNormShell (8*m)) : ℤ))

noncomputable def columns : Fin 2 → PowerSeries ℂ :=
  ![PowerSeries.map (Int.castRingHom ℂ) sumTheta,
    PowerSeries.map (Int.castRingHom ℂ) (theta 16)]

end ArithmeticThetaRank16
