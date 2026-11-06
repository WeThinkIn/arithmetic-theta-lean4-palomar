module
public import Mathlib
public import Rank16Nonisometry
public import Rank16Theta
public import GeneralDPlusEvenUnimodularR0242
public import GeneralDPlusDualR0242
public import GeneralDPlusThetaRealizationR0242

@[expose] public section
set_option autoImplicit false

namespace ArithmeticThetaPalomarRank16_260.Rank16

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

end ArithmeticThetaPalomarRank16_260.Rank16

namespace ArithmeticThetaPalomarRank16_260.Rank16

def latticeBasis (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if j.val = 0 then 1/2
  else if j.val = n-1 then (if i.val = n-1 then 2 else 0)
  else if i = j then 1 else if i.val = n-1 then -1 else 0

def doubledBasis (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if j.val = 0 then 1
  else if j.val = n-1 then (if i.val = n-1 then 4 else 0)
  else if i = j then 2 else if i.val = n-1 then -2 else 0

def latticeGram (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.val = 0 then
    (if j.val = 0 then (n/4 : ℕ) else if j.val = n-1 then 1 else 0)
  else if j.val = 0 then (if i.val = n-1 then 1 else 0)
  else if i.val = n-1 then (if j.val = n-1 then 4 else -2)
  else if j.val = n-1 then -2
  else if i = j then 2 else 1

def sumBasis : Matrix (Fin 16) (Fin 16) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (latticeBasis 8) 0 0 (latticeBasis 8))

def sumGram : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (latticeGram 8) 0 0 (latticeGram 8))

def originalDPlus (n : ℕ) (v : Fin n → ℚ) : Prop :=
  (∃ x : Fin n → ℤ, (∑ i, x i) % 2 = 0 ∧ ∀ i, v i = x i) ∨
  (∃ x : Fin n → ℤ, (∑ i, x i) % 2 = 0 ∧ ∀ i, v i = x i + 1/2)

def doubledRealization (n : ℕ) (y : Fin n → ℤ) : Fin n → ℚ :=
  fun i => (y i : ℚ)/2

def basisCoordinates (n : ℕ) (y : Fin n → ℤ) : Fin n → ℤ := fun j =>
  if hj : j.val = 0 then y j
  else if j.val = n-1 then
    ((∑ i, y i) - (n : ℤ) * y ⟨0, by omega⟩) / 4
  else (y j - y ⟨0, by omega⟩) / 2

end ArithmeticThetaPalomarRank16_260.Rank16

namespace ArithmeticThetaPalomarRank16_260.GeneralDPlus

def lattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range (fun j : Fin n =>
    fun i : Fin n => ArithmeticThetaPalomarRank16_260.Rank16.latticeBasis n i j))

def dualMember (n : ℕ) (v : Fin n → ℚ) : Prop :=
  ∀ w : lattice n, ∃ z : ℤ, (∑ i, v i * w.val i) = (z : ℚ)

abbrev OriginalShell (n m : ℕ) :=
  {v : Fin n → ℚ // ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v ∧
    (∑ i, v i ^ 2) / 2 = (m : ℚ)}

noncomputable def originalTheta (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (OriginalShell n m) : ℤ))

end ArithmeticThetaPalomarRank16_260.GeneralDPlus

namespace ArithmeticThetaPalomarRank16_260.Computed
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef

noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))


end ArithmeticThetaPalomarRank16_260.Computed

namespace ArithmeticThetaPalomarRank16_260.Hadamard
noncomputable def a : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ)} : ℤ))
noncomputable def b : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 0} : ℤ) -
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 1} : ℤ))
noncomputable def c : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // (2 * r + 1) ^ 2 = (m : ℤ)} : ℤ))

end ArithmeticThetaPalomarRank16_260.Hadamard

namespace ArithmeticThetaPalomarRank16_260

/-- Exact independent target for accepted-014. -/
theorem no_similarity :
  ¬ ∃ (s : ℚ) (U : Matrix (Fin 16) (Fin 16) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (ArithmeticThetaPalomarRank16_260.Rank16.sumGram).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram 16).map (Int.castRingHom ℚ) := by
  exact ArithmeticThetaRank16.no_similarity

/-- Exact independent target for accepted-015. -/
theorem integral_identity :
  ArithmeticThetaPalomarRank16_260.Rank16.sumTheta = ArithmeticThetaPalomarRank16_260.Rank16.theta 16 := by
  exact ArithmeticThetaRank16.integral_identity

/-- Exact independent target for accepted-016. -/
theorem two_column_kernel :
  ∀ v : Fin 2 → ℂ, (∑ i, v i • ArithmeticThetaPalomarRank16_260.Rank16.columns i) = 0 ↔ ∃ t : ℂ, v = ![t, -t] := by
  exact ArithmeticThetaRank16.two_column_kernel

/-- Exact independent target for accepted-077. -/
theorem general_dplus_even_unimodular :
  ∀ n : ℕ, 8 ∣ n → ArithmeticThetaPalomarRank16_260.Computed.validGram (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n) ∧ (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n).det = 1 ∧ (∀ v : Fin n → ℚ, v ∈ ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n ↔ ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v) ∧ (∃ b : Module.Basis (Fin n) ℤ (ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n), ∀ (j i : Fin n), (b j).val i = ArithmeticThetaPalomarRank16_260.Rank16.latticeBasis n i j) ∧ (∀ v : Fin n → ℚ, ArithmeticThetaPalomarRank16_260.Rank16.originalDPlus n v → ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ)) := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular

/-- Exact independent target for accepted-078. -/
theorem general_dplus_dual :
  ∀ n : ℕ, 8 ∣ n → ∀ v : Fin n → ℚ, ArithmeticThetaPalomarRank16_260.GeneralDPlus.dualMember n v ↔ v ∈ ArithmeticThetaPalomarRank16_260.GeneralDPlus.lattice n := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_dual

/-- Exact independent target for accepted-079. -/
theorem general_dplus_theta_realization :
  ∀ n : ℕ, 8 ∣ n → (∀ m : ℕ, ∃ e : ArithmeticThetaPalomarRank16_260.GeneralDPlus.OriginalShell n m ≃ ArithmeticThetaPalomarRank16_260.Rank16.NormShell n (8 * m), ∀ v, ArithmeticThetaPalomarRank16_260.Rank16.doubledRealization n (e v).val = v.val) ∧ ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n = ArithmeticThetaPalomarRank16_260.Rank16.theta n ∧ ArithmeticThetaPalomarRank16_260.Computed.theta (ArithmeticThetaPalomarRank16_260.Rank16.latticeGram n) = PowerSeries.map (Int.castRingHom ℂ) (ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n) ∧ (0 < n → (2 : PowerSeries ℤ) * PowerSeries.expand 8 (by decide) (ArithmeticThetaPalomarRank16_260.GeneralDPlus.originalTheta n) = ArithmeticThetaPalomarRank16_260.Hadamard.a ^ n + ArithmeticThetaPalomarRank16_260.Hadamard.b ^ n + ArithmeticThetaPalomarRank16_260.Hadamard.c ^ n) := by
  exact ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization

end ArithmeticThetaPalomarRank16_260
#print axioms ArithmeticThetaPalomarRank16_260.no_similarity
#print axioms ArithmeticThetaPalomarRank16_260.integral_identity
#print axioms ArithmeticThetaPalomarRank16_260.two_column_kernel
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_even_unimodular
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_dual
#print axioms ArithmeticThetaPalomarRank16_260.general_dplus_theta_realization
