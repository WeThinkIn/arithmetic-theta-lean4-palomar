module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

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
