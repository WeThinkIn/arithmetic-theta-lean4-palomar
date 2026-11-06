module

public import ComputedOrthogonalization
public import CosetThetaFactorization
public import IntegrationDefinitions
public import FormalSchrodingerDefinitionsR0119
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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

/-! Actual rational preimage lattice, its integral periods, and complete series.
These definitions add no geometric section or finite stopping assumption. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaOrthogonalConsumerR0127

def castVec (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℚ) where
  toFun x := fun j => (x j : ℚ)
  map_zero' := by ext j; simp
  map_add' := by intro x y; ext j; simp

def integerVectors (n : ℕ) : AddSubgroup (Fin n → ℚ) := (castVec n).range

def preimageLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    AddSubgroup (Fin n → ℚ) :=
  (integerVectors n).comap (B.map (Int.castRingHom ℚ)).mulVecLin.toAddMonoidHom

def periods {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    AddSubgroup (preimageLattice B) :=
  (integerVectors n).comap (preimageLattice B).subtype

abbrev RationalCosets {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :=
  (preimageLattice B) ⧸ periods B

def cosetClass {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : preimageLattice B) : RationalCosets B := QuotientAddGroup.mk t

def Representatives {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Fin B.det.natAbs → preimageLattice B) : Prop :=
  Function.Bijective (fun i => cosetClass B (t i))

def OrthogonalData {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℕ) : Prop :=
  B.det ≠ 0 ∧ (∀ j, 0 < m j ∧ Even (m j)) ∧
    B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ))

def thetaZ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (castVec n x) = (a : ℚ)} : ℤ)

def cosetSeries {n : ℕ} (m : Fin n → ℕ) (t : Fin n → ℚ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {x : Fin n → ℤ //
    (∑ j, (m j : ℚ) / 2 * (t j + (x j : ℚ))^2) = (a : ℚ)} : ℤ)

def scaledUnary (m w : ℕ) (ν : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun a => (Nat.card {r : ℤ //
    Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r^2 = (a : ℤ)} : ℤ)

end ArithmeticThetaOrthogonalConsumerR0127
