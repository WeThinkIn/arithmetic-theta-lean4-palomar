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
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ArithmeticThetaBinary

def gram (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2*a, b; b, 2*c]

def gramContent (a b c : ℤ) : ℕ := Nat.gcd (Int.gcd (2*a) b) (Int.natAbs (2*c))

def shear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, k; 0, 1]

def forms : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![gram 1 0 20, gram 3 2 7, gram 4 0 5]

def value (j : Fin 3) (x : Fin 2 → ℤ) : ℤ :=
  (![x 0 ^ 2 + 20*x 1 ^ 2, 3*x 0 ^ 2 + 2*x 0*x 1 + 7*x 1 ^ 2,
    4*x 0 ^ 2 + 5*x 1 ^ 2] : Fin 3 → ℤ) j

def embeddings : Fin 3 → Matrix (Fin 2) (Fin 2) ℚ :=
  ![1, !![3, 1; 0, 1], !![2, 0; 0, 1/2]]

def sameLocalSmith (a b c : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ U V : Matrix (Fin 2) (Fin 2) (PadicInt p),
    IsUnit U.det ∧ IsUnit V.det ∧
      U * (gram a b c).map (Int.castRingHom (PadicInt p)) * V =
        (gram 1 0 20).map (Int.castRingHom (PadicInt p))

end ArithmeticThetaBinary
