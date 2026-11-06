module

public import UnaryThetaProducts
public import TateSeriesDefinitions
public import Mathlib.Tactic.ReduceModChar
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! Literal formal theta coefficients in t=q^(1/(2m)). These are formal
solutions and their valued-field evaluations, not algebraic sections on a curve.
The later geometric realization and theta-structure provider remain open. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

abbrev K (k : Type u) [Zero k] := LaurentSeries k
abbrev Coefficients (k : Type u) [Zero k] := ℤ → K k

def monomial (k : Type u) [Field k] (n : ℤ) : K k := HahnSeries.single n 1

def scalar (k : Type u) [Field k] (a : k) : K k := HahnSeries.single 0 a

def Solutions (k : Type u) [Field k] (m : ℕ) :
    Submodule (K k) (Coefficients k) where
  carrier := {f | ∀ r : ℤ, f (r + m) = monomial k (2 * (m : ℤ) * r + (m : ℤ)^2) * f r}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg r
    simpa only [Pi.add_apply, mul_add] using congrArg₂ (· + ·) (hf r) (hg r)
  smul_mem' := by
    intro a f hf r
    change a * f (r + m) = monomial k (2 * (m : ℤ) * r + (m : ℤ)^2) * (a * f r)
    rw [hf r]
    ring

def theta (k : Type u) [Field k] (m : ℕ) (ν : Fin m) : Coefficients k :=
  fun r => if Int.ModEq (m : ℤ) r (ν.val : ℤ) then monomial k (r^2) else 0

def synth (k : Type u) [Field k] (m : ℕ) (v : Fin m → K k) : Coefficients k :=
  ∑ ν : Fin m, v ν • theta k m ν

def A (k : Type u) [Field k] (ζ : k) (f : Coefficients k) : Coefficients k :=
  fun r => scalar k (ζ ^ r) * f r

def B (k : Type u) [Field k] (f : Coefficients k) : Coefficients k :=
  fun r => monomial k (2*r-1) * f (r-1)

def BInv (k : Type u) [Field k] (f : Coefficients k) : Coefficients k :=
  fun r => monomial k (-2*r-1) * f (r+1)

def inversion (k : Type u) [Zero k] (f : Coefficients k) : Coefficients k := fun r => f (-r)

def next (m : ℕ) [NeZero m] (ν : Fin m) : Fin m :=
  ⟨(ν.val+1)%m, Nat.mod_lt _ (NeZero.pos m)⟩
def prev (m : ℕ) [NeZero m] (ν : Fin m) : Fin m :=
  ⟨(ν.val+m-1)%m, Nat.mod_lt _ (NeZero.pos m)⟩

def standardA (k : Type u) [Field k] (m : ℕ) (ζ : k) (v : Fin m → K k) : Fin m → K k :=
  fun ν => scalar k (ζ ^ ν.val) * v ν

def standardB (k : Type u) [Field k] (m : ℕ) [NeZero m] (v : Fin m → K k) : Fin m → K k :=
  fun ν => v (prev m ν)

def delta (k : Type u) [Field k] (m : ℕ) (ν : Fin m) : Fin m → K k :=
  fun μ => if μ = ν then 1 else 0

/-- The terms obtained by substituting z=x*t^j, including negative j. -/
def annularTerms (k : Type u) [Field k] (f : Coefficients k) (j : ℤ) (x : kˣ) : ℤ → K k :=
  fun r => f r * HahnSeries.single (j*r) ((x : k)^r)

def evaluate (k : Type u) [Field k] (f : Coefficients k) (j : ℤ) (x : kˣ) : K k :=
  ∑' r : ℤ, annularTerms k f j x r

/-- Same exact residue-shell counts as the accepted unary product theorem,
with denominator 2m cleared by the specified t. -/
def unary (k : Type u) [Field k] (m : ℕ) (ν : Fin m) : PowerSeries k :=
  PowerSeries.mk fun n => (Nat.card {r : ℤ // Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2 = (n : ℤ)} : k)

/-- The source's Schrödinger comparison hypotheses, only at the formal stage.
Existence from actual algebraic sections is NOT included or assumed elsewhere. -/
def Intertwines (k : Type u) [Field k] (m : ℕ) [NeZero m] (ζ : k)
    (F : (Fin m → K k) →ₗ[K k] Coefficients k) : Prop :=
  Function.Injective F ∧ (∀ v, F v ∈ Solutions k m) ∧
  (∀ v, F (standardA k m ζ v) = A k ζ (F v)) ∧
  (∀ v, F (standardB k m v) = B k (F v))
end ArithmeticThetaSchrodingerR0119
