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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

def residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) : v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in

def evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dif_pos hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end Place

namespace Divisor

def evalFun (f : F) (D : Divisor K F) : K :=
  D.prod fun v n => v.evalAt f ^ n

theorem evalFun_def (f : F) (D : Divisor K F) :
    evalFun f D = ∏ v ∈ D.support, v.evalAt f ^ D v := rfl

@[simp]
theorem evalFun_zero (f : F) : evalFun f (0 : Divisor K F) = 1 :=
  Finsupp.prod_zero_index

theorem evalFun_single (f : F) (v : Place K F) (n : ℤ) :
    evalFun f (Finsupp.single v n) = v.evalAt f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

end Divisor

variable (K F) in

def WeilReciprocity : Prop :=
  ∀ (f g : F) (Df Dg : Divisor K F), f ≠ 0 → g ≠ 0 →
    (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) →
    (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
    (∀ v ∈ Df.support, Place.IsRational v) → (∀ v ∈ Dg.support, Place.IsRational v) →
    Divisor.evalFun f Dg = Divisor.evalFun g Df

end AlgebraicCurve
