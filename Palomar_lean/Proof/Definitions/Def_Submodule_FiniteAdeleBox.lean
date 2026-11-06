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
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

def finiteAdeleBox (Λ : Submodule ℤ D) : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] a}

def ofFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

def finiteIdeleStabilizer (Λ : Submodule ℤ D) : Subgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  MulAction.stabilizer (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
    ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))

def conjByFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
          (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

variable (D) in

def finiteIdeleDiagonal : Dˣ →* (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    D →+* D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom

@[simp] theorem val_finiteIdeleDiagonal_apply (d : Dˣ) :
    ((finiteIdeleDiagonal D d : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem mem_ofFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ ofFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ conjByFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
  Iff.rfl

theorem mem_finiteIdeleStabilizer_iff (Λ : Submodule ℤ D) (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ finiteIdeleStabilizer Λ ↔
      u • ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
        = ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

end Submodule

end
