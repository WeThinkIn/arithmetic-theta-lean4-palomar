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
public import Mathlib.Algebra.Quaternion
public import Mathlib.Topology.Sheaves.Init
public import Definitions.Def_Submodule_FiniteAdeleBox
public import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

instance instAlgebraRatAdicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v

instance instModuleRatAdicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : Module ℚ (v.adicCompletion ℚ) :=
  Algebra.toModule

end IsDedekindDomain.HeightOneSpectrum

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

variable (D) in

def finiteAdeleEvalAlgHom (v : HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] v.adicCompletion ℚ :=
  { RestrictedProduct.evalRingHom
      (fun w : HeightOneSpectrum (𝓞 ℚ) => w.adicCompletion ℚ) v with
    commutes' := fun _ => rfl }

variable (D) in

def finiteAdeleEvalAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] D ⊗[ℚ] v.adicCompletion ℚ :=
  Algebra.TensorProduct.map (AlgHom.id ℚ D) (finiteAdeleEvalAlgHom v)

def localBox (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    AddSubgroup (D ⊗[ℚ] v.adicCompletion ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

def localBoxUnits (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set (D ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {u | (u : D ⊗[ℚ] v.adicCompletion ℚ) ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) ∧
    ((u⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)
      ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ))}

@[simp] theorem finiteAdeleEvalAt_tmul (v : HeightOneSpectrum (𝓞 ℚ)) (z : D)
    (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    finiteAdeleEvalAt D v (z ⊗ₜ[ℚ] a) = z ⊗ₜ[ℚ] (a v) := rfl

theorem finiteAdeleEvalAlgHom_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    finiteAdeleEvalAlgHom v a = a v := rfl

theorem mem_localBoxUnits_iff (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ localBoxUnits Λ v ↔
      (u : D ⊗[ℚ] v.adicCompletion ℚ) ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) ∧
        ((u⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)
          ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) :=
  Iff.rfl

end Submodule

namespace QuaternionAlgebra

variable {a b : ℚ}

def localQuadSubring (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Subring (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  Subring.closure
    ({α ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)} ∪
      Set.range (fun r : v.adicCompletion ℚ => (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r))

def localQuadUnits (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ where
  carrier := {u | (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ localQuadSubring α v ∧
    ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      ∈ localQuadSubring α v}
  one_mem' :=
    ⟨by rw [Units.val_one]; exact (localQuadSubring α v).one_mem,
     by rw [inv_one, Units.val_one]; exact (localQuadSubring α v).one_mem⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨by rw [Units.val_mul]; exact (localQuadSubring α v).mul_mem hx.1 hy.1,
     by rw [mul_inv_rev, Units.val_mul]; exact (localQuadSubring α v).mul_mem hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

def localEmbeddingSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {β | ∀ y ∈ localQuadSubring α v,
    ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * β
        ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
      ↔ y ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))}

theorem mem_localQuadUnits_iff (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ localQuadUnits α v ↔
      (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ localQuadSubring α v ∧
        ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
          ∈ localQuadSubring α v :=
  Iff.rfl

theorem mem_localEmbeddingSet_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b])
    (v : HeightOneSpectrum (𝓞 ℚ)) (β : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    β ∈ localEmbeddingSet Λ α v ↔
      ∀ y ∈ localQuadSubring α v,
        ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * β
            ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
          ↔ y ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
  Iff.rfl

end QuaternionAlgebra

end
