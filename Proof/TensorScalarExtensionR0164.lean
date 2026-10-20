module

public import InitialBaseChangeDefinitionsR0164
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaInitialBaseChangeR0164

universe u v w

private def scalarTensorMap (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]
    (V : Type w) [AddCommGroup V] [Module K V] (n : ℕ) :
    TensorProduct K L (PiTensorProduct K (fun _ : Fin n => V)) →ₗ[L]
      PiTensorProduct L (fun _ : Fin n => TensorProduct K L V) := by
  let φ :=
    ((PiTensorProduct.tprod L :
        MultilinearMap L (fun _ : Fin n => TensorProduct K L V) _).restrictScalars K).compLinearMap
      (fun _ : Fin n => TensorProduct.mk K L V 1)
  let g := PiTensorProduct.lift φ
  let h : L →ₗ[L]
      (PiTensorProduct K (fun _ : Fin n => V) →ₗ[K]
        PiTensorProduct L (fun _ : Fin n => TensorProduct K L V)) :=
    { toFun := fun l => l • g
      map_add' := by
        intro a b
        ext x
        simp [add_smul]
      map_smul' := by
        intro a b
        ext x
        simp [smul_smul] }
  exact TensorProduct.AlgebraTensorModule.lift h

private theorem scalarTensorMap_pure (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]
    (V : Type w) [AddCommGroup V] [Module K V] (n : ℕ)
    (l : L) (x : Fin n → V) :
    scalarTensorMap K L V n (l ⊗ₜ[K] PiTensorProduct.tprod K x) =
      l • PiTensorProduct.tprod L (fun i => (1 : L) ⊗ₜ[K] x i) := by
  let φ :=
    ((PiTensorProduct.tprod L :
        MultilinearMap L (fun _ : Fin n => TensorProduct K L V) _).restrictScalars K).compLinearMap
      (fun _ : Fin n => TensorProduct.mk K L V 1)
  let g := PiTensorProduct.lift φ
  let h : L →ₗ[L]
      (PiTensorProduct K (fun _ : Fin n => V) →ₗ[K]
        PiTensorProduct L (fun _ : Fin n => TensorProduct K L V)) :=
    { toFun := fun a => a • g
      map_add' := by
        intro a b
        ext y
        simp [add_smul]
      map_smul' := by
        intro a b
        ext y
        simp [smul_smul] }
  change (TensorProduct.AlgebraTensorModule.lift h)
      (l ⊗ₜ[K] PiTensorProduct.tprod K x) = _
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  dsimp [h, g, φ]
  simp

theorem tensor_scalar_extension (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]
    (V : Type w) [AddCommGroup V] [Module K V] (n : ℕ) :
    ∃! e : TensorEquiv K L V n, IsTensorEquiv K L V n e := by
  let ι := Module.Free.ChooseBasisIndex K V
  let b : Module.Basis ι K V := Module.Free.chooseBasis K V
  let bp : Module.Basis (Fin n → ι)
      K (PiTensorProduct K (fun _ : Fin n => V)) :=
    Basis.piTensorProduct (fun _ : Fin n => b)
  let bs : Module.Basis (Fin n → ι) L
      (TensorProduct K L (PiTensorProduct K (fun _ : Fin n => V))) :=
    Algebra.TensorProduct.basis L bp
  let bt : Module.Basis (Fin n → ι) L
      (PiTensorProduct L (fun _ : Fin n => TensorProduct K L V)) :=
    Basis.piTensorProduct (fun _ : Fin n => Algebra.TensorProduct.basis L b)
  let e : TensorEquiv K L V n := bs.equiv bt (Equiv.refl (Fin n → ι))
  have hmap : scalarTensorMap K L V n = e.toLinearMap := by
    apply bs.ext
    intro p
    have hbs : bs p = (1 : L) ⊗ₜ[K] PiTensorProduct.tprod K (fun i => b (p i)) := by
      simp [bs, bp, Algebra.TensorProduct.basis_apply, Basis.piTensorProduct_apply]
    change scalarTensorMap K L V n (bs p) = e (bs p)
    rw [hbs, scalarTensorMap_pure]
    rw [← hbs]
    dsimp [e]
    rw [Module.Basis.equiv_apply]
    simp [bt, Basis.piTensorProduct_apply, Algebra.TensorProduct.basis_apply]
  refine ⟨e, ?_, ?_⟩
  · intro l x
    change e.toLinearMap (l ⊗ₜ[K] PiTensorProduct.tprod K x) = _
    rw [← hmap]
    exact scalarTensorMap_pure K L V n l x
  · intro e' he'
    apply LinearEquiv.toLinearMap_injective
    apply bs.ext
    intro p
    have hbs : bs p = (1 : L) ⊗ₜ[K] PiTensorProduct.tprod K (fun i => b (p i)) := by
      simp [bs, bp, Algebra.TensorProduct.basis_apply, Basis.piTensorProduct_apply]
    change e' (bs p) = e (bs p)
    rw [hbs, he' (1 : L) (fun i => b (p i))]
    rw [← hbs]
    dsimp [e]
    rw [Module.Basis.equiv_apply]
    simp [bt, Basis.piTensorProduct_apply, Algebra.TensorProduct.basis_apply]

end ArithmeticThetaInitialBaseChangeR0164
