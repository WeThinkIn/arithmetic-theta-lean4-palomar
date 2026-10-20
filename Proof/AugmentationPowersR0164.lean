module

public import InitialBaseChangeDefinitionsR0164
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

/-! Scalar extension of the actual augmentation ideal and all of its powers. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace ArithmeticThetaInitialBaseChangeR0164
open TensorProduct ArithmeticThetaConormalInitialR0162
namespace AugmentationPowers
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

/-- Tensoring an ideal inclusion is injective because the scalar field extension is flat. -/
def idealEquiv (I : Ideal A) :
    L ⊗[K] I ≃ₗ[L] (I.map (inclusion K L A).toRingHom) :=
  (LinearEquiv.ofInjective
    (AlgebraTensorModule.lTensor L L (I.subtype.restrictScalars K))
    (Module.Flat.lTensor_preserves_injective_linearMap
      (I.subtype.restrictScalars K) I.subtype_injective)).trans
    (LinearEquiv.ofEq _ _ (AlgebraTensorModule.range_lTensor_idealMap L L I))

@[simp] theorem idealEquiv_tmul (I : Ideal A) (l : L) (a : I) :
    (idealEquiv K L A I (l ⊗ₜ[K] a)).1 = l ⊗ₜ[K] a.1 := rfl

/-- The augmentation is the tensor of the original augmentation followed by contraction. -/
theorem augmentation_eq (ε : A →ₐ[K] K) (x : L ⊗[K] A) :
    augmentation K L A ε x =
      TensorProduct.rid K L (LinearMap.lTensor L ε.toLinearMap x) := by
  induction x with
  | zero => simp
  | tmul l a => simp [augmentation, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp_all

/-- The actual augmented kernel is the extension of the original kernel. -/
theorem kernel_eq (ε : A →ₐ[K] K) :
    ideal (augmentation K L A ε) = (ideal ε).map (inclusion K L A).toRingHom := by
  have hsurj : Function.Surjective ε := fun k => ⟨algebraMap K A k, ε.commutes k⟩
  have h := Algebra.TensorProduct.lTensor_ker (A := L) ε hsurj
  calc
    _ = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K L) ε) := by
      ext x
      change augmentation K L A ε x = 0 ↔
        Algebra.TensorProduct.map (AlgHom.id K L) ε x = 0
      rw [augmentation_eq]
      exact (TensorProduct.rid K L).map_eq_zero_iff
    _ = _ := h

/-- Ideal extension commutes with powers, including the zeroth power. -/
theorem power_eq (ε : A →ₐ[K] K) (n : ℕ) :
    (ideal ε ^ n).map (inclusion K L A).toRingHom =
      ideal (augmentation K L A ε) ^ n := by
  rw [Ideal.map_pow, kernel_eq]

def powerEquiv (ε : A →ₐ[K] K) (n : ℕ) : PowerEquiv K L A ε n :=
  (idealEquiv K L A (ideal ε ^ n)).trans
    (LinearEquiv.ofEq _ _ (congrArg (Submodule.restrictScalars L) (power_eq K L A ε n)))

theorem powerEquiv_spec (ε : A →ₐ[K] K) (n : ℕ) :
    IsPowerEquiv K L A ε n (powerEquiv K L A ε n) := by
  intro l a
  change l ⊗ₜ[K] a.1 = l • (1 ⊗ₜ[K] a.1)
  simp [smul_tmul']

theorem powerEquiv_unique (ε : A →ₐ[K] K) (n : ℕ)
    (e : PowerEquiv K L A ε n) (he : IsPowerEquiv K L A ε n e) :
    e = powerEquiv K L A ε n := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro l a
  apply Subtype.ext
  exact (he l a).trans (powerEquiv_spec K L A ε n l a).symm
end AugmentationPowers

/-- The actual augmentation kernel and its powers commute canonically with field extension. -/
theorem augmentation_powers :
    ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
      (A : Type w) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K),
      ideal (augmentation K L A ε) = Ideal.map (inclusion K L A).toRingHom (ideal ε) ∧
      ∀ n : ℕ, ∃! e : PowerEquiv K L A ε n, IsPowerEquiv K L A ε n e := by
  intro K _ L _ _ A _ _ ε
  refine ⟨AugmentationPowers.kernel_eq K L A ε, fun n => ?_⟩
  exact ⟨AugmentationPowers.powerEquiv K L A ε n,
    AugmentationPowers.powerEquiv_spec K L A ε n,
    AugmentationPowers.powerEquiv_unique K L A ε n⟩
end ArithmeticThetaInitialBaseChangeR0164
