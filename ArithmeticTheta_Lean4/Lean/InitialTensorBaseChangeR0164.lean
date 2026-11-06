import GradedBaseChangeR0164
import DifferentialFiberBaseChangeR0164
import TensorScalarExtensionR0164
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Canonical transport of the differential initial tensor under field extension. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u v w
namespace ArithmeticThetaInitialBaseChangeR0164
open TensorProduct ArithmeticThetaConormalInitialR0162
namespace InitialTensorBaseChange
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K)

def idealInclusion (x : ideal ε) : ideal (augmentation K L A ε) :=
  ⟨inclusion K L A x.1, by
    change augmentation K L A ε (inclusion K L A x.1) = 0
    have hx : ε x.1 = 0 := x.2
    simp [augmentation, inclusion, hx]⟩

lemma ideal_span : Submodule.span L (Set.range (idealInclusion K L A ε)) = ⊤ := by
  let E : L ⊗[K] ideal ε ≃ₗ[L] ideal (augmentation K L A ε) :=
    (AugmentationPowers.idealEquiv K L A (ideal ε)).trans
      (LinearEquiv.ofEq _ _ (congrArg (Submodule.restrictScalars L)
        (AugmentationPowers.kernel_eq K L A ε).symm))
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := E.surjective y
  induction z with
  | zero =>
    rw [E.map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | tmul l x =>
    have h : E (l ⊗ₜ[K] x) = l • idealInclusion K L A ε x := by
      apply Subtype.ext
      change l ⊗ₜ[K] x.1 = l • (1 ⊗ₜ[K] x.1)
      simp [smul_tmul']
    rw [h]
    exact Submodule.smul_mem _ l (Submodule.subset_span ⟨x, rfl⟩)

variable {K A}
def productClass (n : ℕ) : MultilinearMap K (fun _ : Fin n => ideal ε) (Grade ε n) :=
  ((nextPower ε n).mkQ.restrictScalars K).compMultilinearMap
    (((MultilinearMap.mkPiAlgebra K (Fin n) A).compLinearMap
      (fun _ => (ideal ε).subtype.restrictScalars K)).codRestrict
        ((ideal ε ^ n).restrictScalars K) (by
          intro x
          simpa using (Ideal.prod_mem_prod (I := fun _ : Fin n => ideal ε)
            (s := Finset.univ) (x := fun i => (x i).1) (fun i _ => (x i).2))))

def differentialProduct (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => ideal ε) (DifferentialTensor ε n) :=
  (PiTensorProduct.tprod K).compLinearMap
    (fun _ => (AugmentedConormal.forwardIdeal ε).restrictScalars K)

lemma comparison_unique (n : ℕ) (e f : DifferentialTensor ε n ≃ₗ[K] Grade ε n)
    (he : IsDifferentialPower ε n e) (hf : IsDifferentialPower ε n f) : e = f := by
  classical
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro z
  choose x hx using fun i => InitialTensorNaturality.differential_surjective ε (z i)
  have hz : z = fun i => differentialClass ε (x i).1 := funext fun i => (hx i).symm
  let b : ↥(ideal ε ^ n) := ⟨∏ i, (x i).1, by
    simpa using (Ideal.prod_mem_prod (I := fun _ : Fin n => ideal ε)
      (s := Finset.univ) (x := fun i => (x i).1) (fun i _ => (x i).2))⟩
  change e (PiTensorProduct.tprod K z) = f (PiTensorProduct.tprod K z)
  rw [hz, he x b rfl, hf x b rfl]
end InitialTensorBaseChange

/-- The canonical initial-tensor square and reflection of zero, in all degrees. -/
theorem initial_tensor_base_change :
    ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
      (A : Type w) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K),
      ∀ (n : ℕ) (eA : DifferentialTensor ε n ≃ₗ[K] Grade ε n),
      IsDifferentialPower ε n eA → InitialTransport K L A ε n eA := by
  classical
  intro K _ L _ _ A _ _ ε n eA hA
  obtain ⟨p, hp, _⟩ := graded_base_change K L A ε n
  obtain ⟨q, hq, _⟩ := differential_fiber_base_change K L A ε
  obtain ⟨t, ht, _⟩ := tensor_scalar_extension K L (DifferentialFiber ε) n
  let c := PiTensorProduct.congr (fun _ : Fin n => q)
  let s := t.trans c
  let eB := s.symm.trans ((eA.baseChange K L _ _).trans p)
  have square (l : L) (x : DifferentialTensor ε n) :
      eB (c (t (l ⊗ₜ[K] x))) = p (l ⊗ₜ[K] eA x) := by
    change p ((eA.baseChange K L _ _) (s.symm (s (l ⊗ₜ[K] x)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]
  have pure (x : Fin n → ideal ε) :
      eB (PiTensorProduct.tprod L (fun i => differentialClass (augmentation K L A ε)
        (inclusion K L A (x i).1))) =
      InitialTensorBaseChange.productClass (augmentation K L A ε) n
        (fun i => InitialTensorBaseChange.idealInclusion K L A ε (x i)) := by
    let a : ↥(ideal ε ^ n) := ⟨∏ i, (x i).1, by
      simpa using (Ideal.prod_mem_prod (I := fun _ : Fin n => ideal ε)
        (s := Finset.univ) (x := fun i => (x i).1) (fun i _ => (x i).2))⟩
    let b : ↥(ideal (augmentation K L A ε) ^ n) :=
      ⟨∏ i, inclusion K L A (x i).1, by
        simpa using (Ideal.prod_mem_prod
          (I := fun _ : Fin n => ideal (augmentation K L A ε))
          (s := Finset.univ) (x := fun i => inclusion K L A (x i).1)
          (fun i _ => (InitialTensorBaseChange.idealInclusion K L A ε (x i)).2))⟩
    have H := square 1 (PiTensorProduct.tprod K (fun i => differentialClass ε (x i).1))
    rw [ht, one_smul] at H
    change eB (PiTensorProduct.congr (fun _ : Fin n => q) _) = _ at H
    rw [PiTensorProduct.congr_tprod] at H
    have hq1 (a : A) := hq 1 a
    simp only [one_smul] at hq1
    simp_rw [hq1] at H
    rw [hA x a rfl, hp 1 a b (by dsimp [a, b]; rw [map_prod]), one_smul] at H
    exact H
  have hB : IsDifferentialPower (augmentation K L A ε) n eB := by
    have H : eB.toLinearMap.compMultilinearMap
        (InitialTensorBaseChange.differentialProduct (augmentation K L A ε) n) =
        InitialTensorBaseChange.productClass (augmentation K L A ε) n := by
      apply MultilinearMap.ext_of_span_eq_top
        (g := fun (_ : Fin n) (x : ideal ε) => InitialTensorBaseChange.idealInclusion K L A ε x)
        (fun _ => InitialTensorBaseChange.ideal_span K L A ε)
      exact pure
    intro x b hb
    have Hx := DFunLike.congr_fun H x
    change eB (PiTensorProduct.tprod L (fun i => differentialClass (augmentation K L A ε)
      (x i).1)) = _ at Hx
    rw [Hx]
    apply congrArg (gradeClass (augmentation K L A ε) n)
    exact Subtype.ext hb.symm
  refine ⟨p, q, t, eB, hp, hq, ht, hB, ?_, square, ?_⟩
  · intro eB' hB'
    exact InitialTensorBaseChange.comparison_unique _ n eB' eB hB' hB
  · intro x
    change s ((1 : L) ⊗ₜ[K] x) = 0 ↔ x = 0
    rw [s.map_eq_zero_iff]
    exact Module.FaithfullyFlat.one_tmul_eq_zero_iff K (DifferentialTensor ε n) x
end ArithmeticThetaInitialBaseChangeR0164
