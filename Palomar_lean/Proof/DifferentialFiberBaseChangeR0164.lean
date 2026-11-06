module

public import InitialBaseChangeDefinitionsR0164
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import InitialTensorNaturalityR0162

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w
namespace ArithmeticThetaInitialBaseChangeR0164
open TensorProduct
open ArithmeticThetaConormalInitialR0162

namespace DifferentialFiberBaseChange

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

private lemma kernel_eq (ε : A →ₐ[K] K) :
    ideal (augmentation K L A ε) =
      (ideal ε).map (inclusion K L A).toRingHom := by
  have hsurj : Function.Surjective ε := fun k =>
    ⟨algebraMap K A k, ε.commutes k⟩
  have h := Algebra.TensorProduct.lTensor_ker (A := L) ε hsurj
  calc
    _ = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K L) ε) := by
      let m : Extended K L A →ₐ[K] TensorProduct K L K :=
        Algebra.TensorProduct.map (R := K) (AlgHom.id K L) ε
      have hcomp : (Algebra.TensorProduct.rid K L L).toRingEquiv.toRingHom.comp m.toRingHom =
          (augmentation K L A ε).toRingHom := by
        apply RingHom.ext
        intro (x : Extended K L A)
        refine TensorProduct.inductionOn x ?_ ?_
        · intro l a
          simp [m, augmentation, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
        · intro x y hx hy
          simpa only [map_add] using congrArg₂ (· + ·) hx hy
      ext x
      change (augmentation K L A ε).toRingHom x = 0 ↔ m x = 0
      rw [← hcomp]
      exact (Algebra.TensorProduct.rid K L L).toLinearEquiv.map_eq_zero_iff
    _ = _ := h

private noncomputable def conormalK (ε : A →ₐ[K] K) :
    (ideal ε).Cotangent ≃ₗ[K] DifferentialFiber ε :=
  Classical.choose (augmented_conormal K A ε)

private lemma conormalK_spec (ε : A →ₐ[K] K) :
    IsConormal ε (conormalK K A ε) :=
  (Classical.choose_spec (augmented_conormal K A ε)).1

private noncomputable def fiberEquiv (ε : A →ₐ[K] K) : FiberEquiv K L A ε := by
  let ε' := augmentation K L A ε
  let eK := conormalK K A ε
  let eL := conormalK L (Extended K L A) ε'
  have hI : (ideal ε).map
      ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) = ideal ε' := by
    simpa [inclusion, ε'] using (kernel_eq K L A ε).symm
  exact
    (AlgebraTensorModule.congr (LinearEquiv.refl L L) eK.symm).trans
      ((Ideal.tensorCotangentEquiv K L (ideal ε)).trans
        (((Ideal.Cotangent.equivOfEq (R := Extended K L A)
          ((ideal ε).map
            ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom))
          (ideal ε') hI).restrictScalars L).trans eL))

private lemma fiberEquiv_spec (ε : A →ₐ[K] K) :
    IsFiberEquiv K L A ε (fiberEquiv K L A ε) := by
  intro l a
  let ε' := augmentation K L A ε
  let eK := conormalK K A ε
  let eL := conormalK L (Extended K L A) ε'
  have hJ : (ideal ε).map
      ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) = ideal ε' := by
    simpa [inclusion, ε'] using (kernel_eq K L A ε).symm
  let r := AugmentedConormal.remainder ε a
  have hr : (r : A) ∈ ideal ε := r.property
  have hK : eK ((ideal ε).toCotangent r) = differentialClass ε (r : A) :=
    conormalK_spec K A ε r
  have hL : eL ((ideal ε').toCotangent
      ⟨inclusion K L A (r : A), by
        rw [show inclusion K L A (r : A) =
          (inclusion K L A).toRingHom (r : A) by rfl]
        have hmem := Ideal.mem_map_of_mem (inclusion K L A).toRingHom hr
        have hmem' : (inclusion K L A).toRingHom (r : A) ∈
            (ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) := by
          simpa [inclusion] using hmem
        exact hJ ▸ hmem'⟩) =
      differentialClass ε' (inclusion K L A (r : A)) := by
    exact conormalK_spec L (Extended K L A) ε' _
  have hmap : inclusion K L A (r : A) =
      inclusion K L A a - algebraMap L (Extended K L A) (algebraMap K L (ε a)) := by
    change (1 ⊗ₜ[K] (a - algebraMap K A (ε a))) =
      (1 ⊗ₜ[K] a) - algebraMap L (Extended K L A) (algebraMap K L (ε a))
    rw [tmul_sub]
    rw [Algebra.TensorProduct.algebraMap_apply]
    rw [show algebraMap L L (algebraMap K L (ε a)) = algebraMap K L (ε a) by simp]
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hd : differentialClass ε' (inclusion K L A (r : A)) =
      differentialClass ε' (inclusion K L A a) := by
    rw [hmap, differentialClass, map_sub]
    have hz : KaehlerDifferential.D L (Extended K L A)
        (algebraMap L (Extended K L A) (algebraMap K L (ε a))) = 0 := by
      exact (KaehlerDifferential.D L (Extended K L A)).map_algebraMap _
    have hs : ((algebraMap K L (ε a) ⊗ₜ[K] (1 : A)) : Extended K L A) =
        algebraMap L (Extended K L A) (algebraMap K L (ε a)) := by
      calc
        _ = (algebraMap L L (algebraMap K L (ε a)) ⊗ₜ[K] (1 : A)) := by simp
        _ = _ := (Algebra.TensorProduct.algebraMap_apply _).symm
    rw [hz]
    rfl
  have ha : differentialClass ε (r : A) = differentialClass ε a := by
    rw [← AugmentedConormal.forward_class ε r]
    rw [← AugmentedConormal.backward_differential ε a]
    exact AugmentedConormal.forward_backward ε _
  change ((AlgebraTensorModule.congr (LinearEquiv.refl L L) eK.symm).trans
      ((Ideal.tensorCotangentEquiv K L (ideal ε)).trans
        (((Ideal.Cotangent.equivOfEq (R := Extended K L A)
          ((ideal ε).map
            ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom))
          (ideal ε') hJ).restrictScalars L).trans eL)))
      (l ⊗ₜ[K] differentialClass ε a) = _
  simp only [LinearEquiv.trans_apply]
  rw [AlgebraTensorModule.congr_tmul, ← ha, hK.symm]
  simp only [LinearEquiv.symm_apply_apply]
  rw [Ideal.tensorCotangentEquiv_tmul]
  simp only [LinearEquiv.refl_apply, map_smul]
  simp only [inclusion]
  simp only [← Algebra.TensorProduct.includeRight_apply]
  change l • eL ((LinearEquiv.restrictScalars L
      (Ideal.Cotangent.equivOfEq
        ((ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom))
        (ideal ε') hJ))
      (((ideal ε).map
        ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom)).toCotangent
        ⟨Algebra.TensorProduct.includeRight (r : A), Ideal.mem_map_of_mem _ hr⟩)) = _
  rw [LinearEquiv.restrictScalars_apply]
  have heq :
      (Ideal.Cotangent.equivOfEq
        ((ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom))
        (ideal ε') hJ)
        (((ideal ε).map
          ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom)).toCotangent
          ⟨Algebra.TensorProduct.includeRight (r : A), Ideal.mem_map_of_mem _ hr⟩) =
      (ideal ε').toCotangent
        ⟨Algebra.TensorProduct.includeRight (r : A), by
          have hmem : Algebra.TensorProduct.includeRight (r : A) ∈
              (ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) :=
            Ideal.mem_map_of_mem _ hr
          exact hJ ▸ hmem⟩ := by
    rw [Ideal.Cotangent.equivOfEq_toCotangent]
    rfl
  rw [heq]
  have hh : eL ((ideal ε').toCotangent
      ⟨inclusion K L A (r : A), by
        have hmem := Ideal.mem_map_of_mem (inclusion K L A).toRingHom hr
        have hmem' : (inclusion K L A).toRingHom (r : A) ∈
            (ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) := by
          simpa [inclusion] using hmem
        exact hJ ▸ hmem'⟩) =
      differentialClass ε' (inclusion K L A a) := hL.trans hd
  have htarget : l • eL ((ideal ε').toCotangent
      ⟨inclusion K L A (r : A), by
        have hmem := Ideal.mem_map_of_mem (inclusion K L A).toRingHom hr
        have hmem' : (inclusion K L A).toRingHom (r : A) ∈
            (ideal ε).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom) := by
          simpa [inclusion] using hmem
        exact hJ ▸ hmem'⟩) =
      l • differentialClass ε' (inclusion K L A a) := by rw [hh]
  simpa only [inclusion, Algebra.TensorProduct.includeRight_apply] using htarget

end DifferentialFiberBaseChange

theorem differential_fiber_base_change :
    ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
      (A : Type w) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K),
      ∃! e : FiberEquiv K L A ε, IsFiberEquiv K L A ε e := by
  intro K _ L _ _ A _ _ ε
  refine ⟨DifferentialFiberBaseChange.fiberEquiv K L A ε,
    DifferentialFiberBaseChange.fiberEquiv_spec K L A ε, ?_⟩
  intro e he
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro l z
  obtain ⟨a, ha⟩ :=
    ArithmeticThetaConormalInitialR0162.InitialTensorNaturality.differential_surjective ε z
  rw [← ha]
  exact (he l (a : A)).trans
    (DifferentialFiberBaseChange.fiberEquiv_spec K L A ε l (a : A)).symm

end ArithmeticThetaInitialBaseChangeR0164
