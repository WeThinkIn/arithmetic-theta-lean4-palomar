module

public import Mathlib

@[expose] public section

open scoped TensorProduct nonZeroDivisors
open TensorProduct

namespace ArithmeticThetaSmoothNormality

universe u
noncomputable section

variable (R S : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]

omit [IsIntegrallyClosed R] in
/-- Étale base change of the fraction field is a field when the total algebra is a domain. -/
theorem etale_genericFiber_isField : IsField (S ⊗[R] FractionRing R) := by
  let K := FractionRing R
  let T := S ⊗[R] K
  let : Algebra K T := Algebra.TensorProduct.rightAlgebra
  have hnonzero : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    apply mem_nonZeroDivisors_iff_ne_zero.mp hr
    apply FaithfulSMul.algebraMap_injective R S
    simpa using hz
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hnonzero
  let e : K ⊗[R] S ≃ₐ[K] T :=
    { (Algebra.TensorProduct.comm R K S).toRingEquiv with
      commutes' x := by
        change (Algebra.TensorProduct.comm R K S) (x ⊗ₜ[R] 1) = 1 ⊗ₜ[R] x
        exact Algebra.TensorProduct.comm_tmul _ _ _ }
  let : Algebra.Etale K T := Algebra.Etale.of_equiv e
  let := Algebra.FormallyUnramified.finite_of_free K T
  let := IsArtinianRing.of_finite K T
  exact IsArtinianRing.isField_of_isDomain T

/-- The smooth integral-closure base-change theorem gives relative normality in the generic fiber. -/
theorem etale_integrallyClosedIn_genericFiber : IsIntegrallyClosedIn S (S ⊗[R] FractionRing R) := by
  let K := FractionRing R
  let T := S ⊗[R] K
  have hnonzero : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S le_rfl
  have hi : Function.Injective (algebraMap S T) := IsLocalization.injective T hnonzero
  have himage (z : S ⊗[R] integralClosure R K) :
      ∃ s : S, algebraMap S T s = (TensorProduct.toIntegralClosure R S K z : T) := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨sx, hsx⟩ := hx
      obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by simp [map_add, hsx, hsy]⟩
    | tmul s b =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp b.property
      refine ⟨s * algebraMap R S r, ?_⟩
      change (s * algebraMap R S r) ⊗ₜ[R] (1 : K) = s ⊗ₜ[R] (b : K)
      rw [← hr, mul_comm]
      simp only [← Algebra.smul_def, smul_tmul]
      rw [Algebra.smul_def, mul_one]
  refine ⟨hi, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2 ⟨x, hx⟩
    obtain ⟨s, hs⟩ := himage z
    exact ⟨s, hs.trans (congrArg Subtype.val hz)⟩
  · rintro ⟨s, rfl⟩
    exact isIntegral_algebraMap

include R in
/-- A domain étale over an integrally closed domain is integrally closed. -/
theorem etaleDomain_integrallyClosed : IsIntegrallyClosed S := by
  let T := S ⊗[R] FractionRing R
  let := (etale_genericFiber_isField R S).toField
  let := etale_integrallyClosedIn_genericFiber R S
  have hnonzero : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S le_rfl
  let : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr
    (IsLocalization.injective T hnonzero)
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn S T

end
end ArithmeticThetaSmoothNormality
