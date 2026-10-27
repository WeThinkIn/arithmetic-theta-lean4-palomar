import AugmentationPowersR0164

/-! Canonical scalar extension of every graded augmentation quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u v w
namespace ArithmeticThetaInitialBaseChangeR0164
open TensorProduct ArithmeticThetaConormalInitialR0162
namespace GradedBaseChange
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

/-- Inclusion of consecutive powers, with the structural scalar action. -/
def step (ε : A →ₐ[K] K) (n : ℕ) :
    ↥(ideal ε ^ (n+1)) →ₗ[K] ↥(ideal ε ^ n) :=
  (Submodule.inclusion (Ideal.pow_le_pow_right (by omega))).restrictScalars K

def quotientMap (ε : A →ₐ[K] K) (n : ℕ) :
    ↥(ideal ε ^ n) →ₗ[K] Grade ε n :=
  (nextPower ε n).mkQ.restrictScalars K

theorem quotient_surjective (ε : A →ₐ[K] K) (n : ℕ) :
    Function.Surjective (quotientMap K A ε n) := by
  intro x
  exact Submodule.mkQ_surjective (nextPower ε n) x

theorem step_exact (ε : A →ₐ[K] K) (n : ℕ) :
    Function.Exact (step K A ε n) (quotientMap K A ε n) := by
  intro x
  change Submodule.Quotient.mk x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

variable (ε : A →ₐ[K] K) (n : ℕ)

abbrev tensorStep := AlgebraTensorModule.lTensor L L (step K A ε n)
abbrev tensorQuotient := AlgebraTensorModule.lTensor L L (quotientMap K A ε n)
abbrev extendedQuotient :=
  (quotientMap L (Extended K L A) (augmentation K L A ε) n).comp
    (AugmentationPowers.powerEquiv K L A ε n).toLinearMap

theorem power_step :
    (AugmentationPowers.powerEquiv K L A ε n).toLinearMap.comp
      (tensorStep K L A ε n) =
    (step L (Extended K L A) (augmentation K L A ε) n).comp
      (AugmentationPowers.powerEquiv K L A ε (n+1)).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro l a
  apply Subtype.ext
  exact (AugmentationPowers.powerEquiv_spec K L A ε n l _).trans
    (AugmentationPowers.powerEquiv_spec K L A ε (n+1) l a).symm

theorem tensor_exact :
    Function.Exact (tensorStep K L A ε n) (tensorQuotient K L A ε n) :=
  lTensor_exact L (step_exact K A ε n) (quotient_surjective K A ε n)

theorem extended_exact :
    Function.Exact (tensorStep K L A ε n) (extendedQuotient K L A ε n) := by
  intro x
  rw [LinearMap.comp_apply, step_exact L (Extended K L A) (augmentation K L A ε) n]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (AugmentationPowers.powerEquiv K L A ε (n+1)).surjective y
    refine ⟨z, (AugmentationPowers.powerEquiv K L A ε n).injective ?_⟩
    exact (LinearMap.congr_fun (power_step K L A ε n) z).trans hy
  · rintro ⟨z, rfl⟩
    exact ⟨AugmentationPowers.powerEquiv K L A ε (n+1) z,
      (LinearMap.congr_fun (power_step K L A ε n) z).symm⟩

theorem tensor_surjective : Function.Surjective (tensorQuotient K L A ε n) :=
  LinearMap.lTensor_surjective L (quotient_surjective K A ε n)

def gradeEquiv : GradeEquiv K L A ε n :=
  ((tensor_exact K L A ε n).linearEquivOfSurjective
    (tensor_surjective K L A ε n)).symm.trans
  ((extended_exact K L A ε n).linearEquivOfSurjective
    ((quotient_surjective L (Extended K L A) (augmentation K L A ε) n).comp
      (AugmentationPowers.powerEquiv K L A ε n).surjective))

theorem gradeEquiv_quotient (x : L ⊗[K] ↥(ideal ε ^ n)) :
    gradeEquiv K L A ε n (tensorQuotient K L A ε n x) =
      extendedQuotient K L A ε n x := by
  unfold gradeEquiv
  rw [LinearEquiv.trans_apply, Function.Exact.linearEquivOfSurjective_symm_apply]
  rfl

theorem gradeEquiv_spec : IsGradeEquiv K L A ε n (gradeEquiv K L A ε n) := by
  intro l a b hb
  change gradeEquiv K L A ε n (tensorQuotient K L A ε n (l ⊗ₜ[K] a)) = _
  rw [gradeEquiv_quotient]
  change quotientMap L (Extended K L A) (augmentation K L A ε) n
    (AugmentationPowers.powerEquiv K L A ε n (l ⊗ₜ[K] a)) = _
  have he : AugmentationPowers.powerEquiv K L A ε n (l ⊗ₜ[K] a) = l • b := by
    apply Subtype.ext
    change (AugmentationPowers.powerEquiv K L A ε n (l ⊗ₜ[K] a)).1 = l • b.1
    rw [AugmentationPowers.powerEquiv_spec, hb]
  rw [he, map_smul]
  rfl

theorem gradeEquiv_unique (e : GradeEquiv K L A ε n) (he : IsGradeEquiv K L A ε n e) :
    e = gradeEquiv K L A ε n := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro l x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (nextPower ε n) x
  let b := AugmentationPowers.powerEquiv K L A ε n ((1 : L) ⊗ₜ[K] a)
  have hb : b.1 = inclusion K L A a.1 := by
    simpa [b] using AugmentationPowers.powerEquiv_spec K L A ε n 1 a
  exact (he l a b hb).trans (gradeEquiv_spec K L A ε n l a b hb).symm
end GradedBaseChange

/-- Every actual graded quotient commutes uniquely with extension of the base field. -/
theorem graded_base_change :
    ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
      (A : Type w) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K),
      ∀ n : ℕ, ∃! e : GradeEquiv K L A ε n, IsGradeEquiv K L A ε n e := by
  intro K _ L _ _ A _ _ ε n
  exact ⟨GradedBaseChange.gradeEquiv K L A ε n,
    GradedBaseChange.gradeEquiv_spec K L A ε n,
    GradedBaseChange.gradeEquiv_unique K L A ε n⟩
end ArithmeticThetaInitialBaseChangeR0164
