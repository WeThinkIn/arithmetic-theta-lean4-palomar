module

public import ConormalInitialDefinitionsR0162

@[expose] public section

/-! The canonical conormal comparison for a split augmentation. -/
noncomputable section
universe u v
namespace ArithmeticThetaConormalInitialR0162
namespace AugmentedConormal
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
variable (ε : A →ₐ[K] K)

abbrev fiberSubmodule : Submodule A (KaehlerDifferential K A) :=
  ideal ε • ⊤

def fiberDerivation : Derivation K A (DifferentialFiber ε) :=
  (fiberSubmodule ε).mkQ.compDer (KaehlerDifferential.D K A)

lemma fiber_smul_zero (a : ideal ε) (m : DifferentialFiber ε) : (a : A) • m = 0 := by
  obtain ⟨m, rfl⟩ := (fiberSubmodule ε).mkQ_surjective m
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul a.property (Submodule.mem_top)

def forwardIdeal : ideal ε →ₗ[A] DifferentialFiber ε where
  toFun x := fiberDerivation ε x.1
  map_add' x y := map_add (fiberDerivation ε) x.1 y.1
  map_smul' a x := by
    change fiberDerivation ε (a * x.1) = a • fiberDerivation ε x.1
    rw [Derivation.leibniz, fiber_smul_zero ε x, add_zero]

def forward : (ideal ε).Cotangent →ₗ[A] DifferentialFiber ε :=
  Ideal.Cotangent.lift (forwardIdeal ε) (by
    intro x y
    change fiberDerivation ε (x.1 * y.1) = 0
    rw [Derivation.leibniz, fiber_smul_zero ε x, fiber_smul_zero ε y, add_zero])

@[simp] lemma forward_class (x : ideal ε) :
    forward ε ((ideal ε).toCotangent x) = differentialClass ε x.1 := rfl

/-- Subtract the constant selected by the given augmentation. -/
def remainder : A →ₗ[K] ideal ε :=
  (LinearMap.id - (Algebra.linearMap K A).comp ε.toLinearMap).codRestrict
    ((ideal ε).restrictScalars K) (by
      intro a
      change ε (a - algebraMap K A (ε a)) = 0
      simp)

@[simp] lemma remainder_val (a : A) :
    (remainder ε a).1 = a - algebraMap K A (ε a) := rfl

/-- The universal first-order remainder is a derivation. -/
def remainderDerivation : Derivation K A (ideal ε).Cotangent where
  toLinearMap := ((ideal ε).toCotangent.restrictScalars K).comp (remainder ε)
  map_one_eq_zero' := by
    change (ideal ε).toCotangent (remainder ε 1) = 0
    have h : remainder ε 1 = 0 := by ext; simp
    rw [h, map_zero]
  leibniz' a b := by
    change (ideal ε).toCotangent (remainder ε (a*b)) =
      a • (ideal ε).toCotangent (remainder ε b) +
      b • (ideal ε).toCotangent (remainder ε a)
    rw [← (ideal ε).toCotangent.map_smul a, ← (ideal ε).toCotangent.map_smul b,
      ← map_add, Ideal.toCotangent_eq]
    have h := Ideal.mul_mem_mul (remainder ε a).property (remainder ε b).property
    rw [← pow_two] at h
    convert (ideal ε ^ 2).neg_mem h using 1
    simp only [remainder_val, map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    ring

def backward : DifferentialFiber ε →ₗ[A] (ideal ε).Cotangent :=
  (fiberSubmodule ε).liftQ (remainderDerivation ε).liftKaehlerDifferential (by
    intro m hm
    change (remainderDerivation ε).liftKaehlerDifferential m = 0
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha m _
      rw [map_smul]
      exact Ideal.Cotangent.smul_eq_zero_of_mem ha _
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero])

@[simp] lemma backward_differential (a : A) :
    backward ε (differentialClass ε a) = (ideal ε).toCotangent (remainder ε a) :=
  Derivation.liftKaehlerDifferential_comp_D (remainderDerivation ε) a

lemma backward_forward (x : (ideal ε).Cotangent) : backward ε (forward ε x) = x := by
  obtain ⟨x, rfl⟩ := (ideal ε).toCotangent_surjective x
  rw [forward_class, backward_differential]
  congr 1
  ext
  have hx : ε x.1 = 0 := x.property
  simp [hx]

lemma forward_backward (x : DifferentialFiber ε) : forward ε (backward ε x) = x := by
  obtain ⟨x, rfl⟩ := (fiberSubmodule ε).mkQ_surjective x
  have h : (forward ε).comp (remainderDerivation ε).liftKaehlerDifferential =
      (fiberSubmodule ε).mkQ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change forward ε ((remainderDerivation ε).liftKaehlerDifferential
      (KaehlerDifferential.D K A a)) = differentialClass ε a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    change forward ε ((ideal ε).toCotangent (remainder ε a)) = _
    rw [forward_class]
    simp [differentialClass, map_sub]
  exact LinearMap.congr_fun h x

end AugmentedConormal

/-- The unique representative-preserving conormal comparison for every augmented algebra. -/
theorem augmented_conormal :
    ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (ε : A →ₐ[K] K),
    ∃! e : (ideal ε).Cotangent ≃ₗ[K] DifferentialFiber ε, IsConormal ε e := by
  intro K _ A _ _ ε
  let eA : (ideal ε).Cotangent ≃ₗ[A] DifferentialFiber ε :=
    { AugmentedConormal.forward ε with
      invFun := AugmentedConormal.backward ε
      left_inv := AugmentedConormal.backward_forward ε
      right_inv := AugmentedConormal.forward_backward ε }
  let e := eA.restrictScalars K
  have he : IsConormal ε e := fun x => AugmentedConormal.forward_class ε x
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply LinearEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (ideal ε).toCotangent_surjective x
  exact (he' x).trans (he x).symm

end ArithmeticThetaConormalInitialR0162
