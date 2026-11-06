module

public import CanonicalDifferentialTensorR0162
public import AugmentedConormalR0162

@[expose] public section

/-! Naturality over one coefficient field of the canonical differential tensor comparison. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace ArithmeticThetaConormalInitialR0162
namespace InitialTensorNaturality
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]
  (ε : A →ₐ[K] K) (η : B →ₐ[K] K) (f : A →ₐ[K] B) (hf : η.comp f = ε)

include hf in
lemma ideal_map : ideal ε ≤ (ideal η).comap f := by
  intro a ha
  change η (f a) = 0
  change ε a = 0 at ha
  rw [← AlgHom.comp_apply, hf, ha]

include hf in
lemma power_map (n : ℕ) : ideal ε ^ n ≤ (ideal η ^ n).comap f :=
  (pow_le_pow_left' (ideal_map ε η f hf) n).trans (Ideal.le_comap_pow f n)

def gradedMap (n : ℕ) : Grade ε n →ₗ[K] Grade η n :=
  Submodule.mapQ ((nextPower ε n).restrictScalars K)
    ((nextPower η n).restrictScalars K)
    (f.toLinearMap.restrict (p := (ideal ε ^ n).restrictScalars K)
      (q := (ideal η ^ n).restrictScalars K) (power_map ε η f hf n))
    (by intro x hx; exact power_map ε η f hf (n+1) hx)

lemma gradedMap_class (n : ℕ) (b : ↥(ideal ε ^ n)) :
    gradedMap ε η f hf n (gradeClass ε n b) =
      gradeClass η n ⟨f b.1, power_map ε η f hf n b.2⟩ := rfl

def fiberMap : DifferentialFiber ε →ₗ[K] DifferentialFiber η :=
  (AugmentedConormal.forward η).restrictScalars K |>.comp
    ((Ideal.mapCotangent (ideal ε) (ideal η) f (ideal_map ε η f hf)).comp
      ((AugmentedConormal.backward ε).restrictScalars K))

lemma fiberMap_differential (a : A) :
    fiberMap ε η f hf (differentialClass ε a) = differentialClass η (f a) := by
  change AugmentedConormal.forward η
    (Ideal.mapCotangent (ideal ε) (ideal η) f (ideal_map ε η f hf)
      (AugmentedConormal.backward ε (differentialClass ε a))) = _
  rw [AugmentedConormal.backward_differential, Ideal.mapCotangent_toCotangent,
    AugmentedConormal.forward_class]
  simp [AugmentedConormal.remainder_val, differentialClass, map_sub]

lemma differential_surjective :
    Function.Surjective (fun x : ideal ε => differentialClass ε x.1) := by
  intro z
  obtain ⟨c, hc, _⟩ := augmented_conormal K A ε
  obtain ⟨x, hx⟩ := (ideal ε).toCotangent_surjective (c.symm z)
  refine ⟨x, ?_⟩
  change differentialClass ε x.1 = z
  rw [← hc x, hx, c.apply_symm_apply]

end InitialTensorNaturality

/-- The uniquely induced differential and graded maps commute with the canonical
comparison, for every degree including zero. -/
theorem initial_tensor_naturality :
    ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A]
      (B : Type w) [CommRing B] [Algebra K B]
      (ε : A →ₐ[K] K) (η : B →ₐ[K] K) (f : A →ₐ[K] B),
      η.comp f = ε → ∀ (n : ℕ)
      (eA : DifferentialTensor ε n ≃ₗ[K] Grade ε n)
      (eB : DifferentialTensor η n ≃ₗ[K] Grade η n),
      IsDifferentialPower ε n eA → IsDifferentialPower η n eB →
      ∃! qp : (DifferentialFiber ε →ₗ[K] DifferentialFiber η) ×
        (Grade ε n →ₗ[K] Grade η n),
        (∀ a : A, qp.1 (differentialClass ε a) = differentialClass η (f a)) ∧
        (∀ (b : ↥(ideal ε ^ n)) (c : ↥(ideal η ^ n)), f b.1 = c.1 →
          qp.2 (gradeClass ε n b) = gradeClass η n c) ∧
        qp.2.comp eA.toLinearMap =
          eB.toLinearMap.comp (PiTensorProduct.map (fun _ : Fin n => qp.1)) := by
  intro K _ A _ _ B _ _ ε η f hf n eA eB hA hB
  let q := InitialTensorNaturality.fiberMap ε η f hf
  let p := InitialTensorNaturality.gradedMap ε η f hf n
  have hq := InitialTensorNaturality.fiberMap_differential ε η f hf
  have hp (b : ↥(ideal ε ^ n)) (c : ↥(ideal η ^ n)) (h : f b.1 = c.1) :
      p (gradeClass ε n b) = gradeClass η n c := by
    rw [InitialTensorNaturality.gradedMap_class]
    congr 1
    exact Subtype.ext h
  refine ⟨(q, p), ⟨hq, hp, ?_⟩, ?_⟩
  · apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro z
    choose x hx using fun i => InitialTensorNaturality.differential_surjective ε (z i)
    have hz : z = fun i => differentialClass ε (x i).1 := funext fun i => (hx i).symm
    subst z
    let y : Fin n → ideal η := fun i =>
      ⟨f (x i).1, InitialTensorNaturality.ideal_map ε η f hf (x i).2⟩
    have hb : ∏ i, (x i).1 ∈ ideal ε ^ n := by
      simpa using (Ideal.prod_mem_prod (I := fun _ : Fin n => ideal ε)
        (s := Finset.univ) (x := fun i => (x i).1) (fun i _ => (x i).2))
    let b : ↥(ideal ε ^ n) := ⟨∏ i, (x i).1, hb⟩
    let c : ↥(ideal η ^ n) :=
      ⟨f b.1, InitialTensorNaturality.power_map ε η f hf n b.2⟩
    change p (eA (PiTensorProduct.tprod K _)) =
      eB (PiTensorProduct.map (fun _ : Fin n => q) (PiTensorProduct.tprod K _))
    rw [hA x b rfl, hp b c rfl, PiTensorProduct.map_tprod]
    change gradeClass η n c =
      eB (PiTensorProduct.tprod K (fun i => q (differentialClass ε (x i).1)))
    have hq' : (fun i => q (differentialClass ε (x i).1)) =
        (fun i => differentialClass η (f (x i).1)) := funext fun i => hq (x i).1
    rw [hq']
    exact (hB y c (by dsimp [c, b, y]; rw [map_prod])).symm
  · intro qp h
    apply Prod.ext
    · apply LinearMap.ext
      intro z
      obtain ⟨x, rfl⟩ := InitialTensorNaturality.differential_surjective ε z
      exact (h.1 x.1).trans (hq x.1).symm
    · apply LinearMap.ext
      intro z
      obtain ⟨b, rfl⟩ := (nextPower ε n).mkQ_surjective z
      let c : ↥(ideal η ^ n) :=
        ⟨f b.1, InitialTensorNaturality.power_map ε η f hf n b.2⟩
      exact (h.2.1 b c rfl).trans (hp b c rfl).symm

end ArithmeticThetaConormalInitialR0162
