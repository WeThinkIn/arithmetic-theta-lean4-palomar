import ConormalInitialDefinitionsR0162
import Mathlib.RingTheory.PiTensorProduct

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u v w
namespace ArithmeticThetaConormalInitialR0162
namespace CartierGradedTensor
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [IsDomain A] [Algebra K A]
variable (ε : A →ₐ[K] K) (t : A) (ht : ideal ε = Ideal.span {t}) (ht0 : t ≠ 0)

include ht in
lemma pow_mem (n : ℕ) : t ^ n ∈ ideal ε ^ n := by
  rw [ht, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

include ht ht0 in
lemma coeff_mem (n : ℕ) (a : A) : a * t ^ n ∈ ideal ε ^ (n+1) ↔ ε a = 0 := by
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    have hab : a = t * b := by
      apply mul_right_cancel₀ (pow_ne_zero n ht0)
      calc
        a * t ^ n = t ^ (n+1) * b := hb
        _ = (t * b) * t ^ n := by rw [pow_succ]; ring
    rw [hab, map_mul]
    have : ε t = 0 := (show t ∈ ideal ε from ht ▸ Ideal.mem_span_singleton_self t)
    simp [this]
  · intro ha
    have ha' : a ∈ ideal ε := ha
    rw [ht, Ideal.mem_span_singleton] at ha'
    obtain ⟨b, rfl⟩ := ha'
    exact ⟨b, by rw [pow_succ]; ring⟩

variable {Q : Type w} [AddCommGroup Q] [Module K Q]

include ht0 in
lemma class_scalar (n : ℕ) (q : ↥(ideal ε ^ n) →ₗ[K] Q)
    (hq : ∀ x, q x = 0 ↔ x.1 ∈ ideal ε ^ (n+1)) (a : A) :
    q ⟨a * t ^ n, Ideal.mul_mem_left _ _ (pow_mem ε t ht n)⟩ =
      ε a • q ⟨t ^ n, pow_mem ε t ht n⟩ := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub, hq]
  change a * t ^ n - (ε a) • t ^ n ∈ ideal ε ^ (n+1)
  rw [Algebra.smul_def]
  rw [← sub_mul, coeff_mem ε t ht ht0]
  simp

noncomputable def coord (n : ℕ) (q : ↥(ideal ε ^ n) →ₗ[K] Q)
    (hs : Function.Surjective q)
    (hq : ∀ x, q x = 0 ↔ x.1 ∈ ideal ε ^ (n+1)) : K ≃ₗ[K] Q :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton K Q
    (q ⟨t ^ n, pow_mem ε t ht n⟩)) (by
      constructor
      · apply (LinearMap.ker_eq_bot).mp
        apply LinearMap.ker_eq_bot'.mpr
        intro c hc
        change c • q ⟨t ^ n, pow_mem ε t ht n⟩ = 0 at hc
        rw [← map_smul, hq] at hc
        change c • t ^ n ∈ ideal ε ^ (n+1) at hc
        rw [Algebra.smul_def] at hc
        have := (coeff_mem ε t ht ht0 n (algebraMap K A c)).mp hc
        simpa using this
      · intro z
        obtain ⟨x, rfl⟩ := hs z
        have hx := x.2
        simp only [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
        obtain ⟨a, ha⟩ := hx
        refine ⟨ε a, ?_⟩
        change ε a • q _ = q x
        rw [← class_scalar ε t ht ht0 n q hq a]
        congr 1
        exact Subtype.ext ha)


def gradeQ (n : ℕ) : ↥(ideal ε ^ n) →ₗ[K] Grade ε n :=
  (nextPower ε n).mkQ.restrictScalars K

lemma gradeQ_ker (n : ℕ) (x : ↥(ideal ε ^ n)) :
    gradeQ ε n x = 0 ↔ x.1 ∈ ideal ε ^ (n+1) :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def gradeCoord (n : ℕ) : K ≃ₗ[K] Grade ε n :=
  coord ε t ht ht0 n (gradeQ ε n) (Submodule.mkQ_surjective (nextPower ε n)) (gradeQ_ker ε n)

lemma gradeCoord_apply (n : ℕ) (a : K) :
    gradeCoord ε t ht ht0 n a = a • gradeClass ε n ⟨t ^ n, pow_mem ε t ht n⟩ := rfl

noncomputable def conormalQ : ↥(ideal ε ^ 1) →ₗ[K] (ideal ε).Cotangent :=
  ((ideal ε).toCotangent.restrictScalars K).comp
    ((LinearEquiv.ofEq (ideal ε ^ 1) (ideal ε) (pow_one _)).restrictScalars K).toLinearMap

lemma conormalQ_ker (x : ↥(ideal ε ^ 1)) :
    conormalQ ε x = 0 ↔ x.1 ∈ ideal ε ^ (1+1) := by
  exact (ideal ε).toCotangent_eq_zero _

noncomputable def conormalCoord : K ≃ₗ[K] (ideal ε).Cotangent :=
  coord ε t ht ht0 1 (conormalQ ε)
    ((ideal ε).toCotangent_surjective.comp (LinearEquiv.ofEq _ _ (pow_one (ideal ε))).surjective)
    (conormalQ_ker ε)

lemma conormalCoord_mul (a : A) (x : ideal ε) (hx : x.1 = a * t) :
    conormalCoord ε t ht ht0 (ε a) = (ideal ε).toCotangent x := by
  have h := class_scalar ε t ht ht0 1 (conormalQ ε) (conormalQ_ker ε) a
  change ε a • conormalQ ε ⟨t ^ 1, pow_mem ε t ht 1⟩ = _
  rw [← h]
  apply congrArg (ideal ε).toCotangent
  apply Subtype.ext
  simpa using hx.symm

noncomputable def tensorCoord (n : ℕ) : ConormalTensor ε n ≃ₗ[K] K :=
  (PiTensorProduct.congr (fun _ : Fin n => (conormalCoord ε t ht ht0).symm)).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin n) K).toLinearEquiv

noncomputable def multiplication (n : ℕ) : ConormalTensor ε n ≃ₗ[K] Grade ε n :=
  (tensorCoord ε t ht ht0 n).trans (gradeCoord ε t ht ht0 n)


lemma multiplication_spec (n : ℕ) :
    IsMultiplication ε n (multiplication ε t ht ht0 n) := by
  classical
  intro x b hb
  have hx (i : Fin n) : ∃ a : A, a * t = (x i).1 := by
    have h := (x i).2
    simpa only [ht, Ideal.mem_span_singleton'] using h
  choose a ha using hx
  have hc (i : Fin n) : (conormalCoord ε t ht ht0).symm
      ((ideal ε).toCotangent (x i)) = ε (a i) := by
    apply (conormalCoord ε t ht ht0).injective
    rw [LinearEquiv.apply_symm_apply, conormalCoord_mul ε t ht ht0 (a i) (x i) (ha i).symm]
  have hb' : b.1 = (∏ i, a i) * t ^ n := by
    rw [hb]
    simp_rw [← ha]
    rw [Finset.prod_mul_distrib]
    simp
  change gradeCoord ε t ht ht0 n
    ((PiTensorProduct.constantBaseRingEquiv (Fin n) K)
      (PiTensorProduct.congr (fun _ : Fin n => (conormalCoord ε t ht ht0).symm)
        (PiTensorProduct.tprod K (fun i => (ideal ε).toCotangent (x i))))) = _
  rw [PiTensorProduct.congr_tprod]
  simp_rw [hc]
  rw [PiTensorProduct.constantBaseRingEquiv_tprod, ← map_prod, gradeCoord_apply]
  change ε (∏ i, a i) • gradeQ ε n ⟨t ^ n, pow_mem ε t ht n⟩ = gradeQ ε n b
  rw [← class_scalar ε t ht ht0 n (gradeQ ε n) (gradeQ_ker ε n)]
  congr 1
  exact Subtype.ext hb'.symm

lemma multiplication_unique (n : ℕ) (e f : ConormalTensor ε n ≃ₗ[K] Grade ε n)
    (he : IsMultiplication ε n e) (hf : IsMultiplication ε n f) : e = f := by
  classical
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro z
  choose x hx using fun i => (ideal ε).toCotangent_surjective (z i)
  have hmem : (∏ i, (x i).1) ∈ ideal ε ^ n := by
    simpa using (Ideal.prod_mem_prod (I := fun _ : Fin n => ideal ε)
      (s := Finset.univ) (x := fun i => (x i).1) (fun i _ => (x i).2))
  let b : ↥(ideal ε ^ n) := ⟨_, hmem⟩
  have hz : z = fun i => (ideal ε).toCotangent (x i) := funext (fun i => (hx i).symm)
  change e (PiTensorProduct.tprod K z) = f (PiTensorProduct.tprod K z)
  rw [hz, he x b rfl, hf x b rfl]

end CartierGradedTensor

/-- Multiplication identifies every graded piece of a nonzero principal
augmentation ideal with the corresponding conormal tensor power. -/
theorem cartier_graded_tensor :
    ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [IsDomain A] [Algebra K A]
      (ε : A →ₐ[K] K), (ideal ε).IsPrincipal → ideal ε ≠ ⊥ →
      ∀ n : ℕ, ∃! e : ConormalTensor ε n ≃ₗ[K] Grade ε n, IsMultiplication ε n e := by
  intro K _ A _ _ _ ε hp hn n
  obtain ⟨t, ht⟩ := hp.principal
  have ht0 : t ≠ 0 := by
    intro h
    apply hn
    simpa [h] using ht
  exact ⟨CartierGradedTensor.multiplication ε t ht ht0 n,
    CartierGradedTensor.multiplication_spec ε t ht ht0 n,
    fun e he => CartierGradedTensor.multiplication_unique ε n e _ he
      (CartierGradedTensor.multiplication_spec ε t ht ht0 n)⟩

end ArithmeticThetaConormalInitialR0162
