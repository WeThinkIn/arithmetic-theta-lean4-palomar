module

public import FormalConstantDefinitions
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

/-! Ring restrictions on actual parameter-adic completions. -/
open AlgebraicGeometry CategoryTheory
universe u v
noncomputable section
namespace ArithmeticThetaFormalConstants

section RingMaps
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Completion projections respect the inverse-system transitions. -/
lemma restriction_factor_eval (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have hc := c.2 h
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at hc
  exact Ideal.Quotient.eq.mpr (by simpa only [neg_sub] using Submodule.neg_mem _ hc)

/-- A ring map preserving ideals gives compatible quotient maps. -/
def restrictionLevel (I : Ideal A) (J : Ideal B) (g : A →+* B)
    (hg : I.map g ≤ J) (n : ℕ) : A ⧸ I ^ n →+* B ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) g (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hg n)

lemma restrictionLevel_transition (I : Ideal A) (J : Ideal B) (g : A →+* B)
    (hg : I.map g ≤ J) {m n : ℕ} (h : m ≤ n) (x : A ⧸ I ^ n) :
    Ideal.Quotient.factorPow J h (restrictionLevel I J g hg n x) =
      restrictionLevel I J g hg m (Ideal.Quotient.factorPow I h x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

lemma restriction_compatible (I : Ideal A) (J : Ideal B) (g : A →+* B)
    (hg : I.map g ≤ J) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp
      ((restrictionLevel I J g hg n).comp (AdicCompletion.evalₐ I n).toRingHom) =
      (restrictionLevel I J g hg m).comp (AdicCompletion.evalₐ I m).toRingHom := by
  apply RingHom.ext
  intro x
  change Ideal.Quotient.factorPow J h
    (restrictionLevel I J g hg n (AdicCompletion.evalₐ I n x)) = _
  rw [restrictionLevel_transition, restriction_factor_eval]
  rfl

/-- The inverse limit ring map uses the actual quotient ring structures. -/
def completionRestriction (I : Ideal A) (J : Ideal B) (g : A →+* B)
    (hg : I.map g ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (restrictionLevel I J g hg n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (restriction_compatible I J g hg)

lemma completionRestriction_of (I : Ideal A) (J : Ideal B) (g : A →+* B)
    (hg : I.map g ≤ J) (a : A) :
    completionRestriction I J g hg (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion J B) (g a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  unfold completionRestriction
  rw [AdicCompletion.evalₐ_liftRingHom J _ (restriction_compatible I J g hg)]
  simp [AdicCompletion.algebraMap_apply, restrictionLevel]

/-- Finite generation of a principal ideal gives approximation with a divisible error. -/
lemma principal_completion_approximation (s : A)
    (x : AdicCompletion (Ideal.span {s}) A) (n : ℕ) :
    ∃ (a : A) (y : AdicCompletion (Ideal.span {s}) A),
      x = algebraMap A (AdicCompletion (Ideal.span {s}) A) a +
        algebraMap A (AdicCompletion (Ideal.span {s}) A) s ^ n * y := by
  let I : Ideal A := Ideal.span {s}
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule A A)
    (AdicCompletion.eval I A n x)
  have he : x - AdicCompletion.of I A a ∈
      (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton s)]
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, ← ha, sub_self]
  rw [show I ^ n = Ideal.span {s ^ n} from Ideal.span_singleton_pow s n,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at he
  obtain ⟨y, _, hy⟩ := he
  refine ⟨a, y, ?_⟩
  rw [Algebra.smul_def, map_pow] at hy
  simpa [AdicCompletion.algebraMap_apply, I, add_comm] using (eq_add_of_sub_eq hy.symm)

/-- No continuity hypothesis is needed: agreement on the original ring forces uniqueness. -/
lemma principal_completion_unique (s : A) (t : B) (g : A →+* B) (hst : g s = t)
    (p q : AdicCompletion (Ideal.span {s}) A →+*
      AdicCompletion (Ideal.span {t}) B)
    (hp : ∀ a, p (algebraMap A _ a) = algebraMap B _ (g a))
    (hq : ∀ a, q (algebraMap A _ a) = algebraMap B _ (g a)) : p = q := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, y, hx⟩ := principal_completion_approximation s x n
  have ht : AdicCompletion.evalₐ (Ideal.span {t}) n
      (algebraMap B (AdicCompletion (Ideal.span {t}) B) t) ^ n = 0 := by
    rw [← map_pow, ← map_pow]
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AdicCompletion.evalₐ_of]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hx]
  simp only [map_add, map_mul, map_pow, hp, hq, hst, ht, zero_mul, add_zero]
end RingMaps

/-- Every actual sheaf restriction extends uniquely to parameter-adic ring completions. -/
theorem completed_ring_restrictions
    (R : Type u) [CommRing R] (X : AlgebraicGeometry.Scheme.{u})
    (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of R))) (t : R)
    (U V : X.Opens) (h : V ≤ U) :
    ∃! phi : RingCompleted R X f t U →+* RingCompleted R X f t V,
      ExtendsRestriction R X f t h phi := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  let g : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
  have hs : g (structuralMap R X f U t) = structuralMap R X f V t :=
    (Scheme.TwoAffineOpenCover.restrictAlgHom f h).commutes t
  have hg : (Ideal.span {structuralMap R X f U t}).map g ≤
      Ideal.span {structuralMap R X f V t} := by
    rw [Ideal.map_span, Set.image_singleton, hs]
  let phi := completionRestriction _ _ g hg
  have hphi : ExtendsRestriction R X f t h phi := fun a =>
    completionRestriction_of _ _ g hg a
  refine ⟨phi, hphi, fun psi hpsi => ?_⟩
  exact principal_completion_unique _ _ g hs psi phi hpsi hphi

end ArithmeticThetaFormalConstants
