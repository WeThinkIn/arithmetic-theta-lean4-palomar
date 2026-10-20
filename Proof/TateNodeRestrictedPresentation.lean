module

public import TateNodeFiniteType
public import NoetherianAdicCompletion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaNodeCharts

section General
variable {R : Type*} [CommRing R] (I : Ideal R)

lemma completion_eval_kernel (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext z
  have hf : Function.Injective (Ideal.Quotient.factor
      (show I ^ n • (⊤ : Ideal R) ≤ I ^ n by simp)) := by
    have h : I ^ n • (⊤ : Ideal R) = I ^ n := by simp
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      using Ideal.map_mk_eq_bot_of_le (le_of_eq h.symm)
  rw [← Ideal.map_pow]
  change AdicCompletion.evalₐ I n z = 0 ↔
    z ∈ (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n)).restrictScalars R
  rw [← Ideal.smul_top_eq_map]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I z (by simp)]
  exact map_eq_zero_iff _ hf

def completionReduction (hI : I.FG) (n : ℕ) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃+*
      R ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (completion_eval_kernel I hI n).symm).trans
    ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ I n))

lemma completionReduction_mk (hI : I.FG) (n : ℕ) (z : AdicCompletion I R) :
    completionReduction I hI n (Ideal.Quotient.mk _ z) = AdicCompletion.evalₐ I n z := by
  simp [completionReduction]

end General

/-- The entire tower of finite reductions, including its zero-ring level. -/
theorem node_completion_finite_reductions :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ n : ℕ,
      ∃! e : (CompletedNode k ⧸ (completedIdeal k) ^ n) ≃+*
        (Node k ⧸ (nodeIdeal k) ^ n),
        ∀ a : Node k, e (Ideal.Quotient.mk ((completedIdeal k) ^ n)
          (toCompleted k a)) = Ideal.Quotient.mk ((nodeIdeal k) ^ n) a := by
  intro k _ _ n
  have := (node_noetherian_finite_type k).1
  have hid : completedIdeal k = (nodeIdeal k).map (toCompleted k) := by
    simp [completedIdeal, nodeIdeal, Ideal.map_span, Set.image_singleton]
  let e := (Ideal.quotEquivOfEq (congrArg (fun J => J ^ n) hid)).trans
    (completionReduction (nodeIdeal k) (IsNoetherian.noetherian _) n)
  have he (a : Node k) : e (Ideal.Quotient.mk _ (toCompleted k a)) =
      Ideal.Quotient.mk ((nodeIdeal k) ^ n) a := by
    simp [e, completionReduction_mk, toCompleted, AdicCompletion.algebraMap_apply,
      AdicCompletion.evalₐ_of]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.ext
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e z)
  have hz : Ideal.Quotient.mk _ (toCompleted k a) = z :=
    e.injective ((he a).trans ha)
  rw [← hz, he', he]


/-! Change of base ideal on every module quotient and on the inverse limit. -/
section ChangeBase
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

def baseQuotient (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top])).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp] lemma baseQuotient_mk (n : ℕ) (s : S) :
    baseQuotient I n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := rfl

lemma baseQuotient_transition {m n : ℕ} (h : m ≤ n)
    (z : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S h (baseQuotient I n z) =
      baseQuotient I m (AdicCompletion.transitionMap I S h z) := by
  induction z using Submodule.Quotient.induction_on
  rfl

def baseCompletion : AdicCompletion I S ≃ₗ[R]
    AdicCompletion (I.map (algebraMap R S)) S where
  toFun z := ⟨fun n => baseQuotient I n (z.val n), fun h => by
    rw [baseQuotient_transition, z.property h]⟩
  invFun z := ⟨fun n => (baseQuotient I n).symm (z.val n), fun h => by
    apply (baseQuotient I _).injective
    rw [← baseQuotient_transition]
    simp only [LinearEquiv.apply_symm_apply, z.property h]⟩
  left_inv z := by ext n; exact (baseQuotient I n).symm_apply_apply _
  right_inv z := by ext n; exact (baseQuotient I n).apply_symm_apply _
  map_add' z w := by ext n; exact map_add _ _ _
  map_smul' r z := by ext n; exact (baseQuotient I n).map_smul r (z.val n)

@[simp] lemma baseCompletion_of (s : S) :
    baseCompletion I (AdicCompletion.of I S s) =
      AdicCompletion.of (I.map (algebraMap R S)) S s := by
  ext n
  exact baseQuotient_mk I n s

end ChangeBase

/-! The completion of the canonical algebra map is a ring map. -/
section Presentation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

lemma completion_base_mk (a : AdicCompletion.AdicCauchySequence I S) :
    baseCompletion I (AdicCompletion.mk I S a) =
      AdicCompletion.mk (I.map (algebraMap R S)) S
        ⟨a.val, fun h => by
          have hh := a.property h
          rw [SModEq.sub_mem]
          change a.val _ - a.val _ ∈
            (((I.map (algebraMap R S)) ^ _ • (⊤ : Submodule S S)).restrictScalars R)
          simpa only [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
            Submodule.restrictScalars_top] using SModEq.sub_mem.mp hh⟩ := by
  ext n
  exact baseQuotient_mk I n (a.val n)

def completionMap : AdicCompletion I R →+* AdicCompletion (I.map (algebraMap R S)) S where
  toFun z := baseCompletion I (AdicCompletion.map I (Algebra.linearMap R S) z)
  map_zero' := by simp
  map_add' z w := by simp
  map_one' := by
    change baseCompletion I (AdicCompletion.map I (Algebra.linearMap R S)
      (AdicCompletion.of I R 1)) = 1
    rw [AdicCompletion.map_of, baseCompletion_of]
    change algebraMap S _ (algebraMap R S 1) = 1
    simp only [map_one]
  map_mul' z w := by
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
    obtain ⟨b, rfl⟩ := AdicCompletion.mk_surjective I R w
    change baseCompletion I (AdicCompletion.map I (Algebra.linearMap R S)
      (AdicCompletion.mkₐ I a * AdicCompletion.mkₐ I b)) = _
    rw [← map_mul]
    change baseCompletion I (AdicCompletion.map I (Algebra.linearMap R S)
      (AdicCompletion.mk I R (a * b))) = _
    simp only [AdicCompletion.map_mk, completion_base_mk]
    apply AdicCompletion.ext_evalₐ
    intro n
    simp [AdicCompletion.evalₐ_mk, AdicCompletion.AdicCauchySequence.map_apply_coe]

@[simp] lemma completionMap_of (r : R) :
    completionMap (S := S) I (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) (algebraMap R S r) := by
  change baseCompletion I (AdicCompletion.map I (Algebra.linearMap R S)
    (AdicCompletion.of I R r)) = AdicCompletion.of _ S _
  rw [AdicCompletion.map_of, baseCompletion_of]
  rfl

lemma completionMap_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (completionMap (S := S) I) :=
  (baseCompletion I).surjective.comp (AdicCompletion.map_surjective I h)

end Presentation

/-! Finite generation identifies the completed ideal image with ideal extension. -/
section Range
variable {R : Type*} [CommRing R] (I J : Ideal R)

lemma completion_subtype_range [Module.Finite R J] :
    (AdicCompletion.map I J.subtype).range = J.map (algebraMap R (AdicCompletion I R)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I J z
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using Ideal.add_mem _ ha hb
    | tmul r j =>
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
      change r * algebraMap R (AdicCompletion I R) (j : R) ∈ _
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ j.property)
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    exact ⟨AdicCompletion.of I J ⟨j, hj⟩, AdicCompletion.map_of I J.subtype _⟩

end Range

/-! Noetherian completion exactness gives the quotient presentation. -/
section Kernel
variable {R : Type*} [CommRing R] [IsNoetherianRing R] (I J : Ideal R)

lemma completion_quotient_kernel :
    RingHom.ker (completionMap (S := R ⧸ J) I) =
      J.map (algebraMap R (AdicCompletion I R)) := by
  have hfg : Function.Exact J.subtype (Algebra.linearMap R (R ⧸ J)) := by
    intro r
    change Ideal.Quotient.mk J r = 0 ↔ _
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have he := AdicCompletion.map_exact (I := I) J.injective_subtype hfg Ideal.Quotient.mk_surjective
  ext z
  change baseCompletion I (AdicCompletion.map I (Algebra.linearMap R (R ⧸ J)) z) = 0 ↔ _
  rw [map_eq_zero_iff _ (baseCompletion I).injective, he z]
  change z ∈ (AdicCompletion.map I J.subtype).range ↔ _
  rw [completion_subtype_range]

def completionQuotientEquiv :
    (AdicCompletion I R ⧸ J.map (algebraMap R (AdicCompletion I R))) ≃+*
      AdicCompletion (I.map (algebraMap R (R ⧸ J))) (R ⧸ J) :=
  (Ideal.quotEquivOfEq (completion_quotient_kernel I J).symm).trans
    ((completionMap (S := R ⧸ J) I).quotientKerEquivOfSurjective
      (completionMap_surjective I Ideal.Quotient.mk_surjective))

@[simp] lemma completionQuotientEquiv_mk (r : R) :
    completionQuotientEquiv I J (Ideal.Quotient.mk _
      (algebraMap R (AdicCompletion I R) r)) =
      algebraMap (R ⧸ J) _ (Ideal.Quotient.mk J r) := by
  simp only [completionQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    completionMap_of]
  rfl

end Kernel

/-! Compatible finite approximations determine an endomorphism of completion. -/
section Unique
variable {R : Type*} [CommRing R] (I : Ideal R)
lemma completion_endomorphism_eq_id (hI : I.FG)
    (happrox : ∀ n (z : AdicCompletion I R), ∃ r : R,
      z - algebraMap R (AdicCompletion I R) r ∈
        (I.map (algebraMap R (AdicCompletion I R))) ^ n)
    (f : AdicCompletion I R →+* AdicCompletion I R)
    (hf : ∀ r, f (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion I R) r) : f = RingHom.id _ := by
  have hcomp : f.comp (algebraMap R (AdicCompletion I R)) =
      algebraMap R (AdicCompletion I R) := RingHom.ext hf
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨r, hz⟩ := happrox n z
  have hr : Ideal.Quotient.mk (I ^ n) r = AdicCompletion.evalₐ I n z := by
    have hh := hz
    rw [← completion_eval_kernel I hI n] at hh
    change AdicCompletion.evalₐ I n (z - algebraMap R _ r) = 0 at hh
    rw [map_sub] at hh
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AdicCompletion.evalₐ_of, sub_eq_zero] at hh
    exact hh.symm
  have hm : f (z - algebraMap R (AdicCompletion I R) r) ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
    have hh := Ideal.mem_map_of_mem f hz
    rwa [← Ideal.map_pow, Ideal.map_map, hcomp, Ideal.map_pow] at hh
  rw [← completion_eval_kernel I hI n] at hm
  change AdicCompletion.evalₐ I n (f (z - algebraMap R _ r)) = 0 at hm
  rw [map_sub, hf, map_sub] at hm
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, sub_eq_zero, hr] using hm

end Unique

/-! Specialization to the literal polynomial node and its structural maps. -/
section Specialize
def completionCongrIdeal {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    AdicCompletion I R ≃+* AdicCompletion J R := h ▸ RingEquiv.refl _

@[simp] lemma completionCongrIdeal_of {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I = J) (r : R) : completionCongrIdeal h (algebraMap R _ r) =
      algebraMap R _ r := by subst J; rfl

variable (k : Type u) [Field k]

lemma polynomialIdeal_map : (polynomialIdeal k).map (algebraMap (PolynomialChart k) (Node k)) =
    nodeIdeal k := by
  simp only [polynomialIdeal, nodeIdeal, Ideal.map_span, Set.image_singleton]
  congr 1

lemma restrictedRelationIdeal_map :
    (relationIdeal k).map (algebraMap (PolynomialChart k) (RestrictedPolynomial k)) =
      restrictedRelationIdeal k := by
  simp [relationIdeal, restrictedRelationIdeal, Ideal.map_span, Set.image_singleton,
    toRestricted]

def presentationEquiv : RestrictedNode k ≃+* CompletedNode k :=
  (Ideal.quotEquivOfEq (restrictedRelationIdeal_map k).symm).trans
    ((completionQuotientEquiv (polynomialIdeal k) (relationIdeal k)).trans
      (completionCongrIdeal (polynomialIdeal_map k)))

lemma presentationEquiv_polynomial (p : PolynomialChart k) :
    presentationEquiv k (restrictedNodeMap k p) = toCompleted k (quotientMap k p) := by
  unfold presentationEquiv restrictedNodeMap toRestricted toCompleted quotientMap
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, completionQuotientEquiv_mk, completionCongrIdeal_of]
theorem node_restricted_presentation :
    ∀ (k : Type u) [Field k] [CharZero k],
      ∃! e : CompletedNode k ≃+* RestrictedNode k,
        e.toRingHom.comp ((toCompleted k).comp (quotientMap k)) = restrictedNodeMap k := by
  intro k _ _
  let e := (presentationEquiv k).symm
  have he : e.toRingHom.comp ((toCompleted k).comp (quotientMap k)) =
      restrictedNodeMap k := by
    apply RingHom.ext
    intro p
    apply (presentationEquiv k).injective
    exact ((presentationEquiv k).apply_symm_apply _).trans
      (presentationEquiv_polynomial k p).symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hf : (presentationEquiv k).toRingHom.comp e'.toRingHom = RingHom.id _ := by
    have happrox : ∀ n (z : CompletedNode k), ∃ a : Node k,
        z - toCompleted k a ∈ ((nodeIdeal k).map (toCompleted k)) ^ n := by
      intro n z
      obtain ⟨red, hred, _⟩ := node_completion_finite_reductions k n
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (red (Ideal.Quotient.mk _ z))
      refine ⟨a, ?_⟩
      have hz : Ideal.Quotient.mk ((completedIdeal k) ^ n) z =
          Ideal.Quotient.mk _ (toCompleted k a) := red.injective (ha.symm.trans (hred a).symm)
      have hid : (nodeIdeal k).map (toCompleted k) = completedIdeal k := by
        simp [nodeIdeal, completedIdeal, Ideal.map_span, Set.image_singleton]
      rw [hid]
      exact Ideal.Quotient.eq.mp hz
    apply completion_endomorphism_eq_id (nodeIdeal k) (Submodule.fg_span_singleton _) happrox
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp := RingHom.congr_fun he' p
    change e' (toCompleted k (quotientMap k p)) = restrictedNodeMap k p at hp
    change presentationEquiv k (e' (toCompleted k (quotientMap k p))) = _
    rw [hp, presentationEquiv_polynomial]
    rfl
  apply RingEquiv.ext
  intro z
  apply (presentationEquiv k).injective
  exact (RingHom.congr_fun hf z).trans ((presentationEquiv k).apply_symm_apply z).symm


end Specialize

end ArithmeticThetaNodeCharts
