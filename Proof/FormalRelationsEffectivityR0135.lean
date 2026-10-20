module

public import FormalHomogeneousPresentationR0135
public import Mathlib.RingTheory.Polynomial.Basic

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Exact reduction and homogeneous finite generation of the tagged relation ideal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace ArithmeticThetaProjectiveEffectivityR0135
namespace FormalRelationsEffectivityR0135
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalHomogeneousPresentationR0135 CompatibleFormalSectionBasisR0134
open MvPolynomial

lemma tag_monomial {S B J : Type*} [CommRing S] [CommRing B]
    (f : S →+* B) (v : J → B) (m : J →₀ ℕ) (c : S) :
    eval₂Hom (Polynomial.C.comp f) (fun j => Polynomial.C (v j) * Polynomial.X)
      (monomial m c) = Polynomial.C (eval₂Hom f v (monomial m c)) * Polynomial.X ^ m.degree := by
  classical
  simp only [eval₂Hom_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  rw [map_mul]
  ring

lemma tag_homogeneous {S B J : Type*} [CommRing S] [CommRing B]
    (f : S →+* B) (v : J → B) {p : MvPolynomial J S} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    eval₂Hom (Polynomial.C.comp f) (fun j => Polynomial.C (v j) * Polynomial.X) p =
      Polynomial.C (eval₂Hom f v p) * Polynomial.X ^ d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, add_mul]
  | monomial m c hm =>
    rw [tag_monomial]
    congr 1
    congr 1
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hm

/-- The degree tag extracts the evaluation of precisely one homogeneous component. -/
lemma tag_component {S B J : Type*} [CommRing S] [CommRing B]
    (f : S →+* B) (v : J → B) (p : MvPolynomial J S) (d : ℕ) :
    Polynomial.coeff
      (eval₂Hom (Polynomial.C.comp f) (fun j => Polynomial.C (v j) * Polynomial.X) p) d =
        eval₂Hom f v (homogeneousComponent d p) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent p]
  simp only [map_sum, Polynomial.finsetSum_coeff,
    tag_homogeneous f v (homogeneousComponent_isHomogeneous _ _), Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d ∈ Finset.range (p.totalDegree+1)
  · simp [hd]
  · have hz : homogeneousComponent d p = 0 := homogeneousComponent_eq_zero d p
      (by simp only [Finset.mem_range] at hd; omega)
    simp [hd, hz]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

omit [CharZero k] in
lemma map_component (n d : ℕ) (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) :
    coefficientReduction k r n (homogeneousComponent d p) =
      homogeneousComponent d (coefficientReduction k r n p) := by
  ext m
  simp only [coefficientReduction, coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

lemma mem_formal (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) :
    p ∈ formalRelations k b ↔ ∀ n i,
      taggedEvaluate k b n i (coefficientReduction k r n p) = 0 := by
  simp [formalRelations, relationsAt, Ideal.mem_comap, RingHom.mem_ker]

lemma reduction_le (n : ℕ) :
    Ideal.map (coefficientReduction k r n) (formalRelations k b) ≤ relationsAt k b n := by
  apply Ideal.map_le_iff_le_comap.mpr
  exact iInf_le _ n

lemma good_C (c : PowerSeries k) : Good k b 0 (C c) := by
  refine ⟨isHomogeneous_C _ _, fun n i => ?_⟩
  simp only [eval_C, mul_zero, pow_zero, mul_one]
  exact RingHom.congr_fun (adjacent_base (T.overlap_spec n)) (trunc (PowerSeries k) PowerSeries.X n c)

lemma good_pow {d : ℕ} {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : Good k b d p) (e : ℕ) : Good k b (d*e) (p^e) := by
  induction e with
  | zero => simpa using good_C k b 1
  | succ e ih => simpa only [pow_succ, Nat.mul_succ] using good_mul k b ih hp

lemma good_monomial (m : Fin (3*r) →₀ ℕ) (c : PowerSeries k) :
    Good k b m.degree (monomial m c) := by
  classical
  induction m using Finsupp.induction with
  | zero => simpa using good_C k b c
  | single_add j e m hj he ih =>
    rw [map_add, Finsupp.degree_single, monomial_single_add]
    simpa only [one_mul] using good_mul k b (good_pow k b (good_X k b j) e) ih

lemma good_of_homogeneous {d : ℕ} {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : p.IsHomogeneous d) : Good k b d p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact good_zero k b d
  | add p q hp hq ihp ihq => exact good_add k b ihp ihq
  | monomial m c hm =>
    have hm' : m.degree = d := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hm
    rw [← hm']
    exact good_monomial k b m c

lemma eval_reduction (n : ℕ) (i : Fin r)
    (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) :
    eval₂Hom (base k n) (fun j => (b n j).val i) (coefficientReduction k r n p) =
      evaluate k b n i p := by
  exact eval₂_map _ _ _ p

lemma homogeneous_relation_iff (n d : ℕ)
    (p : MvPolynomial (Fin (3*r)) (R k n)) (hp : p.IsHomogeneous d) :
    p ∈ relationsAt k b n ↔ ∀ i, eval₂Hom (base k n) (fun j => (b n j).val i) p = 0 := by
  simp only [relationsAt, Ideal.mem_iInf, RingHom.mem_ker, taggedEvaluate,
    tag_homogeneous _ _ hp]
  constructor
  · intro h i
    have he := congrArg (fun q : Polynomial (A k n) => q.coeff d) (h i)
    simpa using he
  · intro h i
    simp [h i]

lemma component_relation (n d : ℕ) {p : MvPolynomial (Fin (3*r)) (R k n)}
    (hp : p ∈ relationsAt k b n) : homogeneousComponent d p ∈ relationsAt k b n := by
  apply (homogeneous_relation_iff k b n d _ (homogeneousComponent_isHomogeneous _ _)).mpr
  intro i
  rw [← tag_component]
  have he : taggedEvaluate k b n i p = 0 := (Ideal.mem_iInf.mp hp) i
  rw [show eval₂Hom (Polynomial.C.comp (base k n))
    (fun j => Polynomial.C ((b n j).val i) * Polynomial.X) p = 0 from he]
  simp

lemma formal_component (d : ℕ) {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : p ∈ formalRelations k b) : homogeneousComponent d p ∈ formalRelations k b := by
  apply Ideal.mem_iInf.mpr
  intro n
  change coefficientReduction k r n (homogeneousComponent d p) ∈ relationsAt k b n
  rw [map_component]
  exact component_relation k b n d (Ideal.mem_iInf.mp hp n)

lemma homogeneous_formal_iff {d : ℕ} {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : p.IsHomogeneous d) : p ∈ formalRelations k b ↔ ∀ n i, evaluate k b n i p = 0 := by
  constructor
  · intro h n i
    have hmem : coefficientReduction k r n p ∈ relationsAt k b n := Ideal.mem_iInf.mp h n
    have hz := (homogeneous_relation_iff k b n d _ (hp.map _)).mp hmem i
    exact (eval_reduction k b n i p).symm.trans hz
  · intro h
    apply Ideal.mem_iInf.mpr
    intro n
    apply (homogeneous_relation_iff k b n d _ (hp.map _)).mpr
    intro i
    exact (eval_reduction k b n i p).trans (h n i)

omit [CharZero k] in
lemma homogeneous_lift (n d : ℕ) (p : MvPolynomial (Fin (3*r)) (R k n))
    (hp : p.IsHomogeneous d) : ∃ q : MvPolynomial (Fin (3*r)) (PowerSeries k),
      q.IsHomogeneous d ∧ coefficientReduction k r n q = p := by
  obtain ⟨q, hq⟩ := map_surjective (trunc (PowerSeries k) PowerSeries.X n)
    Ideal.Quotient.mk_surjective p
  refine ⟨homogeneousComponent d q, homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [map_component]
  change homogeneousComponent d (MvPolynomial.map _ q) = p
  rw [hq, homogeneousComponent_eq_self hp]

/-- Basis coordinates give a correction invisible at the chosen finite stage. -/
lemma positive_relation_lift (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (n d : ℕ) (hd : 0 < d) (q : MvPolynomial (Fin (3*r)) (PowerSeries k))
    (hq : q.IsHomogeneous d)
    (hz : ∀ i, evaluate k b n i q = 0) :
    ∃ q' ∈ formalRelations k b, coefficientReduction k r n q' = coefficientReduction k r n q := by
  classical
  obtain ⟨p, hp, hbas⟩ := polynomial_bases k b h3 hb d hd
  let v : ∀ N, Fin ((3*d)*r) → Sections k r N hr (T.overlap N) a (3*d) :=
    fun N j => ⟨fun i => evaluate k b N i (p j), (hp j).2 N⟩
  let s : ∀ N, Sections k r N hr (T.overlap N) a (3*d) :=
    fun N => ⟨fun i => evaluate k b N i q, (good_of_homogeneous k b hq).2 N⟩
  obtain ⟨c, hc, _⟩ := formal_coordinates k r hr T a (3*d) v hbas
    (fun N P h j i => eval_reduce k b hb N P h i (p j)) s
    (fun N P h i => eval_reduce k b hb N P h i q)
  have hc0 : ∀ j, trunc (PowerSeries k) PowerSeries.X n (c j) = 0 := by
    obtain ⟨e, he, hu⟩ := hbas n (s n)
    have h1 := hu (fun j => trunc (PowerSeries k) PowerSeries.X n (c j)) (hc n)
    have h0 := hu (fun _ => 0) (fun i => by change evaluate k b n i q = _; simp [hz])
    intro j
    exact congrFun (h1.trans h0.symm) j
  let correction := ∑ j, C (c j) * p j
  have hcorr : correction.IsHomogeneous d :=
    (good_sum k b Finset.univ _ d (fun j _ => good_C_mul k b (hp j) (c j))).1
  have heval : ∀ N i, evaluate k b N i correction = evaluate k b N i q := by
    intro N i
    simp only [correction, map_sum, map_mul, eval_C]
    exact (hc N i).symm
  refine ⟨q-correction, (homogeneous_formal_iff k b (hq.sub hcorr)).mpr ?_, ?_⟩
  · intro N i
    rw [map_sub, heval, sub_self]
  · simp only [map_sub]
    have hred : coefficientReduction k r n correction = 0 := by
      simp [correction, coefficientReduction, hc0]
    rw [hred, sub_zero]

lemma base_injective (n : ℕ) : Function.Injective (base k n) := by
  obtain ⟨L, hL, _⟩ := ArithmeticThetaPolygonCohomologyR0131.truncated_laurent_presentation k n
  intro x y h
  have he := congrArg (ArithmeticThetaPolygonCohomologyR0131.PolygonCechKernelR0131.rightMap L) h
  rw [ArithmeticThetaPolygonCohomologyR0131.PolygonCechKernelR0131.right_base L hL,
    ArithmeticThetaPolygonCohomologyR0131.PolygonCechKernelR0131.right_base L hL] at he
  have he' := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff 0) he
  simpa [LaurentPolynomial.C_apply, AddMonoidAlgebra.coeff_single] using he'

lemma relation_lift (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (n d : ℕ) (p : MvPolynomial (Fin (3*r)) (R k n))
    (hp : p.IsHomogeneous d) (hz : p ∈ relationsAt k b n) :
    p ∈ Ideal.map (coefficientReduction k r n) (formalRelations k b) := by
  by_cases hd : d = 0
  · subst d
    have heq : p = C (p.coeff 0) := by
      exact (homogeneousComponent_eq_self hp).symm.trans (homogeneousComponent_zero p)
    have he := (homogeneous_relation_iff k b n 0 p hp).mp hz ⟨0, hr⟩
    rw [heq] at he
    simp only [eval₂Hom_C] at he
    have hc : p.coeff 0 = 0 := base_injective k n (he.trans (map_zero _).symm)
    rw [heq, hc, map_zero]
    exact Ideal.zero_mem _
  · obtain ⟨q, hq, hred⟩ := homogeneous_lift k n d p hp
    have heval : ∀ i, evaluate k b n i q = 0 := by
      intro i
      rw [← eval_reduction, hred]
      exact (homogeneous_relation_iff k b n d p hp).mp hz i
    obtain ⟨q', hq', hred'⟩ := positive_relation_lift k b h3 hb n d (Nat.pos_of_ne_zero hd) q hq heval
    rw [← hred, ← hred']
    exact Ideal.mem_map_of_mem _ hq'

lemma exact_reduction (h3 : 3 ≤ r) (hb : CompatibleBases k T a b) (n : ℕ) :
    Ideal.map (coefficientReduction k r n) (formalRelations k b) = relationsAt k b n := by
  apply le_antisymm (reduction_le k b n)
  intro p hp
  rw [← sum_homogeneousComponent p]
  apply Ideal.sum_mem
  intro d hd
  exact relation_lift k b h3 hb n d _ (homogeneousComponent_isHomogeneous _ _)
    (component_relation k b n d hp)

/-- Noetherianity is applied to the span of homogeneous elements of the actual kernel. -/
lemma finite_homogeneous_generators :
    ∃ (l : ℕ) (f : Fin l → MvPolynomial (Fin (3*r)) (PowerSeries k)) (degree : Fin l → ℕ),
      (∀ j, (f j).IsHomogeneous (degree j)) ∧ Ideal.span (Set.range f) = formalRelations k b := by
  classical
  let S : Set (MvPolynomial (Fin (3*r)) (PowerSeries k)) :=
    {p | p ∈ formalRelations k b ∧ ∃ d, p.IsHomogeneous d}
  have hspan : Ideal.span S = formalRelations k b := by
    apply le_antisymm (Ideal.span_le.mpr (fun p hp => hp.1))
    intro p hp
    rw [← sum_homogeneousComponent p]
    apply Ideal.sum_mem
    intro d hd
    exact Ideal.subset_span ⟨formal_component k b d hp, d, homogeneousComponent_isHomogeneous _ _⟩
  have hfg : (Ideal.span S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hsgen⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  let e := Fintype.equivFin ↥s
  let f : Fin (Fintype.card ↥s) → MvPolynomial (Fin (3*r)) (PowerSeries k) :=
    fun j => (e.symm j).val
  have hf (j) : f j ∈ S := hs (e.symm j).property
  choose degree hdegree using fun j => (hf j).2
  refine ⟨_, f, degree, hdegree, ?_⟩
  have hrange : Set.range f = (s : Set _) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact (e.symm j).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simp [f]
  rw [hrange]
  exact hsgen.symm.trans hspan

end FormalRelationsEffectivityR0135

/-- The single tagged homogeneous relation ideal realizes all finite relation ideals
and is generated by finitely many homogeneous polynomials over the complete base. -/
theorem formal_relations_effectivity :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ)
      (b : ArithmeticThetaProjectiveEffectivityR0135.CubicBases k r hr T a),
    ArithmeticThetaProjectiveEffectivityR0135.CompatibleBases k T a b →
      ArithmeticThetaProjectiveEffectivityR0135.RelationEffectivity k b := by
  intro k _ _ r hr h3 T a b hb
  exact ⟨FormalRelationsEffectivityR0135.exact_reduction k b h3 hb,
    FormalRelationsEffectivityR0135.finite_homogeneous_generators k b⟩

end ArithmeticThetaProjectiveEffectivityR0135
