module

public import GenericOverlapDefinitionsR0065

@[expose] public section

/-! Domainhood and faithfulness for the actual completed coordinate opens. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace ArithmeticThetaGenericOverlapR0065
namespace FaithfulnessSupport
open ArithmeticThetaAnnularGeometry.CompletedNodeSupport

lemma completion_principal_domain {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (t : R) (ht : t ≠ 0)
    (hp : (Ideal.span {t} : Ideal R).IsPrime) :
    IsDomain (AdicCompletion (Ideal.span {t}) R) := by
  let I : Ideal R := Ideal.span {t}
  let A := AdicCompletion I R
  let f : R →+* A := algebraMap R A
  letI : IsNoetherianRing A :=
    ArithmeticThetaFractionalCharts.noetherian_adic_completion R I
  letI : IsHausdorff I R := IsHausdorff.of_isDomain I hp.ne_top
  have hi : Function.Injective f := AdicCompletion.of_injective I R
  letI : Nontrivial A := hi.nontrivial
  letI : I.IsPrime := hp
  have hker : RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom =
      Ideal.span {f t} := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map I (Submodule.fg_span_singleton t)]
    simp only [I, Ideal.map_span, Set.image_singleton]
    rfl
  have hprime : (Ideal.span {f t} : Ideal A).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  have hreg : Function.Injective (fun a : A => f t * a) := by
    simpa only [Algebra.smul_def] using (smul_right_injective (M := A) ht)
  letI : IsAdicComplete (I.map f) A :=
    AdicCompletion.isAdicComplete_self I (Submodule.fg_span_singleton t)
  apply isDomain_of_regular_prime_separated hprime hreg
  intro a ha
  have hmem : a ∈ (⨅ n : ℕ, (I.map f) ^ n • ⊤ : Ideal A) := by
    rw [Submodule.mem_iInf]
    intro n
    simpa [I, Ideal.map_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      using ha n
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
    (IsAdicComplete.le_jacobson_bot (I.map f)), Ideal.mem_bot] at hmem
  exact hmem

lemma completion_approx_one {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (a : AdicCompletion I R) :
    ∃ r : R, a - algebraMap R _ r ∈ I.map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I a)
  refine ⟨r, ?_⟩
  rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI]
  change AdicCompletion.evalOneₐ I (a - algebraMap R _ r) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hr.symm

/-- A map whose kernel is repeatedly divisible by a proper element of a
Noetherian domain is faithful. -/
lemma injective_of_kernel_divisibility {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    (F : A →+* B) (x : A) (hx : ¬ IsUnit x) (hFx : F x ≠ 0)
    (hker : ∀ a, F a = 0 → x ∣ a) : Function.Injective F := by
  apply (injective_iff_map_eq_zero F).2
  intro a ha
  have hd : ∀ n : ℕ, x ^ n ∣ a := by
    intro n
    induction n generalizing a with
    | zero => simp
    | succ n ih =>
      obtain ⟨b, rfl⟩ := hker a ha
      have hb : F b = 0 := (mul_eq_zero.mp (by simpa using ha)).resolve_left hFx
      obtain ⟨c, hc⟩ := ih b hb
      exact ⟨c, by rw [hc, pow_succ]; ring⟩
  have hm : a ∈ (⨅ n : ℕ, (Ideal.span {x}) ^ n • ⊤ : Ideal A) := by
    rw [Submodule.mem_iInf]
    intro n
    simpa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hd n
  rw [Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree (Ideal.span {x})
    (show (Ideal.span {x} : Ideal A) ≠ ⊤ by simpa using hx), Ideal.mem_bot] at hm
  exact hm

lemma completed_restriction_injective {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain S] [IsNoetherianRing S]
    (t x : R) (f : R →+* S) (J : Ideal S) (hJfg : J.FG)
    (hx : (Ideal.span {x} : Ideal R) ≠ ⊤)
    (htx : t ∈ (Ideal.span {x} : Ideal R))
    (hfx : f x ≠ 0)
    (hJ : J ≠ ⊤)
    (hcomap : J.comap f ≤ Ideal.span {x})
    [IsDomain (AdicCompletion (Ideal.span {t}) R)]
    [IsDomain (AdicCompletion J S)]
    (F : AdicCompletion (Ideal.span {t}) R →+*
      AdicCompletion J S)
    (hF : ∀ r, F (algebraMap R _ r) = algebraMap S _ (f r))
    (hfil : ∀ a, a ∈ (Ideal.span {t}).map
      (algebraMap R (AdicCompletion (Ideal.span {t}) R)) →
      F a ∈ J.map
        (algebraMap S (AdicCompletion J S))) :
    Function.Injective F := by
  let I : Ideal R := Ideal.span {t}
  let A := AdicCompletion I R
  let B := AdicCompletion J S
  let i : R →+* A := algebraMap R A
  let q : S →+* B := algebraMap S B
  let K : Ideal R := Ideal.span {x}
  letI : IsNoetherianRing A :=
    ArithmeticThetaFractionalCharts.noetherian_adic_completion R I
  letI : Nontrivial (R ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hx
  have hIK : I ≤ K := by
    exact (Ideal.span_singleton_le_iff_mem K).mpr htx
  let rho : A →+* R ⧸ K := residueExtension I (Ideal.Quotient.mk K)
    (by simpa only [Ideal.mk_ker] using hIK)
  have hrhox : rho (i x) = 0 := by
    rw [show rho (i x) = Ideal.Quotient.mk K x from residueExtension_of _ _ _ x]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hxhat : ¬ IsUnit (i x) := by
    intro h
    exact not_isUnit_zero (hrhox ▸ h.map rho)
  letI : IsHausdorff J S := IsHausdorff.of_isDomain J hJ
  have hq : Function.Injective q := AdicCompletion.of_injective J S
  have hFx : F (i x) ≠ 0 := by
    rw [hF]
    exact fun h => hfx (hq (h.trans (map_zero q).symm))
  apply injective_of_kernel_divisibility F (i x) hxhat hFx
  intro a ha
  obtain ⟨r, hr⟩ := completion_approx_one I (Submodule.fg_span_singleton t) a
  have hFr : q (f r) ∈ J.map q := by
    have hh := hfil (a - i r) hr
    rw [map_sub, ha, hF, zero_sub] at hh
    exact neg_mem_iff.mp hh
  have hfr : f r ∈ J := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map J hJfg]
      at hFr
    change Ideal.Quotient.mk J (f r) = 0 at hFr
    exact Ideal.Quotient.eq_zero_iff_mem.mp hFr
  have hrx : r ∈ K := hcomap hfr
  have hax : a ∈ K.map i := by
    have hd : a - i r ∈ K.map i := Ideal.map_mono hIK hr
    have he := (K.map i).add_mem hd (Ideal.mem_map_of_mem i hrx)
    simpa only [sub_add_cancel] using he
  simpa only [K, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] using hax

lemma localization_branch {R : Type u} [CommRing R] [IsDomain R]
    (x y : R) (hp : (Ideal.span {x} : Ideal R).IsPrime)
    (hy : y ∉ (Ideal.span {x} : Ideal R)) :
    (Ideal.span {algebraMap R (Localization.Away y) (x*y)} :
      Ideal (Localization.Away y)).IsPrime ∧
    (Ideal.span {algebraMap R (Localization.Away y) (x*y)} :
      Ideal (Localization.Away y)).comap (algebraMap R (Localization.Away y)) =
      Ideal.span {x} := by
  let S := Localization.Away y
  let f : R →+* S := algebraMap R S
  have hd : Disjoint (Submonoid.powers y : Set R) (Ideal.span {x}) := by
    rw [Set.disjoint_left]
    intro z hz hzx
    obtain ⟨n, rfl⟩ := hz
    exact hy (hp.mem_of_pow_mem _ hzx)
  have he : (Ideal.span {f (x*y)} : Ideal S) = (Ideal.span {x}).map f := by
    rw [map_mul, Ideal.span_singleton_mul_right_unit
      (IsLocalization.Away.algebraMap_isUnit y), Ideal.map_span, Set.image_singleton]
  rw [he]
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers y) S _ hp hd,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers y) S hp hd⟩

open ArithmeticThetaNodeCharts
open ArithmeticThetaAnnularGeometry
open ArithmeticThetaIndexedOverlapsR0058

variable (k : Type u) [Field k] [CharZero k]

lemma branch_data (side : Bool) :
    (Ideal.span {ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side)} :
      Ideal (ArithmeticThetaNodeCharts.Node k)).IsPrime ∧
    ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side ∉
      (Ideal.span {ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side)} :
        Ideal (ArithmeticThetaNodeCharts.Node k)) := by
  letI := residue_parameter_isMaximal k
  letI : Field (AlgebraicNodeSupport.CrossingResolutionR1.Resid (parameter k)) :=
    Ideal.Quotient.field _
  open AlgebraicNodeSupport.CrossingResolutionR1 in
    cases side <;> simp only [Bool.not_false, Bool.not_true,
      ArithmeticThetaIndexedOverlapsR0058.nodeCoord, Bool.false_eq_true,
      if_false, if_true]
    · have he : RingHom.ker (branchY (parameter k)) = Ideal.span {x k} :=
        ker_branchY (parameter k)
      rw [← he]
      refine ⟨RingHom.ker_isPrime _, ?_⟩
      have hb : branchY (parameter k) (y k) = Polynomial.X := branchY_y (parameter k)
      intro h
      have hh : branchY (parameter k) (y k) = 0 := h
      rw [hb] at hh
      exact Polynomial.X_ne_zero hh
    · have he : RingHom.ker (branchX (parameter k)) = Ideal.span {y k} :=
        ker_branchX (parameter k)
      rw [← he]
      refine ⟨RingHom.ker_isPrime _, ?_⟩
      have hb : branchX (parameter k) (x k) = Polynomial.X := branchX_x (parameter k)
      intro h
      have hh : branchX (parameter k) (x k) = 0 := h
      rw [hb] at hh
      exact Polynomial.X_ne_zero hh

omit [CharZero k] in
lemma node_coordinates_product (side : Bool) :
    ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side) *
      ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side =
      ArithmeticThetaNodeCharts.t k := by
  cases side <;> simpa [ArithmeticThetaIndexedOverlapsR0058.nodeCoord, mul_comm]
    using node_xy k

omit [CharZero k] in
lemma node_equiv_t :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
      ArithmeticThetaNodeCharts.t k := by
  have he : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  change (Ideal.quotientEquivAlgOfEq (PowerSeries k) he)
    (Ideal.Quotient.mk _ (MvPolynomial.C (PowerSeries.X ^ 1))) =
    Ideal.Quotient.mk _ (MvPolynomial.C PowerSeries.X)
  rw [Ideal.quotientEquivAlgOfEq_mk]
  simp

lemma ot_eq (j : ℕ) (side : Bool) :
    ot k j side = algebraMap (ArithmeticThetaNodeCharts.Node k)
      (Open k j side) (ArithmeticThetaNodeCharts.t k) := by
  change (algebraMap _ _) (nodeEquiv k
    ((algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k))
      PowerSeries.X)) = _
  rw [show (algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k))
    PowerSeries.X = ArithmeticThetaScaledTateBridgeR0046.t k 1 by
    simp [ArithmeticThetaScaledTateBridgeR0046.t,
      ArithmeticThetaScaledTateBridgeR0046.parameter]]
  rw [node_equiv_t]

lemma open_algebra_data (j : ℕ) (side : Bool) :
    IsDomain (Open k j side) ∧ IsNoetherianRing (Open k j side) ∧
    (openIdeal k j side).IsPrime ∧ ot k j side ≠ 0 ∧
    (openIdeal k j side).comap (algebraMap (ArithmeticThetaNodeCharts.Node k)
      (Open k j side)) =
      Ideal.span {ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side)} := by
  letI : IsDomain (ArithmeticThetaNodeCharts.Node k) := (node_flat_domain_parameter k).1
  letI : IsNoetherianRing (ArithmeticThetaNodeCharts.Node k) :=
    (node_noetherian_finite_type k).1
  obtain ⟨hp, hy⟩ := branch_data k side
  have hy0 : ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side ≠ 0 :=
    fun h => hy (h ▸ Ideal.zero_mem _)
  have hi := IsLocalization.injective (Open k j side)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hy0)
  have hd := localization_branch _ _ hp hy
  rw [node_coordinates_product k side] at hd
  rw [← ot_eq k j side] at hd
  refine ⟨Localization.Away.isDomain hy0, inferInstance, hd.1, ?_, hd.2⟩
  rw [ot_eq]
  exact fun h => (node_flat_domain_parameter k).2.2.1
    (hi (h.trans (map_zero _).symm))

lemma open_map_t (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.t k 1) = ot k j side := by
  rw [ot_eq]
  change algebraMap _ _ (nodeEquiv k _) = _
  rw [node_equiv_t]

lemma open_hat_domain (j : ℕ) (side : Bool) : IsDomain (OpenHat k j side) := by
  obtain ⟨hdom, hnoeth, hp, ht, _⟩ := open_algebra_data k j side
  letI := hdom
  letI := hnoeth
  exact completion_principal_domain (ot k j side) ht hp

set_option backward.isDefEq.respectTransparency true in
lemma restriction_square (j : ℕ) (s : Bool)
    (F : Chart k →+* OpenHat k j s) (hR : IsRestriction k j s F)
    (r : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    F
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k)
        (AdicCompletion (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1})
          (ArithmeticThetaAnnularTorsionPrereqR0053.Node k)) r) =
      algebraMap (Open k j s) (AdicCompletion (openIdeal k j s) (Open k j s))
        (openMap k j s r) := by
  have hs := RingHom.congr_fun hR.1 r
  simp only [RingHom.comp_apply, ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaScaledTateBridgeR0046.toCompleted, completeOpen,
    AdicCompletion.algebraMap_apply, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
    ArithmeticThetaGenericOverlapR0065.OpenHat, ArithmeticThetaIndexedOverlapsR0058.OpenHat]
    at hs ⊢
  with_reducible_and_instances exact hs

lemma restriction_filtration (j : ℕ) (s : Bool)
    (F : Chart k →+* OpenHat k j s) (hR : IsRestriction k j s F)
    (a : Chart k)
    (ha : a ∈ (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1}).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k))) :
    F a ∈ (openIdeal k j s).map (algebraMap (Open k j s) (OpenHat k j s)) := by
  have he : (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1}).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k)) =
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k 1 := by
    simp only [Ideal.map_span, Set.image_singleton]
    change Ideal.span {_} = Ideal.span {_} ^ 1
    rw [pow_one]
    rfl
  rw [he] at ha
  have hh := hR.2 1 a ha
  simp only [hatPower, pow_one, openIdeal, Ideal.map_span, Set.image_singleton,
    completeOpen, AdicCompletion.algebraMap_apply,
    ArithmeticThetaGenericOverlapR0065.OpenHat, ArithmeticThetaIndexedOverlapsR0058.OpenHat] at hh ⊢
  with_reducible_and_instances exact hh

set_option backward.isDefEq.respectTransparency true

def oppositeCoord (side : Bool) : ArithmeticThetaAnnularTorsionPrereqR0053.Node k :=
  (nodeEquiv k).symm (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side))
lemma branch_comap (side : Bool) :
    (Ideal.span {ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side)}).comap
      (nodeEquiv k).toRingHom = Ideal.span {oppositeCoord k side} := by
  change (Ideal.span {ArithmeticThetaIndexedOverlapsR0058.nodeCoord k (!side)}).comap
    (nodeEquiv k) = _
  rw [← Ideal.map_symm (nodeEquiv k), Ideal.map_span, Set.image_singleton]
  rfl
lemma opposite_proper (side : Bool) :
    (Ideal.span {oppositeCoord k side} : Ideal _) ≠ ⊤ := by
  rw [← branch_comap]
  exact ((branch_data k side).1.comap (nodeEquiv k).toRingHom).ne_top
lemma equiv_preimage_dvd {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) (x y : S) (h : e a = x * y) : e.symm x ∣ a := by
  refine ⟨e.symm y, ?_⟩
  rw [← map_mul, ← h, e.symm_apply_apply]
lemma parameter_mem_opposite (side : Bool) :
    ArithmeticThetaScaledTateBridgeR0046.t k 1 ∈
      (Ideal.span {oppositeCoord k side} : Ideal _) := by
  apply Ideal.mem_span_singleton.mpr
  exact equiv_preimage_dvd (nodeEquiv k) _ _ _
    ((node_equiv_t k).trans (node_coordinates_product k side).symm)
lemma open_contract_opposite (j : ℕ) (side : Bool) :
    (openIdeal k j side).comap (openMap k j side) ≤ Ideal.span {oppositeCoord k side} := by
  rw [← branch_comap]
  change ((openIdeal k j side).comap
    ((algebraMap (ArithmeticThetaNodeCharts.Node k) (Open k j side)).comp
      (nodeEquiv k).toRingHom)) ≤ _
  rw [← Ideal.comap_comap, (open_algebra_data k j side).2.2.2.2]
lemma open_opposite_ne_zero (j : ℕ) (side : Bool) :
    openMap k j side (oppositeCoord k side) ≠ 0 := by
  intro h
  have hdiv := Ideal.mem_span_singleton.mp (parameter_mem_opposite k side)
  obtain ⟨a, ha⟩ := hdiv
  have htf : openMap k j side (ArithmeticThetaScaledTateBridgeR0046.t k 1) = 0 := by
    rw [ha, map_mul, h, zero_mul]
  exact (open_algebra_data k j side).2.2.2.1 ((open_map_t k j side).symm.trans htf)

lemma restriction_injective_of_spec (j : ℕ) (side : Bool)
    (F : Chart k →+* OpenHat k j side) (hR : IsRestriction k j side F) :
    Function.Injective F := by
  let R := ArithmeticThetaAnnularTorsionPrereqR0053.Node k
  let t : R := ArithmeticThetaScaledTateBridgeR0046.t k 1
  letI : IsNoetherianRing R :=
    (ArithmeticThetaScaledTateBridgeR0046.node_algebra k 1 (by omega)).2.1
  letI : IsDomain (Open k j side) := (open_algebra_data k j side).1
  letI : IsNoetherianRing (Open k j side) := (open_algebra_data k j side).2.1
  letI : IsDomain (AdicCompletion (Ideal.span {t}) R) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1
  letI : IsDomain (OpenHat k j side) := open_hat_domain k j side
  apply completed_restriction_injective t (oppositeCoord k side) (openMap k j side)
    (openIdeal k j side) (Ideal.fg_of_isNoetherianRing _) (opposite_proper k side)
    (parameter_mem_opposite k side) (open_opposite_ne_zero k j side)
    (open_algebra_data k j side).2.2.1.ne_top (open_contract_opposite k j side) F
  · exact restriction_square k j side F hR
  · exact restriction_filtration k j side F hR
lemma open_hat_restriction_injective (j : ℕ) (side : Bool) :
    Function.Injective (ArithmeticThetaCorrectedGammaR0061.restrict k j side) :=
  restriction_injective_of_spec k j side _
    (Classical.choose_spec (completed_coordinate_restrictions k j side).exists)

end FaithfulnessSupport

set_option backward.isDefEq.respectTransparency true in
/-- The actual generic coordinate opens are domains, and the specified completed
node restriction remains injective after inverting the structural parameter. -/
theorem generic_open_faithfulness :
    ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ) (side : Bool),
      IsDomain (GenericOpen k j side) ∧
      Function.Injective ((includeOpen k j side).comp
        (ArithmeticThetaCorrectedGammaR0061.restrict k j side)) := by
  intro k _ _ j side
  letI := FaithfulnessSupport.open_hat_domain k j side
  obtain ⟨hdom, hnoeth, hp, ht, _⟩ := FaithfulnessSupport.open_algebra_data k j side
  letI := hdom
  letI := hnoeth
  letI : IsHausdorff (ArithmeticThetaIndexedOverlapsR0058.openIdeal k j side)
      (ArithmeticThetaIndexedOverlapsR0058.Open k j side) :=
    IsHausdorff.of_isDomain _ hp.ne_top
  have hi : Function.Injective (ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side) :=
    AdicCompletion.of_injective _ _
  have ht' : openParameter k j side ≠ 0 := by
    intro h
    exact ht (hi (h.trans (map_zero _).symm))
  have hin : Function.Injective (includeOpen k j side) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht')
  exact ⟨Localization.Away.isDomain ht',
    hin.comp (FaithfulnessSupport.open_hat_restriction_injective k j side)⟩

end ArithmeticThetaGenericOverlapR0065
