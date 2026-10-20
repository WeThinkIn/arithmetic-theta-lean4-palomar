module

public import IndexedAdjacentCoordinatesR0058
public import Mathlib.RingTheory.AdicCompletion.RingHom

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
universe u

namespace ArithmeticThetaIndexedOverlapsR0058

private theorem eval_factor {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
      AdicCompletion.evalₐ I m z := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  apply Ideal.Quotient.eq.mpr
  have h := SModEq.sub_mem.mp (a.property hmn)
  have h' : (a.val m : R) - a.val n ∈ I ^ m := by
    simpa only [smul_eq_mul, Ideal.mul_top] using h
  simpa only [neg_sub] using (I ^ m).neg_mem h'

private def quotientEquiv {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (n : ℕ) :
    (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n) :=
  Ideal.quotientEquiv (I ^ n) (J ^ n) e (by
    rw [h, ← Ideal.map_pow]
    exact (Ideal.map_coe e (I ^ n)).symm)

private theorem quotientEquiv_mk {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (n : ℕ) (a : R) :
    quotientEquiv I J e h n (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk (J ^ n) (e a) := by
  exact Ideal.quotientEquiv_mk (I ^ n) (J ^ n) e (by
    rw [h, ← Ideal.map_pow]
    exact (Ideal.map_coe e (I ^ n)).symm) a

private theorem quotientEquiv_symm_mk {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (n : ℕ) (a : S) :
    (quotientEquiv I J e h n).symm (Ideal.Quotient.mk (J ^ n) a) =
      Ideal.Quotient.mk (I ^ n) (e.symm a) := by
  exact Ideal.quotientEquiv_symm_mk (I ^ n) (J ^ n) e
    (by rw [h, ← Ideal.map_pow]
        exact (Ideal.map_coe e (I ^ n)).symm) a

private theorem quotientEquiv_factor {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (quotientEquiv I J e h n).toRingHom =
      (quotientEquiv I J e h m).toRingHom.comp
        (Ideal.Quotient.factorPow I hmn) := by
  apply RingHom.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ a =>
      change (Ideal.Quotient.factorPow J hmn)
          (quotientEquiv I J e h n (Ideal.Quotient.mk (I ^ n) a)) =
        quotientEquiv I J e h m
          (Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) a))
      simp only [quotientEquiv_mk, Ideal.Quotient.factor_mk]

private theorem quotientEquiv_symm_factor {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (quotientEquiv I J e h n).symm.toRingHom =
      (quotientEquiv I J e h m).symm.toRingHom.comp
        (Ideal.Quotient.factorPow J hmn) := by
  apply RingHom.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ a =>
      change (Ideal.Quotient.factorPow I hmn)
          ((quotientEquiv I J e h n).symm (Ideal.Quotient.mk (J ^ n) a)) =
        (quotientEquiv I J e h m).symm
          (Ideal.Quotient.factorPow J hmn (Ideal.Quotient.mk (J ^ n) a))
      simp only [quotientEquiv_symm_mk, Ideal.Quotient.factor_mk]

private theorem completionForward_compatible {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp
        ((quotientEquiv I J e h n).toRingHom.comp
          (AdicCompletion.evalₐ I n).toRingHom) =
      (quotientEquiv I J e h m).toRingHom.comp
        (AdicCompletion.evalₐ I m).toRingHom := by
  intro m n hmn
  apply RingHom.ext
  intro z
  change (Ideal.Quotient.factorPow J hmn)
    (quotientEquiv I J e h n (AdicCompletion.evalₐ I n z)) =
    quotientEquiv I J e h m (AdicCompletion.evalₐ I m z)
  rw [← eval_factor I hmn z]
  exact RingHom.congr_fun (quotientEquiv_factor I J e h hmn) _

private theorem completionBackward_compatible {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp
        ((quotientEquiv I J e h n).symm.toRingHom.comp
          (AdicCompletion.evalₐ J n).toRingHom) =
      (quotientEquiv I J e h m).symm.toRingHom.comp
        (AdicCompletion.evalₐ J m).toRingHom := by
  intro m n hmn
  apply RingHom.ext
  intro z
  change (Ideal.Quotient.factorPow I hmn)
    ((quotientEquiv I J e h n).symm (AdicCompletion.evalₐ J n z)) =
    (quotientEquiv I J e h m).symm (AdicCompletion.evalₐ J m z)
  rw [← eval_factor J hmn z]
  exact RingHom.congr_fun (quotientEquiv_symm_factor I J e h hmn) _

private def completionForward {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (quotientEquiv I J e h n).toRingHom.comp
      (AdicCompletion.evalₐ I n).toRingHom)
    (completionForward_compatible I J e h)

private def completionBackward {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) : AdicCompletion J S →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (fun n => (quotientEquiv I J e h n).symm.toRingHom.comp
      (AdicCompletion.evalₐ J n).toRingHom)
    (completionBackward_compatible I J e h)

private theorem completionForward_eval {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (n : ℕ) (z : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionForward I J e h z) =
      quotientEquiv I J e h n (AdicCompletion.evalₐ I n z) := by
  exact AdicCompletion.evalₐ_liftRingHom J
    (fun n => (quotientEquiv I J e h n).toRingHom.comp
      (AdicCompletion.evalₐ I n).toRingHom)
    (completionForward_compatible I J e h) n z

private theorem completionBackward_eval {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (n : ℕ) (z : AdicCompletion J S) :
    AdicCompletion.evalₐ I n (completionBackward I J e h z) =
      (quotientEquiv I J e h n).symm (AdicCompletion.evalₐ J n z) := by
  exact AdicCompletion.evalₐ_liftRingHom I
    (fun n => (quotientEquiv I J e h n).symm.toRingHom.comp
      (AdicCompletion.evalₐ J n).toRingHom)
    (completionBackward_compatible I J e h) n z

private def completionEquiv {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) : AdicCompletion I R ≃+* AdicCompletion J S := by
  let F := completionForward I J e h
  let G := completionBackward I J e h
  have hleft (z : AdicCompletion I R) : G (F z) = z := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [completionBackward_eval, completionForward_eval]
    exact (quotientEquiv I J e h n).symm_apply_apply _
  have hright (z : AdicCompletion J S) : F (G z) = z := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [completionForward_eval, completionBackward_eval]
    exact (quotientEquiv I J e h n).apply_symm_apply _
  exact RingEquiv.ofBijective F
    ⟨fun x y hxy => by rw [← hleft x, ← hleft y, hxy],
      fun y => ⟨G y, hright y⟩⟩

private theorem completionEquiv_of {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (a : R) :
    completionEquiv I J e h (algebraMap R (AdicCompletion I R) a) =
      algebraMap S (AdicCompletion J S) (e a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n
    (completionForward I J e h (algebraMap R (AdicCompletion I R) a)) = _
  rw [completionForward_eval]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
    quotientEquiv_mk, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simp

private theorem completionEquiv_symm_of {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : J = I.map e) (a : S) :
    (completionEquiv I J e h).symm (algebraMap S (AdicCompletion J S) a) =
      algebraMap R (AdicCompletion I R) (e.symm a) := by
  apply (completionEquiv I J e h).injective
  rw [RingEquiv.apply_symm_apply, completionEquiv_of, e.apply_symm_apply]

variable (k : Type u) [Field k] [CharZero k]

private theorem adjacent_ideal (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    openIdeal k (next r j) true =
      (openIdeal k j false).map (adjacent k r j) := by
  have hbase := (indexed_adjacent_coordinates k r j hr hj).1
  have ht : adjacent k r j (ot k j false) = ot k (next r j) true :=
    DFunLike.congr_fun hbase PowerSeries.X
  simp [openIdeal, Ideal.map_span, Set.image_singleton, ht]

omit [CharZero k] in
private theorem hatPower_kernel (j : ℕ) (side : Bool) (n : ℕ) :
    hatPower k j side n =
      RingHom.ker (AdicCompletion.evalₐ (openIdeal k j side) n).toRingHom := by
  rw [ArithmeticThetaNodeCharts.completion_eval_kernel
    (openIdeal k j side) (by
      unfold openIdeal
      exact Submodule.fg_span_singleton (ot k j side)) n]
  unfold hatPower openIdeal
  congr 1
  rw [Ideal.map_span]
  simp [completeOpen]
  rfl

theorem completed_indexed_adjacent :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ), 0 < r → j < r →
      ∃! E : OpenHat k j false ≃+* OpenHat k (next r j) true,
        IsCompletedAdjacent k r j E := by
  intro k _ _ r j hr hj
  let I := openIdeal k j false
  let J := openIdeal k (next r j) true
  let e := adjacent k r j
  have hIJ : J = I.map e := adjacent_ideal k r j hr hj
  let E := completionEquiv I J e hIJ
  have ht : e (ot k j false) = ot k (next r j) true :=
    DFunLike.congr_fun (indexed_adjacent_coordinates k r j hr hj).1 PowerSeries.X
  have htback : e.symm (ot k (next r j) true) = ot k j false := by
    apply e.injective
    rw [e.apply_symm_apply, ht]
  have hcomm : E.toRingHom.comp (completeOpen k j false) =
      (completeOpen k (next r j) true).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact completionEquiv_of I J e hIJ a
  have hpow (n : ℕ) : hatPower k (next r j) true n =
      (hatPower k j false n).map E := by
    unfold hatPower
    rw [Ideal.map_pow]
    simp [Ideal.map_span, Set.image_singleton, E, I, J, e,
      completionEquiv_of, completeOpen]
    rw [ht]
  have hpowBack (n : ℕ) : hatPower k j false n =
      (hatPower k (next r j) true n).map E.symm := by
    unfold hatPower
    rw [Ideal.map_pow]
    simp [Ideal.map_span, Set.image_singleton, E, I, J, e,
      completionEquiv_symm_of, completeOpen]
    rw [htback]
  have hE : IsCompletedAdjacent k r j E := by
    refine ⟨hcomm, ?_, ?_⟩
    · intro n f hf
      rw [hpow n]
      exact Ideal.mem_map_of_mem E hf
    · intro n f hf
      rw [hpowBack n]
      exact Ideal.mem_map_of_mem E.symm hf
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  apply RingEquiv.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ I n z)
  have hz : z - completeOpen k j false a ∈ hatPower k j false n := by
    rw [hatPower_kernel]
    change AdicCompletion.evalₐ I n (z - completeOpen k j false a) = 0
    rw [map_sub]
    change AdicCompletion.evalₐ I n z -
      Ideal.Quotient.mk (I ^ n) a = 0
    exact sub_eq_zero.mpr ha.symm
  have hF := hE'.2.1 n (z - completeOpen k j false a) hz
  have hG := hE.2.1 n (z - completeOpen k j false a) hz
  rw [hatPower_kernel] at hF hG
  change AdicCompletion.evalₐ J n (E' (z - completeOpen k j false a)) = 0 at hF
  change AdicCompletion.evalₐ J n (E (z - completeOpen k j false a)) = 0 at hG
  have hcomp' := RingHom.congr_fun hE'.1 a
  have hcomp := RingHom.congr_fun hcomm a
  change E' (completeOpen k j false a) =
    completeOpen k (next r j) true (e a) at hcomp'
  change E (completeOpen k j false a) =
    completeOpen k (next r j) true (e a) at hcomp
  rw [map_sub, hcomp', map_sub] at hF
  rw [map_sub, hcomp, map_sub] at hG
  exact (sub_eq_zero.mp hF).trans (sub_eq_zero.mp hG).symm

end ArithmeticThetaIndexedOverlapsR0058
