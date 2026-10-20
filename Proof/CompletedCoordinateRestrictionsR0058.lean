module

public import IndexedFormalOverlapDefinitionsR0058
public import TateAnnularGeometryDefinitions

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
universe u

namespace ArithmeticThetaIndexedOverlapsR0058

open ArithmeticThetaAnnularTorsionPrereqR0053

variable (k : Type u) [Field k] [CharZero k]

private abbrev sourceNode := ArithmeticThetaAnnularTorsionPrereqR0053.Node k
private abbrev sourceIdeal : Ideal (sourceNode k) :=
  ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1

private lemma open_map_parameter (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
      ot k j side := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal,
      ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  have ht : nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
      ArithmeticThetaNodeCharts.t k := by
    change (Ideal.quotientEquivAlgOfEq (Base k) hrel)
        (Ideal.Quotient.mk _ (MvPolynomial.C (PowerSeries.X ^ 1))) =
      Ideal.Quotient.mk _ (MvPolynomial.C (PowerSeries.X))
    rw [Ideal.quotientEquivAlgOfEq_mk]
    simp
  have hsource : nodeEquiv k
      ((algebraMap (ArithmeticThetaScaledTateBridgeR0046.Base k)
        (ArithmeticThetaScaledTateBridgeR0046.Node k 1)) PowerSeries.X) =
      nodeEquiv k ((nodeBase k) PowerSeries.X) := by
    congr 1
  simpa [openMap, ot, openBase,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter] using
    congrArg (algebraMap (Node k j) (Open k j side)) hsource

private lemma source_parameter_map (j : ℕ) (side : Bool) :
    (completeOpen k j side).comp (openMap k j side)
        (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
      completeOpen k j side (ot k j side) := by
  exact congrArg (completeOpen k j side) (open_map_parameter k j side)

private lemma target_ideal_eq (j : ℕ) (side : Bool) :
    (openIdeal k j side).map (algebraMap (Open k j side) (OpenHat k j side)) =
      Ideal.span {completeOpen k j side (ot k j side)} := by
  simp [openIdeal, completeOpen, Ideal.map_span]

private lemma source_ideal_le (j : ℕ) (side : Bool) :
    sourceIdeal k ≤
      ((openIdeal k j side).map (algebraMap (Open k j side) (OpenHat k j side))).comap
        ((completeOpen k j side).comp (openMap k j side)) := by
  rw [show sourceIdeal k = Ideal.span {
      ArithmeticThetaScaledTateBridgeR0046.t k 1} by
    rfl]
  rw [Ideal.span_le]
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  change completeOpen k j side (openMap k j side
    (ArithmeticThetaScaledTateBridgeR0046.t k 1)) ∈
      (openIdeal k j side).map
        (algebraMap (Open k j side) (OpenHat k j side))
  rw [open_map_parameter]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton _))

private lemma target_complete (j : ℕ) (side : Bool) :
    IsAdicComplete
      ((openIdeal k j side).map (algebraMap (Open k j side) (OpenHat k j side)))
      (OpenHat k j side) := by
  exact AdicCompletion.isAdicComplete_self (openIdeal k j side)
    (Submodule.fg_span (by simp [openIdeal]))

private def adicStage {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)
    (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f
    ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow _ n))).comp
    (AdicCompletion.evalₐ I n).toRingHom

private lemma adicStage_compat {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (adicStage I J f h n) =
      adicStage I J f h m := by
  apply RingHom.ext
  intro z
  have hc : (Ideal.Quotient.factorPow J hmn).comp
      (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow _ n))) =
      (Ideal.quotientMap (J ^ m) f
        ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow _ m))).comp
        (Ideal.Quotient.factorPow I hmn) := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  have hh := RingHom.congr_fun hc (AdicCompletion.evalₐ I n z)
  simp only [RingHom.comp_apply] at hh
  rw [show Ideal.Quotient.factorPow I hmn
      (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z by
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R z
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    have ha := SModEq.sub_mem.mp (a.property hmn)
    simpa only [smul_eq_mul, Ideal.mul_top, neg_sub] using neg_mem ha] at hh
  exact hh

private def adicMap {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (adicStage I J f h)
    (adicStage_compat I J f h)

private lemma adicMap_of {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f) (r : R) :
    adicMap I J f h (algebraMap R _ r) = algebraMap S _ (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [adicMap, AdicCompletion.evalₐ_liftRingHom, adicStage,
    AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
    Ideal.quotientMap_mk]

private def adicLift {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →+* S) (h : I ≤ J.comap f) :
    AdicCompletion I R →+* S :=
  (AdicCompletion.ofAlgEquiv J).symm.toRingEquiv.toRingHom.comp
    (adicMap I J f h)

private lemma adicLift_of {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →+* S) (h : I ≤ J.comap f) (r : R) :
    adicLift I J f h (algebraMap R _ r) = f r := by
  change (AdicCompletion.ofAlgEquiv J).symm
      (adicMap I J f h (algebraMap R _ r)) = _
  rw [adicMap_of]
  exact AdicCompletion.ofAlgEquiv_symm_of J _

private lemma completion_approx (hI : (sourceIdeal k).FG)
    (j : ℕ) (n : ℕ) (z : Chart k j) :
    ∃ r : sourceNode k,
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k r ∈
        ((sourceIdeal k).map
          (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (sourceIdeal k) n z)
  refine ⟨r, ?_⟩
  have hk : RingHom.ker (AdicCompletion.evalₐ (sourceIdeal k) n).toRingHom =
      ((sourceIdeal k).map
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) ^ n := by
    ext w
    have hi : Function.Injective (Ideal.Quotient.factor
        (show (sourceIdeal k) ^ n • (⊤ : Ideal (sourceNode k)) ≤
          (sourceIdeal k) ^ n by simp)) := by
      have he : (sourceIdeal k) ^ n • (⊤ : Ideal (sourceNode k)) =
          (sourceIdeal k) ^ n := by simp
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq he.symm)
    rw [← Ideal.map_pow]
    change AdicCompletion.evalₐ (sourceIdeal k) n w = 0 ↔
      w ∈ (Ideal.map
        (algebraMap (sourceNode k) (ArithmeticThetaAnnularTorsionPrereqR0053.Chart k))
        ((sourceIdeal k) ^ n)).restrictScalars (sourceNode k)
    rw [← Ideal.smul_top_eq_map]
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    rw [← AdicCompletion.factor_eval_eq_evalₐ (sourceIdeal k) w (by simp)]
    exact map_eq_zero_iff _ hi
  rw [← hk]
  change AdicCompletion.evalₐ (sourceIdeal k) n
      (z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k r) = 0
  rw [map_sub]
  have hcomplete : AdicCompletion.evalₐ (sourceIdeal k) n
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k r) =
      Ideal.Quotient.mk _ r := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.complete,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted,
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  rw [hcomplete]
  exact sub_eq_zero.mpr hr.symm

private lemma completion_hom_ext (j : ℕ) (side : Bool)
    (J : Ideal (OpenHat k j side))
    [IsHausdorff J (OpenHat k j side)]
    (f g : Chart k j →+* OpenHat k j side)
    (hf : (sourceIdeal k).map
      (f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) ≤ J)
    (hfg : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) : f = g := by
  apply RingHom.ext
  apply congrFun
  apply IsHausdorff.funext' J
  intro n z
  obtain ⟨r, hr⟩ := completion_approx k
    (Submodule.fg_span (by simp [sourceIdeal])) j n z
  have hmem (q : Chart k j →+* OpenHat k j side)
      (hq : (sourceIdeal k).map
        (q.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) ≤ J) :
      q (z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k r) ∈ J ^ n := by
    have hm := Ideal.mem_map_of_mem q hr
    rw [Ideal.map_pow, Ideal.map_map] at hm
    exact Ideal.pow_right_mono hq n hm
  have hfz := hmem f hf
  have hgz := hmem g (hfg ▸ hf)
  rw [map_sub] at hfz hgz
  exact (Ideal.Quotient.eq.mpr hfz).trans
    ((congrArg (Ideal.Quotient.mk (J ^ n)) (RingHom.congr_fun hfg r)).trans
      (Ideal.Quotient.eq.mpr hgz).symm)

private noncomputable def restriction (j : ℕ) (side : Bool) :
    Chart k j →+* OpenHat k j side := by
  letI := target_complete k j side
  exact adicLift
    (sourceIdeal k)
    ((openIdeal k j side).map (algebraMap (Open k j side) (OpenHat k j side)))
    ((completeOpen k j side).comp (openMap k j side))
    (source_ideal_le k j side)

private lemma restriction_on_node (j : ℕ) (side : Bool) (z : sourceNode k) :
    restriction k j side (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z) =
      completeOpen k j side (openMap k j side z) := by
  letI := target_complete k j side
  change adicLift
      (sourceIdeal k)
      ((openIdeal k j side).map
        (algebraMap (Open k j side) (OpenHat k j side)))
      ((completeOpen k j side).comp (openMap k j side))
      (source_ideal_le k j side)
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z) = _
  simpa [ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaScaledTateBridgeR0046.toCompleted] using
    (adicLift_of
      (sourceIdeal k)
      ((openIdeal k j side).map
        (algebraMap (Open k j side) (OpenHat k j side)))
      ((completeOpen k j side).comp (openMap k j side))
      (source_ideal_le k j side) z)

private lemma restriction_filtered (j : ℕ) (side : Bool) (n : ℕ)
    (f : Chart k j) (hf : f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n) :
    restriction k j side f ∈ hatPower k j side n := by
  let K := (openIdeal k j side).map
    (algebraMap (Open k j side) (OpenHat k j side))
  have hK : K = Ideal.span {completeOpen k j side (ot k j side)} :=
    target_ideal_eq k j side
  have hmap :
      (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).map
          (restriction k j side) ≤ K ^ n := by
    have hfil : ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
        (sourceIdeal k).map
          (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) ^ n := by
      change Ideal.span {
          ArithmeticThetaScaledTateBridgeR0046.toCompleted k 1
            (ArithmeticThetaScaledTateBridgeR0046.t k 1)} ^ n =
        (Ideal.map (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)
          (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1})) ^ n
      rw [Ideal.map_span]
      simp only [Set.image_singleton]
      rfl
    rw [hfil, Ideal.map_pow, Ideal.map_map]
    have hcomp : (restriction k j side).comp
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
        (completeOpen k j side).comp (openMap k j side) := by
      apply RingHom.ext
      intro z
      exact restriction_on_node k j side z
    rw [hcomp]
    apply Ideal.pow_right_mono
    exact (Ideal.map_le_iff_le_comap).2 (source_ideal_le k j side)
  have hmf : restriction k j side f ∈
      (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).map
        (restriction k j side) := Ideal.mem_map_of_mem _ hf
  simpa [K, hatPower, target_ideal_eq k j side] using (hmap hmf)

theorem completed_coordinate_restrictions :
    ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ) (side : Bool),
      ∃! R : Chart k j →+* OpenHat k j side, IsRestriction k j side R := by
  intro k _ _ j side
  letI := target_complete k j side
  refine ⟨restriction k j side, ?_, ?_⟩
  · constructor
    · apply RingHom.ext
      intro z
      exact restriction_on_node k j side z
    · intro n f hf
      exact restriction_filtered k j side n f hf
  · intro R hR
    refine completion_hom_ext (k := k) j side
      ((openIdeal k j side).map
        (algebraMap (Open k j side) (OpenHat k j side)))
      R (restriction k j side) ?_ ?_
    · intro z hz
      rw [show sourceIdeal k = Ideal.span {
          ArithmeticThetaScaledTateBridgeR0046.t k 1} by rfl,
        Ideal.map_span] at hz
      have hfil := hR.2 1
          (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
          (ArithmeticThetaScaledTateBridgeR0046.t k 1)) (by
            simpa [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
              ArithmeticThetaScaledTateBridgeR0046.completedPower,
              ArithmeticThetaScaledTateBridgeR0046.completedParameter,
              ArithmeticThetaAnnularTorsionPrereqR0053.complete,
              ArithmeticThetaScaledTateBridgeR0046.toCompleted,
              ArithmeticThetaScaledTateBridgeR0046.t,
              ArithmeticThetaScaledTateBridgeR0046.nodeIdeal])
      have hcomp : R (complete k
          (ArithmeticThetaScaledTateBridgeR0046.t k 1)) =
          ((completeOpen k j side).comp
            (openMap k j side))
            (ArithmeticThetaScaledTateBridgeR0046.t k 1) := by
        simpa only [RingHom.comp_apply] using
          (RingHom.congr_fun hR.1
            (ArithmeticThetaScaledTateBridgeR0046.t k 1))
      have hsubset : Ideal.span
          (↑(R.comp (complete k)) ''
            {ArithmeticThetaScaledTateBridgeR0046.t k 1}) ≤
          (openIdeal k j side).map
            (algebraMap (Open k j side) (OpenHat k j side)) := by
        apply Ideal.span_le.2
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases Set.mem_singleton_iff.mp hy with rfl
        rw [RingHom.comp_apply]
        rw [hcomp]
        rw [hcomp] at hfil
        simpa [hatPower, target_ideal_eq k j side] using hfil
      exact hsubset hz
    · apply hR.1.trans
      symm
      apply RingHom.ext
      intro z
      exact restriction_on_node k j side z

end ArithmeticThetaIndexedOverlapsR0058
