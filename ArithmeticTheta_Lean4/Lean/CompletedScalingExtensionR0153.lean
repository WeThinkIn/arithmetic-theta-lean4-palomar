import SplitNormDefinitionsR0153

/-! Completed scaling, constructed from the accepted compatible finite-stage maps. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
namespace CompletedScalingExtensionR0153
open ArithmeticThetaKatoAnnularR0152 ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaModelSymmetriesR0137
variable (k : Type u) [Field k] [CharZero k]
private abbrev chartIdeal : Ideal (Chart k) :=
  Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}

omit [CharZero k] in
private lemma parameter_eq :
    ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
  simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private instance chart_noetherian : IsNoetherianRing (Chart k) :=
  (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1 (by omega)).2.1

private instance chart_complete : IsAdicComplete (chartIdeal k) (Chart k) := by
  have h := AdicCompletion.isAdicComplete_map_algebraMap_of_fg
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (Submodule.fg_span (Set.finite_singleton _))
  have he : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k)) = chartIdeal k := by
    simp only [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : Chart k => Ideal.span {z}) (parameter_eq k)
  rw [he] at h
  exact h

private abbrev comparison (n : ℕ) : HatA k n ≃+* A k n :=
  Classical.choose (finite_stage_completion_comparison k n)

private lemma reduction_complete (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
        (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec
    (Classical.choose_spec (finite_stage_completion_comparison k n))).1 a

private lemma approx (n : ℕ) (z : Chart k) :
    ∃ a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k,
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈ chartIdeal k ^ (n+1) := by
  obtain ⟨a, ha⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by omega)).2.2.2.2.2.2 (n+1) z
  refine ⟨ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 a, ?_⟩
  change z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k _ ∈
    (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1}) ^ (n+1) at ha
  rw [parameter_eq] at ha
  exact ha

private lemma reduction_transition (n N : ℕ) (h : n ≤ N) :
    (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h).comp
      (ArithmeticThetaKatoAnnularR0152.reduction k N) = ArithmeticThetaKatoAnnularR0152.reduction k n := by
  apply RingHom.ext
  intro z
  obtain ⟨a, ha⟩ := approx k N z
  have hN : trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) N z =
      trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) N
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) := Ideal.Quotient.eq.mpr ha
  have hn : trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z =
      trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) :=
    Ideal.Quotient.eq.mpr ((Ideal.pow_le_pow_right (by omega : n+1 ≤ N+1)) ha)
  change truncReduce _ _ n N h (comparison k N (trunc _ _ N z)) =
    comparison k n (trunc _ _ n z)
  rw [hN, hn]
  change truncReduce _ _ n N h (ArithmeticThetaKatoAnnularR0152.reduction k N _) = ArithmeticThetaKatoAnnularR0152.reduction k n _
  rw [reduction_complete, reduction_complete]
  rfl

private lemma reduction_base (n : ℕ) :
    (ArithmeticThetaKatoAnnularR0152.reduction k n).comp (ArithmeticThetaAnnularTorsionPrereqR0053.base k) =
      (base k n).comp (trunc (PowerSeries k) PowerSeries.X n) := by
  apply RingHom.ext
  intro a
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) a)) = _
  rw [reduction_complete]
  rfl

private lemma reduction_base_apply (n : ℕ) (b : PowerSeries k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      base k n (trunc (PowerSeries k) PowerSeries.X n b) :=
  RingHom.congr_fun (reduction_base k n) b

private lemma comparison_transition (n : ℕ) :
    (comparison k n).toRingHom.comp
        (Ideal.Quotient.factorPowSucc (chartIdeal k) (n+1)) =
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n (n+1) (Nat.le_succ n)).comp (comparison k (n+1)).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (RingHom.congr_fun (reduction_transition k n (n+1) (Nat.le_succ n)) a).symm


private def stage (a : kˣ) (n : ℕ) : Chart k →+* HatA k n :=
  (comparison k n).symm.toRingHom.comp
    ((TowerScalarTranslation.ringMap k n a).comp (ArithmeticThetaKatoAnnularR0152.reduction k n))

private lemma stage_compat (a : kˣ) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc (chartIdeal k) (n+1)).comp (stage k a (n+1)) =
      stage k a n := by
  apply RingHom.ext
  intro z
  apply (comparison k n).injective
  have hc := RingHom.congr_fun (comparison_transition k n) (stage k a (n+1) z)
  simp only [RingHom.comp_apply] at hc ⊢
  change comparison k n _ = _ at hc
  rw [hc]
  change truncReduce _ _ n (n+1) _
    (comparison k (n+1) ((comparison k (n+1)).symm
      (TowerScalarTranslation.ringMap k (n+1) a (ArithmeticThetaKatoAnnularR0152.reduction k (n+1) z)))) =
    comparison k n ((comparison k n).symm
      (TowerScalarTranslation.ringMap k n a (ArithmeticThetaKatoAnnularR0152.reduction k n z)))
  simp only [RingEquiv.apply_symm_apply]
  have ht := RingHom.congr_fun (TowerScalarTranslation.ringMap_reduce k n (n+1)
    (Nat.le_succ n) a) (ArithmeticThetaKatoAnnularR0152.reduction k (n+1) z)
  have hr := RingHom.congr_fun (reduction_transition k n (n+1) (Nat.le_succ n)) z
  simp only [RingHom.comp_apply] at ht hr
  rw [hr] at ht
  exact ht

private def scalingHom (a : kˣ) : Chart k →+* Chart k :=
  IsAdicComplete.StrictMono.liftRingHom (chartIdeal k)
    (show StrictMono (fun n : ℕ => n+1) from fun _ _ h => Nat.add_lt_add_right h 1)
    (stage k a) (fun {m} => stage_compat k a m)

private lemma scalingHom_reduction (a : kˣ) (n : ℕ) (z : Chart k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (scalingHom k a z) = TowerScalarTranslation.ringMap k n a (ArithmeticThetaKatoAnnularR0152.reduction k n z) := by
  change comparison k n (Ideal.Quotient.mk _ (scalingHom k a z)) = _
  rw [show Ideal.Quotient.mk _ (scalingHom k a z) = stage k a n z from
    IsAdicComplete.StrictMono.mk_liftRingHom (chartIdeal k) _ _ _ (n := n) z]
  exact (comparison k n).apply_symm_apply _

private lemma reduction_ext {z w : Chart k} (h : ∀ n, ArithmeticThetaKatoAnnularR0152.reduction k n z = ArithmeticThetaKatoAnnularR0152.reduction k n w) :
    z = w := by
  have he := IsHausdorff.StrictMono.funext' (chartIdeal k)
    (show StrictMono (fun n : ℕ => n+1) from fun _ _ h => Nat.add_lt_add_right h 1)
    (f := fun _ : Unit => z) (g := fun _ => w)
    (fun n _ => (comparison k n).injective (h n))
  exact congrFun he ()

private lemma reduction_x (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_complete]
  rfl

private lemma reduction_y (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [reduction_complete]
  rfl

private lemma scalingHom_base (a : kˣ) (b : PowerSeries k) :
    scalingHom k a (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k b := by
  apply reduction_ext k
  intro n
  rw [scalingHom_reduction]
  rw [reduction_base_apply]
  exact TowerScalarTranslation.ringMap_base k n a _

private lemma scalingHom_x (a : kˣ) :
    scalingHom k a (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C (a : k)) *
        ArithmeticThetaAnnularTorsionPrereqR0053.cx k := by
  apply reduction_ext k
  intro n
  rw [scalingHom_reduction, reduction_x, TowerScalarTranslation.ringMap_x,
    map_mul, reduction_x, reduction_base_apply]
  rfl

private lemma scalingHom_y (a : kˣ) :
    scalingHom k a (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C ((a⁻¹ : kˣ) : k)) *
        ArithmeticThetaAnnularTorsionPrereqR0053.cy k := by
  apply reduction_ext k
  intro n
  rw [scalingHom_reduction, reduction_y, TowerScalarTranslation.ringMap_y,
    map_mul, reduction_y, reduction_base_apply]
  rfl

private lemma scalingHom_inv (a : kˣ) (z : Chart k) :
    scalingHom k a (scalingHom k a⁻¹ z) = z := by
  apply reduction_ext k
  intro n
  rw [scalingHom_reduction, scalingHom_reduction]
  exact RingHom.congr_fun (TowerScalarTranslation.ringMap_inv k n a) _

private def scalingEquiv (a : kˣ) : Chart k ≃+* Chart k :=
  { scalingHom k a with
    invFun := scalingHom k a⁻¹
    left_inv := by intro z; simpa using scalingHom_inv k a⁻¹ z
    right_inv := scalingHom_inv k a }

private lemma completed_hom_ext (f g : Chart k →+* Chart k)
    (hf : ∀ b, f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k b)
    (hg : ∀ b, g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k b)
    (hx : f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cx k))
    (hy : f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) : f = g := by
  have hfg : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      exact (hf b).trans (hg b).symm
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  have hmap (q : Chart k →+* Chart k)
      (hq : ∀ b, q (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
        ArithmeticThetaAnnularTorsionPrereqR0053.base k b) :
      (chartIdeal k).map q = chartIdeal k := by
    change (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X}).map q = _
    rw [Ideal.map_span, Set.image_singleton, hq]
    rfl
  apply RingHom.ext
  intro z
  apply reduction_ext k
  intro n
  obtain ⟨b, hb⟩ := approx k n z
  have hm (q : Chart k →+* Chart k) (hq : (chartIdeal k).map q = chartIdeal k) :
      q z - q (ArithmeticThetaAnnularTorsionPrereqR0053.complete k b) ∈ chartIdeal k ^ (n+1) := by
    have hh := Ideal.mem_map_of_mem q hb
    rwa [Ideal.map_pow, hq, map_sub] at hh
  change comparison k n (Ideal.Quotient.mk _ (f z)) =
    comparison k n (Ideal.Quotient.mk _ (g z))
  apply congrArg (comparison k n)
  exact (Ideal.Quotient.eq.mpr (hm f (hmap f hf))).trans
    ((congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hfg b)).trans
      (Ideal.Quotient.eq.mpr (hm g (hmap g hg))).symm)

private lemma scaling_spec (a : kˣ) : IsScaling k a (scalingEquiv k a) :=
  ⟨scalingHom_base k a, scalingHom_x k a, scalingHom_y k a⟩

private lemma scaling_unique (a : kˣ) (e : Chart k ≃+* Chart k)
    (he : IsScaling k a e) : e = scalingEquiv k a := by
  apply RingEquiv.toRingHom_injective
  exact completed_hom_ext k e.toRingHom (scalingHom k a) he.1 (scalingHom_base k a)
    (he.2.1.trans (scalingHom_x k a).symm) (he.2.2.trans (scalingHom_y k a).symm)

private def genericEquiv (e : Chart k ≃+* Chart k)
    (he : e (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k) :
    ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k ≃+*
      ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k :=
  IsLocalization.ringEquivOfRingEquiv
    (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
    (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
    (M := Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
    (T := Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) e (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers he)

private lemma field_extension (a : kˣ) (e : Chart k ≃+* Chart k) (he : IsScaling k a e) :
    ∃! E : ChartField k ≃+* ChartField k, ExtendsScaling k e E := by
  have ht : e (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := he.1 PowerSeries.X
  let g := genericEquiv k e ht
  let E : ChartField k ≃+* ChartField k := IsFractionRing.ringEquivOfRingEquiv g
  have hE : ExtendsScaling k e E := by
    intro b
    change E (algebraMap _ _ (algebraMap (Chart k)
      (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) b)) = _
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rw [show g (algebraMap (Chart k) _ b) = algebraMap (Chart k) _ (e b) from
      IsLocalization.ringEquivOfRingEquiv_eq _ b]
    rfl
  refine ⟨E, hE, ?_⟩
  intro F hF
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
  suffices hh : F.toRingHom.comp (algebraMap _ _) = E.toRingHom.comp
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) (ChartField k)) by
    exact fun x => RingHom.congr_fun hh x
  apply IsLocalization.ringHom_ext (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  apply RingHom.ext
  intro b
  exact (hF b).trans (hE b).symm

end CompletedScalingExtensionR0153

/-- The prescribed scaling on the genuine completed chart and its fraction field
exists uniquely, without any additional continuity hypothesis. -/
theorem completed_scaling_extension :
    ∀ (k : Type u) [Field k] [CharZero k] (a : kˣ),
      ∃! e : ArithmeticThetaKatoAnnularR0152.Chart k ≃+* ArithmeticThetaKatoAnnularR0152.Chart k,
        IsScaling k a e ∧ (∃! E : ArithmeticThetaKatoAnnularR0152.ChartField k ≃+*
          ArithmeticThetaKatoAnnularR0152.ChartField k, ExtendsScaling k e E) := by
  intro k _ _ a
  refine ⟨CompletedScalingExtensionR0153.scalingEquiv k a, ⟨?_, ?_⟩, ?_⟩
  · exact CompletedScalingExtensionR0153.scaling_spec k a
  · exact CompletedScalingExtensionR0153.field_extension k a _
      (CompletedScalingExtensionR0153.scaling_spec k a)
  · intro e he
    exact CompletedScalingExtensionR0153.scaling_unique k a e he.1

end ArithmeticThetaSplitNormR0153

#print axioms ArithmeticThetaSplitNormR0153.completed_scaling_extension
