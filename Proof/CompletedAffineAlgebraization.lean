module

public import CompletedChartDefinitions

@[expose] public section

/-! Algebraization of compatible completions of actual affine section modules.
The proof constructs Cech approximations from Cauchy representatives and applies
proper formal functions to the coherent structure sheaf. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AdicCompletion
universe u
namespace ArithmeticThetaCompletedCharts

private lemma pi_mem_parameter {R : Type u} [CommRing R] (t : R)
    {ι : Type u} {M : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (n : ℕ) (a : ∀ i, M i) :
    a ∈ (Ideal.span {t})^n • (⊤ : Submodule R (∀ i, M i)) ↔
      ∀ i, a i ∈ (Ideal.span {t})^n • (⊤ : Submodule R (M i)) := by
  simp only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨b, rfl⟩ i
    exact ⟨b i, rfl⟩
  · intro h
    choose b hb using h
    exact ⟨b, funext hb⟩

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R)

private lemma completedRestriction_comp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V)
    (z : Completed R X f t U) :
    completedRestriction R X f t k (completedRestriction R X f t h z) =
      completedRestriction R X f t (k.trans h) z := by
  change AdicCompletion.map _ _ (AdicCompletion.map _ _ z) = AdicCompletion.map _ _ z
  rw [AdicCompletion.map_comp_apply, ← OModulePresheaf.res_comp]

private lemma compatible_below (C : X.OrderedAffineCover)
    (z : CompletedFamily R X f t C) (hz : Compatible R X f t C z)
    (i j : C.ι) (W : X.Opens) (hi : W ≤ C.U i) (hj : W ≤ C.U j) :
    completedRestriction R X f t hi (z i) = completedRestriction R X f t hj (z j) := by
  have h := congrArg (completedRestriction R X f t (le_inf hi hj)) (hz i j)
  simpa only [completedRestriction_comp] using h

private lemma inter_zero (C : X.OrderedAffineCover) (s : C.Idx 0) :
    C.inter s = C.U (s.1 0) := by
  simp [Scheme.OrderedAffineCover.inter]

private lemma sequence_overlap (C : X.OrderedAffineCover)
    (q : ∀ i : C.ι, AdicCauchySequence (Ideal.span {t}) (Sections R X f (C.U i)))
    (hq : Compatible R X f t C (fun i => AdicCompletion.mk _ _ (q i)))
    (i j : C.ι) (W : X.Opens) (hi : W ≤ C.U i) (hj : W ≤ C.U j) (n : ℕ) :
    (OModulePresheaf.unit f).res hi (q i n) -
      (OModulePresheaf.unit f).res hj (q j n) ∈
        (Ideal.span {t})^n • (⊤ : Submodule R (Sections R X f W)) := by
  apply (Submodule.Quotient.eq _).mp
  exact congrArg (fun x : Completed R X f t W => x.val n)
    (compatible_below R X f t C _ hq i j W hi hj)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Compatible completed affine sections algebraize uniquely on a proper scheme. -/
theorem completed_affine_algebraization :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (C : X.OrderedAffineCover) (z : CompletedFamily R X f t C),
    Compatible R X f t C z → ∃! a : Sections R X f ⊤,
      ∀ i : C.ι, globalToCompleted R X f t (C.U i) a = z i := by
  intro R _ _ t _ X f _ C z hz
  classical
  let F := OModulePresheaf.unit f
  let I : Ideal R := Ideal.span {t}
  obtain ⟨q, hq⟩ := Classical.axiomOfChoice (fun i => AdicCompletion.mk_surjective I _ (z i))
  have hqc : Compatible R X f t C (fun i => AdicCompletion.mk I _ (q i)) := by
    simpa only [hq] using hz
  let a : ℕ → F.cochain C 0 := fun n s =>
    F.res (C.inter_le s 0) (q (s.1 0) (n+1))
  have hd (n : ℕ) : F.d C 0 (a n) ∈ I^(n+1) • (⊤ : Submodule R (F.cochain C 1)) := by
    apply (pi_mem_parameter t _ _).mpr
    intro s
    have h := sequence_overlap R X f t C q hqc (s.1 1) (s.1 0) (C.inter s)
      (C.inter_le s 1) (C.inter_le s 0) (n+1)
    change F.d C 0 (a n) s ∈ _
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      ← sub_eq_add_neg]
    change F.res (C.inter_le_inter_face s 0)
      (F.res (C.inter_le (C.face s 0) 0) (q (s.1 1) (n+1))) -
      F.res (C.inter_le_inter_face s 1)
      (F.res (C.inter_le (C.face s 1) 0) (q (s.1 0) (n+1))) ∈
      I^(n+1) • (⊤ : Submodule R (F.obj (C.inter s)))
    rw [F.res_res, F.res_res]
    exact h
  have ht (n : ℕ) : a (n+1) - a n ∈ I^(n+1) • (⊤ : Submodule R (F.cochain C 0)) := by
    apply (pi_mem_parameter t _ _).mpr
    intro s
    exact SModEq.sub_mem.mp (((q (s.1 0)).property (Nat.le_succ (n+1))).symm.map
      (F.res (C.inter_le s 0)) |>.mono (by
        rw [Submodule.map_smul'']; exact smul_mono_right _ le_top))
  have hc : F.IsCoherent := fun U => inferInstanceAs (Module.Finite Γ(X,U.1) Γ(X,U.1))
  obtain ⟨b, ⟨hdb, hb⟩, huniq⟩ :=
    OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
      I f F hc (OModulePresheaf.isQuasicoherent_unit f) C a hd ht
  letI : ∀ U : X.Opens, Module R Γ(X,U) := Scheme.OrderedAffineCoverOf.moduleSections f
  have hbR : b ∈ LinearMap.range (C.toCoverOf.aug f) := by
    rw [← C.toCoverOf.ker_d_zero_eq_range_aug f]
    exact hdb
  obtain ⟨g, hg⟩ := hbR
  have happrox (i : C.ι) (n : ℕ) :
      F.res (show C.U i ≤ ⊤ from le_top) g - q i (n+1) ∈
        I^(n+1) • (⊤ : Submodule R (F.obj (C.U i))) := by
    let s : C.Idx 0 := ⟨fun _ => i, by intro j k h; exact False.elim (by omega)⟩
    have hs : C.inter s = C.U i := inter_zero X C s
    have h := (pi_mem_parameter t _ _).mp (hb n) s
    have hg' := congrFun hg s
    change F.res (show C.inter s ≤ ⊤ from le_top) g = b s at hg'
    change b s - a n s ∈ _ at h
    rw [← hg'] at h
    dsimp [a] at h
    have hh : ∀ (W : X.Opens) (e : W ≤ C.U i) (e' : W ≤ ⊤), W = C.U i →
        F.res e' g - F.res e (q i (n+1)) ∈ I^(n+1) • (⊤ : Submodule R (F.obj W)) →
        F.res (show C.U i ≤ ⊤ from le_top) g - q i (n+1) ∈
          I^(n+1) • (⊤ : Submodule R (F.obj (C.U i))) := by
      intro W e e' he hw
      subst W
      simpa only [OModulePresheaf.res_refl_apply] using hw
    exact hh _ _ _ hs h
  have hglobal (i : C.ι) : globalToCompleted R X f t (C.U i) g = z i := by
    rw [← hq i]
    apply AdicCompletion.ext
    intro n
    change Submodule.Quotient.mk (F.res (show C.U i ≤ ⊤ from le_top) g) =
      Submodule.Quotient.mk (q i n)
    have h := happrox i n
    have hle : I^(n+1) • (⊤ : Submodule R (F.obj (C.U i))) ≤ I^n • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
    exact ((Submodule.Quotient.eq _).mpr (hle h)).trans
      (AdicCauchySequence.mk_eq_mk (Nat.le_succ n) (q i))
  refine ⟨g, hglobal, ?_⟩
  intro g' hg'
  apply C.toCoverOf.aug_injective f
  apply Eq.trans _ hg.symm
  apply huniq
  refine ⟨ArithmeticThetaGeometricPrerequisites.FormalBridge.global_cocycle R X f C g', ?_⟩
  intro n
  apply (pi_mem_parameter t _ _).mpr
  intro s
  have he := congrArg (completedRestriction R X f t (C.inter_le s 0)) (hg' (s.1 0))
  rw [← hq (s.1 0)] at he
  have hv := congrArg (fun x : Completed R X f t (C.inter s) => x.val (n+1)) he
  apply (Submodule.Quotient.eq _).mp
  change Submodule.Quotient.mk (F.res (show C.inter s ≤ ⊤ from le_top) g') =
    Submodule.Quotient.mk (F.res (C.inter_le s 0) (q (s.1 0) (n+1)))
  change Submodule.Quotient.mk
    (F.res (C.inter_le s 0) (F.res (show C.U (s.1 0) ≤ ⊤ from le_top) g')) =
      Submodule.Quotient.mk (F.res (C.inter_le s 0) (q (s.1 0) (n+1))) at hv
  simpa only [OModulePresheaf.res_res] using hv

#print axioms completed_affine_algebraization
end ArithmeticThetaCompletedCharts
