module

public import AlgebraizedMarkedLineDefinitionsR0136
public import AlgebraizedGeometricConnectednessR0135
public import SplitFiniteMarkedDivisorR0133

@[expose] public section

/-! The algebraized marked union is a split finite étale subscheme. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135

namespace AlgebraizedSplitMarkedDivisorR0136
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

lemma section_closed (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) : IsClosedImmersion s := by
  let : IsProper M.p := hM.1
  have : IsClosedImmersion (s ≫ M.p) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s M.p

lemma sections_disjoint (hM : IsModel k T M)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X))
    (hs : LiftFamily k M a s) (i j : Fin r) (hij : i ≠ j) :
    Disjoint (Set.range (s i)) (Set.range (s j)) := by
  have hi := section_closed k M hM (s i) (hs i).1
  have hj := section_closed k M hM (s j) (hs j).1
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨w, hw⟩
  obtain ⟨y, hzy, hy⟩ :=
    AlgebraizedGenericSmoothnessR0135.specializes_closedFiber k M hM z
  obtain ⟨xi, hxi⟩ := hzy.mem_closed (s i).isClosedEmbedding.isClosed_range ⟨x, hx⟩
  obtain ⟨xj, hxj⟩ := hzy.mem_closed (s j).isClosedEmbedding.isClosed_range ⟨w, hw⟩
  have hi0 : xi = IsLocalRing.closedPoint (PowerSeries k) := by
    have h := (congrArg M.p hxi).trans hy
    change (s i ≫ M.p) xi = _ at h
    rw [(hs i).1] at h
    exact h
  have hj0 : xj = IsLocalRing.closedPoint (PowerSeries k) := by
    have h := (congrArg M.p hxj).trans hy
    change (s j ≫ M.p) xj = _ at h
    rw [(hs j).1] at h
    exact h
  obtain ⟨b, hb⟩ := AlgebraizedGenericSmoothnessR0135.closedPoint_in_baseInclusion k
  have he : (M.inclusion 0) (markedSection k r 0 hr (T.atlas 0) i (a i) b) =
      (M.inclusion 0) (markedSection k r 0 hr (T.atlas 0) j (a j) b) := by
    calc
      _ = s i (baseInclusion k 0 b) := by
        exact congrArg (fun f : specR k 0 ⟶ M.X => f b) ((hs i).2 0).symm
      _ = y := by rw [hb, ← hi0]; exact hxi
      _ = s j (baseInclusion k 0 b) := by rw [hb, ← hj0]; exact hxj.symm
      _ = _ := congrArg (fun f : specR k 0 ⟶ M.X => f b) ((hs j).2 0)
  have := AlgebraizedGeometricConnectednessR0135.stage_closed k M hM 0
  exact Set.disjoint_left.mp
    (CompatibleMarkingsR0131.disjoint_markings k r 0 hr (T.atlas 0) i j hij (a i) (a j))
    ⟨b, rfl⟩ ⟨b, ((M.inclusion 0).isClosedEmbedding.injective he).symm⟩

omit [CharZero k] in
lemma split_finite (r : ℕ) : IsFinite (splitStructure k r) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap (PowerSeries k) (Fin r → PowerSeries k)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

omit [CharZero k] in
lemma split_etale (r : ℕ) : Etale (splitStructure k r) := by
  apply HasRingHomProperty.Spec_iff.mpr
  change (algebraMap (PowerSeries k) (Fin r → PowerSeries k)).Etale
  exact RingHom.etale_algebraMap.mpr inferInstance
end AlgebraizedSplitMarkedDivisorR0136

/-- The actual intersection of algebraized section kernels is the labeled split divisor. -/
theorem algebraized_split_marked_divisor :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : Tower k r hr) (M : Model k T), IsModel k T M →
    ∀ (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)),
      LiftFamily k M a s → SplitDivisor k M s := by
  intro k _ _ r hr _h3 T M hM a s hs
  have hsc (i : Fin r) : IsClosedImmersion (s i) :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM (s i) (hs i).1
  let m : (∐ fun _ : Fin r => baseScheme k) ⟶ M.X := Sigma.desc s
  have hm : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
      (AlgebraizedSplitMarkedDivisorR0136.sections_disjoint k M hM a s hs)
  let I := markedIdeal k M s
  have hker : I = m.ker := by
    rw [← m.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin r => baseScheme k))]
    change (⨅ i, (s i).ker) = _
    congr 1
    funext i
    congr 1
    exact (Sigma.ι_desc s i).symm
  have hker' : I.subschemeι.ker = m.ker := by
    rw [I.ker_subschemeι, hker]
  let f : (∐ fun _ : Fin r => baseScheme k) ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι m hker'.le
  have hf : f ≫ I.subschemeι = m := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ hker'
  let q := sigmaSpec (fun _ : Fin r => CommRingCat.of (PowerSeries k))
  have : IsOpenImmersion q := by
    classical
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have ht : DFinsupp.single (β := fun _ : Fin r => PowerSeries k) j 1 j ∈ y.asIdeal :=
      (PrimeSpectrum.ext_iff.mp heq).le
        (x := DFinsupp.single j 1)
        (show DFinsupp.single (β := fun _ : Fin r => PowerSeries k) j 1 i ∈ x.asIdeal by
          simp [hij.symm])
    simp [← Ideal.eq_top_iff_one, y.2.ne_top] at ht
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin r => PowerSeries k)).surjective x
    refine ⟨Sigma.ι (fun _ : Fin r => baseScheme k) i y, ?_⟩
    change (Sigma.ι (fun _ : Fin r => Spec (CommRingCat.of (PowerSeries k))) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : Fin r => Spec (CommRingCat.of (PowerSeries k))) i ≫ q =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => PowerSeries k) i)) from
        ι_sigmaSpec _ i]
    exact hy
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩
  let e : I.subscheme ≅ Spec (CommRingCat.of (Fin r → PowerSeries k)) :=
    (asIso f).symm ≪≫ asIso q
  have hq : q ≫ splitStructure k r = m ≫ M.p := by
    apply Sigma.hom_ext
    intro i
    simp only [q, ι_sigmaSpec_assoc, m, Sigma.ι_desc_assoc]
    rw [(hs i).1]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => PowerSeries k) i)) ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi (fun _ : Fin r => RingHom.id (PowerSeries k)))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of (PowerSeries k)) using 1
    congr 1
  have he : e.hom ≫ splitStructure k r = I.subschemeι ≫ M.p := by
    apply (cancel_epi f).mp
    simpa [e, Category.assoc, ← hf] using hq
  have hl (i : Fin r) : componentMap k r i ≫ e.inv ≫ I.subschemeι = s i := by
    rw [show componentMap k r i = Sigma.ι (fun _ : Fin r => baseScheme k) i ≫ q from
      (ι_sigmaSpec (fun _ : Fin r => CommRingCat.of (PowerSeries k)) i).symm]
    simp [e, Category.assoc, hf, m]
  have : IsFinite (splitStructure k r) := AlgebraizedSplitMarkedDivisorR0136.split_finite k r
  have : Etale (splitStructure k r) := AlgebraizedSplitMarkedDivisorR0136.split_etale k r
  refine ⟨inferInstance, ?_, ?_, e, he, hl⟩
  · change IsFinite (I.subschemeι ≫ M.p)
    rw [← he]
    infer_instance
  · change Etale (I.subschemeι ≫ M.p)
    rw [← he]
    infer_instance


end ArithmeticThetaAlgebraizedMarkedLineR0136
