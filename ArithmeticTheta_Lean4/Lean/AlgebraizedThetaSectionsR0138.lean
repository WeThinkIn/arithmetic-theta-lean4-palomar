import IdentityStageSectionRealizationR0138
import ThetaNumeratorCompatibilityR0138

/-! Algebraization of the literal theta numerators for the single identity divisor. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace AlgebraizedThetaSectionsR0138
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCartierR0133 GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (comap_power effective_invertible idealPullbackIso idealPullbackIso_inclusion
   chartIso chartIso_inclusion witness_iso pull_witness chartReduction_value
   compIso compIso_inclusion pullback_dual_completion)
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

local instance chart_open_instance (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (D.chart i) := D.chart_open i

local instance specA_affine (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))

lemma chart_principal (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (i : Fin r) :
    ∃ f : D.X.presheaf.obj (Opposite.op ((D.chart i) ''ᵁ ⊤)),
      IsRegular f ∧ (stageIdeal k D).ideal
        ⟨(D.chart i) ''ᵁ ⊤, (isAffineOpen_top (specA k n)).image_of_isOpenImmersion
          (D.chart i)⟩ = Ideal.span ({f} : Set _) := by
  letI : IsOpenImmersion (D.chart i) := D.chart_open i
  letI : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  let p := equation k r n i
  let e := ((D.chart i).appIso ⊤).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv
  refine ⟨e.symm p, regular_equiv e.symm (identity_chart_ideal k r n hr h3 E hE D i).2, ?_⟩
  have h := (identity_chart_ideal k r n hr h3 E hE D i).1
  unfold chartIdeal at h
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  have he : Ideal.map e.toRingHom ((stageIdeal k D).ideal
      ⟨(D.chart i) ''ᵁ ⊤, (isAffineOpen_top (specA k n)).image_of_isOpenImmersion
        (D.chart i)⟩) = Ideal.span ({p} : Set _) := by
    rw [show e.toRingHom = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom.comp
      ((D.chart i).appIso ⊤).hom.hom from rfl, ← Ideal.map_map]
    convert h using 1
    exact congrArg (Ideal.map _) (Ideal.map_comap_of_equiv ((D.chart i).appIso ⊤).commRingCatIsoToRingEquiv)
  apply_fun Ideal.map e.symm.toRingHom at he
  simpa [Ideal.map_map, Ideal.map_span, Set.image_singleton] using he

lemma single_effective_cartier (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) :
    IsEffectiveCartierIdeal (stageIdeal k D) := by
  intro x
  obtain ⟨i, z, rfl⟩ := D.covers x
  letI : IsOpenImmersion (D.chart i) := D.chart_open i
  letI : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  refine ⟨⟨(D.chart i) ''ᵁ ⊤,
    (isAffineOpen_top (specA k n)).image_of_isOpenImmersion (D.chart i)⟩,
    ⟨z, trivial, rfl⟩, ?_⟩
  exact chart_principal k r n hr h3 E hE D i


lemma stage_invertible (h3 : 3 ≤ r) (d n : ℕ) :
    ((stageIdeal k (T.atlas n))^d).IsInvertible :=
  (effective_invertible _ (single_effective_cartier k r n hr h3
    (T.overlap n) (T.overlap_spec n) (T.atlas n))).pow d

lemma power_invertible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ) :
    (s.ker^d).IsInvertible :=
  (ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedEffectiveCartierR0136.section_invertible
    k h3 M hM (zeroIndex r hr) 1 s hs).pow d

lemma stage_power (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n : ℕ) :
    (s.ker^d).comap (M.inclusion n) = (stageIdeal k (T.atlas n))^d := by
  rw [comap_power]
  congr 1
  letI : IsClosedImmersion s :=
    ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM s hs.1
  apply ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange
  have outer : IsPullback
      (ArithmeticThetaPolygonCohomologyR0131.markedSection k r n hr (T.atlas n) (zeroIndex r hr) 1 ≫ (T.atlas n).p)
      (baseInclusion k n)
      (baseInclusion k n) (s ≫ M.p) := by
    rw [ArithmeticThetaPolygonCohomologyR0131.SmoothMarkedSections.section_over, hs.1]
    exact IsPullback.id_horiz _
  exact outer.of_right (hs.2 n).symm (hM.2.2.1 n).flip

def stageIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).obj
      (powerModule k M s d) ≅
        stageModule k (T.atlas n) d :=
  idealPullbackIso (M.inclusion n) _ _ (power_invertible k h3 M hM s hs d)
    (stage_invertible k h3 d n) (stage_power k M hM s hs d n)

lemma stageIso_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n : ℕ) :
    (stageIso k h3 M hM s hs d n).hom ≫
      GlobalCartierIdealLineR0133.idealInclusion
        ((stageIdeal k (T.atlas n))^d) =
      (Scheme.Modules.pullback (M.inclusion n)).map
        (GlobalCartierIdealLineR0133.idealInclusion
          ((s.ker)^d)) ≫ unitPullback (M.inclusion n) :=
  idealPullbackIso_inclusion (M.inclusion n) _ _ _ _ _



def FormalNumerators (d : ℕ) :=
  {v : ∀ n, Sections k r n hr (T.overlap n) d // ∀ n N (h : n ≤ N) i,
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      ((v N).val i) = (v n).val i}

lemma reduce_equation (r n N : ℕ) (h : n ≤ N) (i : Fin r) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      (equation k r N i) = equation k r n i := by
  unfold equation
  split_ifs <;> simp only [map_mul, map_sub, map_one] <;> rfl

def finiteIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n N : ℕ) (h : n ≤ N) :
    (Scheme.Modules.pullback (T.transition n N h)).obj
      (stageModule k (T.atlas N) d) ≅
        stageModule k (T.atlas n) d :=
  idealPullbackIso _ _ _ (stage_invertible k h3 d N) (stage_invertible k h3 d n)
    (by rw [← stage_power k M hM s hs d N, ← Scheme.IdealSheafData.comap_comp,
      hM.2.2.2 n N h, stage_power k M hM s hs d n])

lemma finiteIso_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n N : ℕ) (h : n ≤ N) :
    (finiteIso k h3 M hM s hs d n N h (T := T)).hom ≫
      idealInclusion ((stageIdeal k (T.atlas n))^d) =
      pulledInclusion (T.transition n N h)
        (idealInclusion ((stageIdeal k (T.atlas N))^d)) :=
  idealPullbackIso_inclusion _ _ _ _ _ _

def finiteReduce (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n N : ℕ) (h : n ≤ N)
    (φ : StageDual k (T.atlas N) d) :
    StageDual k (T.atlas n) d :=
  (finiteIso k h3 M hM s hs d n N h).inv ≫ pulledInclusion (T.transition n N h) φ

lemma finiteReduce_realizes (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)
    (v : FormalNumerators k (T := T) d) (n N : ℕ) (h : n ≤ N)
    (φ : StageDual k (T.atlas N) d)
    (hφ : StageRealizes k (T.atlas N) d ((v.val N).val) φ) :
    StageRealizes k (T.atlas n) d ((v.val n).val)
      (finiteReduce k h3 M hM s hs d n N h φ) := by
  intro i
  let f := T.transition n N h
  let cn := (T.atlas n).chart i
  let cN := (T.atlas N).chart i
  let g := chartReduction k n N h
  let L := stageModule k (T.atlas N) d
  let Q := stageModule k (T.atlas n) d
  let jL := idealInclusion ((stageIdeal k (T.atlas N))^d)
  let jQ := idealInclusion ((stageIdeal k (T.atlas n))^d)
  let e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback cN).obj L) ≅
      (Scheme.Modules.pullback cn).obj Q :=
    squareIso f cn cN g ((T.transition_spec n N h).2 i) L ≪≫
      (Scheme.Modules.pullback cn).mapIso (finiteIso k h3 M hM s hs d n N h)
  have hj : e.hom ≫ pulledInclusion cn jQ = pulledInclusion g (pulledInclusion cN jL) :=
    square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q jL jQ
      (finiteIso k h3 M hM s hs d n N h).hom (finiteIso_inclusion k h3 M hM s hs d n N h)
  have hq : e.hom ≫ pulledInclusion cn (finiteReduce k h3 M hM s hs d n N h φ) =
      pulledInclusion g (pulledInclusion cN φ) := by
    apply square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q φ
      (finiteReduce k h3 M hM s hs d n N h φ) (finiteIso k h3 M hM s hs d n N h).hom
    simp only [finiteReduce, Iso.hom_inv_id_assoc]
    rfl
  have hw := pull_witness g ((Scheme.Modules.pullback cN).obj L)
    (pulledInclusion cN jL) (pulledInclusion cN φ) _ _ (hφ i)
  have ht := (witness_iso e _ _ _ _ hj hq _ _).mp hw
  dsimp only [g] at ht
  rw [chartReduction_value, chartReduction_value, map_pow,
    reduce_equation,
    v.property n N h i] at ht
  exact ht

lemma stageIso_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n N : ℕ) (h : n ≤ N) :
    (compIso (T.transition n N h) (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h)
      (powerModule k M s d)).hom ≫ (stageIso k h3 M hM s hs d n).hom =
      (Scheme.Modules.pullback (T.transition n N h)).map (stageIso k h3 M hM s hs d N).hom ≫
        (finiteIso k h3 M hM s hs d n N h).hom := by
  let jn := idealInclusion ((stageIdeal k (T.atlas n))^d)
  letI : Mono jn := (ideal_realization _).1
  apply (cancel_mono jn).mp
  rw [Category.assoc, Category.assoc]
  change _ ≫ ((stageIso k h3 M hM s hs d n).hom ≫ idealInclusion _) =
    _ ≫ ((finiteIso k h3 M hM s hs d n N h).hom ≫ idealInclusion _)
  rw [stageIso_inclusion, finiteIso_inclusion]
  change _ ≫ pulledInclusion (M.inclusion n) (idealInclusion _) = _
  rw [compIso_inclusion]
  change pulledInclusion (T.transition n N h) (pulledInclusion (M.inclusion N) (idealInclusion _)) = _
  have he : (stageIso k h3 M hM s hs d N).hom ≫
      idealInclusion ((stageIdeal k (T.atlas N))^d) =
      pulledInclusion (M.inclusion N)
        (idealInclusion ((s.ker)^d)) :=
    stageIso_inclusion k h3 M hM s hs d N
  rw [← he]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

def finiteDual (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)
    (v : FormalNumerators k (T := T) d) (n : ℕ) :
    StageDual k (T.atlas n) d :=
  (IdentityStageSectionRealizationR0138.exists_realizes
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (v.val n)).choose

lemma finiteDual_realizes (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)
    (v : FormalNumerators k (T := T) d) (n : ℕ) :
    StageRealizes k (T.atlas n) d (v.val n).val
      (finiteDual k h3 M hM s hs d v n) :=
  (IdentityStageSectionRealizationR0138.exists_realizes
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (v.val n)).choose_spec

lemma finiteDual_compatible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)
    (v : FormalNumerators k (T := T) d) (n N : ℕ) (h : n ≤ N) :
    finiteDual k h3 M hM s hs d v n = finiteReduce k h3 M hM s hs d n N h (finiteDual k h3 M hM s hs d v N) := by
  apply IdentityStageSectionRealizationR0138.realizes_unique
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (v.val n)
  · exact finiteDual_realizes k h3 M hM s hs d v n
  · exact finiteReduce_realizes k h3 M hM s hs d v n N h _ (finiteDual_realizes k h3 M hM s hs d v N)

def prescribedDual (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ) (v : FormalNumerators k (T := T) d) (n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).obj (powerModule k M s d) ⟶
      (SheafOfModules.unit (T.atlas n).X.ringCatSheaf : (T.atlas n).X.Modules) :=
  (stageIso k h3 M hM s hs d n).hom ≫ finiteDual k h3 M hM s hs d v n

lemma prescribedDual_compatible (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ) (v : FormalNumerators k (T := T) d) (n N : ℕ) (h : n ≤ N) :
    (compIso (T.transition n N h) (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h)
      (powerModule k M s d)).hom ≫ prescribedDual k h3 M hM s hs d v n =
      pulledInclusion (T.transition n N h) (prescribedDual k h3 M hM s hs d v N) := by
  dsimp only [prescribedDual]
  rw [← Category.assoc, stageIso_transition, Category.assoc,
    finiteDual_compatible k h3 M hM s hs d v n N h]
  simp only [finiteReduce, Iso.hom_inv_id_assoc]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]


def FormalRealizes (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (v : FormalNumerators k (T := T) d) (φ : Dual k M s d) : Prop :=
  ∀ n (i : Fin r),
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj (powerModule k M s d)
    let j := pulledInclusion f (idealInclusion (s.ker^d))
    let q := pulledInclusion f φ
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k r n i)^d) ∧
      q.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((v.val n).val i)

def reduceDual (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n : ℕ) (φ : Dual k M s d) :
    StageDual k (T.atlas n) d :=
  (stageIso k h3 M hM s hs d n).inv ≫ pulledInclusion (M.inclusion n) φ

/-- The frozen chartwise realization predicate is exactly realization of every
canonical finite-stage reduction, including stage and degree zero. -/
lemma realizes_iff_reductions (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ) (v : FormalNumerators k (T := T) d)
    (φ : Dual k M s d) :
    FormalRealizes k M s d v φ ↔ ∀ n,
      StageRealizes k (T.atlas n) d (v.val n).val
        (reduceDual k h3 M hM s hs d n φ) := by
  apply forall_congr'
  intro n
  apply forall_congr'
  intro i
  apply witness_iso (chartIso (T.atlas n |>.chart i) (M.inclusion n) _ _
    (stageIso k h3 M hM s hs d n))
  · exact chartIso_inclusion _ _ _ _ _ _ _ (stageIso_inclusion k h3 M hM s hs d n)
  · apply chartIso_inclusion
    simp only [reduceDual, Iso.hom_inv_id_assoc]

lemma realizes_iff_prescribed (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ) (v : FormalNumerators k (T := T) d)
    (φ : Dual k M s d) :
    FormalRealizes k M s d v φ ↔ ∀ n,
      pulledInclusion (M.inclusion n) φ = prescribedDual k h3 M hM s hs d v n := by
  rw [realizes_iff_reductions k h3 M hM s hs d v φ]
  apply forall_congr'
  intro n
  constructor
  · intro hφ
    have he := IdentityStageSectionRealizationR0138.realizes_unique
      k r n hr h3 (T.overlap_spec n) (T.atlas n) d (v.val n) hφ (finiteDual_realizes k h3 M hM s hs d v n)
    have hh := congrArg (fun q => (stageIso k h3 M hM s hs d n).hom ≫ q) he
    simpa only [reduceDual, Iso.hom_inv_id_assoc, prescribedDual] using hh
  · intro hφ
    have he : reduceDual k h3 M hM s hs d n φ = finiteDual k h3 M hM s hs d v n := by
      dsimp only [reduceDual]
      rw [hφ]
      simp only [prescribedDual, Iso.inv_hom_id_assoc]
    rw [he]
    exact finiteDual_realizes k h3 M hM s hs d v n


lemma algebraize_formal (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)
    (v : FormalNumerators k (T := T) d) :
    ∃! φ : Dual k M s d, FormalRealizes k M s d v φ := by
  letI : IsProper M.p := hM.1
  obtain ⟨φ, hφ, hu⟩ := pullback_dual_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n)
    (fun n => T.transition n (n + 1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n + 1) (Nat.le_succ n))
    (powerModule k M s d) ((power_invertible k h3 M hM s hs d).isInvertible_module)
    (prescribedDual k h3 M hM s hs d v)
    (fun n => prescribedDual_compatible k h3 M hM s hs d v n (n + 1) (Nat.le_succ n))
  exact ⟨φ, (realizes_iff_prescribed k h3 M hM s hs d v φ).mpr hφ,
    fun ψ hψ => hu ψ ((realizes_iff_prescribed k h3 M hM s hs d v ψ).mp hψ)⟩

end AlgebraizedThetaSectionsR0138
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open AlgebraizedThetaSectionsR0138

/-- Every literal full theta combination gives one and only one algebraic section
of the dual of the actual identity ideal power, with all prescribed chart values. -/
theorem algebraized_theta_sections :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m),
    ∀ (T : Tower k (2*m) (Nat.mul_pos (by decide) hm)),
    ∀ (M : Model k T), IsModel k T M →
    ∀ (s : baseScheme k ⟶ M.X), MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s →
    ∀ w : Fin m → PowerSeries k, ∃! φ : Dual k M s m, Realizes k (hm := hm) he M s 0 w φ := by
  intro k _ _ m hm he T M hM s hs w
  have h3 : 3 ≤ 2*m := by obtain ⟨a, ha⟩ := he; omega
  have hc := theta_numerator_compatibility k m hm he T w
  let v : FormalNumerators k (T := T) m :=
    ⟨fun n => ⟨finiteNumerator k m hm he w n, hc.1 n⟩, hc.2⟩
  have eqv (φ : Dual k M s m) : Realizes k (hm := hm) he M s 0 w φ ↔ FormalRealizes k M s m v φ := by
    simp only [Realizes, FormalRealizes, pow_zero, map_one, one_mul]
    apply forall_congr'
    intro n
    apply forall_congr'
    intro i
    apply exists_congr
    intro z
    apply and_congr_right
    intro _
    exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.eq_symm_apply.symm
  obtain ⟨φ, hφ, hu⟩ := algebraize_formal k h3 M hM s hs m v
  exact ⟨φ, (eqv φ).mpr hφ, fun ψ hψ => hu ψ ((eqv ψ).mp hψ)⟩

end ArithmeticThetaIdentitySectionsR0138
#print axioms ArithmeticThetaIdentitySectionsR0138.algebraized_theta_sections
