module

public import IdentityChartIdealR0138
public import GlobalPositiveSectionRealizationR0134

@[expose] public section

/-! Actual sheaf morphisms and compatible numerators for the single marked divisor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace IdentityStageSectionRealizationR0138
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (comap_pow_open affine_pullback_inv frame_cross multiplication_eq pullFrame
   pullFrame_isIso pullFrame_evaluation frame_maps_glue hom_ext_pullback_cover)

local instance chart_isOpen (k : Type u) [Field k] [CharZero k]
    (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (D.chart i) := D.chart_open i

local instance specA_isAffine (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))

local instance unitSectionsCommRing (X : Scheme.{u}) (U : X.Opens) :
    CommRing Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) :=
  inferInstanceAs (CommRing (X.presheaf.obj (Opposite.op U)))

variable (k : Type u) [Field k] [CharZero k]
variable (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
variable {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
variable (D : Atlas k r n hr E) (d : ℕ)

/-- The equation is transported through the actual affine global-section isomorphism. -/
def localEquation (i : Fin r) : Γ(specA k n, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k r n i)^d)

include h3 hE D

lemma localEquation_regular (i : Fin r) : IsRegular (localEquation k r n d i) := by
  apply regular_equiv (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm
  exact ((identity_chart_ideal k r n hr h3 E hE D i).2).pow d

lemma chart_equation_ideal (i : Fin r) :
    ((stageIdeal k D).comap (D.chart i)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span ({(Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (equation k r n i)} : Set _) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv
  have he : Ideal.map e.toRingHom
      (((stageIdeal k D).comap (D.chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.span ({equation k r n i} : Set _) :=
    (identity_chart_ideal k r n hr h3 E hE D i).1
  apply_fun Ideal.map e.symm.toRingHom at he
  change _ = Ideal.span ({e.symm (equation k r n i)} : Set _)
  simpa [Ideal.map_map, Ideal.map_span, Set.image_singleton] using he

lemma power_chart_ideal (i : Fin r) :
    (((stageIdeal k D)^d).comap (D.chart i)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span ({localEquation k r n d i} : Set _) := by
  rw [comap_pow_open]
  change (((stageIdeal k D).comap (D.chart i)).ideal
    ⟨⊤, isAffineOpen_top _⟩)^d = _
  rw [chart_equation_ideal k r n hr h3 hE D i, Ideal.span_singleton_pow]
  congr 2
  exact (map_pow (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom _ d).symm

/-- The canonical categorical kernel has the required generator on each chart. -/
lemma local_generator (i : Fin r) :
    ∃ t : Γ((Scheme.Modules.pullback (D.chart i)).obj (stageModule k D d), ⊤),
      (pulledInclusion (D.chart i) (idealInclusion ((stageIdeal k D)^d))).app ⊤ t =
        localEquation k r n d i := by
  have h := pullback_open_realization (D.chart i) ((stageIdeal k D)^d)
    (stageModule k D d) (idealInclusion _) (ideal_realization _)
  have hp : localEquation k r n d i ∈
      ((((stageIdeal k D)^d).comap (D.chart i)).ideal
        ⟨⊤, isAffineOpen_top _⟩).carrier := by
    rw [power_chart_ideal k r n hr h3 hE D d i]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [← h.2 ⟨⊤, isAffineOpen_top _⟩] at hp
  exact hp

def localGenerator (i : Fin r) :
    Γ((Scheme.Modules.pullback (D.chart i)).obj (stageModule k D d), ⊤) :=
  (local_generator k r n hr h3 hE D d i).choose

lemma localGenerator_spec (i : Fin r) :
    (pulledInclusion (D.chart i) (idealInclusion ((stageIdeal k D)^d))).app ⊤
      (localGenerator k r n hr h3 hE D d i) = localEquation k r n d i :=
  (local_generator k r n hr h3 hE D d i).choose_spec

/-- The specified generator is a frame, not merely a section of the kernel. -/
lemma localGenerator_frame (i : Fin r) : IsIso (C := (specA k n).Modules)
    (fromSection _ (localGenerator k r n hr h3 hE D d i)) := by
  apply principal_frame
    (((stageIdeal k D)^d).comap (D.chart i)) _
    (pulledInclusion (D.chart i) (idealInclusion ((stageIdeal k D)^d)))
    (pullback_open_realization (D.chart i) _ _ _ (ideal_realization _))
    (localEquation k r n d i) (localEquation_regular k r n hr h3 hE D d i)
    (power_chart_ideal k r n hr h3 hE D d i)
  exact localGenerator_spec k r n hr h3 hE D d i

/-- Evaluation at the prescribed local generator determines a local dual map. -/
lemma local_hom_ext (i : Fin r)
    {φ ψ : (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D d) ⟶
      (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)}
    (h : φ.app ⊤ (localGenerator k r n hr h3 hE D d i) =
      ψ.app ⊤ (localGenerator k r n hr h3 hE D d i)) : φ = ψ := by
  let F := fromSection _ (localGenerator k r n hr h3 hE D d i)
  letI : IsIso (C := (specA k n).Modules) F := localGenerator_frame k r n hr h3 hE D d i
  apply (cancel_epi F).mp
  apply unit_hom_ext
  simpa [F, fromSection_apply] using h

/-- The concrete numerator obtained from an actual global sheaf morphism. -/
def numerator (φ : StageDual k D d) (i : Fin r) : A k n :=
  (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
    ((pulledInclusion (D.chart i) φ).app ⊤ (localGenerator k r n hr h3 hE D d i))

lemma numerator_injective : Function.Injective (numerator k r n hr h3 hE D d) := by
  intro φ ψ h
  apply hom_ext_pullback_cover (fun _ : Fin r => specA k n)
    D.chart D.chart_open D.covers
  intro i
  letI := unitPullback_isIso (D.chart i)
  apply (cancel_mono (unitPullback (D.chart i))).mp
  apply local_hom_ext k r n hr h3 hE D d i
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective (congrFun h i)

/-- The generator condition in the frozen statement is equivalent to exact evaluation. -/
lemma realizes_iff (s : Sections k r n hr E d) (φ : StageDual k D d) :
    StageRealizes k D d s.val φ ↔ numerator k r n hr h3 hE D d φ = s.val := by
  constructor
  · intro h
    funext i
    obtain ⟨t, ht, hφ⟩ := h i
    have hj := pullback_open_realization (D.chart i) ((stageIdeal k D)^d)
      (stageModule k D d) (idealInclusion _) (ideal_realization _)
    letI := hj.1
    have he : t = localGenerator k r n hr h3 hE D d i :=
      mono_app_injective (pulledInclusion (D.chart i) (idealInclusion _)) ⊤
        (ht.trans (localGenerator_spec k r n hr h3 hE D d i).symm)
    unfold numerator
    rw [← he]
    change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
      (((Scheme.Modules.pullback (D.chart i)).map φ ≫ unitPullback (D.chart i)).app ⊤ t) = _
    rw [hφ]
    exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _
  · intro h i
    refine ⟨localGenerator k r n hr h3 hE D d i,
      localGenerator_spec k r n hr h3 hE D d i, ?_⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective
    exact (congrFun h i).trans
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

lemma realizes_unique (s : Sections k r n hr E d) {φ ψ : StageDual k D d}
    (hφ : StageRealizes k D d s.val φ) (hψ : StageRealizes k D d s.val ψ) : φ = ψ := by
  apply numerator_injective k r n hr h3 hE D d
  exact ((realizes_iff k r n hr h3 hE D d s φ).mp hφ).trans
    ((realizes_iff k r n hr h3 hE D d s ψ).mp hψ).symm

lemma frame_inclusion (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D d i) ≫
      pulledInclusion (D.chart i) (idealInclusion ((stageIdeal k D)^d)) =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          (localEquation k r n d i) := by
  apply unit_hom_ext
  convert localGenerator_spec k r n hr h3 hE D d i using 1 <;>
    simp [fromSection_apply] <;> rfl

lemma frame_evaluation (φ : StageDual k D d) (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D d i) ≫
      pulledInclusion (D.chart i) φ =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
            (numerator k r n hr h3 hE D d φ i)) := by
  apply unit_hom_ext
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, fromSection_apply]
  simpa [numerator] using
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm_apply_apply
      ((pulledInclusion (D.chart i) φ).app ⊤ (localGenerator k r n hr h3 hE D d i))).symm

lemma numerator_compatible (φ : StageDual k D d) :
    Compatible k r n hr E d (numerator k r n hr h3 hE D d φ) := by
  intro i
  let α := fromSection _ (localGenerator k r n hr h3 hE D d i)
  let β := fromSection _ (localGenerator k r n hr h3 hE D d (next r hr i))
  letI : IsIso (C := (specA k n).Modules) α := localGenerator_frame k r n hr h3 hE D d i
  let L := leftLeg k n E
  let R := rightLeg k n
  let e := squareIso (D.chart i) L (D.chart (next r hr i)) R
    (D.adjacent i).w (stageModule k D d)
  let α' := pullFrame L α
  let β' := pullFrame R β ≫ e.hom
  let J := pulledInclusion L (pulledInclusion (D.chart i)
    (idealInclusion ((stageIdeal k D)^d)))
  let Q := pulledInclusion L (pulledInclusion (D.chart i) φ)
  letI : IsIso α' := pullFrame_isIso L α
  have h := frame_cross α' β' J Q
  have he (q : StageDual k D d) :
      e.hom ≫ pulledInclusion L (pulledInclusion (D.chart i) q) =
        pulledInclusion R (pulledInclusion (D.chart (next r hr i)) q) :=
    squareIso_inclusion (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w _ q
  have hαJ : α' ≫ J = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (L.appTop (localEquation k r n d i)) :=
    pullFrame_evaluation L α _ _ (frame_inclusion k r n hr h3 hE D d i)
  have hβJ : β' ≫ J = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (R.appTop (localEquation k r n d (next r hr i))) := by
    change (pullFrame R β ≫ e.hom) ≫ J = _
    rw [Category.assoc, he]
    exact pullFrame_evaluation R β _ _ (frame_inclusion k r n hr h3 hE D d _)
  have hαQ : α' ≫ Q = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (L.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k r n hr h3 hE D d φ i))) :=
    pullFrame_evaluation L α _ _ (frame_evaluation k r n hr h3 hE D d φ i)
  have hβQ : β' ≫ Q = fromSection (SheafOfModules.unit (specB k n true).ringCatSheaf)
      (R.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k r n hr h3 hE D d φ (next r hr i)))) := by
    change (pullFrame R β ≫ e.hom) ≫ Q = _
    rw [Category.assoc, he]
    exact pullFrame_evaluation R β _ _ (frame_evaluation k r n hr h3 hE D d φ _)
  rw [hαQ, hβJ, hβQ, hαJ] at h
  have hv := multiplication_eq _ _ _ _ h
  have hv' := congrArg (fun z : Γ(specB k n true, ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom z) hv
  change (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
      (L.appTop _ * R.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
      (R.appTop _ * L.appTop _) at hv'
  simp only [map_mul] at hv'
  have hn {S T : CommRingCat.{u}} (f : S ⟶ T) (x : S) :
      (Scheme.ΓSpecIso T).hom ((Spec.map f).appTop ((Scheme.ΓSpecIso S).inv x)) = f x := by
    rw [ArithmeticThetaPolygonCohomologyR0131.PolygonGlobalFunctionsR0131.affine_pullback]
    exact congrArg f ((Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.apply_symm_apply x)
  dsimp only [L, R, leftLeg, rightLeg, localEquation] at hv'
  erw [hn, hn, hn, hn] at hv'
  simp only [map_pow] at hv'
  exact hv'

/-- The actual sheaf morphism determines a compatible numerator tuple. -/
def toSections (φ : StageDual k D d) : Sections k r n hr E d :=
  ⟨numerator k r n hr h3 hE D d φ, numerator_compatible k r n hr h3 hE D d φ⟩

lemma toSections_realizes (φ : StageDual k D d) :
    StageRealizes k D d (toSections k r n hr h3 hE D d φ).val φ :=
  (realizes_iff k r n hr h3 hE D d _ φ).mpr rfl

lemma toSections_injective : Function.Injective (toSections k r n hr h3 hE D d) := by
  intro φ ψ h
  exact numerator_injective k r n hr h3 hE D d (congrArg Subtype.val h)

/-- An arbitrary numerator gives a local linear map by the inverse of the proven frame. -/
def localDual (b : A k n) (i : Fin r) :
    (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D d) ⟶
      (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) := by
  let F := fromSection _ (localGenerator k r n hr h3 hE D d i)
  letI : IsIso (C := (specA k n).Modules) F := localGenerator_frame k r n hr h3 hE D d i
  exact inv F ≫ fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b)

lemma frame_localDual (b : A k n) (i : Fin r) :
    fromSection _ (localGenerator k r n hr h3 hE D d i) ≫
      localDual k r n hr h3 hE D d b i =
        fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
          ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b) := by
  letI := localGenerator_frame k r n hr h3 hE D d i
  simp [localDual]

lemma localDual_value (b : A k n) (i : Fin r) :
    (localDual k r n hr h3 hE D d b i).app ⊤ (localGenerator k r n hr h3 hE D d i) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv b := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun q => Scheme.Modules.Hom.app q ⊤) (frame_localDual k r n hr h3 hE D d b i))
    (1 : Γ(specA k n, ⊤))
  simpa [fromSection_apply] using h

omit D in
set_option maxHeartbeats 100000 in
lemma compatible_on_overlap (s : Sections k r n hr E d) (i : Fin r) :
    (leftLeg k n E).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val i)) *
        (rightLeg k n).appTop (localEquation k r n d (next r hr i)) =
      (rightLeg k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val (next r hr i))) *
        (leftLeg k n E).appTop (localEquation k r n d i) := by
  apply (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).commRingCatIsoToRingEquiv.injective
  simp only [map_mul]
  dsimp only [leftLeg, rightLeg, localEquation]
  erw [affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true)),
    affine_pullback_inv (S := CommRingCat.of (A k n)) (T := CommRingCat.of (B k n true))]
  simp only [map_pow]
  exact s.property i

set_option maxHeartbeats 1600000 in
/-- Adjacent local maps agree over the prescribed actual intersection. -/
lemma localDual_adjacent (s : Sections k r n hr E d) (i : Fin r) :
    CategoryStruct.comp (obj := (specB k n true).Modules)
      (squareIso (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n)
        (D.adjacent i).w (stageModule k D d)).hom
      (pulledInclusion (leftLeg k n E) (localDual k r n hr h3 hE D d (s.val i) i)) =
      pulledInclusion (rightLeg k n)
        (localDual k r n hr h3 hE D d (s.val (next r hr i)) (next r hr i)) := by
  let α := fromSection _ (localGenerator k r n hr h3 hE D d i)
  let β := fromSection _ (localGenerator k r n hr h3 hE D d (next r hr i))
  letI : IsIso (C := (specA k n).Modules) α := localGenerator_frame k r n hr h3 hE D d i
  letI : IsIso (C := (specA k n).Modules) β := localGenerator_frame k r n hr h3 hE D d _
  let L := leftLeg k n E
  let R := rightLeg k n
  have hci := pullback_open_realization (D.chart i) ((stageIdeal k D)^d)
    (stageModule k D d) (idealInclusion _) (ideal_realization _)
  have hj := pullback_open_realization L _ _ _ hci
  letI := hj.1
  exact frame_maps_glue L R
    (squareIso (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w (stageModule k D d)) α β
    (pulledInclusion (D.chart i) (idealInclusion ((stageIdeal k D)^d)))
    (localDual k r n hr h3 hE D d (s.val i) i)
    (pulledInclusion (D.chart (next r hr i)) (idealInclusion ((stageIdeal k D)^d)))
    (localDual k r n hr h3 hE D d (s.val (next r hr i)) (next r hr i))
    (squareIso_inclusion (D.chart i) L (D.chart (next r hr i)) R
      (D.adjacent i).w _ (idealInclusion ((stageIdeal k D)^d)))
    (localEquation k r n d i)
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val i))
    (localEquation k r n d (next r hr i))
    ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (s.val (next r hr i)))
    (frame_inclusion k r n hr h3 hE D d i)
    (frame_inclusion k r n hr h3 hE D d (next r hr i))
    (frame_localDual k r n hr h3 hE D d (s.val i) i)
    (frame_localDual k r n hr h3 hE D d (s.val (next r hr i)) (next r hr i))
    (compatible_on_overlap k r n hr h3 hE d s i)

/-- Every compatible numerator tuple descends to a global morphism of the canonical ideal power. -/
lemma exists_realizes (s : Sections k r n hr E d) :
    ∃ φ : StageDual k D d, StageRealizes k D d s.val φ := by
  let q := fun i => localDual k r n hr h3 hE D d (s.val i) i
  obtain ⟨φ, hφ⟩ := ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.glue_local_maps
    (fun _ : Fin r => specA k n) D.chart D.chart_open D.covers (stageModule k D d) q (by
      intro i j V hi hj m
      by_cases hij : i = j
      · subst j
        rfl
      have hadj (i : Fin r) (V : D.X.Opens)
          (hi : V ≤ (D.chart i).opensRange) (hj : V ≤ (D.chart (next r hr i)).opensRange)
          (m : Γ(stageModule k D d, V)) :
          ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.localValue (D.chart i) (q i) V hi m =
            ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.localValue (D.chart (next r hr i)) (q (next r hr i)) V hj m := by
        apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.localValue_square
          (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n)
          (D.adjacent i).w (stageModule k D d) (q i) (q (next r hr i))
          (localDual_adjacent k r n hr h3 hE D d s i) V hi hj
        rw [ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.square_range
          (D.chart i) (leftLeg k n E) (D.chart (next r hr i)) (rightLeg k n) (D.adjacent i)]
        exact le_inf hi hj
      by_cases hn : next r hr i = j
      · subst j
        exact hadj i V hi hj m
      by_cases hm : next r hr j = i
      · subst i
        exact (hadj j V hj hi m).symm
      apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134.section_eq_of_empty V
      apply le_antisymm _ bot_le
      intro x hx
      exact (Set.disjoint_left.mp (D.disjoint i j hij hn hm)) (hi hx) (hj hx))
  refine ⟨φ, ?_⟩
  intro i
  refine ⟨localGenerator k r n hr h3 hE D d i,
    localGenerator_spec k r n hr h3 hE D d i, ?_⟩
  change (pulledInclusion (D.chart i) φ).app ⊤ _ = _
  rw [hφ i]
  exact localDual_value k r n hr h3 hE D d (s.val i) i

lemma toSections_surjective : Function.Surjective (toSections k r n hr h3 hE D d) := by
  intro s
  obtain ⟨φ, hφ⟩ := exists_realizes k r n hr h3 hE D d s
  refine ⟨φ, Subtype.ext ?_⟩
  exact (realizes_iff k r n hr h3 hE D d s φ).mp hφ

end IdentityStageSectionRealizationR0138

/-- Compatible numerators and actual dual sections determine each other uniquely, including degree zero. -/
theorem identity_stage_section_realization :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r → ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+* ArithmeticThetaInfinitesimalPolygonR0129.B k n true), ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E → ∀ D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E, ∀ d : ℕ, (∀ v : ArithmeticThetaIdentitySectionsR0138.Sections k r n hr E d, ∃! φ : ArithmeticThetaIdentitySectionsR0138.StageDual k D d, ArithmeticThetaIdentitySectionsR0138.StageRealizes k D d v.val φ) ∧ (∀ φ : ArithmeticThetaIdentitySectionsR0138.StageDual k D d, ∃! v : ArithmeticThetaIdentitySectionsR0138.Sections k r n hr E d, ArithmeticThetaIdentitySectionsR0138.StageRealizes k D d v.val φ) := by
  intro k _ _ r n hr h3 E hE D d
  constructor
  · intro v
    obtain ⟨φ, hφ⟩ := IdentityStageSectionRealizationR0138.exists_realizes k r n hr h3 hE D d v
    exact ⟨φ, hφ, fun ψ hψ =>
      IdentityStageSectionRealizationR0138.realizes_unique k r n hr h3 hE D d v hψ hφ⟩
  · intro φ
    refine ⟨IdentityStageSectionRealizationR0138.toSections k r n hr h3 hE D d φ,
      IdentityStageSectionRealizationR0138.toSections_realizes k r n hr h3 hE D d φ, ?_⟩
    intro v hv
    apply Subtype.ext
    exact ((IdentityStageSectionRealizationR0138.realizes_iff k r n hr h3 hE D d v φ).mp hv).symm

end ArithmeticThetaIdentitySectionsR0138
