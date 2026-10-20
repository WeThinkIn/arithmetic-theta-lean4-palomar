module

public import CompactHodgeConstantComparisonR0235
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import FPQCSquareRootDescentR0197
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

variable (k : Type) [Field k] [CharZero k] (L : ℕ)

/-- Normalize all disks whose centers lie in a given finite set. A center
without a disk over the coefficient field imposes no condition here. This
lemma does not assert geometric canonicity at such a center. -/
lemma normalize_tested_centers (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (S : Finset X.space) (hS : ∀ x ∈ S, x ∈ boundary k L D X)
    (H : Extension k L D X) :
    ∃ H' : Extension k L D X, ∀ T : DiskTest k L D X,
      T.disk (closedPoint k) ∈ S → diskOrder k L H' T = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨H, fun T h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert x S hxS ih =>
    have hx := hS x (Finset.mem_insert_self x S)
    have hS' : ∀ y ∈ S, y ∈ boundary k L D X :=
      fun y hy => hS y (Finset.mem_insert_of_mem hy)
    obtain ⟨H', hH'⟩ := ih hS'
    by_cases ht : ∃ T : DiskTest k L D X, T.disk (closedPoint k) = x
    · obtain ⟨T0, hT0⟩ := ht
      obtain ⟨H'', hH''⟩ := exists_cusp_shift k L hL heven H' x hx
        (-diskOrder k L H' T0)
      refine ⟨H'', fun T hT => ?_⟩
      rw [hH'']
      rcases Finset.mem_insert.mp hT with hc | hc
      · rw [if_pos hc, mul_one]
        have he := diskOrder_shared_center k L hL heven H' T T0
          (hc.trans hT0.symm)
        omega
      · have hne : T.disk (closedPoint k) ≠ x := fun he => hxS (he ▸ hc)
        rw [if_neg hne, mul_zero, add_zero]
        exact hH' T hc
    · refine ⟨H', fun T hT => ?_⟩
      rcases Finset.mem_insert.mp hT with hc | hc
      · exact False.elim (ht ⟨T, hc⟩)
      · exact hH' T hc

/-- The native-field disk predicate admits a lattice over every
characteristic-zero field. The stronger geometric predicate still requires
control of the nonrational boundary centers. -/
lemma native_canonical_exists (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    ∃ H : Extension k L D X, Canonical k L H := by
  classical
  obtain ⟨H⟩ := extension_exists k L D X
  let S := (BoundaryGeometry.boundary_finite k L D X).toFinset
  have hS : ∀ x ∈ S, x ∈ boundary k L D X := by
    intro x hx
    exact (BoundaryGeometry.boundary_finite k L D X).mem_toFinset.mp hx
  obtain ⟨H', hH'⟩ := normalize_tested_centers k L hL heven S hS H
  refine ⟨H', (canonical_iff_diskOrder_zero k L H').2 ?_⟩
  intro T
  exact hH' T ((BoundaryGeometry.boundary_finite k L D X).mem_toFinset.mpr
    T.extends_eq.2.2)

/-- The accepted compact comparison supplies the full geometric predicate
when the original coefficient field is already algebraically closed. -/
lemma geometric_of_algClosed [IsAlgClosed k] (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) :
    GeometricallyCanonical H := by
  intro l _ _ _ ι E Y f F hf hF e he J hJ
  exact compact_hodge_constant_comparison k l ι L hL heven D E f hf e he
    X Y F hF H J hH hJ

/-- An isomorphism preserving the actual open identification transports
existence of normalized integral frames. Uniqueness is the accepted generic
restriction injectivity theorem, so no choice of scalar is introduced. -/
lemma canonical_of_open_iso {D : LevelData k L} {X : Compactification k L D}
    (H J : Extension k L D X) (a : H.line ≅ J.line)
    (ha : (Scheme.Modules.pullback X.inclusion).map a.hom ≫ J.onOpen.hom =
      H.onOpen.hom) (hH : Canonical k L H) : Canonical k L J := by
  apply (canonical_iff_exists k L J).2
  intro T
  obtain ⟨η, hη, _⟩ := hH T
  refine ⟨((Scheme.Modules.pullback T.disk).map a.hom).app ⊤ η, ?_, ?_⟩
  · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso ((Scheme.Modules.pullback T.disk).mapIso a) η hη.1
  · change diskRestriction k L J T
      (((Scheme.Modules.pullback T.disk).map a.hom).app ⊤ η) = _
    rw [diskRestriction_naturality k L H J T a.hom ha]
    exact hη.2

lemma canonical_iff_open_iso {D : LevelData k L} {X : Compactification k L D}
    (H J : Extension k L D X) (a : H.line ≅ J.line)
    (ha : (Scheme.Modules.pullback X.inclusion).map a.hom ≫ J.onOpen.hom =
      H.onOpen.hom) : Canonical k L H ↔ Canonical k L J := by
  refine ⟨canonical_of_open_iso k L H J a ha, ?_⟩
  apply canonical_of_open_iso k L J H a.symm
  rw [← ha, ← Category.assoc, ← Functor.map_comp]
  simp

/-- The all-extension comparison predicate is equivalent to canonicity of
the actual pullback extension on every algebraically closed target. This
retains all specified maps, differential comparisons, and open identifications. -/
lemma geometric_iff_pullback_canonical (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) :
    GeometricallyCanonical H ↔
      ∀ (l : Type) [Field l] [CharZero l] [IsAlgClosed l] (ι : k →+* l)
        (E : LevelData l L) (Y : Compactification l L E)
        (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
        (_hf : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f)
        (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
        (e : (Scheme.Modules.pullback f).obj
          (ArithmeticThetaLevelConstantsR0234.weight D) ≅
          ArithmeticThetaLevelConstantsR0234.weight E),
        ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e →
        Canonical l L (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) := by
  constructor
  · intro h l _ _ _ ι E Y f F hf hF e he
    obtain ⟨J, hJ⟩ := compact_hodge_lattice_extension l L hL heven E Y
    obtain ⟨a, ha, _⟩ := h l ι E Y f F hf hF e he J hJ
    exact (canonical_iff_open_iso l L
      (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) J a
      ((CompactHodgeConstantComparison.compatible_iff ι f F hF e H J a).mp ha)).mpr hJ
  · intro h l _ _ _ ι E Y f F hf hF e he J hJ
    obtain ⟨a, ha⟩ := CompactHodgeConstantComparison.canonical_comparison_exists
      hL heven (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) J
      (h l ι E Y f F hf hF e he) hJ
    have hac : CompactCompatible ι f F hF e H J a :=
      (CompactHodgeConstantComparison.compatible_iff ι f F hF e H J a).mpr ha
    refine ⟨a, hac, fun b hb => ?_⟩
    exact CompactHodgeConstantComparison.compact_comparison_unique
      ι f F hF e H J b a hb hac

/-- One rational full Tate marking suffices to descend every target test.
Algebraic closure of the source field is unnecessary in this step. -/
lemma tests_descend_of_tateLevel {l : Type} [Field l] [CharZero l]
    (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (hf : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj
      (ArithmeticThetaLevelConstantsR0234.weight D) ≅
      ArithmeticThetaLevelConstantsR0234.weight E)
    (he : ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e)
    (X : Compactification k L D) (Y : Compactification l L E)
    (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (S : DiskTest l L E Y) :
    ∃ T : DiskTest k L D X, TestCompatible ι T.toTest S.toTest f e ∧
      S.disk ≫ F = diskMap ι ≫ T.disk := by
  obtain ⟨b, hb, _⟩ := tate_coordinate_constant_map k l ι L hL heven
  obtain ⟨A', _, ht⟩ := CompactHodgeConstantComparison.marking_descends
    ι (by omega) A S.level b hb
  obtain ⟨t, htc, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D A'
  obtain ⟨V, hVA, hVt⟩ := (tate_hodge_comparison_tests k L hL heven D).1 A' t htc
  obtain ⟨d, hd, _⟩ := tate_cusp_disk_extension k L hL heven D A' X t htc
  let T : DiskTest k L D X :=
    { toTest := V, disk := d, extends_eq := hVt.symm ▸ hd }
  have hT : Transfers ι T.level S.level b := by
    change Transfers ι V.level S.level b
    rw [hVA]
    exact ht
  exact ⟨T, classified_tate_disk_transfer k l ι L hL heven
    D E f hf e he X Y F hF T S b hb hT⟩

omit [CharZero k] in
/-- The coefficient disk map preserves its literal closed point. -/
lemma diskMap_closedPoint {l : Type} [Field l] [CharZero l] (ι : k →+* l) :
    diskMap ι (closedPoint l) = closedPoint k := by
  exact IsLocalRing.comap_closedPoint (PowerSeries.map ι)

/-- A rational full Tate marking detects every boundary center, even when
the coefficient field is not algebraically closed. Coverage is descended
from the accepted algebraically closed coverage theorem through the actual
Cartesian compact coefficient map. -/
lemma tests_cover_of_tateLevel (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (hx : x ∈ boundary k L D X) :
    ∃ T : DiskTest k L D X, T.disk (closedPoint k) = x := by
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  obtain ⟨A'⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l L hL
  obtain ⟨B, hB, C, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l L hL heven A'
  let E : LevelData l L := ⟨A', B, hB, C, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l L hL heven E
  obtain ⟨f, hf, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.open_constant_comparison k l ι L hL heven D E
  obtain ⟨hfc, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.open_constant_cartesian k l ι L hL heven D E f hf
  obtain ⟨F, hF, _⟩ := ArithmeticThetaLevelConstantsR0234.compact_constant_comparison
    k l ι L hL heven D E X Y f hfc
  letI : Surjective (ArithmeticThetaLevelConstantsR0234.constants ι) :=
    ⟨Function.surjective_to_subsingleton _⟩
  letI : Surjective F := MorphismProperty.of_isPullback hF.2.1.flip inferInstance
  obtain ⟨y, hy⟩ := F.surjective x
  have hyb : y ∈ boundary l L E Y := by
    intro hyi
    obtain ⟨z, hz⟩ := hyi
    apply hx
    refine ⟨f z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hF.1.2, Scheme.Hom.comp_apply, hz, hy]
  obtain ⟨S, hS⟩ := (tate_hodge_comparison_tests l L hL heven E).2 Y y hyb
  obtain ⟨e, he, _⟩ := ArithmeticThetaLevelConstantsR0234.open_hodge_constant_comparison
    k l ι L hL heven D E f hf
  obtain ⟨T, _, hT⟩ := tests_descend_of_tateLevel k L ι hL heven A
    D E f hf e he X Y F hF.1 S
  refine ⟨T, ?_⟩
  have hc := congrArg (fun q : Disk l ⟶ X.space => q (closedPoint l)) hT
  simpa only [Scheme.Hom.comp_apply, diskMap_closedPoint k ι, hS, hy] using hc.symm

section SplitComparisons
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open CompactHodgeConstantComparison
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Extend the comparison locally at every cusp over a field with one full
Tate marking, using the proved coverage and normalized scalar regularity. -/
lemma comparison_local_lifts_of_tateLevel (hL : 3 ≤ L) (heven : Even L)
    (A : TateLevel k L)
    {D : LevelData k L} {X : Compactification k L D}
    (H J : Extension k L D X) (hH : Canonical k L H) (hJ : Canonical k L J)
    (x : X.space) :
    ∃ (V : X.space.Opens) (u : Γ(H.line, V)) (v : Γ(J.line, V)),
      x ∈ V ∧ IsFrame H.line V u ∧
      J.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion v) =
        H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u) := by
  letI := X.openImmersion
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨W, u, hxW, hu⟩ := local_frame_exists H.invertible x
    let V := W ⊓ X.inclusion.opensRange
    let u' := res H.line (inf_le_left : V ≤ W) u
    have hs := (ConcreteCategory.bijective_of_isIso (J.onOpen.hom.app (X.inclusion ⁻¹ᵁ V))).comp
      (Scheme.Modules.bijective_unit_app_of_le_opensRange X.inclusion J.line V inf_le_right)
    obtain ⟨v, hv⟩ := hs.surjective
      (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u'))
    exact ⟨V, u', v, ⟨hxW, hx⟩, frame_restrict _ _ _ hu, hv⟩
  · obtain ⟨T, hTx⟩ := tests_cover_of_tateLevel k L hL heven A D X x hx
    obtain ⟨W, u, hxW, hu, hWI⟩ := integral_frame_neighborhood k L H x
    obtain ⟨Z, v, hxZ, hv⟩ := local_frame_exists J.invertible x
    let U := W ⊓ Z
    have hxU : x ∈ U := ⟨hxW, hxZ⟩
    letI := hWI
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion
      (X.space.homOfLE (inf_le_left : U ≤ W))
    let u' := res H.line (inf_le_left : U ≤ W) u
    let v' := res J.line (inf_le_right : U ≤ Z) v
    have hu' : IsFrame H.line U u' := frame_restrict _ _ _ hu
    have hv' : IsFrame J.line U v' := frame_restrict _ _ _ hv
    have hvO := frame_iso J.onOpen _ (pullback_frame X.inclusion J.line v' hv')
    obtain ⟨r, hr⟩ := (hvO (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u'))
    rw [InitialHodgeSection.res_self] at hr
    obtain ⟨V, hTV, hVU, q, hq⟩ := comparison_scalar_lift hL heven H J hH hJ T U
      u' hu' v' hv' (hTx ▸ hxU) r hr.symm
    refine ⟨V, res H.line hVU u', q • res J.line hVU v', hTx ▸ hTV,
      frame_restrict _ _ _ hu', ?_⟩
    exact scalar_lift_frame_image X.inclusion H.onOpen J.onOpen U u' v' r hr V hVU q hq

/-- Canonical lattices over a split coefficient field admit a comparison
preserving the specified open Hodge identification. -/
lemma canonical_comparison_of_tateLevel
    (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L) {D : LevelData k L}
    {X : Compactification k L D} (H J : Extension k L D X)
    (hH : Canonical k L H) (hJ : Canonical k L J) :
    ∃ a : H.line ≅ J.line,
      (Scheme.Modules.pullback X.inclusion).map a.hom ≫ J.onOpen.hom = H.onOpen.hom := by
  letI := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.inclusion_schematic k L D X
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  obtain ⟨a, ha⟩ := hom_of_local_frame_lifts X.inclusion H.line J.line J.invertible
    _ H.onOpen J.onOpen (comparison_local_lifts_of_tateLevel k L hL heven A H J hH hJ)
  obtain ⟨b, hb⟩ := hom_of_local_frame_lifts X.inclusion J.line H.line H.invertible
    _ J.onOpen H.onOpen (comparison_local_lifts_of_tateLevel k L hL heven A J H hJ hH)
  have hab : a ≫ b = 𝟙 H.line := by
    apply hom_eq_of_pullback X.inclusion H.invertible
    apply (cancel_mono H.onOpen.hom).mp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, hb, ha]
  have hba : b ≫ a = 𝟙 J.line := by
    apply hom_eq_of_pullback X.inclusion J.invertible
    apply (cancel_mono J.onOpen.hom).mp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, ha, hb]
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

end SplitComparisons

/-- Native canonicity on a field with a full Tate marking survives every
coefficient extension, without any algebraic-closure premise on the target. -/
lemma pullback_canonical_of_tateLevel {l : Type} [Field l] [CharZero l]
    (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (hf : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj
      (ArithmeticThetaLevelConstantsR0234.weight D) ≅
      ArithmeticThetaLevelConstantsR0234.weight E)
    (he : ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e)
    (X : Compactification k L D) (Y : Compactification l L E)
    (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (H : Extension k L D X) (hH : Canonical k L H) :
    Canonical l L (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) := by
  let J := CompactHodgeConstantComparison.pullbackExtension ι f F hF e H
  apply (canonical_iff_exists l L J).mpr
  intro S
  obtain ⟨T, ht, hd⟩ := tests_descend_of_tateLevel k L ι hL heven
    A D E f hf e he X Y F hF S
  obtain ⟨η, hη, _⟩ := hH T
  have ha : CompactCompatible ι f F hF e H J (Iso.refl _) := by
    apply (CompactHodgeConstantComparison.compatible_iff
      ι f F hF e H J (Iso.refl _)).mpr
    simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  exact ⟨_, CompactHodgeConstantComparison.disk_generator_transport
    ι f F hF e H J (Iso.refl _) ha T S hd ht η hη⟩

/-- Unique compact comparison over fields with rational full Tate markings.
In particular this applies to every coefficient automorphism of the splitting
field used for descent. -/
lemma compact_comparison_of_tateLevels {l : Type} [Field l] [CharZero l]
    (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    (A : TateLevel k L) (B : TateLevel l L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (hf : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj
      (ArithmeticThetaLevelConstantsR0234.weight D) ≅
      ArithmeticThetaLevelConstantsR0234.weight E)
    (he : ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e)
    (X : Compactification k L D) (Y : Compactification l L E)
    (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (H : Extension k L D X) (J : Extension l L E Y)
    (hH : Canonical k L H) (hJ : Canonical l L J) :
    ∃! a : (Scheme.Modules.pullback F).obj H.line ≅ J.line,
      CompactCompatible ι f F hF e H J a := by
  obtain ⟨a, ha⟩ := canonical_comparison_of_tateLevel l L hL heven B
    (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) J
    (pullback_canonical_of_tateLevel k L ι hL heven A D E f hf e he X Y F hF H hH) hJ
  have hac : CompactCompatible ι f F hF e H J a :=
    (CompactHodgeConstantComparison.compatible_iff ι f F hF e H J a).mpr ha
  exact ⟨a, hac, fun b hb => CompactHodgeConstantComparison.compact_comparison_unique
    ι f F hF e H J b a hb hac⟩

/-- Over a field with a full Tate marking, native canonical lattices satisfy
the full geometric comparison predicate. -/
lemma geometric_of_tateLevel (hL : 3 ≤ L) (heven : Even L) (A : TateLevel k L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) :
    GeometricallyCanonical H := by
  apply (geometric_iff_pullback_canonical k L hL heven H).mpr
  intro l _ _ _ ι E Y f F hf hF e he
  exact pullback_canonical_of_tateLevel k L ι hL heven A D E f hf e he X Y F hF H hH

/-- Geometric existence over every characteristic-zero field containing a
primitive root at the prescribed level, including such number fields.
This is a construction provider for a splitting extension, not the arbitrary
coefficient-field descent theorem. -/
lemma exists_of_primitiveRoot (hL : 3 ≤ L) (heven : Even L)
    (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (D : LevelData k L) (X : Compactification k L D) :
    ∃ H : Extension k L D X, Canonical k L H ∧ GeometricallyCanonical H := by
  obtain ⟨A, _⟩ := tate_full_level_marking k L hL heven ζ hζ
  obtain ⟨H, hH⟩ := native_canonical_exists k L hL heven D X
  exact ⟨H, hH, geometric_of_tateLevel k L hL heven A H hH⟩

omit [CharZero k] in
/-- A concrete finite coefficient extension on which the full normalized
geometric lattice can be constructed. The finite-dimensional structure is
induced by the displayed coefficient homomorphism. -/
lemma cyclotomic_finite : ArithmeticThetaLevelConstantsR0234.FiniteConstants
    (algebraMap k (CyclotomicField L k)) := by
  unfold ArithmeticThetaLevelConstantsR0234.FiniteConstants
  rw [toAlgebra_algebraMap]
  unfold CyclotomicField
  infer_instance

lemma cyclotomic_primitiveRoot (hL : 3 ≤ L) :
    ∃ ζ : CyclotomicField L k, IsPrimitiveRoot ζ L := by
  exact IsCyclotomicExtension.exists_isPrimitiveRoot k (CyclotomicField L k)
    (Set.mem_singleton L) (by omega)

/-- Existence on the prescribed finite splitting field, for every actual
level datum and compactification over that field. Descent back to k remains
necessary for the assigned theorem. -/
lemma cyclotomic_geometric_exists (hL : 3 ≤ L) (heven : Even L)
    (E : LevelData (CyclotomicField L k) L)
    (Y : Compactification (CyclotomicField L k) L E) :
    ∃ J : Extension (CyclotomicField L k) L E Y,
      Canonical (CyclotomicField L k) L J ∧ GeometricallyCanonical J := by
  obtain ⟨ζ, hζ⟩ := cyclotomic_primitiveRoot k L hL
  exact exists_of_primitiveRoot (CyclotomicField L k) L hL heven ζ hζ E Y

/-- The coefficient cover used by the proposed descent is finite etale
and surjective; no finite-dimensionality is asserted for arbitrary embeddings. -/
lemma cyclotomic_cover_properties :
    IsFinite (ArithmeticThetaLevelConstantsR0234.constants
      (algebraMap k (CyclotomicField L k))) ∧
    Etale (ArithmeticThetaLevelConstantsR0234.constants
      (algebraMap k (CyclotomicField L k))) ∧
    Surjective (ArithmeticThetaLevelConstantsR0234.constants
      (algebraMap k (CyclotomicField L k))) := by
  obtain ⟨hf, he, hs, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.CompactComparison.finite_constants_properties
      (algebraMap k (CyclotomicField L k)) (cyclotomic_finite k L)
  exact ⟨hf, he, hs⟩

/-- Actual finite etale cover and normalized Hodge lattice on the chosen
cyclotomic coefficient extension. Every geometric field is a concrete map or
a proved predicate; this record contains no unproved descent assumption. -/
structure SplittingCover (D : LevelData k L) (X : Compactification k L D) where
  level : LevelData (CyclotomicField L k) L
  compact : Compactification (CyclotomicField L k) L level
  openMap : OpenBase (CyclotomicField L k) L level ⟶ OpenBase k L D
  compactMap : compact.space ⟶ X.space
  classifies : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers
    (algebraMap k (CyclotomicField L k)) D level openMap
  extendsOpen : ArithmeticThetaLevelConstantsR0234.Extends
    (algebraMap k (CyclotomicField L k)) D level X compact openMap compactMap
  cartesian : CategoryTheory.IsPullback compactMap compact.projection X.projection
    (ArithmeticThetaLevelConstantsR0234.constants (algebraMap k (CyclotomicField L k)))
  openCartesian : CategoryTheory.IsPullback compact.inclusion openMap
    compactMap X.inclusion
  hodgeMap : (Scheme.Modules.pullback openMap).obj
    (ArithmeticThetaLevelConstantsR0234.weight D) ≅
      ArithmeticThetaLevelConstantsR0234.weight level
  normalized : ArithmeticThetaLevelConstantsR0234.HodgeCompatible
    (algebraMap k (CyclotomicField L k)) D level openMap hodgeMap
  finite : IsFinite compactMap
  etale : Etale compactMap
  surjective : Surjective compactMap
  hodge : Extension (CyclotomicField L k) L level compact
  canonical : Canonical (CyclotomicField L k) L hodge
  geometric : GeometricallyCanonical hodge

/-- Construct the finite splitting cover, its actual coefficient maps, and
its canonical lattice. The remaining descent problem is on this very cover. -/
lemma splittingCover_exists (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    Nonempty (SplittingCover k L D X) := by
  let l := CyclotomicField L k
  let ι : k →+* l := algebraMap k l
  obtain ⟨A⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l L hL
  obtain ⟨B, hB, C, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l L hL heven A
  let E : LevelData l L := ⟨A, B, hB, C, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l L hL heven E
  obtain ⟨f, hf, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.open_constant_comparison k l ι L hL heven D E
  obtain ⟨hfc, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.open_constant_cartesian k l ι L hL heven D E f hf
  obtain ⟨F, hF, _⟩ := ArithmeticThetaLevelConstantsR0234.compact_constant_comparison
    k l ι L hL heven D E X Y f hfc
  obtain ⟨e, he, _⟩ := ArithmeticThetaLevelConstantsR0234.open_hodge_constant_comparison
    k l ι L hL heven D E f hf
  obtain ⟨hfinite, hetale, hsurj, _⟩ :=
    ArithmeticThetaLevelConstantsR0234.finite_constant_degree
      k l ι L hL heven D E X Y f hfc F hF.1 (cyclotomic_finite k L)
  obtain ⟨J, hJ, hgeom⟩ := cyclotomic_geometric_exists k L hL heven E Y
  exact ⟨⟨E, Y, f, F, hf, hF.1, hF.2.1, hF.2.2, e, he,
    hfinite, hetale, hsurj, J, hJ, hgeom⟩⟩

section CoefficientMaps
open ArithmeticThetaLevelConstantsR0234
open ArithmeticThetaLevelConstantsR0234.ConstantComparisonCoherenceProof
variable {l m : Type} [Field l] [CharZero l] [Field m] [CharZero m]

/-- A comparison of the actual coefficient models, retaining the normalized
open Hodge map. Existence is proved from the accepted comparison providers. -/
structure CoefficientMap (ι : k →+* l) (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E) where
  openMap : OpenBase l L E ⟶ OpenBase k L D
  compactMap : Y.space ⟶ X.space
  classifies : RespectsClassifiers ι D E openMap
  extendsOpen : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y openMap compactMap
  hodgeMap : (Scheme.Modules.pullback openMap).obj (weight D) ≅ weight E
  normalized : HodgeCompatible ι D E openMap hodgeMap

lemma coefficientMap_exists (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E) :
    Nonempty (CoefficientMap k L ι D E X Y) := by
  obtain ⟨f, hf, _⟩ := open_constant_comparison k l ι L hL heven D E
  obtain ⟨hfc, _⟩ := open_constant_cartesian k l ι L hL heven D E f hf
  obtain ⟨F, hF, _⟩ := compact_constant_comparison k l ι L hL heven D E X Y f hfc
  obtain ⟨e, he, _⟩ := open_hodge_constant_comparison k l ι L hL heven D E f hf
  exact ⟨⟨f, F, hf, hF.1, e, he⟩⟩

def coefficientMap (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E) :
    CoefficientMap k L ι D E X Y :=
  (coefficientMap_exists k L ι hL heven D E X Y).some

lemma coefficient_open_unique (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C C' : CoefficientMap k L ι D E X Y) : C.openMap = C'.openMap := by
  obtain ⟨f, _, hu⟩ := open_constant_comparison k l ι L hL heven D E
  exact (hu C.openMap C.classifies).trans (hu C'.openMap C'.classifies).symm

lemma coefficient_compact_unique (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C C' : CoefficientMap k L ι D E X Y) : C.compactMap = C'.compactMap := by
  have ho := coefficient_open_unique k L ι hL heven C C'
  apply CompactComparison.extension_unique ι D E X Y C.openMap
    C.compactMap C'.compactMap C.extendsOpen
  rw [ho]
  exact C'.extendsOpen

/-- The coefficient comparison is unique as a complete normalized record. -/
lemma coefficientMap_unique (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C C' : CoefficientMap k L ι D E X Y) : C = C' := by
  have ho := coefficient_open_unique k L ι hL heven C C'
  have hF := coefficient_compact_unique k L ι hL heven C C'
  rcases C with ⟨f, F, hf, hF₁, e, he⟩
  rcases C' with ⟨f', F', hf', hF₂, e', he'⟩
  dsimp only at ho hF
  subst f'; subst F'
  obtain ⟨e₀, _, hu⟩ := open_hodge_constant_comparison k l ι L hL heven D E f hf
  have hee : e = e' := (hu e he).trans (hu e' he').symm
  subst e'
  rfl

/-- Composition retains the standard pullback associator in the normalized
Hodge map. -/
def coefficientComposite (ι : k →+* l) (κ : l →+* m)
    (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L} {V : LevelData m L}
    {X : Compactification k L D} {Y : Compactification l L E}
    {Z : Compactification m L V}
    (C : CoefficientMap k L ι D E X Y) (B : CoefficientMap l L κ E V Y Z) :
    CoefficientMap k L (κ.comp ι) D V X Z where
  openMap := B.openMap ≫ C.openMap
  compactMap := B.compactMap ≫ C.compactMap
  classifies := (composite_constant_comparison k l m ι κ L hL heven D E V
    C.openMap B.openMap C.classifies B.classifies C.hodgeMap B.hodgeMap
    C.normalized B.normalized).1
  extendsOpen := by
    constructor
    · rw [Category.assoc, C.extendsOpen.1, ← Category.assoc,
        B.extendsOpen.1, Category.assoc, ← constants_comp]
    · rw [← Category.assoc, B.extendsOpen.2, Category.assoc,
        C.extendsOpen.2, Category.assoc]
  hodgeMap := ((Scheme.Modules.pullbackComp B.openMap C.openMap).app (weight D)).symm ≪≫
    (Scheme.Modules.pullback B.openMap).mapIso C.hodgeMap ≪≫ B.hodgeMap
  normalized := (composite_constant_comparison k l m ι κ L hL heven D E V
    C.openMap B.openMap C.classifies B.classifies C.hodgeMap B.hodgeMap
    C.normalized B.normalized).2

def coefficientIdentity (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    CoefficientMap k L (RingHom.id k) D D X X where
  openMap := 𝟙 _
  compactMap := 𝟙 _
  classifies := (identity_constant_comparison k L hL heven D).1
  extendsOpen := by constructor <;> simp [constants_id]
  hodgeMap := (Scheme.Modules.pullbackId _).app (weight D)
  normalized := (identity_constant_comparison k L hL heven D).2

lemma coefficientMap_comp (ι : k →+* l) (κ : l →+* m)
    (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L) (V : LevelData m L)
    (X : Compactification k L D) (Y : Compactification l L E)
    (Z : Compactification m L V) :
    (coefficientMap k L (κ.comp ι) hL heven D V X Z).compactMap =
      (coefficientMap l L κ hL heven E V Y Z).compactMap ≫
      (coefficientMap k L ι hL heven D E X Y).compactMap :=
  coefficient_compact_unique k L (κ.comp ι) hL heven _
    (coefficientComposite k L ι κ hL heven
      (coefficientMap k L ι hL heven D E X Y)
      (coefficientMap l L κ hL heven E V Y Z))

lemma coefficientMap_id (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    (coefficientMap k L (RingHom.id k) hL heven D D X X).compactMap = 𝟙 X.space :=
  coefficient_compact_unique k L (RingHom.id k) hL heven _
    (coefficientIdentity k L hL heven D X)

/-- The actual semilinear coefficient automorphism of the fixed compact curve. -/
def coefficientAut (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (σ : k ≃+* k) :
    X.space ⟶ X.space :=
  (coefficientMap k L σ.toRingHom hL heven D D X X).compactMap

lemma coefficientAut_one (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    coefficientAut k L hL heven D X 1 = 𝟙 X.space :=
  coefficientMap_id k L hL heven D X

lemma coefficientAut_mul (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (σ τ : k ≃+* k) :
    coefficientAut k L hL heven D X (σ * τ) =
      coefficientAut k L hL heven D X σ ≫ coefficientAut k L hL heven D X τ :=
  coefficientMap_comp k L τ.toRingHom σ.toRingHom hL heven D D D X X X

lemma coefficientAut_isIso (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (σ : k ≃+* k) :
    IsIso (coefficientAut k L hL heven D X σ) := by
  refine ⟨⟨coefficientAut k L hL heven D X σ⁻¹, ?_, ?_⟩⟩
  · rw [← coefficientAut_mul, mul_inv_cancel, coefficientAut_one]
  · rw [← coefficientAut_mul, inv_mul_cancel, coefficientAut_one]

end CoefficientMaps

section CompactComposition
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open CompactHodgeConstantComparison

/-- Horizontal pasting for the specified pullback-square comparisons. -/
lemma square_horizontal {A B C D E F : Scheme.{0}}
    (i : A ⟶ B) (u : B ⟶ C) (v : C ⟶ D)
    (f : A ⟶ E) (j : E ⟶ C) (g : E ⟶ F) (r : F ⟶ D)
    (h₁ : i ≫ u = f ≫ j) (h₂ : j ≫ v = g ≫ r)
    (h : i ≫ (u ≫ v) = (f ≫ g) ≫ r) (M : D.Modules) :
    (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackComp u v).app M).hom ≫
      (squarePullbackIso i (u ≫ v) (f ≫ g) r h M).hom =
    (squarePullbackIso i u f j h₁ ((Scheme.Modules.pullback v).obj M)).hom ≫
      (Scheme.Modules.pullback f).map (squarePullbackIso j v g r h₂ M).hom ≫
      ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback r).obj M)).hom := by
  apply (cancel_mono (((Scheme.Modules.pullbackComp (f ≫ g) r).app M).hom ≫
    (pullbackEqIso (Category.assoc f g r) M).hom)).mp
  simp only [Category.assoc]
  rw [← tripleComp_assoc, square_post, square_pre_assoc]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, eqIso_trans, tripleComp, Functor.mapIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
/-- Compact comparisons compose with the canonical pullback associator,
and the resulting open restriction is the normalized composite comparison. -/
lemma compactCompatible_composite {l m : Type} [Field l] [CharZero l] [Field m] [CharZero m]
    (ι : k →+* l) (κ : l →+* m) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L} {V : LevelData m L}
    {X : Compactification k L D} {Y : Compactification l L E} {Z : Compactification m L V}
    (C : CoefficientMap k L ι D E X Y) (B : CoefficientMap l L κ E V Y Z)
    (H : Extension k L D X) (J : Extension l L E Y) (K : Extension m L V Z)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (b : (Scheme.Modules.pullback B.compactMap).obj J.line ≅ K.line)
    (ha : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J a)
    (hb : CompactCompatible κ B.openMap B.compactMap B.extendsOpen B.hodgeMap J K b) :
    let CB := coefficientComposite k L ι κ hL heven C B
    CompactCompatible (κ.comp ι) CB.openMap CB.compactMap CB.extendsOpen CB.hodgeMap H K
      (((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).symm ≪≫
        (Scheme.Modules.pullback B.compactMap).mapIso a ≪≫ b) := by
  let CB := coefficientComposite k L ι κ hL heven C B
  change (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom =
    (squarePullbackIso Y.inclusion C.compactMap C.openMap X.inclusion C.extendsOpen.2 H.line).hom ≫
      (Scheme.Modules.pullback C.openMap).map H.onOpen.hom ≫ C.hodgeMap.hom at ha
  change (Scheme.Modules.pullback Z.inclusion).map b.hom ≫ K.onOpen.hom =
    (squarePullbackIso Z.inclusion B.compactMap B.openMap Y.inclusion B.extendsOpen.2 J.line).hom ≫
      (Scheme.Modules.pullback B.openMap).map J.onOpen.hom ≫ B.hodgeMap.hom at hb
  change (Scheme.Modules.pullback Z.inclusion).map
    ((((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).symm ≪≫
      (Scheme.Modules.pullback B.compactMap).mapIso a ≪≫ b).hom) ≫ K.onOpen.hom =
    (squarePullbackIso Z.inclusion (B.compactMap ≫ C.compactMap)
      (B.openMap ≫ C.openMap) X.inclusion CB.extendsOpen.2 H.line).hom ≫
      (Scheme.Modules.pullback (B.openMap ≫ C.openMap)).map H.onOpen.hom ≫ CB.hodgeMap.hom
  apply (cancel_epi ((Scheme.Modules.pullback Z.inclusion).map
    ((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback Z.inclusion).map
    ((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).hom)
    ((Scheme.Modules.pullback Z.inclusion).map
      ((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).inv),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hb]
  rw [← Category.assoc ((Scheme.Modules.pullback Z.inclusion).map
    ((Scheme.Modules.pullback B.compactMap).map a.hom)),
    ← squarePullbackIso_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback B.openMap).map
    ((Scheme.Modules.pullback Y.inclusion).map a.hom)), ← Functor.map_comp, ha]
  have hsq := square_horizontal Z.inclusion B.compactMap C.compactMap
    B.openMap Y.inclusion C.openMap X.inclusion B.extendsOpen.2 C.extendsOpen.2
    CB.extendsOpen.2 H.line
  rw [← Category.assoc ((Scheme.Modules.pullback Z.inclusion).map
    ((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).hom)]
  erw [hsq]
  have hn := (Scheme.Modules.pullbackComp B.openMap C.openMap).hom.naturality H.onOpen.hom
  simp only [Functor.comp_map] at hn
  simp only [CB, coefficientComposite, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp B.openMap C.openMap).app
    ((Scheme.Modules.pullback X.inclusion).obj H.line)).hom]
  erw [← hn]
  simp only [Category.assoc, ← Iso.app_hom]
  erw [Iso.hom_inv_id_assoc]


/-- The two equality-transport presentations of pullback agree. -/
lemma eqIso_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (M : B.Modules) :
    pullbackEqIso h M = (Scheme.Modules.pullbackCongr h).app M := by
  subst g
  rfl

/-- The square comparison preserves the specified pullback unit. -/
lemma square_unit {A B : Scheme.{0}} (i : A ⟶ B)
    (h : i ≫ 𝟙 B = 𝟙 A ≫ i) (M : B.Modules) :
    (squarePullbackIso i (𝟙 B) (𝟙 A) i h M).hom ≫
      ((Scheme.Modules.pullbackId A).app ((Scheme.Modules.pullback i).obj M)).hom =
    (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId B).app M).hom := by
  change _ ≫ (Scheme.Modules.pullbackId A).hom.app _ = _
  rw [← ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_id i M]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← Iso.app_hom]
  rw [Iso.inv_hom_id_assoc]
  rw [← eqIso_congr, eqIso_trans, eqIso_congr]
  exact ArithmeticThetaLevelConstantsR0234.OpenHodgeComparisonProof.pullback_right_unit i M

lemma square_unit_natural {A B : Scheme.{0}} (i : A ⟶ B)
    (h : i ≫ 𝟙 B = 𝟙 A ≫ i) (M : B.Modules) (N : A.Modules)
    (e : (Scheme.Modules.pullback i).obj M ≅ N) :
    (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId B).app M).hom ≫ e.hom =
      (squarePullbackIso i (𝟙 B) (𝟙 A) i h M).hom ≫
        (Scheme.Modules.pullback (𝟙 A)).map e.hom ≫
          ((Scheme.Modules.pullbackId A).app N).hom := by
  erw [(Scheme.Modules.pullbackId A).hom.naturality e.hom]
  simp only [Functor.id_map]
  simp only [← Iso.app_hom]
  rw [← Category.assoc, square_unit]

set_option backward.isDefEq.respectTransparency.types false in
lemma compactCompatible_identity (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) :
    let C := coefficientIdentity k L hL heven D X
    CompactCompatible (RingHom.id k) C.openMap C.compactMap C.extendsOpen C.hodgeMap
      H H ((Scheme.Modules.pullbackId X.space).app H.line) := by
  simpa only [coefficientIdentity, CompactCompatible, squarePullbackIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    square_unit_natural X.inclusion
      (coefficientIdentity k L hL heven D X).extendsOpen.2 H.line (ArithmeticThetaLevelConstantsR0234.weight D) H.onOpen



/-- Transport a normalized compact comparison along equality of complete
coefficient-map records, with the actual compact map equality retained. -/
lemma compactCompatible_congr {l : Type} [Field l] [CharZero l]
    (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C C' : CoefficientMap k L ι D E X Y)
    (h : C.compactMap = C'.compactMap)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback C'.compactMap).obj H.line ≅ J.line)
    (ha : CompactCompatible ι C'.openMap C'.compactMap C'.extendsOpen C'.hodgeMap H J a) :
    CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J
      (pullbackEqIso h H.line ≪≫ a) := by
  have he := coefficientMap_unique k L ι hL heven C C'
  subst C'
  simpa [pullbackEqIso] using ha

end CompactComposition

#print axioms compactCompatible_composite
#print axioms square_horizontal

section DescentGeometry
open CategoryTheory.Limits

/-- Two embeddings of a finite normal field into the same field differ by
an actual automorphism of the source field. -/
lemma embeddings_differ_by_aut {K E F : Type} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E] [Normal K E]
    (a b : E →ₐ[K] F) : ∃ σ : E ≃ₐ[K] E, ∀ x, a (σ x) = b x := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField K E
  letI := hp
  have hr : b.range = a.range :=
    (Polynomial.IsSplittingField.adjoin_rootSet_eq_range E p b).symm.trans
      (Polynomial.IsSplittingField.adjoin_rootSet_eq_range E p a)
  let ea := AlgEquiv.ofInjective a a.injective
  let eb := AlgEquiv.ofInjective b b.injective
  let σ := eb.trans ((Subalgebra.equivOfEq _ _ hr).trans ea.symm)
  refine ⟨σ, fun x => ?_⟩
  have hh := ea.apply_symm_apply ((Subalgebra.equivOfEq _ _ hr) (eb x))
  exact congrArg Subtype.val hh

/-- For an etale target over a base, agreement at a residue-field point
extends to an open neighborhood, including on nonreduced source tests. -/
lemma etale_equality_open {S Y Z : Scheme.{0}} (q : Y ⟶ S) [Etale q]
    (f g : Z ⟶ Y) (h : f ≫ q = g ≫ q) :
    ∃ U : Z.Opens, U.ι ≫ f = U.ι ≫ g ∧
      ∀ z : Z, Z.fromSpecResidueField z ≫ f = Z.fromSpecResidueField z ≫ g → z ∈ U := by
  let t := pullback.lift f g h
  let p := pullback.snd (pullback.diagonal q) t
  letI : IsOpenImmersion p := inferInstance
  have hpfg : p ≫ f = p ≫ g := by
    have hc := pullback.condition (f := pullback.diagonal q) (g := t)
    have h1 := congrArg (fun a => a ≫ pullback.fst q q) hc
    have h2 := congrArg (fun a => a ≫ pullback.snd q q) hc
    simp only [t, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id, pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact h1.symm.trans h2
  let U := p.opensRange
  let j := IsOpenImmersion.lift p U.ι (by simp [U])
  have hj : j ≫ p = U.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, ?_, ?_⟩
  · rw [← hj, Category.assoc, hpfg, ← Category.assoc, hj]
  · intro z hz
    have ht : (Z.fromSpecResidueField z ≫ f) ≫ pullback.diagonal q =
        Z.fromSpecResidueField z ≫ t := by
      apply pullback.hom_ext
      · simp [t, Category.assoc]
      · simpa [t, Category.assoc] using hz
    let r := pullback.lift (Z.fromSpecResidueField z ≫ f) (Z.fromSpecResidueField z) ht
    have hr : r ≫ p = Z.fromSpecResidueField z := pullback.lift_snd _ _ _
    change z ∈ Set.range p
    refine ⟨r (IsLocalRing.closedPoint (Z.residueField z)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hr]
    simp

lemma etale_equal_on_neighborhood {S Y Z : Scheme.{0}} (q : Y ⟶ S) [Etale q]
    (f g : Z ⟶ Y) (h : f ≫ q = g ≫ q) (z : Z)
    (hz : Z.fromSpecResidueField z ≫ f = Z.fromSpecResidueField z ≫ g) :
    ∃ U : Z.Opens, z ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  obtain ⟨U, hU, hzU⟩ := etale_equality_open q f g h
  exact ⟨U, hzU z hz, hU⟩

end DescentGeometry

#print axioms embeddings_differ_by_aut
#print axioms etale_equal_on_neighborhood

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelConstantsR0234

lemma coefficientHodge_congr {l : Type} [Field l] [CharZero l]
    (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C C' : CoefficientMap k L ι D E X Y) (h : C.openMap = C'.openMap) :
    C.hodgeMap = pullbackEqIso h (weight D) ≪≫ C'.hodgeMap := by
  have hh := coefficientMap_unique k L ι hL heven C C'
  subst C'
  simp [pullbackEqIso]


namespace GaloisDescent
open CategoryTheory.Limits
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback.LDescDatumAux
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.Loc
abbrev MF := (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁
lemma loc_congr {X Z : Scheme.{0}} (M : X.Modules)
    {f₀ f₁ g₀ g₁ : Z ⟶ X} (hf : f₀ = f₁) (hg : g₀ = g₁)
    (T : X ⟶ X) (a : M ≅ (Scheme.Modules.pullback T).obj M)
    (h₀ : f₀ ≫ T = g₀) (h₁ : f₁ ≫ T = g₁) :
    (Scheme.Modules.pullbackCongr hf).inv.app M ≫ loc M f₀ g₀ T a h₀ ≫
      (Scheme.Modules.pullbackCongr hg).hom.app M = loc M f₁ g₁ T a h₁ := by
  subst f₁; subst g₁
  simp [Scheme.Modules.pullbackCongr]

variable {X Y : Scheme.{0}} (q : X ⟶ Y)
  (G : Type) [AddGroup G] (σ : G → (X ⟶ X))
  (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
  (hfree : ∀ ⦃Z : Scheme.{0}⦄ (v : Z ⟶ X) (g : G), Nonempty Z → v ≫ σ g = v → g = 0)
  (hsplit : ∀ ⦃Z : Scheme.{0}⦄ (f g : Z ⟶ X), f ≫ q = g ≫ q →
    ∃ U : G → Z.Opens, ⨆ a, U a = ⊤ ∧ ∀ a, (U a).ι ≫ g = (U a).ι ≫ f ≫ σ a)
  (M : X.Modules) (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
  (hψadd : ∀ g h : G, ψ (g + h) = ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
    (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫
      ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)

include hσ0 hσadd hfree hsplit hψadd in
lemma effective_datum :
    ∃ D : MF.DescentData (fun _ : Unit => q), ∃ e : ∀ i, D.obj i ≅ M,
      ∀ (a : G) {Z : Scheme.{0}} (f g : Z ⟶ X) (hf : f ≫ q = g ≫ q)
        (hfg : f ≫ σ a = g),
        (Scheme.Modules.pullback f).map (e ()).inv ≫
          D.hom (g ≫ q) (i₁ := ()) (i₂ := ()) f g hf rfl ≫
            (Scheme.Modules.pullback g).map (e ()).hom = loc M f g (σ a) (ψ a) hfg := by
  let a₁ := pullback.fst q q
  let a₂ := pullback.snd q q
  have ha : a₁ ≫ q = a₂ ≫ q := pullback.condition
  let b₁₂ := pullback.fst a₂ a₁
  let b₂₃ := pullback.snd a₂ a₁
  have h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁ := pullback.condition
  let b₁₃ : pullback a₂ a₁ ⟶ pullback q q := pullback.lift (b₁₂ ≫ a₁) (b₂₃ ≫ a₂)
    (by rw [Category.assoc, ha, ← Category.assoc, h₂, Category.assoc, Category.assoc, ha])
  have h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁ := (pullback.lift_fst _ _ _).symm
  have h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂ := pullback.lift_snd _ _ _
  obtain ⟨Ψ, hΨ⟩ := Scheme.Modules.exists_iso_pullback_forall_mapIso_eq_of_free_of_split
    q G σ hσ0 hσadd hfree hsplit M ψ a₁ a₂ ha
  have hcoc := Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
    q G σ hσadd hsplit M ψ hψadd a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ Ψ hΨ
  let D := datum q a₁ a₂ (IsPullback.of_hasPullback q q) b₁₂ b₁₃ b₂₃ h₁ h₂ h₃
    (IsPullback.of_hasPullback a₂ a₁) M Ψ hcoc
  refine ⟨D, fun _ => Iso.refl _, ?_⟩
  intro a Z f g hf hfg
  change (Scheme.Modules.pullback f).map (𝟙 M) ≫
    D.hom (g ≫ q) (i₁ := ()) (i₂ := ()) f g hf rfl ≫
      (Scheme.Modules.pullback g).map (𝟙 M) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [(Scheme.Modules.pullback g).map_id M, Category.comp_id]
  let t : Z ⟶ pullback q q := pullback.lift f g hf
  have ht₁ : t ≫ a₁ = f := pullback.lift_fst _ _ _
  have ht₂ : t ≫ a₂ = g := pullback.lift_snd _ _ _
  have ht : (t ≫ a₁) ≫ σ a = t ≫ a₂ := by rw [ht₁, ht₂]; exact hfg
  have hh := congrArg Iso.hom (hΨ a t ht)
  change CategoryTheory.Pseudofunctor.DescentData'.pullHom' (F := MF)
    (sq := fun _ _ : Unit => sqC q a₁ a₂ (IsPullback.of_hasPullback q q))
    (fun _ _ => Ψ.hom) (g ≫ q) (i₁ := ()) (i₂ := ()) f g hf rfl = _
  rw [CategoryTheory.Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ t hf rfl ht₁ ht₂]
  rw [pullHom_FF]
  change (Scheme.Modules.pullbackCongr ht₁).inv.app M ≫
    (Scheme.Modules.pullbackComp t a₁).inv.app M ≫
      (Scheme.Modules.pullback t).map Ψ.hom ≫
        (Scheme.Modules.pullbackComp t a₂).hom.app M ≫
          (Scheme.Modules.pullbackCongr ht₂).hom.app M = _
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv] at hh
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [loc, Category.assoc] using loc_congr M ht₁ ht₂ (σ a) (ψ a) ht hfg
def dataEval {X Y : Scheme.{0}} (q : X ⟶ Y) :
    MF.DescentData (fun _ : Unit => q) ⥤ X.Modules where
  obj D := D.obj ()
  map f := f.hom ()

set_option backward.isDefEq.respectTransparency.types false in
include hσ0 hσadd hfree hsplit hψadd in
lemma effective_line [QuasiCompact q] [Flat q] [Surjective q]
    (hM : Scheme.Modules.IsInvertible M) :
    ∃ N : Y.Modules, Scheme.Modules.IsInvertible N ∧
      ∃ a : (Scheme.Modules.pullback q).obj N ≅ M,
        ∀ (s : G) {Z : Scheme.{0}} (f g : Z ⟶ X) (hf : f ≫ q = g ≫ q)
          (hfg : f ≫ σ s = g),
          ((MF.toDescentData (fun _ : Unit => q)).obj N).hom (g ≫ q)
              (i₁ := ()) (i₂ := ()) f g hf rfl ≫
            (Scheme.Modules.pullback g).map a.hom =
              (Scheme.Modules.pullback f).map a.hom ≫ loc M f g (σ s) (ψ s) hfg := by
  obtain ⟨D, e, hD⟩ := effective_datum q G σ hσ0 hσadd hfree hsplit M ψ hψadd
  have hInv : ∀ i, Scheme.Modules.IsInvertible (D.obj i) := fun i =>
    P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective.AlgebraicGeometry.Scheme.Modules.InvDescAssembly.isInvertible_of_iso (e i).symm hM
  obtain ⟨N, hN, ⟨b⟩⟩ :=
    ArithmeticThetaRootDescentR0197.FPQCSquareRootDescentR0197.module_effective q D hInv
  let J : X.Modules := D.obj ()
  let e₀ : J ≅ M := e ()
  let b₀ : (Scheme.Modules.pullback q).obj N ≅ J := (dataEval q).mapIso b
  let a := b₀ ≪≫ e₀
  refine ⟨N, hN, a, ?_⟩
  intro s Z f g hf hfg
  have hb := b.hom.comm (g ≫ q) (i₁ := ()) (i₂ := ()) f g hf rfl
  have hd := hD s f g hf hfg
  let dh : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback q).obj N) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj N) :=
    ((MF.toDescentData (fun _ : Unit => q)).obj N).hom (g ≫ q) (i₁ := ()) (i₂ := ()) f g hf rfl
  let th : (Scheme.Modules.pullback f).obj J ⟶
      (Scheme.Modules.pullback g).obj J := D.hom (g ≫ q) f g hf rfl
  change (Scheme.Modules.pullback f).map b₀.hom ≫ th =
    dh ≫ (Scheme.Modules.pullback g).map b₀.hom at hb
  change (Scheme.Modules.pullback f).map e₀.inv ≫ th ≫
    (Scheme.Modules.pullback g).map e₀.hom = _ at hd
  change dh ≫ (Scheme.Modules.pullback g).map (b₀.hom ≫ e₀.hom) =
    (Scheme.Modules.pullback f).map (b₀.hom ≫ e₀.hom) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  rw [← hd]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map e₀.hom)
    ((Scheme.Modules.pullback f).map e₀.inv),
    ← (Scheme.Modules.pullback f).map_comp e₀.hom e₀.inv,
    e₀.hom_inv_id, (Scheme.Modules.pullback f).map_id, Category.id_comp]
  rw [← Category.assoc, ← hb]
  simp only [Category.assoc]



#print axioms effective_datum
#print axioms effective_line
end GaloisDescent

namespace GaloisMorphisms
lemma pullback_comm {X Z Z' : Scheme.{0}} (f g : Z ⟶ X) (u : Z' ⟶ Z)
    (M N : X.Modules) (a : M ⟶ N)
    (d : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback g).obj M)
    (e : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback g).obj N)
    (d' : (Scheme.Modules.pullback (u ≫ f)).obj M ⟶ (Scheme.Modules.pullback (u ≫ g)).obj M)
    (e' : (Scheme.Modules.pullback (u ≫ f)).obj N ⟶ (Scheme.Modules.pullback (u ≫ g)).obj N)
    (hd : ((Scheme.Modules.pullbackComp u f).app M).inv ≫
      (Scheme.Modules.pullback u).map d ≫ ((Scheme.Modules.pullbackComp u g).app M).hom = d')
    (he : ((Scheme.Modules.pullbackComp u f).app N).inv ≫
      (Scheme.Modules.pullback u).map e ≫ ((Scheme.Modules.pullbackComp u g).app N).hom = e')
    (ha : (Scheme.Modules.pullback (u ≫ f)).map a ≫ e' =
      d' ≫ (Scheme.Modules.pullback (u ≫ g)).map a) :
    (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback f).map a ≫ e) =
      (Scheme.Modules.pullback u).map (d ≫ (Scheme.Modules.pullback g).map a) := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp u f).app M).inv).mp
  apply (cancel_mono ((Scheme.Modules.pullbackComp u g).app N).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  have hf := (Scheme.Modules.pullbackComp u f).inv.naturality a
  have hg := (Scheme.Modules.pullbackComp u g).hom.naturality a
  simp only [Functor.comp_map, ← Iso.app_hom, ← Iso.app_inv] at hf hg
  rw [← Category.assoc ((Scheme.Modules.pullbackComp u f).app M).inv
    ((Scheme.Modules.pullback u).map ((Scheme.Modules.pullback f).map a)), ← hf]
  simp only [Category.assoc]
  rw [he, hg]
  rw [← Category.assoc ((Scheme.Modules.pullback u).map d),
    ← Category.assoc ((Scheme.Modules.pullbackComp u f).app M).inv, hd]
  exact ha

open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback.LDescDatumAux
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.KPGlue
abbrev MF := (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁

lemma comm_of_split {X Y : Scheme.{0}} (q : X ⟶ Y) (G : Type) (σ : G → (X ⟶ X))
    (hsplit : ∀ ⦃Z : Scheme.{0}⦄ (f g : Z ⟶ X), f ≫ q = g ≫ q →
      ∃ U : G → Z.Opens, ⨆ a, U a = ⊤ ∧ ∀ a, (U a).ι ≫ g = (U a).ι ≫ f ≫ σ a)
    (D E : MF.DescentData (fun _ : Unit => q)) (a : D.obj () ⟶ E.obj ())
    (ha : ∀ (s : G) {Z : Scheme.{0}} (p : Z ⟶ Y) (f g : Z ⟶ X)
      (hf : f ≫ q = p) (hg : g ≫ q = p) (hfg : f ≫ σ s = g),
      (Scheme.Modules.pullback f).map a ≫ E.hom p (i₁ := ()) (i₂ := ()) f g hf hg =
        D.hom p (i₁ := ()) (i₂ := ()) f g hf hg ≫ (Scheme.Modules.pullback g).map a) :
    ∀ {Z : Scheme.{0}} (p : Z ⟶ Y) (f g : Z ⟶ X) (hf : f ≫ q = p) (hg : g ≫ q = p),
      (Scheme.Modules.pullback f).map a ≫ E.hom p (i₁ := ()) (i₂ := ()) f g hf hg =
        D.hom p (i₁ := ()) (i₂ := ()) f g hf hg ≫ (Scheme.Modules.pullback g).map a := by
  intro Z p f g hf hg
  obtain ⟨U, hU, hUs⟩ := hsplit f g (hf.trans hg.symm)
  apply hom_ext_of_cover U hU
  intro s
  let u := (U s).ι
  have hfu : (u ≫ f) ≫ q = u ≫ p := by rw [Category.assoc, hf]
  have hgu : (u ≫ g) ≫ q = u ≫ p := by rw [Category.assoc, hg]
  have hfg : (u ≫ f) ≫ σ s = u ≫ g := by
    rw [Category.assoc]
    exact (hUs s).symm
  have hd := D.pullHom_hom u p (u ≫ p) rfl (i₁ := ()) (i₂ := ()) f g hf hg
    (u ≫ f) (u ≫ g) rfl rfl
  have he := E.pullHom_hom u p (u ≫ p) rfl (i₁ := ()) (i₂ := ()) f g hf hg
    (u ≫ f) (u ≫ g) rfl rfl
  simp only [pullHom_FF, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id] at hd he
  exact pullback_comm f g u (D.obj ()) (E.obj ()) a (D.hom p f g hf hg)
    (E.hom p f g hf hg) (D.hom (u ≫ p) (u ≫ f) (u ≫ g) hfu hgu)
    (E.hom (u ≫ p) (u ≫ f) (u ≫ g) hfu hgu) hd he (ha s (u ≫ p) _ _ hfu hgu hfg)

lemma iso_of_split {X Y : Scheme.{0}} (q : X ⟶ Y)
    [QuasiCompact q] [Flat q] [Surjective q] (G : Type) (σ : G → (X ⟶ X))
    (hsplit : ∀ ⦃Z : Scheme.{0}⦄ (f g : Z ⟶ X), f ≫ q = g ≫ q →
      ∃ U : G → Z.Opens, ⨆ a, U a = ⊤ ∧ ∀ a, (U a).ι ≫ g = (U a).ι ≫ f ≫ σ a)
    (M N : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj N)
    (ha : ∀ (s : G) {Z : Scheme.{0}} (p : Z ⟶ Y) (f g : Z ⟶ X)
      (hf : f ≫ q = p) (hg : g ≫ q = p) (hfg : f ≫ σ s = g),
      (Scheme.Modules.pullback f).map a.hom ≫
          ((MF.toDescentData (fun _ : Unit => q)).obj N).hom p (i₁ := ()) (i₂ := ()) f g hf hg =
        ((MF.toDescentData (fun _ : Unit => q)).obj M).hom p (i₁ := ()) (i₂ := ()) f g hf hg ≫
          (Scheme.Modules.pullback g).map a.hom) :
    ∃ b : M ≅ N, (Scheme.Modules.pullback q).mapIso b = a := by
  let F := MF.toDescentData (fun _ : Unit => q)
  let e : F.obj M ≅ F.obj N := Pseudofunctor.DescentData.isoMk (fun _ => a)
    (by
      intro Z p i j f g hf hg
      cases i; cases j
      exact comm_of_split q G σ hsplit (F.obj M) (F.obj N) a.hom ha p f g hf hg)
  have hMN := ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q M N hM hN
  have hNM := ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q N M hN hM
  obtain ⟨b, hb⟩ := hMN.2 e.hom
  obtain ⟨c, hc⟩ := hNM.2 e.inv
  have hbc : b ≫ c = 𝟙 M := by
    apply (ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q M M hM hM).1
    change F.map (b ≫ c) = F.map (𝟙 M)
    rw [F.map_comp, F.map_id, hb, hc, e.hom_inv_id]
  have hcb : c ≫ b = 𝟙 N := by
    apply (ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q N N hN hN).1
    change F.map (c ≫ b) = F.map (𝟙 N)
    rw [F.map_comp, F.map_id, hc, hb, e.inv_hom_id]
  refine ⟨⟨b, c, hbc, hcb⟩, ?_⟩
  apply Iso.ext
  exact congrArg (fun φ => φ.hom ()) hb

#print axioms iso_of_split
#print axioms comm_of_split
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.Loc
lemma loc_natural {X Z : Scheme.{0}} (f g : Z ⟶ X) (T : X ⟶ X) (h : f ≫ T = g)
    (M N : X.Modules) (ψ : M ≅ (Scheme.Modules.pullback T).obj M)
    (χ : N ≅ (Scheme.Modules.pullback T).obj N) (a : M ⟶ N)
    (ha : a ≫ χ.hom = ψ.hom ≫ (Scheme.Modules.pullback T).map a) :
    (Scheme.Modules.pullback f).map a ≫ loc N f g T χ h =
      loc M f g T ψ h ≫ (Scheme.Modules.pullback g).map a := by
  have hn := (Scheme.Modules.pullbackComp f T).hom.naturality a
  have he := (Scheme.Modules.pullbackCongr h).hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [loc, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map a), ← Functor.map_comp, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback T).map a)), hn]
  simp only [Category.assoc]
  rw [he]
#print axioms loc_natural

set_option backward.isDefEq.respectTransparency.types false in
lemma datum_transition {X Y : Scheme.{0}} (q : X ⟶ Y) (T : X ⟶ X) (hT : T ≫ q = q)
    (D : MF.DescentData (fun _ : Unit => q))
    (ψ : D.obj () ≅ (Scheme.Modules.pullback T).obj (D.obj ()))
    (hψ : D.hom q (i₁ := ()) (i₂ := ()) (𝟙 X) T (Category.id_comp q) hT =
      ((Scheme.Modules.pullbackId X).app (D.obj ())).hom ≫ ψ.hom)
    {Z : Scheme.{0}} (f g : Z ⟶ X) (hfg : f ≫ T = g) :
    D.hom (f ≫ q) (i₁ := ()) (i₂ := ()) f g rfl
      (by rw [← hfg, Category.assoc, hT]) = loc (D.obj ()) f g T ψ hfg := by
  have hd := D.pullHom_hom f q (f ≫ q) rfl (i₁ := ()) (i₂ := ())
    (𝟙 X) T (Category.id_comp q) hT f g (Category.comp_id f) hfg
  rw [hψ, pullHom_FF] at hd
  have hu := ArithmeticThetaLevelConstantsR0234.OpenHodgeComparisonProof.pullback_right_unit f (D.obj ())
  simp only [Functor.map_comp, Iso.app_hom] at hd
  rw [← hu] at hd
  simpa only [loc, Category.assoc, Iso.inv_hom_id_app_assoc] using hd.symm

#print axioms datum_transition

end GaloisMorphisms



namespace SplittingCover
open ArithmeticThetaLevelConstantsR0234
variable {k L} {D : LevelData k L} {X : Compactification k L D}

def galoisAction (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) : C.compact.space ⟶ C.compact.space :=
  coefficientAut (CyclotomicField L k) L hL heven C.level C.compact σ.toRingEquiv

lemma galoisAction_one (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L) :
    C.galoisAction hL heven 1 = 𝟙 C.compact.space :=
  coefficientAut_one (CyclotomicField L k) L hL heven C.level C.compact

lemma galoisAction_mul (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ τ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    C.galoisAction hL heven (σ * τ) = C.galoisAction hL heven σ ≫ C.galoisAction hL heven τ :=
  coefficientAut_mul (CyclotomicField L k) L hL heven C.level C.compact
    σ.toRingEquiv τ.toRingEquiv

lemma galoisAction_projection (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    C.galoisAction hL heven σ ≫ C.compact.projection =
      C.compact.projection ≫ constants σ.toRingHom :=
  (coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
    C.level C.level C.compact C.compact).extendsOpen.1

/-- Galois coefficient automorphisms preserve the actual compact cover map. -/
lemma galoisAction_over (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    C.galoisAction hL heven σ ≫ C.compactMap = C.compactMap := by
  let A : CoefficientMap k L (algebraMap k (CyclotomicField L k)) D C.level X C.compact :=
    ⟨C.openMap, C.compactMap, C.classifies, C.extendsOpen, C.hodgeMap, C.normalized⟩
  let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
    C.level C.level C.compact C.compact
  let AB := coefficientComposite k L (algebraMap k (CyclotomicField L k)) σ.toRingHom
    hL heven A B
  have hι : σ.toRingHom.comp (algebraMap k (CyclotomicField L k)) =
      algebraMap k (CyclotomicField L k) := by ext a; exact σ.commutes a
  have hf : RespectsClassifiers (algebraMap k (CyclotomicField L k)) D C.level
      (B.openMap ≫ C.openMap) := by simpa only [AB, coefficientComposite, A, hι] using AB.classifies
  have hF : ArithmeticThetaLevelConstantsR0234.Extends
      (algebraMap k (CyclotomicField L k)) D C.level X C.compact
      (B.openMap ≫ C.openMap) (B.compactMap ≫ C.compactMap) := by
    simpa only [AB, coefficientComposite, A, hι] using AB.extendsOpen
  obtain ⟨f, _, hu⟩ := open_constant_comparison k (CyclotomicField L k)
    (algebraMap k (CyclotomicField L k)) L hL heven D C.level
  have ho : B.openMap ≫ C.openMap = C.openMap :=
    (hu _ hf).trans (hu _ C.classifies).symm
  rw [ho] at hF
  exact CompactComparison.extension_unique (algebraMap k (CyclotomicField L k))
    D C.level X C.compact C.openMap _ _ hF C.extendsOpen

/-- A nonempty test cannot be fixed by a nonidentity coefficient automorphism.
The argument uses an actual residue-field point of the test. -/
lemma galoisAction_free (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    {Z : Scheme.{0}} (v : Z ⟶ C.compact.space)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k)
    (hZ : Nonempty Z) (hv : v ≫ C.galoisAction hL heven σ = v) : σ = 1 := by
  obtain ⟨z⟩ := hZ
  let p := Z.fromSpecResidueField z ≫ v ≫ C.compact.projection
  have hp : p ≫ constants σ.toRingHom = p := by
    have hproj := congrArg (fun q => Z.fromSpecResidueField z ≫ v ≫ q)
      (C.galoisAction_projection hL heven σ).symm
    have hfix := congrArg (fun q => Z.fromSpecResidueField z ≫ q ≫ C.compact.projection) hv
    simp only [Category.assoc] at hproj hfix
    exact hproj.trans hfix
  have hr := congrArg Spec.preimage hp
  rw [Spec.preimage_comp, Spec.preimage_map] at hr
  apply AlgEquiv.ext
  intro a
  apply (Spec.preimage p).hom.injective
  exact ConcreteCategory.congr_hom hr a

/-- The two maps to the coefficient field at any residue-field point
are conjugate by a Galois automorphism, and the Cartesian square lifts this
to the same equality of maps into the compact curve. -/
lemma galoisAction_residue (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    {Z : Scheme.{0}} (f g : Z ⟶ C.compact.space)
    (hfg : f ≫ C.compactMap = g ≫ C.compactMap) (z : Z) :
    ∃ σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k,
      Z.fromSpecResidueField z ≫ f ≫ C.galoisAction hL heven σ =
        Z.fromSpecResidueField z ≫ g := by
  let l := CyclotomicField L k
  let ι : k →+* l := algebraMap k l
  let p := Z.fromSpecResidueField z ≫ f ≫ C.compact.projection
  let q := Z.fromSpecResidueField z ≫ g ≫ C.compact.projection
  let a : l →+* Z.residueField z := (Spec.preimage p).hom
  let b : l →+* Z.residueField z := (Spec.preimage q).hom
  have hpq : p ≫ constants ι = q ≫ constants ι := by
    have h := congrArg (fun t => Z.fromSpecResidueField z ≫ t ≫ X.projection) hfg
    simpa only [p, q, Category.assoc, C.extendsOpen.1] using h
  have hab : a.comp ι = b.comp ι := by
    have h := congrArg Spec.preimage hpq
    simp only [Spec.preimage_comp, Spec.preimage_map] at h
    exact congrArg CommRingCat.Hom.hom h
  letI : Algebra k (Z.residueField z) := (a.comp ι).toAlgebra
  let aa : l →ₐ[k] Z.residueField z := ⟨a, fun _ => rfl⟩
  let bb : l →ₐ[k] Z.residueField z := ⟨b, fun x => (RingHom.congr_fun hab x).symm⟩
  letI : FiniteDimensional k l := by dsimp [l, CyclotomicField]; infer_instance
  letI : Normal k l := by dsimp [l, CyclotomicField]; infer_instance
  obtain ⟨σ, hσ⟩ := embeddings_differ_by_aut aa bb
  have hbase : p ≫ constants σ.toRingHom = q := by
    have hh : Spec.preimage (p ≫ constants σ.toRingHom) = Spec.preimage q := by
      rw [Spec.preimage_comp, Spec.preimage_map]
      ext x
      exact hσ x
    rw [← Spec.map_preimage (p ≫ constants σ.toRingHom), ← Spec.map_preimage q, hh]
  refine ⟨σ, C.cartesian.hom_ext ?_ ?_⟩
  · simp only [Category.assoc, C.galoisAction_over hL heven σ]
    exact congrArg (fun t => Z.fromSpecResidueField z ≫ t) hfg
  · have hp := C.galoisAction_projection hL heven σ
    change C.galoisAction hL heven σ ≫ C.compact.projection =
      C.compact.projection ≫ constants σ.toRingHom at hp
    calc
      (Z.fromSpecResidueField z ≫ f ≫ C.galoisAction hL heven σ) ≫ C.compact.projection =
          Z.fromSpecResidueField z ≫ f ≫ (C.galoisAction hL heven σ ≫ C.compact.projection) := by
            simp only [Category.assoc]
      _ = Z.fromSpecResidueField z ≫ f ≫ (C.compact.projection ≫ constants σ.toRingHom) :=
        congrArg (fun t => Z.fromSpecResidueField z ≫ f ≫ t) hp
      _ = (Z.fromSpecResidueField z ≫ g) ≫ C.compact.projection := by
        simpa only [p, q, Category.assoc] using hbase

/-- The actual Galois cover splits over arbitrary scheme tests, using
open equality loci for the etale cover. -/
lemma galoisAction_split (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    {Z : Scheme.{0}} (f g : Z ⟶ C.compact.space)
    (hfg : f ≫ C.compactMap = g ≫ C.compactMap) :
    ∃ U : (CyclotomicField L k ≃ₐ[k] CyclotomicField L k) → Z.Opens,
      (⨆ σ, U σ) = ⊤ ∧ ∀ σ,
        (U σ).ι ≫ g = (U σ).ι ≫ f ≫ C.galoisAction hL heven σ := by
  classical
  letI := C.etale
  have hex : ∀ σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k,
      ∃ U : Z.Opens, U.ι ≫ g = U.ι ≫ f ≫ C.galoisAction hL heven σ ∧
        ∀ z : Z, Z.fromSpecResidueField z ≫ g =
          Z.fromSpecResidueField z ≫ f ≫ C.galoisAction hL heven σ → z ∈ U := by
    intro σ
    apply etale_equality_open C.compactMap g (f ≫ C.galoisAction hL heven σ)
    rw [Category.assoc, C.galoisAction_over hL heven σ]
    exact hfg.symm
  choose U hU hzU using hex
  refine ⟨U, ?_, hU⟩
  apply top_unique
  intro z _
  obtain ⟨σ, hσ⟩ := C.galoisAction_residue hL heven f g hfg z
  exact (le_iSup U σ) (hzU σ z hσ.symm)

/-- Normalized comparison of the splitting-cover Hodge line with its
pullback by an actual Galois coefficient automorphism. -/
lemma galoisLine_exists (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    ∃! a : (Scheme.Modules.pullback (C.galoisAction hL heven σ)).obj C.hodge.line ≅
        C.hodge.line,
      let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
        C.level C.level C.compact C.compact
      CompactCompatible σ.toRingHom B.openMap B.compactMap B.extendsOpen B.hodgeMap
        C.hodge C.hodge a := by
  obtain ⟨ζ, hζ⟩ := cyclotomic_primitiveRoot k L hL
  obtain ⟨A, _⟩ := tate_full_level_marking (CyclotomicField L k) L hL heven ζ hζ
  let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
    C.level C.level C.compact C.compact
  exact compact_comparison_of_tateLevels (CyclotomicField L k) L σ.toRingHom hL heven A A
    C.level C.level B.openMap B.classifies B.hodgeMap B.normalized
    C.compact C.compact B.compactMap B.extendsOpen C.hodge C.hodge C.canonical C.canonical

/-- The orientation required by equivariant module descent. -/
def galoisLine (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    C.hodge.line ≅ (Scheme.Modules.pullback (C.galoisAction hL heven σ)).obj C.hodge.line :=
  (C.galoisLine_exists hL heven σ).choose.symm

lemma galoisLine_normalized (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
      C.level C.level C.compact C.compact
    CompactCompatible σ.toRingHom B.openMap B.compactMap B.extendsOpen B.hodgeMap
      C.hodge C.hodge (C.galoisLine hL heven σ).symm :=
  (C.galoisLine_exists hL heven σ).choose_spec.1

/-- The normalized Galois line comparisons satisfy the full sheaf cocycle
with the original pullback composition and map-equality constraints. -/
lemma galoisLine_mul (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ τ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    C.galoisLine hL heven (σ * τ) =
      C.galoisLine hL heven σ ≪≫
      (Scheme.Modules.pullback (C.galoisAction hL heven σ)).mapIso (C.galoisLine hL heven τ) ≪≫
      (Scheme.Modules.pullbackComp (C.galoisAction hL heven σ)
        (C.galoisAction hL heven τ)).app C.hodge.line ≪≫
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso
        (C.galoisAction_mul hL heven σ τ) C.hodge.line).symm := by
  let l := CyclotomicField L k
  let B := coefficientMap l L σ.toRingHom hL heven C.level C.level C.compact C.compact
  let A := coefficientMap l L τ.toRingHom hL heven C.level C.level C.compact C.compact
  let AB := coefficientComposite l L τ.toRingHom σ.toRingHom hL heven A B
  let P := coefficientMap l L (σ * τ).toRingHom hL heven C.level C.level C.compact C.compact
  let a := (C.galoisLine hL heven τ).symm
  let b := (C.galoisLine hL heven σ).symm
  let ab := ((Scheme.Modules.pullbackComp B.compactMap A.compactMap).app C.hodge.line).symm ≪≫
    (Scheme.Modules.pullback B.compactMap).mapIso a ≪≫ b
  have hab := compactCompatible_composite l L τ.toRingHom σ.toRingHom hL heven
    A B C.hodge C.hodge C.hodge a b
    (C.galoisLine_normalized hL heven τ) (C.galoisLine_normalized hL heven σ)
  have hp := compactCompatible_congr l L (σ * τ).toRingHom hL heven P AB
    (C.galoisAction_mul hL heven σ τ) C.hodge C.hodge ab hab
  have heq := CompactHodgeConstantComparison.compact_comparison_unique
    (σ * τ).toRingHom P.openMap P.compactMap P.extendsOpen P.hodgeMap C.hodge C.hodge
    (C.galoisLine hL heven (σ * τ)).symm
    (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso
      (C.galoisAction_mul hL heven σ τ) C.hodge.line ≪≫ ab)
    (C.galoisLine_normalized hL heven (σ * τ)) hp
  have hi := congrArg Iso.symm heq
  apply Iso.ext
  exact congrArg Iso.hom hi

/-- The identity coefficient automorphism acts by the actual pullback unit. -/
lemma galoisLine_one (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L) :
    C.galoisLine hL heven 1 =
      ((Scheme.Modules.pullbackId C.compact.space).app C.hodge.line).symm ≪≫
        ((Scheme.Modules.pullbackCongr (C.galoisAction_one hL heven)).app C.hodge.line).symm := by
  let l := CyclotomicField L k
  let B := coefficientMap l L (RingHom.id l) hL heven C.level C.level C.compact C.compact
  let P := coefficientIdentity l L hL heven C.level C.compact
  have hp := compactCompatible_congr l L (RingHom.id l) hL heven B P
    (C.galoisAction_one hL heven) C.hodge C.hodge
    ((Scheme.Modules.pullbackId C.compact.space).app C.hodge.line)
    (compactCompatible_identity l L hL heven C.hodge)
  have heq := CompactHodgeConstantComparison.compact_comparison_unique
    (RingHom.id l) B.openMap B.compactMap B.extendsOpen B.hodgeMap C.hodge C.hodge
    (C.galoisLine hL heven 1).symm
    (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso
      (C.galoisAction_one hL heven) C.hodge.line ≪≫
      (Scheme.Modules.pullbackId C.compact.space).app C.hodge.line)
    (C.galoisLine_normalized hL heven 1) hp
  have hi := congrArg Iso.symm heq
  rw [eqIso_congr] at hi
  exact hi

lemma galoisOpen_over (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    (coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
      C.level C.level C.compact C.compact).openMap ≫ C.openMap = C.openMap := by
  let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
    C.level C.level C.compact C.compact
  letI := X.openImmersion
  apply (cancel_mono X.inclusion).mp
  change (B.openMap ≫ C.openMap) ≫ X.inclusion = C.openMap ≫ X.inclusion
  rw [Category.assoc, ← C.extendsOpen.2, ← Category.assoc, ← B.extendsOpen.2,
    Category.assoc]
  change C.compact.inclusion ≫ (C.galoisAction hL heven σ ≫ C.compactMap) = _
  rw [C.galoisAction_over hL heven σ, C.extendsOpen.2]

lemma galoisHodge_over (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
      C.level C.level C.compact C.compact
    (Scheme.Modules.pullback B.openMap).map C.hodgeMap.hom ≫ B.hodgeMap.hom =
      ((Scheme.Modules.pullbackComp B.openMap C.openMap).app (weight D)).hom ≫
        (pullbackEqIso (C.galoisOpen_over hL heven σ) (weight D)).hom ≫ C.hodgeMap.hom := by
  let B := coefficientMap (CyclotomicField L k) L σ.toRingHom hL heven
    C.level C.level C.compact C.compact
  let A : CoefficientMap k L (algebraMap k (CyclotomicField L k)) D C.level X C.compact :=
    ⟨C.openMap, C.compactMap, C.classifies, C.extendsOpen, C.hodgeMap, C.normalized⟩
  let AB := coefficientComposite k L (algebraMap k (CyclotomicField L k)) σ.toRingHom
    hL heven A B
  have hι : σ.toRingHom.comp (algebraMap k (CyclotomicField L k)) =
      algebraMap k (CyclotomicField L k) := by ext a; exact σ.commutes a
  let P : CoefficientMap k L (σ.toRingHom.comp (algebraMap k (CyclotomicField L k)))
      D C.level X C.compact :=
    { openMap := C.openMap
      compactMap := C.compactMap
      classifies := by rw [hι]; exact C.classifies
      extendsOpen := by rw [hι]; exact C.extendsOpen
      hodgeMap := C.hodgeMap
      normalized := by rw [hι]; exact C.normalized }
  have hh := congrArg Iso.hom (coefficientHodge_congr k L _ hL heven AB P
    (C.galoisOpen_over hL heven σ))
  have ht := congrArg (fun t =>
    ((Scheme.Modules.pullbackComp B.openMap C.openMap).app (weight D)).hom ≫ t) hh
  simpa only [AB, coefficientComposite, A, P, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc] using ht


open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.Loc

lemma open_cover_properties (C : SplittingCover k L D X) :
    IsFinite C.openMap ∧ Etale C.openMap ∧ Surjective C.openMap :=
  ⟨MorphismProperty.of_isPullback C.openCartesian C.finite,
    MorphismProperty.of_isPullback C.openCartesian C.etale,
    MorphismProperty.of_isPullback C.openCartesian C.surjective⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma galoisOpen_split (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    {Z : Scheme.{0}} (f g : Z ⟶ OpenBase (CyclotomicField L k) L C.level)
    (hfg : f ≫ C.openMap = g ≫ C.openMap) :
    ∃ U : (CyclotomicField L k ≃ₐ[k] CyclotomicField L k) → Z.Opens,
      (⨆ s, U s) = ⊤ ∧ ∀ s, (U s).ι ≫ g = (U s).ι ≫ f ≫
        (coefficientMap (CyclotomicField L k) L s.toRingHom hL heven
          C.level C.level C.compact C.compact).openMap := by
  letI := C.compact.openImmersion
  have hf : (f ≫ C.compact.inclusion) ≫ C.compactMap =
      (g ≫ C.compact.inclusion) ≫ C.compactMap := by
    simp only [Category.assoc, C.extendsOpen.2]
    exact congrArg (fun t => t ≫ X.inclusion) hfg
  obtain ⟨U, hU, heq⟩ := C.galoisAction_split hL heven
    (f ≫ C.compact.inclusion) (g ≫ C.compact.inclusion) hf
  refine ⟨U, hU, ?_⟩
  intro s
  let B := coefficientMap (CyclotomicField L k) L s.toRingHom hL heven
    C.level C.level C.compact C.compact
  apply (cancel_mono C.compact.inclusion).mp
  simp only [Category.assoc]
  rw [← B.extendsOpen.2]
  have hb : B.compactMap = C.galoisAction hL heven s := rfl
  rw [hb]
  simpa only [Category.assoc] using heq s


/-- An actual descended invertible module together with its equivariant
comparison to the splitting-cover canonical lattice. The open identification
is a further construction, not a field of this intermediate record. -/
structure DescendedLine (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L) where
  line : X.space.Modules
  invertible : Scheme.Modules.IsInvertible line
  comparison : (Scheme.Modules.pullback C.compactMap).obj line ≅ C.hodge.line
  equivariant : ∀ (σ : CyclotomicField L k ≃ₐ[k] CyclotomicField L k)
    {Z : Scheme.{0}} (f g : Z ⟶ C.compact.space)
    (hf : f ≫ C.compactMap = g ≫ C.compactMap)
    (hfg : f ≫ C.galoisAction hL heven σ = g),
    ((GaloisDescent.MF.toDescentData (fun _ : Unit => C.compactMap)).obj line).hom
        (g ≫ C.compactMap) (i₁ := ()) (i₂ := ()) f g hf rfl ≫
      (Scheme.Modules.pullback g).map comparison.hom =
        (Scheme.Modules.pullback f).map comparison.hom ≫
          loc C.hodge.line f g (C.galoisAction hL heven σ) (C.galoisLine hL heven σ) hfg

lemma galoisLine_add (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (g h : Additive (CyclotomicField L k ≃ₐ[k] CyclotomicField L k)) :
    C.galoisLine hL heven (g + h).toMul =
      C.galoisLine hL heven g.toMul ≪≫
        (Scheme.Modules.pullback (C.galoisAction hL heven g.toMul)).mapIso
          (C.galoisLine hL heven h.toMul) ≪≫
        (Scheme.Modules.pullbackComp (C.galoisAction hL heven g.toMul)
          (C.galoisAction hL heven h.toMul)).app C.hodge.line ≪≫
        ((Scheme.Modules.pullbackCongr (C.galoisAction_mul hL heven g.toMul h.toMul)).app
          C.hodge.line).symm := by
  have hm := C.galoisLine_mul hL heven g.toMul h.toMul
  rw [eqIso_congr] at hm
  exact hm

/-- Effective fpqc descent of the canonical cyclotomic Hodge line, retaining
all test-scheme transition equations. -/
lemma descendedLine_exists (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L) :
    Nonempty (DescendedLine C hL heven) := by
  letI := C.finite
  letI := C.etale
  letI := C.surjective
  let G := Additive (CyclotomicField L k ≃ₐ[k] CyclotomicField L k)
  let σ : G → (C.compact.space ⟶ C.compact.space) := fun g => C.galoisAction hL heven g.toMul
  let ψ : ∀ g : G, C.hodge.line ≅ (Scheme.Modules.pullback (σ g)).obj C.hodge.line :=
    fun g => C.galoisLine hL heven g.toMul
  have hmul : ∀ g h : G, ψ (g + h) = ψ g ≪≫
      (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
      (Scheme.Modules.pullbackComp (σ g) (σ h)).app C.hodge.line ≪≫
      ((Scheme.Modules.pullbackCongr (C.galoisAction_mul hL heven g.toMul h.toMul)).app
        C.hodge.line).symm := by
    intro g h
    exact C.galoisLine_add hL heven g h
  obtain ⟨N, hN, a, ha⟩ := GaloisDescent.effective_line C.compactMap G σ
    (C.galoisAction_one hL heven) (fun g h => C.galoisAction_mul hL heven g.toMul h.toMul)
    (fun {_} v g => C.galoisAction_free hL heven v g.toMul)
    (fun {_} f g hfg => C.galoisAction_split hL heven f g hfg)
    C.hodge.line ψ hmul C.hodge.invertible
  exact ⟨⟨N, hN, a, fun g => ha (Additive.ofMul g)⟩⟩


/-- The normalized comparison on the inverse image of the original open
curve, constructed from the descended compact line comparison. -/
def DescendedLine.openComparison (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (N : DescendedLine C hL heven) :
    (Scheme.Modules.pullback C.openMap).obj ((Scheme.Modules.pullback X.inclusion).obj N.line) ≅
      (Scheme.Modules.pullback C.openMap).obj (openHodge k L D) :=
  (squarePullbackIso C.compact.inclusion C.compactMap C.openMap X.inclusion
    C.extendsOpen.2 N.line).symm ≪≫
    (Scheme.Modules.pullback C.compact.inclusion).mapIso N.comparison ≪≫
      C.hodge.onOpen ≪≫ C.hodgeMap.symm

/-- A descended normalized open comparison produces an actual Hodge
extension, with the compact comparison retaining its normalization. -/
lemma DescendedLine.extension_of_open_descent (C : SplittingCover k L D X)
    (hL : 3 ≤ L) (heven : Even L) (N : DescendedLine C hL heven)
    (b : (Scheme.Modules.pullback X.inclusion).obj N.line ≅ openHodge k L D)
    (hb : (Scheme.Modules.pullback C.openMap).mapIso b = N.openComparison C hL heven) :
    ∃ H : Extension k L D X, ∃ a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ C.hodge.line,
      CompactCompatible (algebraMap k (CyclotomicField L k)) C.openMap C.compactMap
        C.extendsOpen C.hodgeMap H C.hodge a := by
  let H : Extension k L D X := ⟨N.line, N.invertible, b⟩
  refine ⟨H, N.comparison, ?_⟩
  have h := congrArg Iso.hom hb
  simp only [Functor.mapIso_hom, DescendedLine.openComparison, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] at h
  have hh := congrArg (fun t =>
    (squarePullbackIso C.compact.inclusion C.compactMap C.openMap X.inclusion
      C.extendsOpen.2 N.line).hom ≫ t ≫ C.hodgeMap.hom) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at hh
  simpa only [CompactCompatible, H, squarePullbackIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc] using hh.symm


end SplittingCover

/-- A normalized comparison with the finite cyclotomic canonical lattice
implies the full geometric predicate over every algebraically closed target. -/
lemma geometric_of_split_comparison (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (C : SplittingCover k L D X) (H : Extension k L D X)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ C.hodge.line)
    (ha : CompactCompatible (algebraMap k (CyclotomicField L k)) C.openMap C.compactMap
      C.extendsOpen C.hodgeMap H C.hodge a) : GeometricallyCanonical H := by
  intro l _ _ _ ι E Y f F hf hF e he J hJ
  letI : Algebra k l := ι.toAlgebra
  letI : FiniteDimensional k (CyclotomicField L k) := by
    dsimp [CyclotomicField]; infer_instance
  let κa : CyclotomicField L k →ₐ[k] l := IsAlgClosed.lift
  let κ : CyclotomicField L k →+* l := κa.toRingHom
  have hκι : κ.comp (algebraMap k (CyclotomicField L k)) = ι := by
    ext x
    exact κa.commutes x
  let A : CoefficientMap k L (algebraMap k (CyclotomicField L k)) D C.level X C.compact :=
    ⟨C.openMap, C.compactMap, C.classifies, C.extendsOpen, C.hodgeMap, C.normalized⟩
  let B := coefficientMap (CyclotomicField L k) L κ hL heven C.level E C.compact Y
  obtain ⟨b, hb, _⟩ := C.geometric l κ E Y B.openMap B.compactMap
    B.classifies B.extendsOpen B.hodgeMap B.normalized J hJ
  let AB := coefficientComposite k L (algebraMap k (CyclotomicField L k)) κ hL heven A B
  let P : CoefficientMap k L (κ.comp (algebraMap k (CyclotomicField L k))) D E X Y :=
    { openMap := f
      compactMap := F
      classifies := by rw [hκι]; exact hf
      extendsOpen := by rw [hκι]; exact hF
      hodgeMap := e
      normalized := by rw [hκι]; exact he }
  have hp : P.compactMap = AB.compactMap :=
    coefficient_compact_unique k L _ hL heven P AB
  let ab := ((Scheme.Modules.pullbackComp B.compactMap A.compactMap).app H.line).symm ≪≫
    (Scheme.Modules.pullback B.compactMap).mapIso a ≪≫ b
  have hab := compactCompatible_composite k L (algebraMap k (CyclotomicField L k)) κ
    hL heven A B H C.hodge J a b ha hb
  have hz := compactCompatible_congr k L _ hL heven P AB hp H J ab hab
  let z := ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso hp H.line ≪≫ ab
  have hz' : CompactCompatible ι f F hF e H J z := hz
  refine ⟨z, hz', ?_⟩
  intro z' hz''
  exact CompactHodgeConstantComparison.compact_comparison_unique ι f F hF e H J z' z hz'' hz'


/-- Once a geometrically canonical extension is constructed, the simultaneous
existence assertion also satisfies the native disk condition. If a native test
exists it supplies a full Tate marking; otherwise that condition is vacuous. -/
lemma canonical_geometric_of_geometric_exists (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (h : ∃ H : Extension k L D X, GeometricallyCanonical H) :
    ∃ H : Extension k L D X, Canonical k L H ∧ GeometricallyCanonical H := by
  classical
  by_cases hA : Nonempty (TateLevel k L)
  · obtain ⟨A⟩ := hA
    obtain ⟨H, hH⟩ := native_canonical_exists k L hL heven D X
    exact ⟨H, hH, geometric_of_tateLevel k L hL heven A H hH⟩
  · obtain ⟨H, hH⟩ := h
    exact ⟨H, fun T => (hA ⟨T.level⟩).elim, hH⟩


/-- The remaining normalized open-descent equation suffices for the full
simultaneous existence conclusion, without a restriction on the base field. -/
lemma exists_of_descended_open (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (C : SplittingCover k L D X) (N : SplittingCover.DescendedLine C hL heven)
    (b : (Scheme.Modules.pullback X.inclusion).obj N.line ≅ openHodge k L D)
    (hb : (Scheme.Modules.pullback C.openMap).mapIso b =
      SplittingCover.DescendedLine.openComparison C hL heven N) :
    ∃ H : Extension k L D X, Canonical k L H ∧ GeometricallyCanonical H := by
  obtain ⟨H, a, ha⟩ := SplittingCover.DescendedLine.extension_of_open_descent C hL heven N b hb
  exact canonical_geometric_of_geometric_exists k L hL heven
    ⟨H, geometric_of_split_comparison k L hL heven C H a ha⟩

#print axioms exists_of_descended_open
#print axioms canonical_geometric_of_geometric_exists
#print axioms SplittingCover.galoisOpen_split
#print axioms SplittingCover.DescendedLine.extension_of_open_descent
#print axioms SplittingCover.galoisHodge_over
#print axioms geometric_of_split_comparison
#print axioms SplittingCover.descendedLine_exists
#print axioms SplittingCover.galoisLine_one
#print axioms SplittingCover.galoisLine_mul
#print axioms SplittingCover.galoisAction_split
#print axioms SplittingCover.galoisAction_residue
#print axioms SplittingCover.galoisLine_exists
#print axioms SplittingCover.galoisLine_normalized
#print axioms SplittingCover.galoisAction_over
#print axioms SplittingCover.galoisAction_free

#print axioms coefficientAut_one
#print axioms coefficientAut_mul
#print axioms coefficientAut_isIso

#print axioms splittingCover_exists

#print axioms cyclotomic_finite
#print axioms cyclotomic_primitiveRoot
#print axioms cyclotomic_geometric_exists
#print axioms cyclotomic_cover_properties

#print axioms pullback_canonical_of_tateLevel
#print axioms compact_comparison_of_tateLevels
#print axioms comparison_local_lifts_of_tateLevel
#print axioms canonical_comparison_of_tateLevel
#print axioms diskMap_closedPoint
#print axioms tests_cover_of_tateLevel
#print axioms tests_descend_of_tateLevel
#print axioms geometric_of_tateLevel
#print axioms exists_of_primitiveRoot

#print axioms canonical_of_open_iso
#print axioms canonical_iff_open_iso
#print axioms geometric_iff_pullback_canonical

#print axioms normalize_tested_centers
#print axioms native_canonical_exists
#print axioms geometric_of_algClosed

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent


namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback.LDescDatumAux
namespace CanonicalDatum
abbrev MF := (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁
lemma mapComp_hom {X Y Z : Scheme.{0}} (q : X ⟶ Y) (f : Z ⟶ X) (p : Z ⟶ Y)
    (h : f ≫ q = p) (hh : q.op.toLoc ≫ f.op.toLoc = p.op.toLoc) (M : Y.Modules) :
    (MF.mapComp' q.op.toLoc f.op.toLoc p.op.toLoc hh).hom.toNatTrans.app M =
      (Scheme.Modules.pullbackCongr h).inv.app M ≫ (Scheme.Modules.pullbackComp f q).inv.app M := by
  subst p
  simp only [Pseudofunctor.mapComp', Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
    eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.comp_app]
  rw [cat_eqToHom_app]
  rfl
lemma mapComp_inv {X Y Z : Scheme.{0}} (q : X ⟶ Y) (f : Z ⟶ X) (p : Z ⟶ Y)
    (h : f ≫ q = p) (hh : q.op.toLoc ≫ f.op.toLoc = p.op.toLoc) (M : Y.Modules) :
    (MF.mapComp' q.op.toLoc f.op.toLoc p.op.toLoc hh).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp f q).hom.app M ≫ (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst p
  simp only [Pseudofunctor.mapComp', Iso.trans_inv, PrelaxFunctor.map₂Iso_inv,
    eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.comp_app]
  rw [cat_eqToHom_app]
  rfl
lemma canonical_transition {X Y Z : Scheme.{0}} (q : X ⟶ Y) (M : Y.Modules)
    (p : Z ⟶ Y) (f g : Z ⟶ X) (hf : f ≫ q = p) (hg : g ≫ q = p) :
    ((MF.toDescentData (fun _ : Unit => q)).obj M).hom p (i₁ := ()) (i₂ := ()) f g hf hg =
      (Scheme.Modules.pullbackComp f q).hom.app M ≫ (Scheme.Modules.pullbackCongr hf).hom.app M ≫
        (Scheme.Modules.pullbackCongr hg).inv.app M ≫ (Scheme.Modules.pullbackComp g q).inv.app M := by
  change (MF.mapComp' q.op.toLoc f.op.toLoc p.op.toLoc _).inv.toNatTrans.app M ≫
    (MF.mapComp' q.op.toLoc g.op.toLoc p.op.toLoc _).hom.toNatTrans.app M = _
  rw [mapComp_inv q f p hf, mapComp_hom q g p hg]
  simp only [Category.assoc]

lemma canonical_action {X Y : Scheme.{0}} (q : X ⟶ Y) (M : Y.Modules)
    (T : X ⟶ X) (hT : T ≫ q = q) :
    ((MF.toDescentData (fun _ : Unit => q)).obj M).hom q (i₁ := ()) (i₂ := ())
        (𝟙 X) T (Category.id_comp q) hT =
      ((Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback q).obj M)).hom ≫
        (Scheme.Modules.pullbackCongr hT).inv.app M ≫ (Scheme.Modules.pullbackComp T q).inv.app M := by
  rw [canonical_transition]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp (𝟙 X) q).hom.app M)]
  rw [ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_id]
  rfl

#print axioms canonical_action
#print axioms canonical_transition
end CanonicalDatum

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent


namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryConstantsR0235.CompactHodgeConstantComparison
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
namespace ActionCoherence

def action {X Y : Scheme.{0}} (q : X ⟶ Y) (t : X ⟶ X) (ht : t ≫ q = q) (M : Y.Modules) :
    (Scheme.Modules.pullback q).obj M ≅
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback q).obj M) :=
  ((Scheme.Modules.pullbackComp t q).app M ≪≫ pullbackEqIso ht M).symm

lemma square_congr {A B C D : Scheme.{0}} (j : A ⟶ B) (i : C ⟶ D)
    {F F' : B ⟶ D} {q q' : A ⟶ C} (hF : F = F') (hq : q = q')
    (h : j ≫ F = q ≫ i) (h' : j ≫ F' = q' ≫ i) (M : D.Modules) :
    (Scheme.Modules.pullback j).map (pullbackEqIso hF M).hom ≫
      (squarePullbackIso j F' q' i h' M).hom =
    (squarePullbackIso j F q i h M).hom ≫
      (pullbackEqIso hq ((Scheme.Modules.pullback i).obj M)).hom := by
  subst F'; subst q'
  simp [pullbackEqIso]

lemma square_action {A B C D : Scheme.{0}} (j : A ⟶ B) (i : C ⟶ D)
    (F : B ⟶ D) (q : A ⟶ C) (h : j ≫ F = q ≫ i)
    (t : B ⟶ B) (u : A ⟶ A) (ht : t ≫ F = F) (hu : u ≫ q = q)
    (hs : j ≫ t = u ≫ j) (M : D.Modules) :
    (Scheme.Modules.pullback j).map (action F t ht M).hom ≫
      (squarePullbackIso j t u j hs ((Scheme.Modules.pullback F).obj M)).hom ≫
      (Scheme.Modules.pullback u).map (squarePullbackIso j F q i h M).hom =
    (squarePullbackIso j F q i h M).hom ≫
      (action q u hu ((Scheme.Modules.pullback i).obj M)).hom := by
  have hbig : j ≫ (t ≫ F) = (u ≫ q) ≫ i := by rw [ht, hu]; exact h
  have hhor := square_horizontal j t F u j q i hs h hbig M
  have hc := square_congr j i ht hu hbig h M
  apply (cancel_epi ((Scheme.Modules.pullback j).map (action F t ht M).inv)).mp
  apply (cancel_mono (action q u hu ((Scheme.Modules.pullback i).obj M)).inv).mp
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [action, Iso.symm_inv, Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc ((Scheme.Modules.pullback j).map
    ((Scheme.Modules.pullbackComp t F).app M).hom), hhor]
  simp only [Category.assoc]

section Equivariant
variable {V : Type*} [Category V] (P : V ⥤ V)
def Equivariant {M N : V} (a : M ≅ N) (ψ : M ≅ P.obj M) (χ : N ≅ P.obj N) : Prop :=
  a.hom ≫ χ.hom = ψ.hom ≫ P.map a.hom
lemma equivariant_symm {M N : V} (a : M ≅ N) (ψ : M ≅ P.obj M) (χ : N ≅ P.obj N)
    (h : Equivariant P a ψ χ) : Equivariant P a.symm χ ψ := by
  change a.inv ≫ ψ.hom = χ.hom ≫ P.map a.inv
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, a.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, ← P.map_comp, a.hom_inv_id, P.map_id, Category.comp_id]
lemma equivariant_trans {M N K : V} (a : M ≅ N) (b : N ≅ K)
    (ψ : M ≅ P.obj M) (χ : N ≅ P.obj N) (ω : K ≅ P.obj K)
    (ha : Equivariant P a ψ χ) (hb : Equivariant P b χ ω) :
    Equivariant P (a ≪≫ b) ψ ω := by
  change (a.hom ≫ b.hom) ≫ ω.hom = ψ.hom ≫ P.map (a.hom ≫ b.hom)
  rw [Category.assoc, hb, ← Category.assoc, ha, P.map_comp, Category.assoc]
end Equivariant

lemma restrict_equivariant {A B : Scheme.{0}} (j : A ⟶ B)
    (t : B ⟶ B) (u : A ⟶ A) (h : j ≫ t = u ≫ j)
    (M N : B.Modules) (a : M ≅ N)
    (ψ : M ≅ (Scheme.Modules.pullback t).obj M)
    (χ : N ≅ (Scheme.Modules.pullback t).obj N)
    (ha : Equivariant (Scheme.Modules.pullback t) a ψ χ) :
    Equivariant (Scheme.Modules.pullback u) ((Scheme.Modules.pullback j).mapIso a)
      ((Scheme.Modules.pullback j).mapIso ψ ≪≫ squarePullbackIso j t u j h M)
      ((Scheme.Modules.pullback j).mapIso χ ≪≫ squarePullbackIso j t u j h N) := by
  change (Scheme.Modules.pullback j).map a.hom ≫
    ((Scheme.Modules.pullback j).map χ.hom ≫ (squarePullbackIso j t u j h N).hom) =
    ((Scheme.Modules.pullback j).map ψ.hom ≫ (squarePullbackIso j t u j h M).hom) ≫
      (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback j).map a.hom)
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp]
  simp only [Category.assoc]
  rw [squarePullbackIso_naturality]


#print axioms square_action
end ActionCoherence

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent


namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open ActionCoherence
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.Loc
namespace CanonicalDescent
lemma hom_congr {X Y Z : Scheme.{0}} (q : X ⟶ Y)
    (D : GaloisDescent.MF.DescentData (fun _ : Unit => q))
    (p p' : Z ⟶ Y) (h : p = p') (f g : Z ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ q = p) (hf' : f ≫ q = p') (hg' : g ≫ q = p') :
    D.hom p (i₁ := ()) (i₂ := ()) f g hf hg = D.hom p' f g hf' hg' := by
  subst p'
  rfl

lemma canonical_loc {X Y Z : Scheme.{0}} (q : X ⟶ Y) (M : Y.Modules)
    (t : X ⟶ X) (ht : t ≫ q = q) (p : Z ⟶ Y) (f g : Z ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ q = p) (hfg : f ≫ t = g) :
    ((GaloisDescent.MF.toDescentData (fun _ : Unit => q)).obj M).hom p (i₁ := ()) (i₂ := ()) f g hf hg =
      loc ((Scheme.Modules.pullback q).obj M) f g t (action q t ht M) hfg := by
  let D := ((GaloisDescent.MF.toDescentData (fun _ : Unit => q)).obj M)
  have hψ : D.hom q (i₁ := ()) (i₂ := ()) (𝟙 X) t (Category.id_comp q) ht =
      ((Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback q).obj M)).hom ≫
        (action q t ht M).hom := by
    simpa only [action, Iso.symm_hom, Iso.trans_inv, eqIso_congr, Iso.app_inv,
      Category.assoc] using CanonicalDatum.canonical_action q M t ht
  have hd := GaloisMorphisms.datum_transition q t ht D (action q t ht M) hψ f g hfg
  rw [hom_congr q _ p (f ≫ q) hf.symm f g hf hg rfl (hg.trans hf.symm)]
  exact hd

lemma iso_descend {X Y : Scheme.{0}} (q : X ⟶ Y)
    [QuasiCompact q] [Flat q] [Surjective q] (G : Type) (σ : G → (X ⟶ X))
    (hσ : ∀ s, σ s ≫ q = q)
    (hsplit : ∀ ⦃Z : Scheme.{0}⦄ (f g : Z ⟶ X), f ≫ q = g ≫ q →
      ∃ U : G → Z.Opens, ⨆ a, U a = ⊤ ∧ ∀ a, (U a).ι ≫ g = (U a).ι ≫ f ≫ σ a)
    (M N : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj N)
    (ha : ∀ s, Equivariant (Scheme.Modules.pullback (σ s)) a
      (action q (σ s) (hσ s) M) (action q (σ s) (hσ s) N)) :
    ∃ b : M ≅ N, (Scheme.Modules.pullback q).mapIso b = a := by
  apply GaloisMorphisms.iso_of_split q G σ hsplit M N hM hN a
  intro s Z p f g hf hg hfg
  rw [canonical_loc q N (σ s) (hσ s) p f g hf hg hfg,
    canonical_loc q M (σ s) (hσ s) p f g hf hg hfg]
  exact GaloisMorphisms.loc_natural f g (σ s) hfg _ _ _ _ a.hom (ha s)
#print axioms iso_descend
end CanonicalDescent

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent


namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryConstantsR0235.CompactHodgeConstantComparison
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.Loc
open ActionCoherence
namespace OpenAction
lemma datum_hom_congr {X Y Z : Scheme.{0}} (q : X ⟶ Y)
    (D : GaloisDescent.MF.DescentData (fun _ : Unit => q))
    (p p' : Z ⟶ Y) (h : p = p') (f g : Z ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ q = p) (hf' : f ≫ q = p') (hg' : g ≫ q = p') :
    D.hom p (i₁ := ()) (i₂ := ()) f g hf hg = D.hom p' f g hf' hg' := by
  subst p'
  rfl

lemma loc_identity {X : Scheme.{0}} (M : X.Modules) (t : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback t).obj M) :
    loc M (𝟙 X) t t ψ (Category.id_comp t) =
      ((Scheme.Modules.pullbackId X).app M).hom ≫ ψ.hom := by
  simp only [loc]
  rw [ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_id]
  exact (Scheme.Modules.pullbackId X).hom.naturality ψ.hom

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaLevelConstantsR0234
variable {k : Type} [Field k] [CharZero k] {L : ℕ} {D : LevelData k L}
  {X : Compactification k L D}

set_option backward.isDefEq.respectTransparency.types false in
lemma compact_equivariant (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (N : SplittingCover.DescendedLine C hL heven)
    (s : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    Equivariant (Scheme.Modules.pullback (C.galoisAction hL heven s)) N.comparison
      (action C.compactMap (C.galoisAction hL heven s) (C.galoisAction_over hL heven s) N.line)
      (C.galoisLine hL heven s) := by
  let t := C.galoisAction hL heven s
  have ht : t ≫ C.compactMap = C.compactMap := C.galoisAction_over hL heven s
  have hn := N.equivariant s (𝟙 C.compact.space) t
    ((Category.id_comp _).trans ht.symm) (Category.id_comp t)
  rw [datum_hom_congr C.compactMap _ (t ≫ C.compactMap) C.compactMap ht
    (𝟙 C.compact.space) t _ _ (Category.id_comp _) ht] at hn
  rw [CanonicalDatum.canonical_action, loc_identity] at hn
  simp only [Iso.app_hom] at hn
  erw [← Category.assoc ((Scheme.Modules.pullback (𝟙 C.compact.space)).map N.comparison.hom),
    (Scheme.Modules.pullbackId C.compact.space).hom.naturality N.comparison.hom] at hn
  simp only [Functor.id_map, Category.assoc] at hn
  have hh := (cancel_epi ((Scheme.Modules.pullbackId C.compact.space).hom.app
    ((Scheme.Modules.pullback C.compactMap).obj N.line))).mp hn
  simpa only [Equivariant, action, Iso.symm_hom, Iso.trans_inv, eqIso_congr, Iso.app_inv,
    Category.assoc] using hh.symm

set_option backward.isDefEq.respectTransparency.types false in
lemma open_equivariant (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (N : SplittingCover.DescendedLine C hL heven)
    (s : CyclotomicField L k ≃ₐ[k] CyclotomicField L k) :
    let B := coefficientMap (CyclotomicField L k) L s.toRingHom hL heven
      C.level C.level C.compact C.compact
    Equivariant (Scheme.Modules.pullback B.openMap) (N.openComparison C hL heven)
      (action C.openMap B.openMap (C.galoisOpen_over hL heven s)
        ((Scheme.Modules.pullback X.inclusion).obj N.line))
      (action C.openMap B.openMap (C.galoisOpen_over hL heven s) (openHodge k L D)) := by
  let B := coefficientMap (CyclotomicField L k) L s.toRingHom hL heven
    C.level C.level C.compact C.compact
  let t := C.galoisAction hL heven s
  let u := B.openMap
  let j := C.compact.inclusion
  let P := Scheme.Modules.pullback u
  let S := squarePullbackIso j C.compactMap C.openMap X.inclusion C.extendsOpen.2 N.line
  let ψ := C.galoisLine hL heven s
  let R := fun M => squarePullbackIso j t u j B.extendsOpen.2 M
  let a₀ := action C.compactMap t (C.galoisAction_over hL heven s) N.line
  let a₁ := (Scheme.Modules.pullback j).mapIso a₀ ≪≫ R ((Scheme.Modules.pullback C.compactMap).obj N.line)
  let a₂ := (Scheme.Modules.pullback j).mapIso ψ ≪≫ R C.hodge.line
  let a₃ := B.hodgeMap.symm
  let a₄ := action C.openMap u (C.galoisOpen_over hL heven s) (openHodge k L D)
  let a₅ := action C.openMap u (C.galoisOpen_over hL heven s)
    ((Scheme.Modules.pullback X.inclusion).obj N.line)
  have hS : Equivariant P S a₁ a₅ := by
    exact (square_action j X.inclusion C.compactMap C.openMap C.extendsOpen.2 t u
      (C.galoisAction_over hL heven s) (C.galoisOpen_over hL heven s)
      B.extendsOpen.2 N.line).symm
  have hα : Equivariant P ((Scheme.Modules.pullback j).mapIso N.comparison) a₁ a₂ :=
    restrict_equivariant j t u B.extendsOpen.2 _ _ N.comparison a₀ ψ
      (compact_equivariant C hL heven N s)
  have hβ : Equivariant P C.hodge.onOpen a₂ a₃ := by
    have hn := C.galoisLine_normalized hL heven s
    change (Scheme.Modules.pullback j).map ψ.inv ≫ C.hodge.onOpen.hom =
      (R C.hodge.line).hom ≫ P.map C.hodge.onOpen.hom ≫ B.hodgeMap.hom at hn
    change C.hodge.onOpen.hom ≫ B.hodgeMap.inv =
      ((Scheme.Modules.pullback j).map ψ.hom ≫ (R C.hodge.line).hom) ≫ P.map C.hodge.onOpen.hom
    apply (cancel_epi ((Scheme.Modules.pullback j).map ψ.inv)).mp
    apply (cancel_mono B.hodgeMap.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact hn
  have he : Equivariant P C.hodgeMap a₄ a₃ := by
    have hh := C.galoisHodge_over hL heven s
    change C.hodgeMap.hom ≫ B.hodgeMap.inv = a₄.hom ≫ P.map C.hodgeMap.hom
    apply (cancel_epi a₄.inv).mp
    apply (cancel_mono B.hodgeMap.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact hh.symm
  exact equivariant_trans P
    (S.symm ≪≫ (Scheme.Modules.pullback j).mapIso N.comparison ≪≫ C.hodge.onOpen)
    C.hodgeMap.symm a₅ a₃ a₄
    (equivariant_trans P (S.symm ≪≫ (Scheme.Modules.pullback j).mapIso N.comparison)
      C.hodge.onOpen a₅ a₂ a₃
      (equivariant_trans P S.symm ((Scheme.Modules.pullback j).mapIso N.comparison)
        a₅ a₁ a₂ (equivariant_symm P S a₁ a₅ hS) hα) hβ)
    (equivariant_symm P C.hodgeMap a₄ a₃ he)

#print axioms open_equivariant
#print axioms compact_equivariant
end OpenAction

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent


namespace ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
namespace FinalAssembly
variable {k : Type} [Field k] [CharZero k] {L : ℕ} {D : LevelData k L}
  {X : Compactification k L D}
lemma openComparison_descends (C : SplittingCover k L D X) (hL : 3 ≤ L) (heven : Even L)
    (N : SplittingCover.DescendedLine C hL heven) :
    ∃ b : (Scheme.Modules.pullback X.inclusion).obj N.line ≅ openHodge k L D,
      (Scheme.Modules.pullback C.openMap).mapIso b = N.openComparison C hL heven := by
  obtain ⟨hfin, het, hsur⟩ := C.open_cover_properties
  letI := hfin
  letI := het
  letI := hsur
  let G := CyclotomicField L k ≃ₐ[k] CyclotomicField L k
  let σ : G → (OpenBase (CyclotomicField L k) L C.level ⟶ OpenBase (CyclotomicField L k) L C.level) :=
    fun s => (coefficientMap (CyclotomicField L k) L s.toRingHom hL heven
      C.level C.level C.compact C.compact).openMap
  exact CanonicalDescent.iso_descend C.openMap G σ
    (C.galoisOpen_over hL heven) (fun {_} f g hfg => C.galoisOpen_split hL heven f g hfg)
    ((Scheme.Modules.pullback X.inclusion).obj N.line) (openHodge k L D)
    (N.invertible.pullback X.inclusion) (openHodge_invertible k L D)
    (N.openComparison C hL heven) (OpenAction.open_equivariant C hL heven N)

lemma final_exists (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    ∃ H : Extension k L D X, Canonical k L H ∧ ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H := by
  obtain ⟨C⟩ := splittingCover_exists k L hL heven D X
  obtain ⟨N⟩ := C.descendedLine_exists hL heven
  obtain ⟨b, hb⟩ := openComparison_descends C hL heven N
  exact exists_of_descended_open k L hL heven C N b hb
#print axioms final_exists
end FinalAssembly

end ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent

namespace ArithmeticThetaBoundaryConstantsR0235
/-- The normalized canonical compact Hodge extension exists over every
characteristic-zero coefficient field, on all components, and compares uniquely
after every algebraically closed coefficient embedding. -/
theorem geometric_canonical_hodge_descent :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
      (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D),
    ∃ H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X,
      ArithmeticThetaBoundaryHodgeR0182.Canonical k L H ∧
      ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H := by
  intro k _ _ L hL heven D X
  exact GeometricCanonicalHodgeDescent.FinalAssembly.final_exists k L hL heven D X

#print axioms geometric_canonical_hodge_descent
end ArithmeticThetaBoundaryConstantsR0235
