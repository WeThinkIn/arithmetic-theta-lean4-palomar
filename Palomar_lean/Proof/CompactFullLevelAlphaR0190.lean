module

public import OpenFullLevelAlphaR0190
public import FourTorsionTateBehaviorR0190
public import CompactNormalizedPowerExtensionR0183

@[expose] public section

/-! The compact extension of the intrinsic four-torsion Hodge section. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaGlobalFourTorsionR0190.CompactFullLevelAlpha
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open GlobalFamilyDiscriminantR0180
variable (k : Type) [Field k] [CharZero k] (L : ℕ)

/-- The boundary and relative constructions use the identical pointed
Cartesian differential comparison. -/
lemma open_comparison_eq {D : LevelData k L}
    (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    openComparison L k D (LaurentSeries k) (TateCurve k L) T.level.law
      T.level.marking T.base T.map T.classifies = openTestIso k L T := by
  rfl

lemma pull_open_eq {D : LevelData k L}
    (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D) (a : Γ(openHodge k L D, ⊤)) :
    pullOpenAlpha L k D (LaurentSeries k) (TateCurve k L) T.level.law
      T.level.marking T.base T.map T.classifies a =
    transportSection T.base _ _ (openTestIso k L T) a := by
  simp only [pullOpenAlpha, open_comparison_eq, pullbackGlobalSection,
    transportSection, Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top, res_refl]

lemma open_tate_behavior (hL : 0 < L) (h4 : 4 ∣ L) {D : LevelData k L}
    (a : Γ(openHodge k L D, ⊤)) (ha : IsOpenAlpha L k D a)
    (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧
      transportSection T.base _ _ (openTestIso k L T) a =
        scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.X^j * (v : PowerSeries k))) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential) ∧
    (∀ ζ : k, IsPrimitiveRoot ζ L → CanonicalMarking k L ζ T.level →
      transportSection T.base _ _ (openTestIso k L T) a =
        scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k)
          (thetaAt k L ^ 2)) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential) := by
  letI := T.level.elliptic
  have hr := ha.2 (LaurentSeries k) (TateCurve k L) T.level.law T.level.originLaw
    T.level.marking T.base T.map T.classifies
  rw [pull_open_eq] at hr
  exact four_torsion_tate_behavior k L hL h4 T.level T.differential T.normalized _ hr

lemma transport_local_scalar {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    (M : Y.Modules) (N : Z.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (d : Γ(M, ⊤)) (U : Y.Opens) (s : Γ(M, U)) (r : Γ(Y, U))
    (hr : res M le_top d = r • s) (h : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ U) :
    transportSection p M N e d = p.appLE U ⊤ h r •
      res N h (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s)) := by
  have ht := transportSection_restrict p M N e d U ⊤ h
  rw [res_refl, hr, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul, InitialHodgeSection.res_smul] at ht
  exact ht

/-- Integrality in the canonical generator implies integrality in every
ambient frame; its transition coefficient is a power-series unit. -/
lemma local_scalar_integral
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (d : Γ(openHodge k L D, ⊤))
    (hd : ∃ f : PowerSeries k, transportSection T.base _ _ (openTestIso k L T.toTest) d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openHodge k L D) le_top d =
      r • H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e))
    (h : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    ∃ b : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) b =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ h r) := by
  let hdisk := (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  let η := res ((Scheme.Modules.pullback T.disk).obj H.line) hdisk
    (Scheme.Modules.pullbackLocalSection T.disk e)
  have hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η :=
    frame_restrict _ _ _ (pullback_frame _ _ _ he)
  obtain ⟨a, ha, _⟩ := disk_coefficient_exists k L H T η hη
  obtain ⟨u, hu⟩ := (extendsGenerator_iff_coefficient_unit k L H T η hη a ha).mp (hH T).exists
  obtain ⟨f, hf⟩ := hd
  rw [← ha, smul_smul] at hf
  have hf' : transportSection T.base _ _ (openTestIso k L T.toTest) d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k)
        (f * (u : PowerSeries k))) • diskRestriction k L H T η := by
    simpa only [map_mul, hu, scalar] using hf
  have ht := transport_local_scalar T.base (openHodge k L D)
    (Hodge (LaurentSeries k) (TateCurve k L)) (openTestIso k L T.toTest)
    d (X.inclusion ⁻¹ᵁ U)
    (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)) r hr h
  rw [← diskRestriction_local_section k L H T U e hdisk h] at ht
  have hinj := diskRestriction_frame k L H T η hη ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at hinj
  have hc := hinj.1 (ht.symm.trans hf')
  refine ⟨f * (u : PowerSeries k), ?_⟩
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom hc).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id _)).symm

lemma scalar_stalk_integral (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (d : Γ(openHodge k L D, ⊤))
    (hd : ∃ f : PowerSeries k, transportSection T.base _ _ (openTestIso k L T.toTest) d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openHodge k L D) le_top d =
      r • H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)) :
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    ∃ (β : Spec (CommRingCat.of (FractionRing (CuspStalk k L D X T.disk))) ⟶ OpenBase k L D)
      (hβU : (⊤ : (Spec (CommRingCat.of (FractionRing (CuspStalk k L D X T.disk)))).Opens) ≤
        β ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)),
      β ≫ X.inclusion = Spec.map (CommRingCat.ofHom (algebraMap (CuspStalk k L D X T.disk)
        (FractionRing (CuspStalk k L D X T.disk)))) ≫
          X.space.fromSpecStalk (T.disk (closedPoint k)) ∧
      ∃ a : CuspStalk k L D X T.disk,
        algebraMap _ (FractionRing (CuspStalk k L D X T.disk)) a =
          (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (CuspStalk k L D X T.disk)))).hom
            (β.appLE (X.inclusion ⁻¹ᵁ U) ⊤ hβU r) := by
  letI : IsDomain (CuspStalk k L D X T.disk) :=
    (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
  obtain ⟨β, θ, _, hβ, hβT, _, hθ, _, _⟩ :=
    disk_shared_center_fraction_maps k L hL heven D X T T rfl
  have hT : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z _
    change X.inclusion (T.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge (Set.mem_univ _)
  have hβU : (⊤ : (Spec (CommRingCat.of
      (FractionRing (CuspStalk k L D X T.disk)))).Opens) ≤ β ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z _
    let w : Puncture k := (⊥ : PrimeSpectrum (LaurentSeries k))
    have hz : Spec.map (CommRingCat.ofHom θ) w = z := Subsingleton.elim _ _
    change X.inclusion (β z) ∈ U
    rw [← hz]
    change X.inclusion ((Spec.map (CommRingCat.ofHom θ) ≫ β) w) ∈ U
    rw [hβT]
    exact hT (Set.mem_univ _)
  refine ⟨β, hβU, hβ, ?_⟩
  apply integral_of_completed_order_nonneg k L hL heven D X T _ θ hθ
  rw [field_section_factor θ β T.base hβT _ hβU hT r]
  obtain ⟨b, hb⟩ := local_scalar_integral k L H hH T U e he hU d hd r hr hT
  rw [← hb]
  exact ArithmeticThetaCompactUnaryR0183.CompactNormalizedPowerExtensionR0183.integral_series_order k b

/-- Local lifts are actual sections on Zariski neighborhoods, obtained by
reflecting completed integrality in the normal local ring. -/
lemma alpha_local_lifts (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) [IsAlgClosed k] (X : Compactification k L D)
    (H : Extension k L D X) (hH : Canonical k L H)
    (d : Γ(openHodge k L D, ⊤))
    (hd : ∀ T : ArithmeticThetaBoundaryHodgeR0182.Test k L D, ∃ f : PowerSeries k,
      transportSection T.base _ _ (openTestIso k L T) d =
        scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
          ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential) :
    ∀ x : X.space, ∃ (V : X.space.Opens) (s : Γ(H.line, V)), x ∈ V ∧
      H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s) =
      res (openHodge k L D) (show X.inclusion ⁻¹ᵁ V ≤ ⊤ from le_top) d := by
  letI := X.openImmersion
  intro x
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨s, hs⟩ := section_lift_open X.inclusion H.line
      (openHodge k L D) H.onOpen d
    exact ⟨X.inclusion.opensRange, s, hx, hs⟩
  · obtain ⟨T, hTx⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X x hx
    obtain ⟨U, e, hxU, he, hUI⟩ := integral_frame_neighborhood k L H x
    letI := hUI
    have hTU : T.disk (closedPoint k) ∈ U := hTx ▸ hxU
    let σ := H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)
    have hσ : IsFrame (openHodge k L D) (X.inclusion ⁻¹ᵁ U) σ :=
      frame_iso H.onOpen _ (pullback_frame _ _ _ he)
    obtain ⟨r, hr⟩ := (hσ (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (res (openHodge k L D) le_top d)
    rw [InitialHodgeSection.res_self] at hr
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    obtain ⟨β, hβU, hβ, a, ha⟩ := scalar_stalk_integral
      k L hL heven H hH T U e he hTU d (hd T.toTest) r hr.symm
    obtain ⟨V, hTV, hVU, q, hq⟩ := local_scalar_lift X.inclusion
      (T.disk (closedPoint k)) U hTU β hβ hβU r a ha
    refine ⟨V, q • res H.line hVU e, hTx ▸ hTV, ?_⟩
    have hh := congrArg (res (openHodge k L D)
      (show X.inclusion ⁻¹ᵁ V ≤ X.inclusion ⁻¹ᵁ U from fun _ hx => hVU hx)) hr.symm
    rw [InitialHodgeSection.res_res, InitialHodgeSection.res_smul] at hh
    dsimp only [σ] at hh
    rw [hom_res, InitialSectionNaturality.pullback_res] at hh
    rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, hq]
    exact hh.symm

lemma restrict_eq_transport {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (s : Γ(H.line, ⊤)) :
    restrictAlpha L k D X H s = transportSection X.inclusion _ _ H.onOpen s := by
  simp only [restrictAlpha, pullbackGlobalSection, transportSection, Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top, res_refl]

lemma disk_generic {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) (s : Γ(H.line, ⊤)) :
    diskRestriction k L H T (pullbackGlobalSection T.disk H.line s) =
      transportSection T.base _ _ (openTestIso k L T.toTest) (restrictAlpha L k D X H s) := by
  have ht := diskRestriction_local_section k L H T ⊤ s (by simp) (by simp)
  simpa only [pullbackGlobalSection, restrictAlpha, transportSection,
    Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top, res_refl] using ht

/-- Generic injectivity retains the entire signed coefficient on the disk. -/
lemma disk_coefficient_of_restrict
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (d : Γ(openHodge k L D, ⊤))
    (s : Γ(H.line, ⊤)) (hs : restrictAlpha L k D X H s = d)
    (T : DiskTest k L D X) (f : PowerSeries k)
    (hf : transportSection T.base _ _ (openTestIso k L T.toTest) d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
        ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) :
    pullbackGlobalSection T.disk H.line s = scalar (PowerSeries k) f • η := by
  letI := generic_schematic k
  letI : QuasiCompact (genericInclusion k) := by unfold genericInclusion; infer_instance
  have hi : Function.Injective (diskRestriction k L H T) := by
    intro u v huv
    apply pullback_injective_of_frame (genericInclusion k) _ η hη.1
    apply (ConcreteCategory.bijective_of_isIso ((diskGenericIso k L H T).hom.app _)).1
    exact (res_bijective _ (by simp) le_top).1 huv
  apply hi
  rw [disk_generic, hs, diskRestriction_smul]
  change _ = _ • transportSection (genericInclusion k) _ _ (diskGenericIso k L H T) η
  rw [show transportSection (genericInclusion k) _ _ (diskGenericIso k L H T) η =
    ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L T.differential from hη.2]
  exact hf

lemma restrict_injective {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) : Function.Injective (restrictAlpha L k D X H) := by
  letI := inclusion_schematic k L D X
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  intro s t h
  apply pullback_injective_of_invertible X.inclusion H.line H.invertible
  apply (ConcreteCategory.bijective_of_isIso (H.onOpen.hom.app _)).1
  rw [restrict_eq_transport, restrict_eq_transport] at h
  exact (res_bijective _ (by simp) le_top).1 h

end ArithmeticThetaGlobalFourTorsionR0190.CompactFullLevelAlpha

namespace ArithmeticThetaGlobalFourTorsionR0190
open CategoryTheory AlgebraicGeometry ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open CompactFullLevelAlpha

/-- The same intrinsic open section extends uniquely over the compact curve.
Every marked cusp has order zero or L/4, both even, and the canonical cusp
retains the literal signed theta-square series. -/
theorem compact_full_level_alpha :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
      (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D)
      (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X),
    ArithmeticThetaBoundaryHodgeR0182.Canonical k L H →
    ∃! a : (H.line).presheaf.obj (Opposite.op ⊤),
      ArithmeticThetaGlobalFourTorsionR0190.IsOpenAlpha L k D
        (ArithmeticThetaGlobalFourTorsionR0190.restrictAlpha L k D X H a) ∧
      ArithmeticThetaGlobalFourTorsionR0190.CuspOrders L k D X H a ∧
      ArithmeticThetaGlobalFourTorsionR0190.ExactTateAlpha L k D X H a := by
  intro k _ _ _ L hL h8 D X H hH
  have h4 : 4 ∣ L := dvd_trans (by norm_num) h8
  have h3 : 3 ≤ L := le_trans (by norm_num) (Nat.le_of_dvd hL h8)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hquarter : Even (L / 4) := by
    obtain ⟨n, rfl⟩ := h8
    refine ⟨n, ?_⟩
    omega
  obtain ⟨d, hd, hdu⟩ := open_full_level_alpha k L hL h4 D
  have ht := open_tate_behavior k L hL h4 d hd
  letI := X.openImmersion
  letI := compact_noetherian k L D X
  letI := inclusion_schematic k L D X
  obtain ⟨a, ha, _⟩ := existsUnique_extension_of_local_lifts X.inclusion
    H.line H.invertible (openHodge k L D) H.onOpen d
    (alpha_local_lifts k L h3 heven D X H hH d (by
      intro T
      obtain ⟨v, j, _, hj⟩ := (ht T).1
      exact ⟨PowerSeries.X^j * (v : PowerSeries k), hj⟩))
  have har : restrictAlpha L k D X H a = d := (restrict_eq_transport k L H a).trans ha
  refine ⟨a, ⟨har.symm ▸ hd, ?_, ?_⟩, ?_⟩
  · intro T η hη
    obtain ⟨v, j, hj, hf⟩ := (ht T.toTest).1
    refine ⟨v, j, hj, ?_, disk_coefficient_of_restrict k L H d a har T _ hf η hη⟩
    rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact hquarter
  · intro T ζ hζ hcan η hη
    exact disk_coefficient_of_restrict k L H d a har T _
      ((ht T.toTest).2 ζ hζ hcan) η hη
  · intro b hb
    apply restrict_injective k L H
    exact (hdu _ hb.1).trans har.symm

#print axioms compact_full_level_alpha
end ArithmeticThetaGlobalFourTorsionR0190
