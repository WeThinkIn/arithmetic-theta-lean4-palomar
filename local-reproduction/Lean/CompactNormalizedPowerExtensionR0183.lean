import AllCuspNormalizedPowerIntegralityR0183

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCompactUnaryR0183.CompactNormalizedPowerExtensionR0183
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open GlobalFamilyDiscriminantR0180
variable (k : Type) [Field k] [CharZero k] (L : ℕ)

/-- Integrality of the full coefficient in the canonical frame implies
integrality of the scalar in any ambient local frame. -/
lemma local_scalar_integral
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (n : ℕ) (d : Γ(power D.atlas.descent.family n, ⊤))
    (hd : ∃ f : PowerSeries k, pullAmbientPower k L T.toTest n d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L))
        n ⊤ (hodgeGenerator k L T.differential))
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openPower k L D n) le_top (pullToOpen k L n d) =
      r • tensorPowerSection (OpenBase k L D) (openHodge k L D) n
        (X.inclusion ⁻¹ᵁ U)
        (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)))
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
  rw [← ha, InitialHodgeSection.tensor_smul, smul_smul] at hf
  have hf' : pullAmbientPower k L T.toTest n d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (f * (u : PowerSeries k)^n)) •
        tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L))
          n ⊤ (diskRestriction k L H T η) := by
    simpa only [map_mul, map_pow, hu, scalar] using hf
  have ht := transportSection_local_scalar T.base (openHodge k L D)
    (Hodge (LaurentSeries k) (TateCurve k L)) (openTestIso k L T.toTest)
    n (pullToOpen k L n d) (X.inclusion ⁻¹ᵁ U)
    (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)) r hr h
  rw [pullToOpen_test, ← diskRestriction_local_section k L H T U e hdisk h] at ht
  have hinj := tensorPower_frame _ (diskRestriction k L H T η)
    (diskRestriction_frame k L H T η hη) n ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at hinj
  have hc := hinj.1 (ht.symm.trans hf')
  refine ⟨f * (u : PowerSeries k)^n, ?_⟩
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom hc).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id _)).symm

omit [CharZero k] in
lemma integral_series_order (b : PowerSeries k) :
    0 ≤ (algebraMap (PowerSeries k) (LaurentSeries k) b).order := by
  by_cases hb : algebraMap (PowerSeries k) (LaurentSeries k) b = 0
  · rw [hb, HahnSeries.order_zero]
  · exact (HahnSeries.le_order_iff_forall hb).2 (fun i hi => laurent_coeff_negative k b i hi)

lemma scalar_stalk_integral (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (n : ℕ) (d : Γ(power D.atlas.descent.family n, ⊤))
    (hd : ∃ f : PowerSeries k, pullAmbientPower k L T.toTest n d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L))
        n ⊤ (hodgeGenerator k L T.differential))
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openPower k L D n) le_top (pullToOpen k L n d) =
      r • tensorPowerSection (OpenBase k L D) (openHodge k L D) n
        (X.inclusion ⁻¹ᵁ U)
        (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e))) :
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
  obtain ⟨b, hb⟩ := local_scalar_integral k L H hH T U e he hU n d hd r hr hT
  rw [← hb]
  exact integral_series_order k b

lemma power_local_lifts (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) [IsAlgClosed k] (X : Compactification k L D)
    (H : Extension k L D X) (hH : Canonical k L H)
    (n : ℕ) (d : Γ(power D.atlas.descent.family n, ⊤))
    (hd : ∀ T : Test k L D, ∃ f : PowerSeries k, pullAmbientPower k L T n d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L))
        n ⊤ (hodgeGenerator k L T.differential)) :
    ∀ x : X.space, ∃ (V : X.space.Opens) (s : Γ(tensorPower X.space H.line n, V)), x ∈ V ∧
      (tensorComparison X.inclusion H.line (openHodge k L D) H.onOpen n).hom.app _
        (Scheme.Modules.pullbackLocalSection X.inclusion s) =
      res (openPower k L D n) (show X.inclusion ⁻¹ᵁ V ≤ ⊤ from le_top) (pullToOpen k L n d) := by
  letI := X.openImmersion
  intro x
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨s, hs⟩ := section_lift_open X.inclusion (tensorPower X.space H.line n)
      (openPower k L D n) (tensorComparison X.inclusion H.line _ H.onOpen n) (pullToOpen k L n d)
    exact ⟨X.inclusion.opensRange, s, hx, hs⟩
  · obtain ⟨T, hTx⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X x hx
    obtain ⟨U, e, hxU, he, hUI⟩ := integral_frame_neighborhood k L H x
    letI := hUI
    have hTU : T.disk (closedPoint k) ∈ U := hTx ▸ hxU
    let σ := H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)
    have hσ : IsFrame (openHodge k L D) (X.inclusion ⁻¹ᵁ U) σ :=
      frame_iso H.onOpen _ (pullback_frame _ _ _ he)
    obtain ⟨r, hr⟩ := (tensorPower_frame _ σ hσ n (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (res (openPower k L D n) le_top (pullToOpen k L n d))
    rw [InitialHodgeSection.res_self] at hr
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    obtain ⟨β, hβU, hβ, a, ha⟩ := scalar_stalk_integral
      k L hL heven H hH T U e he hTU n d (hd T.toTest) r hr.symm
    obtain ⟨V, hTV, hVU, q, hq⟩ := local_scalar_lift X.inclusion
      (T.disk (closedPoint k)) U hTU β hβ hβU r a ha
    refine ⟨V, q • tensorPowerSection X.space H.line n V (res H.line hVU e),
      hTx ▸ hTV, ?_⟩
    exact tensor_lift_of_scalar X.inclusion H.line (openHodge k L D) H.onOpen n
      (pullToOpen k L n d) U e r hr.symm V hVU q hq


/-- Generic injectivity upgrades the entire open coefficient identity to the
same literal identity on the actual disk, for every extended generator. -/
lemma disk_coefficient_of_restrict
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (n : ℕ)
    (d : Γ(power D.atlas.descent.family n, ⊤))
    (s : Γ(tensorPower X.space H.line n, ⊤))
    (hs : restrictPower k L H n s = pullToOpen k L n d)
    (T : DiskTest k L D X) (f : PowerSeries k)
    (hf : pullAmbientPower k L T.toTest n d =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k L))
        n ⊤ (hodgeGenerator k L T.differential))
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) :
    diskPower k L H T n s = scalar (PowerSeries k) f •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) n ⊤ η := by
  letI := generic_schematic k
  letI : QuasiCompact (genericInclusion k) := by unfold genericInclusion; infer_instance
  let e := tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H T) n
  have hi : Function.Injective (transportSection (genericInclusion k) _ _ e) := by
    intro u v huv
    apply pullback_injective_of_frame (genericInclusion k) _
      (tensorPowerSection (Disk k) _ n ⊤ η) (tensorPower_frame _ η hη.1 n)
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
    exact (GlobalFamilyDiscriminantR0180.res_bijective _ (by simp) le_top).1 huv
  apply hi
  change transportSection (genericInclusion k) _ _
    (tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H T) n) _ = _
  rw [diskPower_generic, hs, pullToOpen_test]
  rw [transportSection_smul, transportSection_tensor]
  have hgen : transportSection (genericInclusion k) _ _ (diskGenericIso k L H T) η =
      hodgeGenerator k L T.differential := hη.2
  rw [hgen]
  have hscalar : (genericInclusion k).appLE ⊤ ⊤ (by simp)
      (scalar (PowerSeries k) f) =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) := by
    change (genericInclusion k).app ⊤ (scalar (PowerSeries k) f) = _
    exact ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.scalar_restriction k _
  rw [hscalar]
  exact hf

#print axioms local_scalar_integral
#print axioms scalar_stalk_integral
#print axioms power_local_lifts
#print axioms disk_coefficient_of_restrict
end ArithmeticThetaCompactUnaryR0183.CompactNormalizedPowerExtensionR0183

namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open CompactNormalizedPowerExtensionR0183

/-- The unique compact extension of the same normalized open section, with
nonzero full integral coefficients in every actual Tate disk. -/
theorem compact_normalized_power_extension :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ (a b : Fin N), (a.val ≠ 0 ∨ b.val ≠ 0) → ∀ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaBoundaryHodgeR0182.restrictPower k (ArithmeticThetaCompactUnaryR0183.level N) H (ArithmeticThetaCompactUnaryR0183.weight N) s = ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ ∧ ∀ V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X, ∃ f : PowerSeries k, f ≠ 0 ∧ ArithmeticThetaCompactUnaryR0183.DiskCoefficient k N H V s f := by
  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH a b hab A
  have hL : 3 ≤ level N := by
    dsimp [level]
    have : 1 ≤ N^2 := Nat.one_le_pow 2 N hN
    omega
  have heven : Even (level N) := ⟨12*N^2, by dsimp [level]; omega⟩
  have hint := all_cusp_normalized_power_integrality k m N hm hmeven hN hNeven hmN D a b hab A
  letI := X.openImmersion
  letI := compact_noetherian k (level N) D X
  letI := inclusion_schematic k (level N) D X
  obtain ⟨s, hs, _⟩ := existsUnique_extension_of_local_lifts X.inclusion
    (tensorPower X.space H.line (weight N)) (tensorPower_invertible H.line H.invertible (weight N))
    (openPower k (level N) D (weight N))
    (tensorComparison X.inclusion H.line _ H.onOpen (weight N))
    (pullToOpen k (level N) (weight N) A.section_)
    (power_local_lifts k (level N) hL heven D X H hH (weight N) A.section_ (by
      intro T
      obtain ⟨f, _, hf⟩ := hint T
      exact ⟨f, hf⟩))
  change restrictPower k (level N) H (weight N) s =
    pullToOpen k (level N) (weight N) A.section_ at hs
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · intro V
    obtain ⟨f, hf0, hf⟩ := hint V.toTest
    refine ⟨f, hf0, ?_⟩
    intro η hη
    exact disk_coefficient_of_restrict k (level N) H (weight N) A.section_ s hs V f hf η hη
  · intro t ht
    exact restrictPower_injective k (level N) H (weight N) (ht.1.trans hs.symm)

#print axioms compact_normalized_power_extension
end ArithmeticThetaCompactUnaryR0183
