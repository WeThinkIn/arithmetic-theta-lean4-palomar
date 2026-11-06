module

public import CompactHodgeLatticeExtensionR0182

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open CompactHodgeLatticeExtensionR0182 OpenDiscriminantFullTateExpansionR0182

variable (k : Type) [Field k] [CharZero k] (L : ℕ)

/-- The literal complete series has its first coefficient exactly one. -/
lemma discriminant_coefficients (hL : 0 < L) :
    (∀ j : ℕ, j < 2 * L → PowerSeries.coeff j
      (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 0) ∧
    PowerSeries.coeff (2 * L)
      (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 1 := by
  constructor
  · exact (PowerSeries.order_eq_nat.mp
      (ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.series_order k L hL)).2
  · have hp : PowerSeries.HasSubst (PowerSeries.X ^ L : PowerSeries k) :=
      PowerSeries.HasSubst.X_pow (Nat.ne_of_gt hL)
    unfold ArithmeticThetaHodgeInitialR0163.discriminantSeries
    rw [map_mul, map_pow, PowerSeries.map_X, map_pow,
      PowerSeries.subst_mul hp, PowerSeries.subst_pow hp,
      PowerSeries.subst_X hp, PowerSeries.subst_pow hp, ← pow_mul,
      Nat.mul_comm L 2]
    rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      PowerSeries.constantCoeff_subst_X_pow (Nat.ne_of_gt hL),
      ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, ArithmeticThetaDiscriminant.P_constant,
      map_one]
    simp only [map_one, one_pow]

lemma pullback_local_injective_of_invertible {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (W : Y.Opens) :
    Function.Injective (fun s : Γ(M, W) => Scheme.Modules.pullbackLocalSection p s) := by
  intro s t hst
  change Scheme.Modules.pullbackLocalSection p s = Scheme.Modules.pullbackLocalSection p t at hst
  apply GlobalFamilyDiscriminantR0180.sections_eq_local
  intro y hyW
  obtain ⟨V, eV, hyV, heV⟩ := local_frame_exists hM y
  let U := V ⊓ W
  let e := res M (inf_le_left : U ≤ V) eV
  have he : IsFrame M U e := frame_restrict _ _ _ heV
  refine ⟨U, ⟨hyV, hyW⟩, inf_le_right, ?_⟩
  obtain ⟨a, ha⟩ := (he U le_rfl).2 (res M (inf_le_right : U ≤ W) s)
  obtain ⟨b, hb⟩ := (he U le_rfl).2 (res M (inf_le_right : U ≤ W) t)
  rw [InitialHodgeSection.res_self] at ha hb
  have hlocal : Scheme.Modules.pullbackLocalSection p (res M (show U ≤ W from inf_le_right) s) =
      Scheme.Modules.pullbackLocalSection p (res M (show U ≤ W from inf_le_right) t) := by
    rw [← InitialSectionNaturality.pullback_res,
      ← InitialSectionNaturality.pullback_res, hst]
  rw [← ha, ← hb, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.pullbackLocalSection_smul] at hlocal
  have hframe := pullback_frame p M e he
  have hab : p.app U a = p.app U b := (hframe _ le_rfl).1 (by
    simpa only [InitialHodgeSection.res_self] using hlocal)
  rw [← ha, ← hb, p.app_injective U hab]

/-- A schematically dominant pullback detects sections of any invertible
module. The proof uses actual local frames and structure-sheaf injectivity. -/
lemma pullback_injective_of_invertible {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Function.Injective (fun s : Γ(M, ⊤) => Scheme.Modules.pullbackLocalSection p s) :=
  pullback_local_injective_of_invertible p M hM ⊤

lemma tensorPower_invertible {Y : Scheme.{0}} (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    Scheme.Modules.IsInvertible (tensorPower Y M n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit Y
  | succ n ih => exact sheafTensor_invertible ih hM

lemma inclusion_schematic (D : LevelData k L) (X : Compactification k L D) :
    IsSchemeTheoreticallyDominant X.inclusion := by
  letI : ∀ x : X.space, IsDomain (X.space.presheaf.stalk x) :=
    fun x => (compact_stalk_normal k L D X x).1
  letI : IsReduced X.space := isReduced_of_isReduced_stalk X.space
  letI : IsDominant X.inclusion := ⟨X.dense⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant X.inclusion

/-- A compact tensor section is uniquely determined by its specified open
restriction, even when the compact curve has several components. -/
lemma restrictPower_injective {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (n : ℕ) : Function.Injective (restrictPower k L H n) := by
  letI := inclusion_schematic k L D X
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  intro s t h
  apply pullback_injective_of_invertible X.inclusion _ (tensorPower_invertible H.line H.invertible n)
  apply (ConcreteCategory.bijective_of_isIso
    ((tensorComparison X.inclusion H.line (openHodge k L D) H.onOpen n).hom.app _)).1
  exact (GlobalFamilyDiscriminantR0180.res_bijective _ (by simp) le_top).1 h

open GlobalFamilyDiscriminantR0180

lemma tensorComparison_comp_eq {Y Z W : Scheme.{0}}
    (p : Z ⟶ Y) (q : W ⟶ Z) (r : W ⟶ Y) (hr : r = q ≫ p)
    (M : Y.Modules) (N : Z.Modules) (P : W.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) (n : ℕ) :
    tensorComparison r M P (composeComparison p q r hr M N P e f) n =
      composeComparison p q r hr (tensorPower Y M n) (tensorPower Z N n)
        (tensorPower W P n) (tensorComparison p M N e n) (tensorComparison q N P f n) := by
  subst r
  exact tensorComparison_comp p q M N P hM e f n

lemma transportSection_comp_eq {Y Z W : Scheme.{0}}
    (p : Z ⟶ Y) (q : W ⟶ Z) (r : W ⟶ Y) (hr : r = q ≫ p)
    (M : Y.Modules) (N : Z.Modules) (P : W.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) (s : Γ(M, ⊤)) :
    transportSection r M P (composeComparison p q r hr M N P e f) s =
      transportSection q N P f (transportSection p M N e s) := by
  subst r
  exact transportSection_comp p q M N P e f s

/-- The generic disk comparison and the open comparison use the same
classifying square, before taking tensor powers. -/
lemma disk_comparison_square {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    composeComparison T.disk (genericInclusion k) (genericInclusion k ≫ T.disk) rfl
      H.line ((Scheme.Modules.pullback T.disk).obj H.line)
      (Hodge (LaurentSeries k) (TateCurve k L)) (Iso.refl _) (diskGenericIso k L H T) =
    composeComparison X.inclusion T.base (genericInclusion k ≫ T.disk) T.extends_eq.2.1
      H.line (openHodge k L D) (Hodge (LaurentSeries k) (TateCurve k L))
      H.onOpen (openTestIso k L T.toTest) := by
  apply Iso.ext
  simp [composeComparison, diskGenericIso, pullbackEqIso]

/-- Tensor transport around the actual classifying square commutes on every
global compact section. -/
lemma diskPower_generic {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) (n : ℕ)
    (s : Γ(tensorPower X.space H.line n, ⊤)) :
    transportSection (genericInclusion k) _ _
      (tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H T) n)
      (diskPower k L H T n s) =
    transportSection T.base _ _
      (tensorComparison T.base _ _ (openTestIso k L T.toTest) n)
      (restrictPower k L H n s) := by
  change transportSection (genericInclusion k) _ _ _
    (transportSection T.disk _ _ (ArithmeticThetaPullback.pullback_tensorPower_iso _ _ _ _ n) s) =
    transportSection T.base _ _ _ (transportSection X.inclusion _ _ _ s)
  rw [← tensorComparison_refl T.disk H.line H.invertible,
    ← transportSection_comp, ← tensorComparison_comp _ _ _ _ _ H.invertible,
    disk_comparison_square,
    tensorComparison_comp_eq _ _ _ _ _ _ _ H.invertible,
    transportSection_comp_eq]

/-- Once a compact regular extension exists, its complete disk value is
forced by the accepted open expansion and generic injectivity. -/
lemma disk_expansion_of_restrict (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (hs : restrictPower k L H 24 s = pullToOpen k L 24 d)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) :
    diskPower k L H T 24 s =
      scalar (PowerSeries k) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) •
        tensorPowerSection (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) 24 ⊤ η := by
  letI := generic_schematic k
  letI : QuasiCompact (genericInclusion k) := by unfold genericInclusion; infer_instance
  let e := tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H T) 24
  have hi : Function.Injective (transportSection (genericInclusion k) _ _ e) := by
    intro u v huv
    apply pullback_injective_of_frame (genericInclusion k) _
      (tensorPowerSection (Disk k) _ 24 ⊤ η) (tensorPower_frame _ η hη.1 24)
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
    exact (GlobalFamilyDiscriminantR0180.res_bijective _ (by simp) le_top).1 huv
  apply hi
  change transportSection (genericInclusion k) _ _
    (tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H T) 24) _ = _
  rw [diskPower_generic, hs, pullToOpen_test]
  rw [transportSection_smul, transportSection_tensor]
  have hgen : transportSection (genericInclusion k) _ _ (diskGenericIso k L H T) η =
      hodgeGenerator k L T.differential := hη.2
  rw [hgen]
  have hscalar : (genericInclusion k).appLE ⊤ ⊤ (by simp)
      (scalar (PowerSeries k) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L)) =
      scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L) := by
    change (genericInclusion k).app ⊤
      (scalar (PowerSeries k) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L)) = _
    exact ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.scalar_restriction k _
  rw [hscalar]
  exact open_discriminant_full_tate_expansion k L hL heven D T.toTest d hd

/-- An unramified completed cusp map detects integrality in the actual
fraction field of the cusp stalk. No regularity assumption is made on c. -/
lemma integral_of_completed_order_nonneg (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (F : Type) [Field F] [Algebra (CuspStalk k L D X T.disk) F]
    [IsFractionRing (CuspStalk k L D X T.disk) F]
    (θ : F →+* LaurentSeries k)
    (hθ : ∀ a : CuspStalk k L D X T.disk, θ (algebraMap _ F a) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X T.disk a))
    (c : F) (hc : 0 ≤ (θ c).order) :
    ∃ a : CuspStalk k L D X T.disk, algebraMap _ F a = c := by
  obtain ⟨hdom, hdvr⟩ := CompletedLocalParameter.cuspStalk_dvr k L D X T.base T.disk T.extends_eq
  letI := hdom
  letI := hdvr
  by_cases hz : c = 0
  · exact ⟨0, by simp [hz]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (CuspStalk k L D X T.disk) c
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hz
    rw [← hab, ha, map_zero, zero_div]
  rw [← hab, map_div₀, hθ, hθ,
    disk_rational_germ_order k L hL heven D X T a b ha0 hb0] at hc
  have hle : Ring.ord (CuspStalk k L D X T.disk) b ≤
      Ring.ord (CuspStalk k L D X T.disk) a := by
    have ha' := ENat.natCast_toNat_eq_self.mpr (Ring.ord_ne_top
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha0))
    have hb' := ENat.natCast_toNat_eq_self.mpr (Ring.ord_ne_top hb)
    rw [← ha', ← hb']
    exact_mod_cast (show (Ring.ord (CuspStalk k L D X T.disk) b).toNat ≤
      (Ring.ord (CuspStalk k L D X T.disk) a).toNat by omega)
  rw [Ring.ord_eq_addVal, Ring.ord_eq_addVal,
    IsDiscreteValuationRing.addVal_le_iff_dvd] at hle
  obtain ⟨q, hq⟩ := hle
  refine ⟨q, ?_⟩
  rw [← hab, hq, map_mul, mul_div_cancel_left₀]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

/-- Canonical Hodge lattices make the local scalar of the same open D2
have order 2L in every actual completed cusp map. -/
lemma canonical_local_scalar_order (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openPower k L D 24) le_top (pullToOpen k L 24 d) =
      r • tensorPowerSection (OpenBase k L D) (openHodge k L D) 24
        (X.inclusion ⁻¹ᵁ U)
        (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)))
    (h : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ h r)).order = (2 * L : ℕ) := by
  let η := res ((Scheme.Modules.pullback T.disk).obj H.line)
    (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
    (Scheme.Modules.pullbackLocalSection T.disk e)
  have hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η :=
    frame_restrict _ _ _ (pullback_frame _ _ _ he)
  obtain ⟨a, ha, _⟩ := disk_coefficient_exists k L H T η hη
  have ha0 := (extendsGenerator_iff_order_zero k L H T η hη a ha).1 (hH T).exists
  rw [disk_local_discriminant_scalar k L hL heven H T U e he hU d hd r hr a ha,
    discriminant_coefficient_order k L (by omega) a
      (disk_coefficient_ne_zero k L H T η hη a ha), ha0, mul_zero, add_zero]

/-- The local open scalar is an actual regular stalk element under the
specified generic lift through the same cusp. -/
lemma canonical_scalar_stalk_integral (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (hH : Canonical k L H) (T : DiskTest k L D X)
    (U : X.space.Opens) (e : Γ(H.line, U)) (he : IsFrame H.line U e)
    (hU : T.disk (closedPoint k) ∈ U)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openPower k L D 24) le_top (pullToOpen k L 24 d) =
      r • tensorPowerSection (OpenBase k L D) (openHodge k L D) 24
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
  rw [field_section_factor θ β T.base hβT _ hβU hT r,
    canonical_local_scalar_order k L hL heven H hH T U e he hU d hd r hr hT]
  positivity

lemma fromSpecStalk_dominant {Y : Scheme.{0}} [IsIntegral Y] (y : Y) :
    IsDominant (Y.fromSpecStalk y) := by
  constructor
  intro z
  have hη : genericPoint Y ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hh := closure_mono (Set.singleton_subset_iff.mpr hη)
  rw [genericPoint_spec Y] at hh
  exact hh (Set.mem_univ z)

lemma specMap_dominant_of_injective {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

/-- The actual fraction field of a stalk dominates every integral open
neighborhood of that stalk. -/
lemma fraction_stalk_dominant {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U)
    [IsIntegral U.toScheme] [IsDomain (Y.presheaf.stalk y)] :
    IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫
        U.fromSpecStalkOfMem y hy) := by
  letI := specMap_dominant_of_injective
    (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))
    (IsFractionRing.injective _ _)
  letI := fromSpecStalk_dominant (Y := U.toScheme) (⟨y, hy⟩ : U.toScheme)
  haveI : IsDominant (U.fromSpecStalkOfMem y hy) := by
    unfold Scheme.Opens.fromSpecStalkOfMem
    infer_instance
  infer_instance

/-- Generic evaluation along the actual fraction-stalk lift is injective
on the portion of any integral neighborhood lying in the open base. -/
lemma open_scalar_generic_injective {Y Z : Scheme.{0}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (y : Y) (U : Y.Opens) (hy : y ∈ U)
    [IsIntegral U.toScheme] [IsDomain (Y.presheaf.stalk y)]
    (β : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ Z)
    (hβ : β ≫ j = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫ Y.fromSpecStalk y)
    (h : (⊤ : (Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).Opens) ≤
      β ⁻¹ᵁ (j ⁻¹ᵁ U)) :
    Function.Injective (β.appLE (j ⁻¹ᵁ U) ⊤ h) := by
  let V := j ⁻¹ᵁ U
  have hrange : Set.range β ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨β z, h (Set.mem_univ z)⟩, rfl⟩
  let b := IsOpenImmersion.lift V.ι β hrange
  have hb : b ≫ V.ι = β := IsOpenImmersion.lift_fac _ _ _
  have hcomp : b ≫ j ∣_ U = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫
        U.fromSpecStalkOfMem y hy := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb, hβ,
      Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  letI : IsDominant (b ≫ j ∣_ U) := hcomp ▸ fraction_stalk_dominant y U hy
  letI : IsDominant b := IsDominant.of_comp_of_isOpenImmersion b (j ∣_ U)
  letI : Nonempty V := ⟨b (⊥ : PrimeSpectrum (FractionRing (Y.presheaf.stalk y)))⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (j ∣_ U)
  letI : IsSchemeTheoreticallyDominant b := IsSchemeTheoreticallyDominant.of_isDominant b
  have hinj : Function.Injective (b.appLE ⊤ ⊤ (by simp)) := by
    change Function.Injective (b.app ⊤)
    exact b.app_injective ⊤
  have heq : V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫ b.appLE ⊤ ⊤ (by simp) =
      β.appLE V ⊤ h := by
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
  rw [← heq]
  exact hinj.comp (ConcreteCategory.bijective_of_isIso
    (V.ι.appLE V ⊤ V.ι_preimage_self.ge)).1

lemma fromSpecStalk_appLE_top {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (h : (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ≤ (Y.fromSpecStalk y) ⁻¹ᵁ U) :
    (Y.fromSpecStalk y).appLE U ⊤ h = Y.presheaf.germ U y hy ≫
      (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp, homOfLE_refl, op_id]
  rw [(Spec (Y.presheaf.stalk y)).presheaf.map_id, Category.comp_id]

/-- Evaluation of an ambient regular function through the fraction-stalk
map is exactly the image of its germ. -/
lemma fraction_stalk_evaluation {Y Z : Scheme.{0}} (j : Z ⟶ Y)
    (y : Y) (U : Y.Opens) (hy : y ∈ U) [IsDomain (Y.presheaf.stalk y)]
    (β : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ Z)
    (hβ : β ≫ j = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫ Y.fromSpecStalk y)
    (h : (⊤ : (Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).Opens) ≤
      β ⁻¹ᵁ (j ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).hom
      (β.appLE (j ⁻¹ᵁ U) ⊤ h (j.app U r)) =
        algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))
          (Y.presheaf.germ U y hy r) := by
  have hσ : (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ≤ (Y.fromSpecStalk y) ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y) (by simpa using hy)).ge
  let f := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))
  have heq : j.appLE U (j ⁻¹ᵁ U) le_rfl ≫ β.appLE (j ⁻¹ᵁ U) ⊤ h =
      (Y.fromSpecStalk y).appLE U ⊤ hσ ≫ f.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
  rw [Scheme.Hom.appLE_eq_app, fromSpecStalk_appLE_top] at heq
  have hv := ConcreteCategory.congr_hom heq r
  change β.appLE (j ⁻¹ᵁ U) ⊤ h (j.app U r) =
    f.app ⊤ ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv (Y.presheaf.germ U y hy r)) at hv
  rw [hv]
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))))
      (Y.presheaf.germ U y hy r)
  change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).inv _ =
    f.app ⊤ ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv _) at hn
  rw [← hn]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).inv_hom_id _

/-- A scalar on the open base whose generic value is a regular stalk
element extends to an actual neighborhood of that stalk. -/
lemma local_scalar_lift {Y Z : Scheme.{0}} (j : Z ⟶ Y) [IsOpenImmersion j]
    (y : Y) (U : Y.Opens) (hy : y ∈ U)
    [IsIntegral U.toScheme] [IsDomain (Y.presheaf.stalk y)]
    (β : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ Z)
    (hβ : β ≫ j = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫ Y.fromSpecStalk y)
    (h : (⊤ : (Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).Opens) ≤
      β ⁻¹ᵁ (j ⁻¹ᵁ U)) (r : Γ(Z, j ⁻¹ᵁ U))
    (a : Y.presheaf.stalk y)
    (ha : algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) a =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).hom
        (β.appLE (j ⁻¹ᵁ U) ⊤ h r)) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (hVU : V ≤ U) (q : Γ(Y, V)),
      j.app V q = Z.presheaf.map (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from
        fun _ hx => hVU hx)).op r := by
  obtain ⟨W, hyW, qW, hqW⟩ := Y.presheaf.exists_germ_eq a
  let V : Y.Opens := W ⊓ U
  have hyV : y ∈ V := ⟨hyW, hy⟩
  let q := Y.presheaf.map (homOfLE (inf_le_left : V ≤ W)).op qW
  letI : Nonempty V := ⟨⟨y, hyV⟩⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (Y.homOfLE (inf_le_right : V ≤ U))
  have hV : (⊤ : (Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).Opens) ≤
      β ⁻¹ᵁ (j ⁻¹ᵁ V) := by
    intro z _
    change (β ≫ j) z ∈ V
    rw [hβ, Scheme.Hom.comp_apply]
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y)
      (by simpa using hyV)).ge (Set.mem_univ _)
  refine ⟨V, hyV, inf_le_right, q, ?_⟩
  apply open_scalar_generic_injective j y V hyV β hβ hV
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))).hom).1
  rw [fraction_stalk_evaluation j y V hyV β hβ hV q]
  change algebraMap _ _ (Y.presheaf.germ V y hyV
    (Y.presheaf.map (homOfLE inf_le_left).op qW)) = _
  rw [TopCat.Presheaf.germ_res_apply, hqW, ha]
  congr 1
  exact (ConcreteCategory.congr_hom (β.map_appLE hV
    (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from fun _ hx => hx.2)).op) r).symm

/-- Actual local regular lifts glue uniquely. Compatibility is proved by
schematic density on overlaps, and the resulting section retains the given
open comparison. -/
lemma existsUnique_extension_of_local_lifts {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (N : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (d : Γ(N, ⊤))
    (hlocal : ∀ y : Y, ∃ (U : Y.Opens) (s : Γ(M, U)), y ∈ U ∧
      e.hom.app _ (Scheme.Modules.pullbackLocalSection p s) =
        res N (show p ⁻¹ᵁ U ≤ ⊤ from le_top) d) :
    ∃! s : Γ(M, ⊤), transportSection p M N e s = d := by
  classical
  choose U s hy hs using hlocal
  have hc : TopCat.Presheaf.IsCompatible M.presheaf U s := by
    intro i j
    apply pullback_local_injective_of_invertible p M hM (U i ⊓ U j)
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
    change e.hom.app _ (Scheme.Modules.pullbackLocalSection p (res M inf_le_left (s i))) =
      e.hom.app _ (Scheme.Modules.pullbackLocalSection p (res M inf_le_right (s j)))
    rw [← InitialSectionNaturality.pullback_res, ← InitialSectionNaturality.pullback_res,
      ← hom_res, ← hom_res, hs i, hs j,
      InitialHodgeSection.res_res, InitialHodgeSection.res_res]
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨M.presheaf, M.isSheaf⟩ U ⊤ (fun _ => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩) s hc
  have htd : transportSection p M N e t = d := by
    apply GlobalFamilyDiscriminantR0180.sections_eq_local
    intro z _
    refine ⟨p ⁻¹ᵁ U (p z), hy (p z), le_top, ?_⟩
    rw [transportSection_restrict p M N e t (U (p z)) (p ⁻¹ᵁ U (p z)) le_rfl]
    change res N le_rfl (e.hom.app _
      (Scheme.Modules.pullbackLocalSection p (M.presheaf.map (homOfLE le_top).op t))) = _
    rw [ht, hs, InitialHodgeSection.res_self]
  refine ⟨t, htd, ?_⟩
  intro u hu
  apply pullback_injective_of_invertible p M hM
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
  exact (GlobalFamilyDiscriminantR0180.res_bijective _ (by simp) le_top).1 (hu.trans htd.symm)

lemma integral_frame_neighborhood {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (x : X.space) :
    ∃ (U : X.space.Opens) (e : Γ(H.line, U)), x ∈ U ∧
      IsFrame H.line U e ∧ IsIntegral U.toScheme := by
  obtain ⟨V, e, hxV, he⟩ := local_frame_exists H.invertible x
  let C := compactComponent k L D X x
  let U : X.space.Opens := V ⊓ C
  have hxU : x ∈ U := ⟨hxV, mem_irreducibleComponent⟩
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI : IsIntegral C.toScheme := compactComponent_integral k L D X x
  refine ⟨U, res H.line inf_le_left e, hxU, frame_restrict _ _ _ he, ?_⟩
  exact isIntegral_of_isOpenImmersion (X.space.homOfLE (inf_le_right : U ≤ C))

lemma section_lift_open {Y Z : Scheme.{0}} (p : Z ⟶ Y) [IsOpenImmersion p]
    (M : Y.Modules) (N : Z.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (d : Γ(N, ⊤)) :
    ∃ s : Γ(M, p.opensRange), e.hom.app _ (Scheme.Modules.pullbackLocalSection p s) =
      res N (show p ⁻¹ᵁ p.opensRange ≤ ⊤ from le_top) d := by
  have hb := (ConcreteCategory.bijective_of_isIso (e.hom.app (p ⁻¹ᵁ p.opensRange))).comp
    (Scheme.Modules.bijective_unit_app_of_le_opensRange p M p.opensRange le_rfl)
  exact hb.surjective _

lemma tensor_lift_of_scalar {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    (M : Y.Modules) (N : Z.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (n : ℕ) (d : Γ(tensorPower Z N n, ⊤))
    (U : Y.Opens) (s : Γ(M, U)) (r : Γ(Z, p ⁻¹ᵁ U))
    (hr : res (tensorPower Z N n) le_top d = r • tensorPowerSection Z N n (p ⁻¹ᵁ U)
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s)))
    (V : Y.Opens) (hVU : V ≤ U) (q : Γ(Y, V))
    (hq : p.app V q = Z.presheaf.map
      (homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hVU hx)).op r) :
    (tensorComparison p M N e n).hom.app _
      (Scheme.Modules.pullbackLocalSection p
        (q • tensorPowerSection Y M n V (res M hVU s))) =
      res (tensorPower Z N n) (show p ⁻¹ᵁ V ≤ ⊤ from le_top) d := by
  have hh := congrArg (res (tensorPower Z N n)
    (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hVU hx)) hr
  rw [InitialHodgeSection.res_res, InitialHodgeSection.res_smul] at hh
  change res (tensorPower Z N n) _ d =
    _ • (tensorPower Z N n).presheaf.map (homOfLE _).op _ at hh
  rw [tensorPowerSection_restrict] at hh
  change res (tensorPower Z N n) _ d = _ • tensorPowerSection Z N n (p ⁻¹ᵁ V)
    (res N (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hVU hx)
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))) at hh
  rw [hom_res, InitialSectionNaturality.pullback_res] at hh
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    tensorComparison_section, hq]
  exact hh.symm

/-- Every point has an actual regular tensor lift of the same open D2.
At a cusp the coefficient is descended from its integral rational germ. -/
lemma discriminant_local_lifts (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) [IsAlgClosed k] (X : Compactification k L D)
    (H : Extension k L D X) (hH : Canonical k L H)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d) :
    ∀ x : X.space, ∃ (V : X.space.Opens) (s : Γ(tensorPower X.space H.line 24, V)), x ∈ V ∧
      (tensorComparison X.inclusion H.line (openHodge k L D) H.onOpen 24).hom.app _
        (Scheme.Modules.pullbackLocalSection X.inclusion s) =
      res (openPower k L D 24) (show X.inclusion ⁻¹ᵁ V ≤ ⊤ from le_top) (pullToOpen k L 24 d) := by
  letI := X.openImmersion
  intro x
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨s, hs⟩ := section_lift_open X.inclusion (tensorPower X.space H.line 24)
      (openPower k L D 24) (tensorComparison X.inclusion H.line _ H.onOpen 24) (pullToOpen k L 24 d)
    exact ⟨X.inclusion.opensRange, s, hx, hs⟩
  · obtain ⟨T, hTx⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X x hx
    obtain ⟨U, e, hxU, he, hUI⟩ := integral_frame_neighborhood k L H x
    letI := hUI
    have hTU : T.disk (closedPoint k) ∈ U := hTx ▸ hxU
    let σ := H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion e)
    have hσ : IsFrame (openHodge k L D) (X.inclusion ⁻¹ᵁ U) σ :=
      frame_iso H.onOpen _ (pullback_frame _ _ _ he)
    obtain ⟨r, hr⟩ := (tensorPower_frame _ σ hσ 24 (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (res (openPower k L D 24) le_top (pullToOpen k L 24 d))
    rw [InitialHodgeSection.res_self] at hr
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    obtain ⟨β, hβU, hβ, a, ha⟩ := canonical_scalar_stalk_integral
      k L hL heven H hH T U e he hTU d hd r hr.symm
    obtain ⟨V, hTV, hVU, q, hq⟩ := local_scalar_lift X.inclusion
      (T.disk (closedPoint k)) U hTU β hβ hβU r a ha
    refine ⟨V, q • tensorPowerSection X.space H.line 24 V (res H.line hVU e),
      hTx ▸ hTV, ?_⟩
    exact tensor_lift_of_scalar X.inclusion H.line (openHodge k L D) H.onOpen 24
      (pullToOpen k L 24 d) U e r hr.symm V hVU q hq

#print axioms discriminant_coefficients
#print axioms pullback_injective_of_invertible
#print axioms restrictPower_injective
#print axioms diskPower_generic
#print axioms disk_expansion_of_restrict
#print axioms integral_of_completed_order_nonneg
#print axioms canonical_local_scalar_order
#print axioms canonical_scalar_stalk_integral
#print axioms fraction_stalk_dominant
#print axioms open_scalar_generic_injective
#print axioms fraction_stalk_evaluation
#print axioms local_scalar_lift
#print axioms existsUnique_extension_of_local_lifts
#print axioms discriminant_local_lifts
end ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182


namespace ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open CompactHodgeLatticeExtensionR0182 CompactDiscriminantSectionR0182

/-- The unique global regular extension of the intrinsic open discriminant,
with its literal complete series and exact normalized order at every Tate cusp. -/
theorem compact_discriminant_section :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∀ [IsAlgClosed k] (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (d : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d → ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaBoundaryHodgeR0182.restrictPower k L H 24 s = ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L 24 d ∧ ∀ V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X, ∀ η : ((AlgebraicGeometry.Scheme.Modules.pullback V.disk).obj H.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaBoundaryHodgeR0182.ExtendsGenerator k L H V η → ArithmeticThetaBoundaryHodgeR0182.diskPower k L H V 24 s = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback V.disk).obj H.line) 24 ⊤ η ∧ (∀ j : ℕ, j < 2*L → PowerSeries.coeff j (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 0) ∧ PowerSeries.coeff (2*L) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 1 := by
  intro k _ _ L hL heven D _ X H hH d hd
  letI := X.openImmersion
  letI := compact_noetherian k L D X
  letI := inclusion_schematic k L D X
  obtain ⟨s, hs, _⟩ := existsUnique_extension_of_local_lifts X.inclusion
    (tensorPower X.space H.line 24) (tensorPower_invertible H.line H.invertible 24)
    (openPower k L D 24) (tensorComparison X.inclusion H.line _ H.onOpen 24)
    (pullToOpen k L 24 d) (discriminant_local_lifts k L hL heven D X H hH d hd)
  change restrictPower k L H 24 s = pullToOpen k L 24 d at hs
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · intro V η hη
    exact ⟨disk_expansion_of_restrict k L hL heven H d hd s hs V η hη,
      discriminant_coefficients k L (by omega)⟩
  · intro t ht
    exact restrictPower_injective k L H 24 (ht.1.trans hs.symm)

#print axioms compact_discriminant_section
end ArithmeticThetaBoundaryHodgeR0182
