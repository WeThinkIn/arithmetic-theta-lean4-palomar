module

public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_module_of_forall_ideal_eq_span
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
public import LocalExpansionOrder
public import TateHodgeComparisonTestsR0182
public import OpenDiscriminantFullTateExpansionR0182
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
public import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180

variable (k : Type) [Field k] [CharZero k] (L : ℕ)

omit [CharZero k] in
/-- The open line is the actual pullback of the identity cotangent line. -/
lemma openHodge_invertible (D : LevelData k L) :
    Scheme.Modules.IsInvertible (openHodge k L D) :=
  (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible
    D.atlas.descent.family).pullback D.quotient.inclusion

/-- Every test used in the canonical-lattice predicate has the accepted
unramified completion map, with its original classifying morphism. -/
lemma disk_completed_parameter (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    IsCompletedParameter k L D X T.disk :=
  tate_completed_local_parameter k L hL heven D T.level X T.base
    ⟨T.map, T.classifies⟩ T.disk T.extends_eq

/-- The exact discriminant expansion holds on each of the disks whose
lattice must be extended. -/
lemma disk_discriminant_expansion (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (d : Γ(power D.atlas.descent.family 24, ⊤))
    (hd : IsD2 D.atlas.descent.family d) : ExactD2 k L T.toTest d :=
  open_discriminant_full_tate_expansion k L hL heven D T.toTest d hd

/-- Schematic density of the specified inclusion of Laurent series. -/
lemma generic_schematic : IsSchemeTheoreticallyDominant (genericInclusion k) :=
  ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140.genericBase_schematic k

/-- A section in a framed module is determined by its generic pullback. -/
lemma pullback_injective_of_frame {X Y : Scheme} (f : Y ⟶ X)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (M : X.Modules) (s : Γ(M, ⊤)) (hs : IsFrame M ⊤ s) :
    Function.Injective (fun t : Γ(M, ⊤) => Scheme.Modules.pullbackLocalSection f t) := by
  intro t u htu
  obtain ⟨a, ha⟩ := (hs ⊤ le_rfl).2 t
  obtain ⟨b, hb⟩ := (hs ⊤ le_rfl).2 u
  rw [InitialHodgeSection.res_self] at ha hb
  change Scheme.Modules.pullbackLocalSection f t = Scheme.Modules.pullbackLocalSection f u at htu
  change a • s = t at ha
  change b • s = u at hb
  rw [← ha, ← hb, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.pullbackLocalSection_smul] at htu
  have hp := pullback_frame f M s hs
  have he : f.app ⊤ a = f.app ⊤ b := (hp _ le_rfl).1 (by
    simpa only [InitialHodgeSection.res_self] using htu)
  have hab := f.app_injective ⊤ he
  rw [← ha, ← hb, hab]

/-- Uniqueness in the canonical-lattice condition follows from schematic
density; it does not require a choice of coordinates or a new hypothesis. -/
lemma extendsGenerator_unique {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η ξ : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) (hξ : ExtendsGenerator k L H T ξ) : η = ξ := by
  letI := generic_schematic k
  letI : QuasiCompact (genericInclusion k) := by
    unfold genericInclusion
    infer_instance
  apply pullback_injective_of_frame (genericInclusion k) _ η hη.1
  have he := hη.2.trans hξ.2.symm
  apply (ConcreteCategory.bijective_of_isIso
    ((diskGenericIso k L H T).hom.app ((genericInclusion k) ⁻¹ᵁ ⊤))).1
  exact (GlobalFamilyDiscriminantR0180.res_bijective _ (by simp) le_top).1 he

/-- It suffices to construct the integral generator on each actual disk;
the required uniqueness is automatic. -/
lemma canonical_iff_exists {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) :
    Canonical k L H ↔ ∀ T : DiskTest k L D X,
      ∃ η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
        ExtendsGenerator k L H T η := by
  constructor
  · intro h T
    exact (h T).exists
  · intro h T
    obtain ⟨η, hη⟩ := h T
    exact ⟨η, hη, fun ξ hξ => extendsGenerator_unique k L H T ξ η hξ hη⟩

/-- Each actual disk carries a uniformizer from its own geometric cusp
stalk, and the specified local map sends it to a power-series uniformizer. -/
lemma disk_uniformizer (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    ∃ π : CuspStalk k L D X T.disk,
      IsLocalRing.maximalIdeal (CuspStalk k L D X T.disk) = Ideal.span {π} ∧
      IsLocalRing.maximalIdeal (PowerSeries k) =
        Ideal.span {CompletedLocalParameter.localMap k L D X T.disk π} :=
  (CompletedLocalParameter.isCompletedParameter_iff_uniformizer k L D X
    T.base T.disk T.extends_eq).1 (disk_completed_parameter k L hL heven D X T)

section LatticeRigidity
variable {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]

/-- A positive power equal to an integral unit forces the original generic
scalar to be an integral unit. This is the root step in lattice comparison. -/
lemma exists_unit_of_pow_eq_unit (a : K) (n : ℕ) (hn : 0 < n) (u : Rˣ)
    (ha : a ^ n = algebraMap R K (u : R)) :
    ∃ v : Rˣ, algebraMap R K (v : R) = a := by
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (IsIntegrallyClosed.isIntegral_iff.mpr ⟨(u : R), ha.symm⟩)
  have hbn : b ^ n = (u : R) := by
    apply IsFractionRing.injective R K
    rw [map_pow, hb, ha]
  have hbunit : IsUnit b := (isUnit_pow_iff (Nat.ne_of_gt hn)).1 (hbn ▸ u.isUnit)
  exact ⟨hbunit.unit, by simpa only [hbunit.unit_spec] using hb⟩

/-- Equality up to a scalar with unit positive power preserves the complete
rank-one lattice, not just its valuation or leading coefficient. -/
lemma span_eq_of_pow_eq_unit {M : Type*} [AddCommGroup M] [Module K M]
    [Module R M] [IsScalarTower R K M]
    (a : K) (n : ℕ) (hn : 0 < n) (u : Rˣ)
    (ha : a ^ n = algebraMap R K (u : R)) (e : M) :
    Submodule.span R {a • e} = Submodule.span R {e} := by
  obtain ⟨v, hv⟩ := exists_unit_of_pow_eq_unit a n hn u ha
  rw [← hv, algebraMap_smul]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    have h := Submodule.smul_mem (Submodule.span R {(v : R) • e})
      (↑(v⁻¹) : R) (Submodule.subset_span (Set.mem_singleton ((v : R) • e)))
    rw [smul_smul, v.inv_mul, one_smul] at h
    exact h
end LatticeRigidity

section Components
open TopologicalSpace
variable (D : LevelData k L) (X : Compactification k L D)

lemma compact_noetherian : IsNoetherian X.space := by
  letI := X.proper
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  letI : CompactSpace X.space := QuasiCompact.compactSpace_of_compactSpace X.projection
  exact {}

lemma compact_stalk_normal (x : X.space) :
    IsDomain (X.space.presheaf.stalk x) ∧ IsIntegrallyClosed (X.space.presheaf.stalk x) := by
  letI := X.smooth
  letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  exact Smooth.isDomain_and_isIntegrallyClosed_stalk X.projection x

/-- The extension must be constructed on every component; no connectedness
of the full-level base is imposed. -/
def compactComponent (x : X.space) : X.space.Opens := by
  letI := compact_noetherian k L D X
  exact ⟨irreducibleComponent x,
    (isOpen_irreducibleComponent_of_isDomain_stalk
      (fun y => (compact_stalk_normal k L D X y).1) x).1⟩

lemma compactComponent_integral (x : X.space) :
    IsIntegral (compactComponent k L D X x).toScheme := by
  letI := compact_noetherian k L D X
  letI : ∀ y : X.space, IsDomain (X.space.presheaf.stalk y) :=
    fun y => (compact_stalk_normal k L D X y).1
  letI : IsReduced X.space := isReduced_of_isReduced_stalk X.space
  letI : IrreducibleSpace (compactComponent k L D X x).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp (isIrreducible_irreducibleComponent (x := x))
  exact isIntegral_of_irreducibleSpace_of_isReduced _

lemma compactComponent_closed (x : X.space) :
    IsClosed ((compactComponent k L D X x : X.space.Opens) : Set X.space) :=
  isClosed_irreducibleComponent

lemma compactComponent_cover : (⨆ x, compactComponent k L D X x) = ⊤ := by
  apply top_unique
  intro x _
  exact (Opens.mem_iSup).2 ⟨x, mem_irreducibleComponent⟩

end Components

/-- General extension on an integral smooth curve. Its boundary lattices
are not asserted here; they must still be fixed using the Tate tests. -/
lemma exists_extension_integral_curve {Y U : Scheme} [IsIntegral Y] [IsNoetherian Y]
    (f : Y ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
    (j : U ⟶ Y) [IsOpenImmersion j] (M : U.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    ∃ N : Y.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty ((Scheme.Modules.pullback j).obj N ≅ M) := by
  apply hM.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
    (j := j)
  intro x
  letI := Smooth.isRegularLocalRing_stalk (f := f) x
  apply IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
  have hd : ringKrullDim (Y.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm x]
    exact (Order.coheight_le_krullDim _).trans
      (SmoothOfRelativeDimension.topologicalKrullDim_le f 1)
  exact hd.trans (by norm_num)

/-- Each actual compact component admits an extension of the restriction
of the actual open Hodge sheaf. The remaining construction has to choose
compatible Tate lattices on these extensions. -/
lemma component_extension (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) :
    ∃ N : (compactComponent k L D X x).toScheme.Modules,
      Scheme.Modules.IsInvertible N ∧ Nonempty
        ((Scheme.Modules.pullback (Limits.pullback.snd X.inclusion
          (compactComponent k L D X x).ι)).obj N ≅
        (Scheme.Modules.pullback (Limits.pullback.fst X.inclusion
          (compactComponent k L D X x).ι)).obj (openHodge k L D)) := by
  letI := compact_noetherian k L D X
  letI := compactComponent_integral k L D X x
  letI := X.openImmersion
  letI := X.smooth
  letI := X.proper
  let C := compactComponent k L D X x
  letI : IsClosedImmersion C.ι := IsClosedImmersion.of_isPreimmersion C.ι
    (by rw [Scheme.Opens.range_ι]; exact compactComponent_closed k L D X x)
  letI : CompactSpace C.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (C.ι ≫ X.projection)
  letI : IsLocallyNoetherian C.toScheme := LocallyOfFiniteType.isLocallyNoetherian C.ι
  letI : IsNoetherian C.toScheme := {}
  letI : SmoothOfRelativeDimension 1 (C.ι ≫ X.projection) :=
    smoothOfRelativeDimension_comp 0 1 C.ι X.projection
  exact exists_extension_integral_curve k (C.ι ≫ X.projection)
    (Limits.pullback.snd X.inclusion C.ι) _
      ((openHodge_invertible k L D).pullback (Limits.pullback.fst X.inclusion C.ι))

section GlobalExtension
open TopologicalSpace CategoryTheory.Limits

/-- Local factoriality trivializes the overlap on a locally integral scheme.
This is the library's affine-local argument with the domain chart chosen inside
an actual integral neighborhood, so it does not assume global connectedness. -/
lemma overlap_trivialization
    {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hcomp : ∀ z : X, ∃ C : X.Opens, z ∈ C ∧ IsIntegral C.toScheme) (W : X.Opens) {𝓛 : X.Modules}
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{0}).ringCatSheaf))
    (z : X) (hz : UniqueFactorizationMonoid (X.presheaf.stalk z)) :
    ∃ V : X.Opens, z ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{0}).ringCatSheaf) := by
  classical
  obtain ⟨C, hzC, hC⟩ := hcomp z
  letI := hC
  obtain ⟨U₀, hU₀, hz0, hUC⟩ := exists_isAffineOpen_mem_and_subset hzC
  letI : Nonempty U₀ := ⟨⟨z, hz0⟩⟩
  letI : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE hUC)
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : Nonempty U₀ := ⟨⟨z, hz0⟩⟩

  let S : Type := Γ(X, U₀)
  let 𝔭 : Ideal S := (hU₀.primeIdealOf ⟨z, hz0⟩).asIdeal
  haveI h𝔭 : 𝔭.IsPrime := (hU₀.primeIdealOf ⟨z, hz0⟩).isPrime

  let A : Scheme.{0} := (W ⊓ U₀ : X.Opens)
  let f : A ⟶ Spec (CommRingCat.of S) := X.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀) ≫ hU₀.isoSpec.hom
  haveI : IsOpenImmersion f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of S)) := inferInstance
  haveI : QuasiCompact f := inferInstance
  haveI : QuasiSeparated f := inferInstance

  let ι1 : Spec (CommRingCat.of (Localization.Away (1 : S))) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (1 : S))))
  let ι𝔭 : Spec (CommRingCat.of (Localization.AtPrime 𝔭)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))
  let ψ : Localization.Away (1 : S) →+* Localization.AtPrime 𝔭 :=
    IsLocalization.Away.lift (1 : S) (g := algebraMap S (Localization.AtPrime 𝔭)) (by simp)
  have hψ : ψ.comp (algebraMap S (Localization.Away (1 : S))) = algebraMap S (Localization.AtPrime 𝔭) :=
    IsLocalization.Away.lift_comp (1 : S) _

  let 𝓛A : A.Modules := (Scheme.Modules.pullback (W ⊓ U₀).ι).obj 𝓛
  have hAinv : Scheme.Modules.IsInvertible 𝓛A := by
    constructor
    intro y
    obtain ⟨U, hyU, hUW, ⟨eU⟩⟩ := hW y.1 y.2.1
    let V : A.Opens := (W ⊓ U₀).ι ⁻¹ᵁ U
    have hyV : y ∈ V := hyU
    refine ⟨V, hyV, ⟨?_⟩⟩
    let j : (V : Scheme.{0}) ⟶ (U : Scheme.{0}) := (W ⊓ U₀).ι.resLE U V le_rfl
    have hj : j ≫ U.ι = V.ι ≫ (W ⊓ U₀).ι := Scheme.Hom.resLE_comp_ι _ _
    exact (Scheme.Modules.pullbackComp V.ι (W ⊓ U₀).ι).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hj.symm).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp j U.ι).app 𝓛).symm ≪≫ (Scheme.Modules.pullback j).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso j
  let 𝓛₁ : (pullback f ι1).Modules := (Scheme.Modules.pullback (pullback.fst f ι1)).obj 𝓛A
  have h₁ : Scheme.Modules.IsInvertible 𝓛₁ := hAinv.pullback _
  let 𝓛₂ : (pullback f ι1).Modules := SheafOfModules.unit (pullback f ι1).ringCatSheaf
  have h₂ : Scheme.Modules.IsInvertible 𝓛₂ := Scheme.Modules.isInvertible_unit _

  let φ𝔭 : pullback f ι𝔭 ⟶ pullback f ι1 :=
    pullback.lift (pullback.fst f ι𝔭) (pullback.snd f ι𝔭 ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])

  haveI : IsDomain S := U₀.topIso.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
  letI : Algebra S (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk (⟨z, hz0⟩ : U₀)
  let eSt : X.presheaf.stalk z ≃ₐ[S] Localization.AtPrime 𝔭 :=
    @IsLocalization.algEquiv S _ 𝔭.primeCompl (X.presheaf.stalk z) _ _ (hU₀.isLocalization_stalk ⟨z, hz0⟩)
      (Localization.AtPrime 𝔭) _ _ _
  haveI : UniqueFactorizationMonoid (Localization.AtPrime 𝔭) := MulEquiv.uniqueFactorizationMonoid eSt.toMulEquiv hz

  obtain ⟨e𝔭⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
    (pullback.snd f ι𝔭) (h₁.pullback φ𝔭)

  have h1𝔭 : (1 : S) ∉ 𝔭 := (Ideal.ne_top_iff_one 𝔭).mp h𝔭.ne_top
  obtain ⟨r, hr, ψr, hψr, ⟨er⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
      f 𝔭 (1 : S) h1𝔭 ψ hψ 𝓛₁ 𝓛₂ h₁ h₂ ⟨e𝔭 ≪≫ (Scheme.Modules.pullbackUnitIso φ𝔭).symm⟩

  let ιr : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  let φr : pullback f ιr ⟶ pullback f ι1 :=
    pullback.lift (pullback.fst f ιr) (pullback.snd f ιr ≫ Spec.map (CommRingCat.ofHom ψr))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr])
  have memD : ∀ (x : X) (hx : x ∈ U₀), hU₀.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen r ↔ x ∈ X.basicOpen r := by
    intro x hx
    have h1 : hU₀.primeIdealOf ⟨x, hx⟩ ∈ hU₀.fromSpec ⁻¹ᵁ X.basicOpen r ↔ x ∈ X.basicOpen r := by
      show hU₀.fromSpec (hU₀.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
      rw [hU₀.fromSpec_primeIdealOf]
    rw [hU₀.fromSpec_preimage_basicOpen] at h1
    exact h1
  refine ⟨X.basicOpen r, (memD z hz0).mp hr, ⟨?_⟩⟩

  let h : pullback f ιr ⟶ X := pullback.fst f ιr ≫ (W ⊓ U₀).ι
  have hfapp : ∀ a : A, f a = hU₀.primeIdealOf ⟨a.1, a.2.2⟩ := fun a => by
    have ha : (X.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀)) a = ⟨a.1, a.2.2⟩ := Subtype.ext (Scheme.homOfLE_apply _ a)
    show (X.homOfLE _ ≫ hU₀.isoSpec.hom) a = hU₀.isoSpec.hom ⟨a.1, a.2.2⟩
    rw [Scheme.Hom.comp_apply, ha]
  have hrange : Set.range (W ⊓ X.basicOpen r).ι.base = Set.range h.base := by
    rw [Scheme.Opens.range_ι]
    have hιr : Set.range ιr.base = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := by
      change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r))) = _
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    ext x
    constructor
    · rintro ⟨hxW, hxr⟩
      let a : A := ⟨x, hxW, X.basicOpen_le r hxr⟩
      have hfa : f a ∈ Set.range ιr.base := by
        rw [hιr, hfapp]; exact (memD x _).mpr hxr
      obtain ⟨t, ht⟩ := hfa
      obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback a t ht.symm
      refine ⟨p, ?_⟩
      show ((W ⊓ U₀).ι) ((pullback.fst f ιr) p) = x
      rw [hp1]; rfl
    · rintro ⟨p, rfl⟩
      show ((W ⊓ U₀).ι ((pullback.fst f ιr) p)) ∈ (W ⊓ X.basicOpen r : Set X)
      refine ⟨((pullback.fst f ιr) p).2.1, ?_⟩
      have hc : f ((pullback.fst f ιr) p) = ιr ((pullback.snd f ιr) p) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have hmemr : f ((pullback.fst f ιr) p) ∈ Set.range ιr.base := ⟨_, hc.symm⟩
      rw [hιr] at hmemr
      have : f ((pullback.fst f ιr) p) ∈ PrimeSpectrum.basicOpen r := hmemr
      rw [hfapp] at this
      exact (memD _ _).mp this
  haveI : IsOpenImmersion h := inferInstance
  let e := IsOpenImmersion.isoOfRangeEq (W ⊓ X.basicOpen r).ι h hrange
  have he : e.hom ≫ h = (W ⊓ X.basicOpen r).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hφr : φr ≫ pullback.fst f ι1 = pullback.fst f ιr := pullback.lift_fst _ _ _

  have T1 : (Scheme.Modules.pullback (pullback.fst f ιr)).obj 𝓛A ≅ SheafOfModules.unit (pullback f ιr).ringCatSheaf :=
    (Scheme.Modules.pullbackCongr hφr.symm).app 𝓛A ≪≫ ((Scheme.Modules.pullbackComp φr (pullback.fst f ι1)).app 𝓛A).symm ≪≫
      er ≪≫ Scheme.Modules.pullbackUnitIso φr
  have T2 : (Scheme.Modules.pullback h).obj 𝓛 ≅ SheafOfModules.unit (pullback f ιr).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp (pullback.fst f ιr) (W ⊓ U₀).ι).app 𝓛).symm ≪≫ T1
  exact (Scheme.Modules.pullbackCongr he.symm).app 𝓛 ≪≫ ((Scheme.Modules.pullbackComp e.hom h).app 𝓛).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso T2 ≪≫ Scheme.Modules.pullbackUnitIso e.hom


/-- Local triviality over an open subset, using actual restricted sheaves. -/
def LocTriv {X : Scheme.{0}} (M : X.Modules) (W : X.Opens) : Prop :=
  ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

lemma restrict_iso_further {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.Opens) (hW : j.opensRange ≤ W) {M N : X.Modules}
    (e : (Scheme.Modules.pullback W.ι).obj M ≅ (Scheme.Modules.pullback W.ι).obj N) :
    Nonempty ((Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N) := by
  have hr : Set.range j.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hW
  let j' := IsOpenImmersion.lift W.ι j hr
  have hj : j' ≫ W.ι = j := IsOpenImmersion.lift_fac W.ι j hr
  exact ⟨((Scheme.Modules.pullbackCongr hj).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp j' W.ι).app M).symm ≪≫
    (Scheme.Modules.pullback j').mapIso e ≪≫
    (Scheme.Modules.pullbackComp j' W.ι).app N ≪≫
    (Scheme.Modules.pullbackCongr hj).app N⟩

/-- Extend across a noetherian locally factorial scheme by enlarging the
open of local triviality. This allows multiple disjoint integral components. -/
lemma exists_extension_locally_integral {X U : Scheme.{0}} [IsNoetherian X]
    (hcomp : ∀ z : X, ∃ C : X.Opens, z ∈ C ∧ IsIntegral C.toScheme)
    (hfact : ∀ z : X, UniqueFactorizationMonoid (X.presheaf.stalk z))
    (j : U ⟶ X) [IsOpenImmersion j] (M : U.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty ((Scheme.Modules.pullback j).obj N ≅ M) := by
  classical
  let S : Set X.Opens := fun W => j.opensRange ≤ W ∧
    ∃ N : X.Modules, LocTriv N W ∧ Nonempty ((Scheme.Modules.pullback j).obj N ≅ M)
  have hS : j.opensRange ∈ S := by
    obtain ⟨N, hN, e⟩ := hM.exists_locallyTrivial_opensRange_nonempty_pullback_iso j
    exact ⟨le_rfl, N, hN, e⟩
  have hwf : WellFounded ((· > ·) : X.Opens → X.Opens → Prop) := wellFounded_gt
  obtain ⟨W, ⟨hjW, N, hN, ⟨eN⟩⟩, hmax⟩ := hwf.has_min S ⟨_, hS⟩
  by_cases htop : W = ⊤
  · subst htop
    refine ⟨N, ⟨?_⟩, ⟨eN⟩⟩
    intro x
    obtain ⟨V, hx, _, he⟩ := hN x trivial
    exact ⟨V, hx, he⟩
  · obtain ⟨z, hz⟩ : ∃ z : X, z ∉ W := by
      by_contra h; push Not at h
      exact htop (top_unique fun x _ => h x)
    obtain ⟨V, hzV, eV⟩ := overlap_trivialization hcomp W hN z (hfact z)
    obtain ⟨N', hN', ⟨e'⟩⟩ :=
      Scheme.Modules.exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
        W V hN eV
    have hmem : W ⊔ V ∈ S := by
      obtain ⟨e''⟩ := restrict_iso_further j W hjW e'
      exact ⟨hjW.trans le_sup_left, N', hN', ⟨e'' ≪≫ eN⟩⟩
    have hlt : W ⊔ V > W := lt_of_le_of_ne le_sup_left
      (fun h => hz (h.symm ▸ (Opens.mem_sup.2 (Or.inr hzV))))
    exact absurd (hmax _ hmem) (not_not.2 hlt)

/-- There is a global invertible extension with the required actual open
identification. Its canonical Tate-lattice property remains to be proved. -/
lemma extension_exists (D : LevelData k L) (X : Compactification k L D) :
    Nonempty (Extension k L D X) := by
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  letI := X.smooth
  have hc : ∀ z : X.space, ∃ C : X.space.Opens, z ∈ C ∧ IsIntegral C.toScheme :=
    fun z => ⟨compactComponent k L D X z, mem_irreducibleComponent,
      compactComponent_integral k L D X z⟩
  have hf : ∀ z : X.space, UniqueFactorizationMonoid (X.space.presheaf.stalk z) := by
    intro z
    letI := (compact_stalk_normal k L D X z).1
    letI := Smooth.isRegularLocalRing_stalk (f := X.projection) z
    apply IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    have hd : ringKrullDim (X.space.presheaf.stalk z) ≤ 1 := by
      rw [ringKrullDim_stalk_eq_coheight,
        ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X.space)).symm z]
      exact (Order.coheight_le_krullDim _).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le X.projection 1)
    exact hd.trans (by norm_num)
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_extension_locally_integral hc hf X.inclusion
    (openHodge k L D) (openHodge_invertible k L D)
  exact ⟨⟨N, hN, e⟩⟩

#print axioms extension_exists

end GlobalExtension

section DiskCoefficients
open OpenDiscriminantFullTateExpansionR0182

lemma iso_one_frame {Y : Scheme.{0}} {M : Y.Modules}
    (e : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ M) :
    IsFrame M ⊤ (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(Y, ⊤))) := by
  apply GlobalFamilyDiscriminantR0180.frame_iso
  intro U h
  change Function.Bijective (fun a : Γ(Y, U) =>
    a * (Y.presheaf.map (homOfLE h).op) 1)
  simp only [map_one, mul_one]
  exact ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

lemma hodgeGenerator_frame (δ : CurveFrame k L) :
    IsFrame (Hodge (LaurentSeries k) (TateCurve k L)) ⊤ (hodgeGenerator k L δ) :=
  frame_restrict _ (by simp) _
    (pullback_frame _ _ _ (iso_one_frame δ))

lemma diskFrame_exists {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    ∃ η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
      IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η := by
  obtain ⟨e⟩ := (H.invertible.pullback T.disk).nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨Scheme.Modules.Hom.app e.inv ⊤ (1 : Γ(Disk k, ⊤)), iso_one_frame e.symm⟩

/-- The actual generic differential restriction, including the specified
open identification and canonical classifying differential comparison. -/
def diskRestriction {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤)) :
    Γ(Hodge (LaurentSeries k) (TateCurve k L), ⊤) :=
  transportSection (genericInclusion k) _ _ (diskGenericIso k L H T) η

lemma diskRestriction_frame {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η) :
    IsFrame (Hodge (LaurentSeries k) (TateCurve k L)) ⊤ (diskRestriction k L H T η) :=
  frame_restrict _ (by simp) _
    (GlobalFamilyDiscriminantR0180.frame_iso (diskGenericIso k L H T) _
      (pullback_frame _ _ η hη))

lemma diskRestriction_smul {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (a : PowerSeries k) (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤)) :
    diskRestriction k L H T (scalar (PowerSeries k) a • η) =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) a) •
        diskRestriction k L H T η := by
  unfold diskRestriction
  rw [transportSection_smul]
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) a).symm

lemma frame_coefficient_unit {Y : Scheme.{0}} {M : Y.Modules}
    (η : Γ(M, ⊤)) (hη : IsFrame M ⊤ η) (a : Γ(Y, ⊤))
    (ha : IsFrame M ⊤ (a • η)) : IsUnit a := by
  have hη' : Function.Bijective (fun b : Γ(Y, ⊤) => b • η) := by
    simpa only [InitialHodgeSection.res_self] using hη ⊤ le_rfl
  obtain ⟨b, hb⟩ := (ha ⊤ le_rfl).2 η
  have hba : b * a = 1 := hη'.1 (by
    simpa only [InitialHodgeSection.res_self, mul_smul, one_smul] using hb)
  exact ⟨⟨a, b, by rw [mul_comm]; exact hba, hba⟩, rfl⟩

/-- Every integral frame expresses the prescribed generic differential in a
unique, nonzero Laurent coefficient through the actual geometric map. -/
lemma disk_coefficient_exists {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η) :
    ∃! a : LaurentSeries k, scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential := by
  have h := diskRestriction_frame k L H T η hη ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at h
  have hs := ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
  exact (h.comp hs).existsUnique _

/-- A prescribed generic frame extends to an integral frame precisely when
its actual Laurent coefficient is the image of a power-series unit. -/
lemma extendsGenerator_iff_coefficient_unit
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential) :
    (∃ ξ : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
      ExtendsGenerator k L H T ξ) ↔
    ∃ u : (PowerSeries k)ˣ, algebraMap (PowerSeries k) (LaurentSeries k) (u : PowerSeries k) = a := by
  constructor
  · rintro ⟨ξ, hξ⟩
    obtain ⟨b, hb⟩ := (hη ⊤ le_rfl).2 ξ
    rw [InitialHodgeSection.res_self] at hb
    change b • η = ξ at hb
    have hbunit : IsUnit b := frame_coefficient_unit η hη b (by rw [hb]; exact hξ.1)
    let c : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom b
    have hc : IsUnit c := hbunit.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
    have hcb : scalar (PowerSeries k) c = b := by
      exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom_inv_id b
    refine ⟨hc.unit, ?_⟩
    rw [hc.unit_spec]
    have hh : scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) c) •
        diskRestriction k L H T η = scalar (LaurentSeries k) a • diskRestriction k L H T η := by
      rw [← diskRestriction_smul, hcb, hb, ha]
      exact hξ.2
    have hinj := diskRestriction_frame k L H T η hη ⊤ le_rfl
    rw [InitialHodgeSection.res_self] at hinj
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).1 (hinj.1 hh)
  · rintro ⟨u, hu⟩
    refine ⟨scalar (PowerSeries k) (u : PowerSeries k) • η, ?_, ?_⟩
    · exact InitialHodgeSection.unit_frame _ η hη
        (u.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom.toMonoidHom)
    · change diskRestriction k L H T _ = _
      rw [diskRestriction_smul, hu, ha]

lemma disk_coefficient_ne_zero {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential) : a ≠ 0 := by
  have hu := frame_coefficient_unit (diskRestriction k L H T η)
    (diskRestriction_frame k L H T η hη) (scalar (LaurentSeries k) a)
    (by rw [ha]; exact hodgeGenerator_frame k L T.differential)
  have hv := hu.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom.hom
  have he : (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (scalar (LaurentSeries k) a) = a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id a
  rw [he] at hv
  exact hv.ne_zero

/-- The accepted full D2 expansion expressed in an arbitrary integral frame.
The coefficient includes the entire discriminant series, not only its order. -/
lemma disk_discriminant_coefficient (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential)
    (d : Γ(power D.atlas.descent.family 24, ⊤))
    (hd : IsD2 D.atlas.descent.family d) :
    pullAmbientPower k L T.toTest 24 d =
      scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L * a^24) •
        ArithmeticThetaTensorPower.tensorPowerSection (Puncture k)
          (Hodge (LaurentSeries k) (TateCurve k L)) 24 ⊤ (diskRestriction k L H T η) := by
  have h := disk_discriminant_expansion k L hL heven D X T d hd
  unfold ExactD2 at h
  rw [← ha, InitialHodgeSection.tensor_smul, smul_smul] at h
  simpa only [scalar, map_mul, map_pow] using h

omit [CharZero k] in
lemma laurent_coeff_negative (b : PowerSeries k) (i : ℤ) (hi : i < 0) :
    (algebraMap (PowerSeries k) (LaurentSeries k) b).coeff i = 0 := by
  rw [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_apply,
    HahnSeries.embDomain_of_notMem_range]
  rintro ⟨n, hn⟩
  simp only [Nat.castOrderEmbedding_apply] at hn
  omega

omit [CharZero k] in
lemma laurent_order_of_powerSeries (b : PowerSeries k) (n : ℕ)
    (hb : b.order = n) :
    (algebraMap (PowerSeries k) (LaurentSeries k) b).order = (n : ℤ) := by
  have hc := (PowerSeries.order_eq_nat.mp hb).1
  have hc' : (algebraMap (PowerSeries k) (LaurentSeries k) b).coeff (n : ℤ) ≠ 0 := by
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_apply_coeff] using hc
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc')
  apply (HahnSeries.le_order_iff_forall (HahnSeries.ne_zero_of_coeff_ne_zero hc')).2
  intro j hj
  by_cases hj0 : 0 ≤ j
  · lift j to ℕ using hj0 with m
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_apply_coeff] using
      (PowerSeries.order_eq_nat.mp hb).2 m (by exact_mod_cast hj)
  · exact laurent_coeff_negative k b j (lt_of_not_ge hj0)

omit [CharZero k] in
/-- A nonzero Laurent series is an integral unit exactly when its order is zero. -/
lemma laurent_unit_iff_order_zero (a : LaurentSeries k) (ha : a ≠ 0) :
    (∃ u : (PowerSeries k)ˣ,
      algebraMap (PowerSeries k) (LaurentSeries k) (u : PowerSeries k) = a) ↔ a.order = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact laurent_order_of_powerSeries k u 0 (PowerSeries.order_zero_of_unit u.isUnit)
  · intro ho
    have hc : PowerSeries.constantCoeff a.powerSeriesPart ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff]
      simpa only [Nat.cast_zero, add_zero] using (HahnSeries.coeff_order_eq_zero.not.mpr ha)
    have hu : IsUnit a.powerSeriesPart :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc)
    refine ⟨hu.unit, ?_⟩
    rw [hu.unit_spec]
    change HahnSeries.ofPowerSeries ℤ k a.powerSeriesPart = a
    rw [LaurentSeries.ofPowerSeries_powerSeriesPart, ho, neg_zero,
      ← HahnSeries.C_apply, HahnSeries.C_one, one_mul]

lemma extendsGenerator_iff_order_zero
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential) :
    (∃ ξ : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
      ExtendsGenerator k L H T ξ) ↔ a.order = 0 :=
  (extendsGenerator_iff_coefficient_unit k L H T η hη a ha).trans
    (laurent_unit_iff_order_zero k a (disk_coefficient_ne_zero k L H T η hη a ha))

lemma discriminant_laurent_order (hL : 0 < L) :
    (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L).order = (2 * L : ℕ) := by
  exact laurent_order_of_powerSeries k _ _
    (ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.series_order k L hL)

lemma discriminant_laurent_ne_zero (hL : 0 < L) :
    ArithmeticThetaUnaryKatoPowerR0160.discriminant k L ≠ 0 := by
  intro hz
  have ho := discriminant_laurent_order k L hL
  rw [hz, HahnSeries.order_zero] at ho
  omega

lemma discriminant_coefficient_order (hL : 0 < L) (a : LaurentSeries k) (ha : a ≠ 0) :
    (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L * a^24).order =
      (2 * L : ℕ) + 24 * a.order := by
  rw [HahnSeries.order_mul (discriminant_laurent_ne_zero k L hL) (pow_ne_zero _ ha),
    discriminant_laurent_order k L hL, HahnSeries.order_pow, nsmul_eq_mul]
  norm_num

/-- Orders of actual completed stalk germs agree with intrinsic DVR length. -/
lemma disk_localMap_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (a : CuspStalk k L D X T.disk) :
    (CompletedLocalParameter.localMap k L D X T.disk a).order =
      Ring.ord (CuspStalk k L D X T.disk) a := by
  obtain ⟨hdom, hdvr⟩ := CompletedLocalParameter.cuspStalk_dvr k L D X T.base T.disk T.extends_eq
  letI := hdom
  letI := hdvr
  obtain ⟨π, hπ, hσ⟩ := disk_uniformizer k L hL heven D X T
  have hp : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hπ
  have hassoc : Associated (CompletedLocalParameter.localMap k L D X T.disk π)
      (PowerSeries.X : PowerSeries k) :=
    Ideal.span_singleton_eq_span_singleton.mp (hσ.symm.trans PowerSeries.maximalIdeal_eq_span_X)
  obtain ⟨u, hu⟩ := hassoc
  have ho : (CompletedLocalParameter.localMap k L D X T.disk π).order = 1 := by
    have hh := congrArg PowerSeries.order hu
    simpa only [PowerSeries.order_mul, PowerSeries.order_zero_of_unit u.isUnit,
      add_zero, PowerSeries.order_X] using hh
  exact ArithmeticThetaFormalOrder.expansion_order _ k _ π hp ho a

lemma disk_localMap_injective (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    Function.Injective (CompletedLocalParameter.localMap k L D X T.disk) := by
  obtain ⟨hdom, hdvr⟩ := CompletedLocalParameter.cuspStalk_dvr k L D X T.base T.disk T.extends_eq
  letI := hdom
  letI := hdvr
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  by_contra hn
  have ho := disk_localMap_order k L hL heven D X T a
  rw [ha, PowerSeries.order_zero] at ho
  exact Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hn) ho.symm

/-- The order of a nonzero disk germ after embedding into Laurent series. -/
lemma disk_localMap_laurent_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (a : CuspStalk k L D X T.disk) (ha : a ≠ 0) :
    (algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk a)).order =
        ((Ring.ord (CuspStalk k L D X T.disk) a).toNat : ℤ) := by
  obtain ⟨hdom, hdvr⟩ := CompletedLocalParameter.cuspStalk_dvr k L D X T.base T.disk T.extends_eq
  letI := hdom
  letI := hdvr
  apply laurent_order_of_powerSeries
  rw [disk_localMap_order k L hL heven D X T]
  exact (ENat.natCast_toNat_eq_self.mpr
    (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha))).symm

omit [CharZero k] in
lemma laurent_order_div (a b : LaurentSeries k) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a / b).order = a.order - b.order := by
  have hi : (b⁻¹).order = -b.order := by
    have h := HahnSeries.order_mul hb (inv_ne_zero hb)
    rw [mul_inv_cancel₀ hb, HahnSeries.order_one] at h
    omega
  rw [div_eq_mul_inv, HahnSeries.order_mul ha (inv_ne_zero hb), hi, sub_eq_add_neg]

/-- Rational germ coefficients are measured by numerator minus denominator
orders through the specified completion map. -/
lemma disk_rational_germ_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (a b : CuspStalk k L D X T.disk) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X T.disk a)) /
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X T.disk b))).order =
      ((Ring.ord (CuspStalk k L D X T.disk) a).toNat : ℤ) -
        ((Ring.ord (CuspStalk k L D X T.disk) b).toNat : ℤ) := by
  have hinj := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)).comp
    (disk_localMap_injective k L hL heven D X T)
  have hzero : algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk 0) = 0 := by simp
  have hna : algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk a) ≠ 0 :=
    fun h => ha (hinj (h.trans hzero.symm))
  have hnb : algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk b) ≠ 0 :=
    fun h => hb (hinj (h.trans hzero.symm))
  rw [laurent_order_div k _ _ hna hnb,
    disk_localMap_laurent_order k L hL heven D X T a ha,
    disk_localMap_laurent_order k L hL heven D X T b hb]

#print axioms disk_rational_germ_order

#print axioms extendsGenerator_iff_order_zero
#print axioms disk_discriminant_coefficient

#print axioms disk_coefficient_exists
#print axioms extendsGenerator_iff_coefficient_unit
end DiskCoefficients

section BoundaryTwists
open ArithmeticThetaSheafTensor ArithmeticThetaPullback

/-- Invertibility is preserved by the same sheafified tensor used in the
frozen Hodge-power definitions. No alternative monoidal presentation is used. -/
lemma sheafTensor_invertible {Y : Scheme.{0}} {M N : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) :
    Scheme.Modules.IsInvertible (sheafTensor Y M N) := by
  constructor
  intro y
  obtain ⟨U, hyU, ⟨eM⟩⟩ := hM.exists_trivialization y
  obtain ⟨V, hyV, ⟨eN⟩⟩ := hN.exists_trivialization y
  let W := U ⊓ V
  obtain ⟨eMW⟩ := restrict_iso_further W.ι U
    (by simpa only [Scheme.Opens.opensRange_ι] using (inf_le_left : W ≤ U))
    (eM ≪≫ (Scheme.Modules.pullbackUnitIso U.ι).symm)
  obtain ⟨eNW⟩ := restrict_iso_further W.ι V
    (by simpa only [Scheme.Opens.opensRange_ι] using (inf_le_right : W ≤ V))
    (eN ≪≫ (Scheme.Modules.pullbackUnitIso V.ι).symm)
  refine ⟨W, ⟨hyU, hyV⟩, ⟨?_⟩⟩
  exact pullback_sheafTensor_iso W.toScheme Y W.ι M N ≪≫
    sheafTensorCongr W.toScheme
      (eMW ≪≫ Scheme.Modules.pullbackUnitIso W.ι)
      (eNW ≪≫ Scheme.Modules.pullbackUnitIso W.ι) ≪≫
    tensorLeftUnitIso W.toScheme _

/-- A line trivialized on the actual open base gives a genuine global twist
of an extension, retaining that chosen trivialization in its open isomorphism. -/
def twistExtension {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (J : X.space.Modules)
    (hJ : Scheme.Modules.IsInvertible J)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf) : Extension k L D X where
  line := sheafTensor X.space J H.line
  invertible := sheafTensor_invertible hJ H.invertible
  onOpen := pullback_sheafTensor_iso _ _ X.inclusion J H.line ≪≫
    sheafTensorCongr _ eJ H.onOpen ≪≫ tensorLeftUnitIso _ _

#print axioms sheafTensor_invertible
#print axioms twistExtension
end BoundaryTwists

section BoundaryIdeals
open scoped MonoidalCategory

/-- The ideal of the actual reduced boundary point on the compactification. -/
def cuspIdeal (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) : X.space.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X.space), isClosed_closure⟩

/-- On an actual affine neighborhood the cusp ideal is the point's prime
ideal, including its scheme-theoretic multiplicity. -/
lemma cuspIdeal_affine (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (U : X.space.affineOpens) (hx : x ∈ (U : X.space.Opens)) :
    (cuspIdeal k L D X x).ideal U = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hinj : Function.Injective U.2.fromSpec := U.2.fromSpec.isOpenEmbedding.injective
  have hpre : (U.2.fromSpec : _ → X.space) ⁻¹' ({x} : Set X.space) =
      {U.2.primeIdealOf ⟨x, hx⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply hinj
      rw [hz, IsAffineOpen.fromSpec_primeIdealOf]
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  have hcl : (U.2.fromSpec : _ → X.space) ⁻¹' closure ({x} : Set X.space) =
      closure ((U.2.fromSpec : _ → X.space) ⁻¹' {x}) :=
    U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      U.2.fromSpec.continuous _
  rw [cuspIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    ((U.2.fromSpec : _ → X.space) ⁻¹' closure ({x} : Set X.space)) = _
  rw [hcl, hpre, PrimeSpectrum.vanishingIdeal_closure,
    PrimeSpectrum.vanishingIdeal_singleton]

/-- The actual germ of the reduced cusp ideal is the full maximal ideal of
the geometric stalk. -/
lemma cuspIdeal_germ (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (U : X.space.affineOpens) (hx : x ∈ (U : X.space.Opens)) :
    Ideal.map (X.space.presheaf.germ (U : X.space.Opens) x hx).hom
      ((cuspIdeal k L D X x).ideal U) =
        IsLocalRing.maximalIdeal (X.space.presheaf.stalk x) := by
  letI := X.space.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : X.space.Opens))
  letI := U.2.isLocalization_stalk ⟨x, hx⟩
  rw [cuspIdeal_affine]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal (X.space.presheaf.stalk x)

/-- The specified completed map sends the entire geometric maximal ideal
onto the power-series maximal ideal, rather than just into it. -/
lemma disk_localMap_maximalIdeal (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    Ideal.map (CompletedLocalParameter.localMap k L D X T.disk)
      (IsLocalRing.maximalIdeal (CuspStalk k L D X T.disk)) =
        IsLocalRing.maximalIdeal (PowerSeries k) := by
  obtain ⟨π, hπ, hσ⟩ := disk_uniformizer k L hL heven D X T
  rw [hπ, Ideal.map_span, Set.image_singleton, ← hσ]

/-- Mapping the actual cusp ideal through an affine germ and the fixed
completion map gives exactly the ideal generated by the disk parameter. -/
lemma cuspIdeal_completed_germ (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (U : X.space.affineOpens) (hU : T.disk (closedPoint k) ∈ (U : X.space.Opens)) :
    Ideal.map ((CompletedLocalParameter.localMap k L D X T.disk).comp
      (X.space.presheaf.germ (U : X.space.Opens) (T.disk (closedPoint k)) hU).hom)
      ((cuspIdeal k L D X (T.disk (closedPoint k))).ideal U) =
        Ideal.span {(PowerSeries.X : PowerSeries k)} := by
  rw [← Ideal.map_map, cuspIdeal_germ, disk_localMap_maximalIdeal k L hL heven,
    PowerSeries.maximalIdeal_eq_span_X]

#print axioms cuspIdeal_completed_germ

/-- The actual pullback ideal on the whole disk has multiplicity exactly
one at its center. The equality uses the fixed completion map. -/
lemma cuspIdeal_disk_ideal (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
      (((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).ideal
        ⟨⊤, isAffineOpen_top _⟩) = Ideal.span {(PowerSeries.X : PowerSeries k)} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.space.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (T.disk (closedPoint k))) isOpen_univ
  have hpre : T.disk ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem T.disk hxU
  have hle : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U := hpre.ge
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ T.disk ⟨U, hU⟩
    ⟨⊤, isAffineOpen_top _⟩ hle, Ideal.map_map]
  have he : (T.disk.appLE U ⊤ hle ≫
      (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom) =
      X.space.presheaf.germ U (T.disk (closedPoint k)) hxU ≫
        Scheme.stalkClosedPointTo T.disk := by
    erw [Scheme.germ_stalkClosedPointTo]
    simp only [Scheme.Hom.appLE, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom]
    rfl
  change Ideal.map (T.disk.appLE U ⊤ hle ≫
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom).hom _ = _
  rw [he]
  exact cuspIdeal_completed_germ k L hL heven D X T ⟨U, hU⟩ hxU

#print axioms cuspIdeal_disk_ideal

lemma cuspIdeal_invertible (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    (cuspIdeal k L D X x).IsInvertible := by
  letI := compact_noetherian k L D X
  letI := X.smooth
  have hclosed := BoundaryGeometry.boundary_point_closed k L D X x hx
  obtain ⟨hdom, hdvr⟩ := BoundaryGeometry.dvr_of_closed X.projection x hclosed
  letI := hdom
  letI := hdvr
  apply Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
  · exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  · intro y hy
    rw [hclosed.closure_eq, Set.mem_singleton_iff] at hy
    subst y
    exact ⟨Smooth.isRegularLocalRing_stalk (f := X.projection) x,
      (IsDiscreteValuationRing.ringKrullDim_eq_one _).le.trans (by norm_num)⟩

lemma cuspIdeal_support (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    ((cuspIdeal k L D X x).support : Set X.space) = {x} := by
  simp only [cuspIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (BoundaryGeometry.boundary_point_closed k L D X x hx).closure_eq

/-- Both signs of a boundary point twist are genuine invertible modules,
and both restrict to the trivial line on the specified open base. -/
lemma cuspIdeal_lines (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    Scheme.Modules.IsInvertible (cuspIdeal k L D X x).module ∧
    Scheme.Modules.IsInvertible (cuspIdeal k L D X x).invModule ∧
    Nonempty ((Scheme.Modules.pullback X.inclusion).obj (cuspIdeal k L D X x).module ≅
      𝟙_ (OpenBase k L D).Modules) ∧
    Nonempty ((Scheme.Modules.pullback X.inclusion).obj (cuspIdeal k L D X x).invModule ≅
      𝟙_ (OpenBase k L D).Modules) := by
  have hi := cuspIdeal_invertible k L D X x hx
  have hs : Disjoint (Set.range X.inclusion.base)
      ((cuspIdeal k L D X x).support : Set X.space) := by
    rw [cuspIdeal_support k L D X x hx, Set.disjoint_singleton_right]
    exact hx
  exact ⟨hi.isInvertible_module, hi.isInvertible_invModule,
    (cuspIdeal k L D X x).nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
      hi X.inclusion hs _ (Or.inl rfl),
    (cuspIdeal k L D X x).nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
      hi X.inclusion hs _ (Or.inr rfl)⟩

#print axioms cuspIdeal_lines

open CategoryTheory.Limits in
/-- The ideal-module comparison commutes with the actual inclusions into
the structure sheaves. This fixes the open trivialization used for twisting. -/
lemma ideal_pullback_inclusion {Y Z : Scheme.{0}} (I : Y.IdealSheafData)
    (f : Z ⟶ Y) :
    I.pullbackModuleComparison f ≫ (I.comap f).moduleι =
      (Scheme.Modules.pullback f).map I.moduleι ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom
  have h : I.moduleToPushforwardComapModule f ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map (I.comap f).moduleι =
      I.moduleι ≫ f.unitToPushforwardUnit := by
    unfold Scheme.IdealSheafData.moduleToPushforwardComapModule
    rw [Category.assoc]
    erw [PreservesKernel.iso_inv_ι (SheafOfModules.pushforward f.toRingCatSheafHom)
      ((I.comap f).subschemeι.unitToPushforwardUnit)]
    exact kernel.lift_ι _ _ _
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Scheme.IdealSheafData.pullbackModuleComparison,
    Equiv.apply_symm_apply]
  change I.moduleToPushforwardComapModule f ≫
    (SheafOfModules.pushforward f.toRingCatSheafHom).map (I.comap f).moduleι =
    adj.homEquiv _ _ ((SheafOfModules.pullback f.toRingCatSheafHom).map I.moduleι ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  rw [adj.homEquiv_naturality_left]
  dsimp only [adj]
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  exact h

open CategoryTheory.Limits in
/-- Off an ideal's support, the inclusion itself is the trivialization. -/
lemma ideal_module_inclusion_isIso {Y : Scheme.{0}} (I : Y.IdealSheafData)
    (hI : I = ⊤) : IsIso I.moduleι := by
  subst I
  have hz : (⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit = 0 := by
    ext U x
    have hs : Subsingleton Γ((⊤ : Y.IdealSheafData).subscheme,
        (⊤ : Y.IdealSheafData).subschemeι ⁻¹ᵁ U.unop) := by
      have hU : (⊤ : Y.IdealSheafData).subschemeι ⁻¹ᵁ U.unop = ⊥ := by
        ext z
        exact isEmptyElim z
      rw [hU]
      exact CommRingCat.subsingleton_of_isTerminal
        (⊤ : Y.IdealSheafData).subscheme.sheaf.isTerminalOfEmpty
    exact @Subsingleton.elim _ hs _ _
  change IsIso (kernel.ι (⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit)
  rw [hz]
  infer_instance

/-- The canonical open cusp-ideal trivialization has the actual pulled
inclusion as its forward map. -/
def cuspIdealOpenIso (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    (Scheme.Modules.pullback X.inclusion).obj (cuspIdeal k L D X x).module ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf := by
  have hi := cuspIdeal_invertible k L D X x hx
  have hs : Disjoint (Set.range X.inclusion.base)
      ((cuspIdeal k L D X x).support : Set X.space) := by
    rw [cuspIdeal_support k L D X x hx, Set.disjoint_singleton_right]
    exact hx
  have ht := ((cuspIdeal k L D X x).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
      X.inclusion hs).1
  have hi' : ((cuspIdeal k L D X x).comap X.inclusion).IsInvertible := by
    rw [ht]
    exact Scheme.IdealSheafData.isInvertible_top
  letI := hi.isIso_pullbackModuleComparison X.inclusion hi'
  letI := ideal_module_inclusion_isIso ((cuspIdeal k L D X x).comap X.inclusion) ht
  exact asIso ((cuspIdeal k L D X x).pullbackModuleComparison X.inclusion) ≪≫
    asIso (((cuspIdeal k L D X x).comap X.inclusion).moduleι)

lemma cuspIdealOpenIso_hom (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    (cuspIdealOpenIso k L D X x hx).hom =
      (Scheme.Modules.pullback X.inclusion).map (cuspIdeal k L D X x).moduleι ≫
        (Scheme.Modules.pullbackUnitIso X.inclusion).hom :=
  ideal_pullback_inclusion _ _

#print axioms cuspIdealOpenIso_hom

/-- A disk cannot meet a different closed boundary point: every disk point
specializes to its center under the actual disk morphism. -/
lemma disk_avoids_other_cusp (D : LevelData k L) (X : Compactification k L D)
    (T : DiskTest k L D X) (x : X.space) (hx : x ∈ boundary k L D X)
    (hne : x ≠ T.disk (closedPoint k)) : x ∉ Set.range T.disk.base := by
  rintro ⟨z, hz⟩
  have hs : T.disk z ⤳ T.disk (closedPoint k) :=
    (IsLocalRing.specializes_closedPoint z).map T.disk.continuous
  rw [hz] at hs
  exact (BoundaryGeometry.boundary_point_closed k L D X x hx).not_specializes
    (Set.mem_singleton x) (by simpa only [Set.mem_singleton_iff] using hne.symm) hs

/-- Pulling a cusp ideal to a disk centered elsewhere gives the unit ideal,
with no contribution at any point of that disk. -/
lemma cuspIdeal_other_disk_eq_top (D : LevelData k L) (X : Compactification k L D)
    (T : DiskTest k L D X) (x : X.space) (hx : x ∈ boundary k L D X)
    (hne : x ≠ T.disk (closedPoint k)) :
    (cuspIdeal k L D X x).comap T.disk = ⊤ := by
  have hs : Disjoint (Set.range T.disk.base)
      ((cuspIdeal k L D X x).support : Set X.space) := by
    rw [cuspIdeal_support k L D X x hx, Set.disjoint_singleton_right]
    exact disk_avoids_other_cusp k L D X T x hx hne
  exact ((cuspIdeal k L D X x).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    T.disk hs).1

/-- The whole centered disk ideal is the principal ideal sheaf `(t)`.
The generator is transported by the fixed structure-sheaf Spec isomorphism. -/
lemma cuspIdeal_disk_eq_principal (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    (cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {scalar (PowerSeries k) (PowerSeries.X : PowerSeries k)}) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  change ((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
    Ideal.map (RingHom.id _) (Ideal.span {scalar (PowerSeries k) (PowerSeries.X : PowerSeries k)})
  rw [Ideal.map_id]
  let e := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv
  apply e.idealComapOrderIso.symm.injective
  change Ideal.map e.toRingHom _ = Ideal.map e.toRingHom _
  rw [Ideal.map_span, Set.image_singleton]
  have he : e (scalar (PowerSeries k) (PowerSeries.X : PowerSeries k)) = PowerSeries.X :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv_hom_id _
  erw [he]
  exact cuspIdeal_disk_ideal k L hL heven D X T

lemma disk_parameter_regular :
    scalar (PowerSeries k) (PowerSeries.X : PowerSeries k) ∈
      nonZeroDivisors Γ(Disk k, ⊤) := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro hz
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom hz
  simp only [scalar, Iso.inv_hom_id_apply, map_zero] at h
  exact PowerSeries.X_ne_zero h

lemma cuspIdeal_disk_invertible (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    ((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).IsInvertible := by
  rw [cuspIdeal_disk_eq_principal k L hL heven]
  exact Scheme.IdealSheafData.isInvertible_ofIdealTop_span_singleton _
    (disk_parameter_regular k)

/-- On an integral affine scheme, a nonzero principal ideal has a frame
whose image under the actual inclusion is its given generator. -/
lemma principalIdeal_frame {Y : Scheme.{0}} [IsIntegral Y] [IsAffine Y]
    (a : Γ(Y, ⊤)) (ha : a ≠ 0) :
    ∃ e : Γ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).module, ⊤),
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).moduleι.app ⊤ e = a ∧
        IsFrame (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).module ⊤ e := by
  obtain ⟨e, he, hf⟩ :=
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).exists_isFrameOn_module_of_forall_ideal_eq_span
      ⊤ a (by
        intro U hU
        refine ⟨by rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
          Set.image_singleton], ?_⟩
        by_cases h : Nonempty (U : Y.Opens)
        · letI := h
          apply mem_nonZeroDivisors_of_ne_zero
          exact fun hz => ha ((map_injective_of_isIntegral Y (homOfLE hU))
            (hz.trans (map_zero _).symm))
        · have hUbot : (U : Y.Opens) = ⊥ := by
            ext x
            change (x ∈ (U : Y.Opens)) ↔ False
            rw [iff_false]
            exact fun hx => h ⟨⟨x, hx⟩⟩
          haveI : Subsingleton Γ(Y, U) := by
            rw [hUbot]
            exact CommRingCat.subsingleton_of_isTerminal Y.sheaf.isTerminalOfEmpty
          exact mem_nonZeroDivisors_iff.mpr
            ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩)
  exact ⟨e, he, fun V hV => hf hV le_top⟩

/-- A frame of the actual disk pullback cusp module with inclusion exactly
equal to the formal parameter, retaining the original comparison map. -/
lemma cuspIdeal_disk_frame (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    ∃ e : Γ((Scheme.Modules.pullback T.disk).obj
        (cuspIdeal k L D X (T.disk (closedPoint k))).module, ⊤),
      IsFrame ((Scheme.Modules.pullback T.disk).obj
        (cuspIdeal k L D X (T.disk (closedPoint k))).module) ⊤ e ∧
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pullback T.disk).map
          (cuspIdeal k L D X (T.disk (closedPoint k))).moduleι ≫
          (Scheme.Modules.pullbackUnitIso T.disk).hom) ⊤ e =
        scalar (PowerSeries k) (PowerSeries.X : PowerSeries k) := by
  have hc := cuspIdeal_disk_eq_principal k L hL heven D X T
  have ht := T.extends_eq.2.2
  have hi := cuspIdeal_invertible k L D X (T.disk (closedPoint k)) ht
  have hi' := cuspIdeal_disk_invertible k L hL heven D X T
  letI := hi.isIso_pullbackModuleComparison T.disk hi'
  let c := asIso ((cuspIdeal k L D X (T.disk (closedPoint k))).pullbackModuleComparison T.disk)
  have ha : scalar (PowerSeries k) (PowerSeries.X : PowerSeries k) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (disk_parameter_regular k)
  have hframe : ∃ e : Γ(((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).module, ⊤),
      ((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).moduleι.app ⊤ e =
        scalar (PowerSeries k) (PowerSeries.X : PowerSeries k) ∧
      IsFrame ((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).module ⊤ e := by
    rw [hc]
    exact principalIdeal_frame _ ha
  obtain ⟨e, he, hf⟩ := hframe
  refine ⟨Scheme.Modules.Hom.app c.inv ⊤ e,
    GlobalFamilyDiscriminantR0180.frame_iso c.symm e hf, ?_⟩
  rw [← ideal_pullback_inclusion]
  change (((cuspIdeal k L D X (T.disk (closedPoint k))).comap T.disk).moduleι.app ⊤)
    ((c.hom.app ⊤) ((c.inv.app ⊤) e)) = _
  rw [show c.hom.app ⊤ (c.inv.app ⊤ e) = e by
    change Scheme.Modules.Hom.app (c.inv ≫ c.hom) ⊤ e = e
    rw [c.inv_hom_id]
    rfl]
  exact he

#print axioms cuspIdeal_disk_frame
#print axioms cuspIdeal_other_disk_eq_top
end BoundaryIdeals

section IdealGenericCompatibility

lemma pullbackEqIso_naturality {A Y : Scheme.{0}} {f g : A ⟶ Y}
    (h : f = g) {M N : Y.Modules} (φ : M ⟶ N) :
    (pullbackEqIso h M).hom ≫ (Scheme.Modules.pullback g).map φ =
      (Scheme.Modules.pullback f).map φ ≫ (pullbackEqIso h N).hom := by
  subst g
  simp [pullbackEqIso]

lemma squarePullbackIso_naturality {A B Y Z : Scheme.{0}}
    (a : A ⟶ B) (s : B ⟶ Z) (t : A ⟶ Y) (b : Y ⟶ Z)
    (h : a ≫ s = t ≫ b) {M N : Z.Modules} (φ : M ⟶ N) :
    (squarePullbackIso a s t b h M).hom ≫
        (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback b).map φ) =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback s).map φ) ≫
        (squarePullbackIso a s t b h N).hom := by
  have ht := (Scheme.Modules.pullbackComp t b).inv.naturality φ
  change (Scheme.Modules.pullback (t ≫ b)).map φ ≫
      ((Scheme.Modules.pullbackComp t b).app N).inv =
    ((Scheme.Modules.pullbackComp t b).app M).inv ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback b).map φ) at ht
  have ha := (Scheme.Modules.pullbackComp a s).hom.naturality φ
  change (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback s).map φ) ≫
      ((Scheme.Modules.pullbackComp a s).app N).hom =
    ((Scheme.Modules.pullbackComp a s).app M).hom ≫
      (Scheme.Modules.pullback (a ≫ s)).map φ at ha
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← ht, ← Category.assoc (pullbackEqIso h M).hom,
    pullbackEqIso_naturality, Category.assoc,
    ← Category.assoc ((Scheme.Modules.pullbackComp a s).app M).hom,
    ← ha]
  simp only [Category.assoc]

lemma pullbackEqIso_unit {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) :
    (pullbackEqIso h (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
        (Scheme.Modules.pullbackUnitIso g).hom =
      (Scheme.Modules.pullbackUnitIso f).hom := by
  subst g
  simp [pullbackEqIso]

lemma squarePullbackIso_unit {A B Y Z : Scheme.{0}}
    (a : A ⟶ B) (s : B ⟶ Z) (t : A ⟶ Y) (b : Y ⟶ Z)
    (h : a ≫ s = t ≫ b) :
    (squarePullbackIso a s t b h (SheafOfModules.unit Z.ringCatSheaf)).hom ≫
        (Scheme.Modules.pullback t).map (Scheme.Modules.pullbackUnitIso b).hom ≫
        (Scheme.Modules.pullbackUnitIso t).hom =
      (Scheme.Modules.pullback a).map (Scheme.Modules.pullbackUnitIso s).hom ≫
        (Scheme.Modules.pullbackUnitIso a).hom := by
  rw [← Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom t b]
  change (((Scheme.Modules.pullbackComp a s).app
      (SheafOfModules.unit Z.ringCatSheaf)).hom ≫
    (pullbackEqIso h (SheafOfModules.unit Z.ringCatSheaf)).hom ≫
    ((Scheme.Modules.pullbackComp t b).app
      (SheafOfModules.unit Z.ringCatSheaf)).inv) ≫
    ((Scheme.Modules.pullbackComp t b).app
      (SheafOfModules.unit Z.ringCatSheaf)).hom ≫
    (Scheme.Modules.pullbackUnitIso (t ≫ b)).hom = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc (pullbackEqIso h _).hom, pullbackEqIso_unit]
  exact Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom a s

/-- The generic identification of a cusp-ideal line uses the same geometric
square and the specified open trivialization as a twist of the Hodge line. -/
def cuspIdealGenericIso (D : LevelData k L) (X : Compactification k L D)
    (T : DiskTest k L D X) (x : X.space) (hx : x ∈ boundary k L D X) :
    (Scheme.Modules.pullback (genericInclusion k)).obj
        ((Scheme.Modules.pullback T.disk).obj (cuspIdeal k L D X x).module) ≅
      SheafOfModules.unit (Puncture k).ringCatSheaf :=
  squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion T.extends_eq.2.1
      (cuspIdeal k L D X x).module ≪≫
    (Scheme.Modules.pullback T.base).mapIso (cuspIdealOpenIso k L D X x hx) ≪≫
    Scheme.Modules.pullbackUnitIso T.base

/-- The specified generic trivialization is exactly generic pullback of
the actual disk inclusion, followed by the structure-sheaf unit comparison. -/
lemma cuspIdealGenericIso_hom (D : LevelData k L) (X : Compactification k L D)
    (T : DiskTest k L D X) (x : X.space) (hx : x ∈ boundary k L D X) :
    (cuspIdealGenericIso k L D X T x hx).hom =
      (Scheme.Modules.pullback (genericInclusion k)).map
        ((Scheme.Modules.pullback T.disk).map (cuspIdeal k L D X x).moduleι ≫
          (Scheme.Modules.pullbackUnitIso T.disk).hom) ≫
        (Scheme.Modules.pullbackUnitIso (genericInclusion k)).hom := by
  simp only [cuspIdealGenericIso, Iso.trans_hom, Functor.mapIso_hom,
    cuspIdealOpenIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    (squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion
      T.extends_eq.2.1 (cuspIdeal k L D X x).module).hom,
    squarePullbackIso_naturality]
  simp only [Category.assoc]
  erw [squarePullbackIso_unit]

/-- Transport along a generic identification induced by an actual inclusion
is the structure-sheaf pullback of that inclusion's value. -/
lemma transportSection_to_unit {A B : Scheme.{0}} (f : A ⟶ B)
    (M : B.Modules) (ψ : M ⟶ SheafOfModules.unit B.ringCatSheaf)
    (e : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit A.ringCatSheaf)
    (he : e.hom = (Scheme.Modules.pullback f).map ψ ≫
      (Scheme.Modules.pullbackUnitIso f).hom) (η : Γ(M, ⊤)) :
    OpenDiscriminantFullTateExpansionR0182.transportSection f M _ e η =
      f.appLE ⊤ ⊤ (by simp) (Scheme.Modules.Hom.app ψ ⊤ η) := by
  unfold OpenDiscriminantFullTateExpansionR0182.transportSection
  rw [he]
  change res _ (by simp)
    ((Scheme.Modules.pullbackUnitIso f).hom.app _
      (((Scheme.Modules.pullback f).map ψ).app _
        (Scheme.Modules.pullbackLocalSection f η))) = _
  rw [← Scheme.Modules.pullbackLocalSection_app]
  change res _ (by simp)
    ((Scheme.Modules.pullbackUnitIso f).hom.app _
      (Scheme.Modules.pullbackLocalSection f
        (Scheme.Modules.toUnitSection ⊤ (Scheme.Modules.Hom.app ψ ⊤ η)))) = _
  erw [Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection]
  rfl

/-- Under the specified open trivialization, the centered cusp-ideal frame
has generic scalar exactly the Laurent image of the disk parameter. -/
lemma cuspIdeal_generic_frame (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X) :
    ∃ e : Γ((Scheme.Modules.pullback T.disk).obj
        (cuspIdeal k L D X (T.disk (closedPoint k))).module, ⊤),
      IsFrame ((Scheme.Modules.pullback T.disk).obj
        (cuspIdeal k L D X (T.disk (closedPoint k))).module) ⊤ e ∧
      OpenDiscriminantFullTateExpansionR0182.transportSection (genericInclusion k) _ _
        (cuspIdealGenericIso k L D X T (T.disk (closedPoint k)) T.extends_eq.2.2) e =
      scalar (LaurentSeries k)
        (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X : PowerSeries k)) := by
  obtain ⟨e, hf, he⟩ := cuspIdeal_disk_frame k L hL heven D X T
  refine ⟨e, hf, ?_⟩
  rw [transportSection_to_unit _ _ _ _
    (cuspIdealGenericIso_hom k L D X T _ T.extends_eq.2.2), he]
  change (genericInclusion k).appLE ⊤ ⊤ (by simp)
      (scalar (PowerSeries k) PowerSeries.X) = _
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) PowerSeries.X).symm

#print axioms cuspIdeal_generic_frame

#print axioms cuspIdealGenericIso_hom
end IdealGenericCompatibility

section ExtensionNaturality

/-- An actual line map compatible with the chosen open identifications
commutes with the frozen disk differential comparison. -/
lemma diskGenericIso_naturality
    {D : LevelData k L} {X : Compactification k L D}
    (H K : Extension k L D X) (T : DiskTest k L D X)
    (φ : H.line ⟶ K.line)
    (hφ : (Scheme.Modules.pullback X.inclusion).map φ ≫ K.onOpen.hom = H.onOpen.hom) :
    (Scheme.Modules.pullback (genericInclusion k)).map
        ((Scheme.Modules.pullback T.disk).map φ) ≫ (diskGenericIso k L K T).hom =
      (diskGenericIso k L H T).hom := by
  change (Scheme.Modules.pullback (genericInclusion k)).map
      ((Scheme.Modules.pullback T.disk).map φ) ≫
    (squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion T.extends_eq.2.1 K.line).hom ≫
    (Scheme.Modules.pullback T.base).map K.onOpen.hom ≫ (openTestIso k L T.toTest).hom =
    (squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion T.extends_eq.2.1 H.line).hom ≫
    (Scheme.Modules.pullback T.base).map H.onOpen.hom ≫ (openTestIso k L T.toTest).hom
  rw [← Category.assoc, ← Category.assoc,
    ← squarePullbackIso_naturality, Category.assoc, Category.assoc,
    ← Category.assoc ((Scheme.Modules.pullback T.base).map
      ((Scheme.Modules.pullback X.inclusion).map φ)), ← Functor.map_comp, hφ]

/-- Naturality at the level of actual disk sections. -/
lemma diskRestriction_naturality
    {D : LevelData k L} {X : Compactification k L D}
    (H K : Extension k L D X) (T : DiskTest k L D X)
    (φ : H.line ⟶ K.line)
    (hφ : (Scheme.Modules.pullback X.inclusion).map φ ≫ K.onOpen.hom = H.onOpen.hom)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤)) :
    diskRestriction k L K T (((Scheme.Modules.pullback T.disk).map φ).app ⊤ η) =
      diskRestriction k L H T η := by
  unfold diskRestriction OpenDiscriminantFullTateExpansionR0182.transportSection
  rw [Scheme.Modules.pullbackLocalSection_app]
  change res _ (by simp)
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullback (genericInclusion k)).map
          ((Scheme.Modules.pullback T.disk).map φ) ≫ (diskGenericIso k L K T).hom) _
        (Scheme.Modules.pullbackLocalSection (genericInclusion k) η)) = _
  rw [diskGenericIso_naturality k L H K T φ hφ]

#print axioms diskRestriction_naturality
end ExtensionNaturality

section FractionFieldGeometry

open ArithmeticThetaTensorPower
open GlobalFamilyDiscriminantR0180
open OpenDiscriminantFullTateExpansionR0182

/-- Invertibility provides a genuine section frame on a neighborhood,
including the sectionwise bijectivity needed for tensor comparisons. -/
lemma local_frame_exists {Y : Scheme.{0}} {M : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (y : Y) :
    ∃ (U : Y.Opens) (s : Γ(M, U)), y ∈ U ∧ IsFrame M U s := by
  obtain ⟨U, hy, ⟨e⟩⟩ := hM.exists_trivialization y
  obtain ⟨s, hs, _⟩ := frame_lift_open U.ι M _ e (1 : Γ(U.toScheme, ⊤)) (by
    intro V h
    change Function.Bijective (fun a : Γ(U.toScheme, V) =>
      a * (U.toScheme.presheaf.map (homOfLE h).op) 1)
    simp only [map_one, mul_one]
    exact Function.bijective_id)
  exact ⟨U.ι.opensRange, s, by simpa only [Scheme.Opens.opensRange_ι] using hy, hs⟩

lemma composeComparison_section_comp {Y Z W : Scheme.{0}}
    (p : Z ⟶ Y) (q : W ⟶ Z) (M : Y.Modules) (N : Z.Modules) (P : W.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (U : Y.Opens) (s : Γ(M, U)) :
    (composeComparison p q (q ≫ p) rfl M N P e f).hom.app ((q ≫ p) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection (q ≫ p) s) =
    f.hom.app _ (Scheme.Modules.pullbackLocalSection q
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))) := by
  simpa only [res_refl] using
    composeComparison_section p q (q ≫ p) rfl M N P e f U s
      ((q ≫ p) ⁻¹ᵁ U) le_rfl le_rfl

/-- The specific sheafified tensor comparisons respect composition.
Local tensor frames prove equality on all sections, not just pure powers. -/
lemma tensorComparison_comp {Y Z W : Scheme.{0}}
    (p : Z ⟶ Y) (q : W ⟶ Z) (M : Y.Modules) (N : Z.Modules) (P : W.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) (n : ℕ) :
    tensorComparison (q ≫ p) M P
      (composeComparison p q (q ≫ p) rfl M N P e f) n =
    composeComparison p q (q ≫ p) rfl
      (tensorPower Y M n) (tensorPower Z N n) (tensorPower W P n)
      (tensorComparison p M N e n) (tensorComparison q N P f n) := by
  apply Iso.ext
  apply hom_ext_frames
  intro w
  obtain ⟨U, s, hw, hs⟩ := local_frame_exists hM ((q ≫ p) w)
  refine ⟨(q ≫ p) ⁻¹ᵁ U,
    Scheme.Modules.pullbackLocalSection (q ≫ p) (tensorPowerSection Y M n U s),
    hw, pullback_frame _ _ _ (tensorPower_frame M s hs n), ?_⟩
  have hline := composeComparison_section_comp p q M N P e f U s
  have hpower := composeComparison_section_comp p q
    (tensorPower Y M n) (tensorPower Z N n) (tensorPower W P n)
    (tensorComparison p M N e n) (tensorComparison q N P f n) U
    (tensorPowerSection Y M n U s)
  rw [tensorComparison_section p M N e n U s] at hpower
  rw [tensorComparison_section q N P f n] at hpower
  rw [tensorComparison_section, hline]
  exact hpower.symm

#print axioms tensorComparison_comp

/-- Tensor comparison with the identity on the pulled line is precisely the
frozen canonical pullback of the tensor power. -/
lemma tensorComparison_refl {Y Z : Scheme.{0}} (p : Z ⟶ Y) (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    tensorComparison p M ((Scheme.Modules.pullback p).obj M) (Iso.refl _) n =
      ArithmeticThetaPullback.pullback_tensorPower_iso Z Y p M n := by
  apply Iso.ext
  apply hom_ext_frames
  intro z
  obtain ⟨U, s, hz, hs⟩ := local_frame_exists hM (p z)
  refine ⟨p ⁻¹ᵁ U, Scheme.Modules.pullbackLocalSection p
    (tensorPowerSection Y M n U s), hz,
    pullback_frame _ _ _ (tensorPower_frame M s hs n), ?_⟩
  rw [tensorComparison_section, pullback_tensorPower_local_section]
  rfl

/-- Composition of specified pullback isomorphisms also composes their
transport of global sections, including the restrictions from preimages of top. -/
lemma transportSection_comp {Y Z W : Scheme.{0}}
    (p : Z ⟶ Y) (q : W ⟶ Z) (M : Y.Modules) (N : Z.Modules) (P : W.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) (s : Γ(M, ⊤)) :
    transportSection (q ≫ p) M P
        (composeComparison p q (q ≫ p) rfl M N P e f) s =
      transportSection q N P f (transportSection p M N e s) := by
  have hh := composeComparison_section p q (q ≫ p) rfl M N P e f
    ⊤ s ⊤ (by simp) (by simp)
  unfold transportSection
  rw [← InitialSectionNaturality.pullback_res, ← hom_res,
    InitialHodgeSection.res_res]
  exact hh

/-- The specific open comparison retains the ambient classifying comparison
when composed with the quotient inclusion; the composition is not a new choice. -/
lemma compose_openTestIso {D : LevelData k L} (T : Test k L D) :
    composeComparison D.quotient.inclusion T.base (T.base ≫ D.quotient.inclusion) rfl
      (hodge D.atlas.descent.family) (openHodge k L D)
      (Hodge (LaurentSeries k) (TateCurve k L)) (Iso.refl _) (openTestIso k L T) =
      testIso k L T := by
  apply Iso.ext
  simp [composeComparison, openTestIso, pullbackEqIso]

/-- Pulling the actual open tensor section to a Tate test is the original
ambient pullback, with its specified geometric differential comparison. -/
lemma pullToOpen_test {D : LevelData k L} (T : Test k L D) (n : ℕ)
    (s : Γ(power D.atlas.descent.family n, ⊤)) :
    transportSection T.base (openPower k L D n)
      (HodgePower (LaurentSeries k) (TateCurve k L) n)
      (tensorComparison T.base (openHodge k L D)
        (Hodge (LaurentSeries k) (TateCurve k L)) (openTestIso k L T) n)
      (pullToOpen k L n s) = pullAmbientPower k L T n s := by
  have hM := EllipticFamilyWeierstrassAtlasR0180.hodge_invertible D.atlas.descent.family
  have hc := tensorComparison_comp D.quotient.inclusion T.base
    (hodge D.atlas.descent.family) (openHodge k L D)
    (Hodge (LaurentSeries k) (TateCurve k L)) hM (Iso.refl _) (openTestIso k L T) n
  rw [compose_openTestIso, tensorComparison_refl _ _ hM] at hc
  change transportSection T.base _ _ _
    (transportSection D.quotient.inclusion _ _
      (ArithmeticThetaPullback.pullback_tensorPower_iso _ _ _ _ n) s) =
    transportSection (T.base ≫ D.quotient.inclusion) _ _ _ s
  rw [← transportSection_comp, ← hc]

#print axioms pullToOpen_test

/-- A local ambient section and its actual open identification give the
same generic disk section through the original geometric square. -/
lemma diskRestriction_local_section {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) (U : X.space.Opens)
    (s : Γ(H.line, U)) (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    diskRestriction k L H T
      (res ((Scheme.Modules.pullback T.disk).obj H.line) hd
        (Scheme.Modules.pullbackLocalSection T.disk s)) =
    res (Hodge (LaurentSeries k) (TateCurve k L)) ho
      ((openTestIso k L T.toTest).hom.app _
        (Scheme.Modules.pullbackLocalSection T.base
          (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)))) := by
  have hg : (⊤ : (Puncture k).Opens) ≤
      (genericInclusion k) ⁻¹ᵁ (T.disk ⁻¹ᵁ U) := by
    intro z hz
    exact hd (Set.mem_univ _)
  have hh := squarePullbackIso_section (genericInclusion k) T.disk T.base X.inclusion
    T.extends_eq.2.1 H.line U s ⊤ hg ho
  unfold diskRestriction transportSection
  rw [← InitialSectionNaturality.pullback_res, ← hom_res,
    InitialHodgeSection.res_res]
  change res _ hg ((openTestIso k L T.toTest).hom.app _
    (((Scheme.Modules.pullback T.base).map H.onOpen.hom).app _
      ((squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion
        T.extends_eq.2.1 H.line).hom.app _
        (Scheme.Modules.pullbackLocalSection (genericInclusion k)
          (Scheme.Modules.pullbackLocalSection T.disk s))))) = _
  rw [hom_res, hom_res, hh, ← hom_res, ← hom_res,
    ← Scheme.Modules.pullbackLocalSection_app]

#print axioms diskRestriction_local_section

/-- The generic point of an actual local domain has a unique lift to the
specified open whenever one faithful field-valued test factors through it.
The lift retains the actual structure-sheaf map and its factorization. -/
lemma fraction_open_lift {A K : Type} [CommRing A] [IsDomain A] [Field K]
    {Y U : Scheme.{0}} (j : U ⟶ Y) [IsOpenImmersion j]
    (σ : Spec (CommRingCat.of A) ⟶ Y)
    (b : Spec (CommRingCat.of K) ⟶ U) (f : A →+* K)
    (hf : Function.Injective f)
    (h : Spec.map (CommRingCat.ofHom f) ≫ σ = b ≫ j) :
    ∃ β : Spec (CommRingCat.of (FractionRing A)) ⟶ U,
      β ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ σ ∧
      Spec.map (CommRingCat.ofHom (IsFractionRing.lift hf : FractionRing A →+* K)) ≫ β = b := by
  let θ : FractionRing A →+* K := IsFractionRing.lift hf
  have hθ : θ.comp (algebraMap A (FractionRing A)) = f := by
    ext a
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hf a
  let η : Spec (CommRingCat.of (FractionRing A)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ σ
  have hη : Spec.map (CommRingCat.ofHom θ) ≫ η = b ≫ j := by
    rw [show η = Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ σ from rfl,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ]
    exact h
  have hrange : Set.range η ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    let w : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hz : Spec.map (CommRingCat.ofHom θ) w = z := Subsingleton.elim _ _
    refine ⟨b w, ?_⟩
    have hh := congrArg (fun g : Spec (CommRingCat.of K) ⟶ Y => g w) hη
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hh
    exact hh.symm
  let β := IsOpenImmersion.lift j η hrange
  have hβ : β ≫ j = η := IsOpenImmersion.lift_fac _ _ _
  refine ⟨β, hβ, ?_⟩
  apply (cancel_mono j).mp
  rw [Category.assoc, hβ, hη]

/-- A different faithful field-valued map uses the same intrinsic open
generic point. Its factorization follows by cancellation of the actual open
immersion, without making a new choice of a generic morphism. -/
lemma fraction_open_lift_factor {A K : Type} [CommRing A] [IsDomain A] [Field K]
    {Y U : Scheme.{0}} (j : U ⟶ Y) [IsOpenImmersion j]
    (σ : Spec (CommRingCat.of A) ⟶ Y)
    (β : Spec (CommRingCat.of (FractionRing A)) ⟶ U)
    (hβ : β ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ σ)
    (b : Spec (CommRingCat.of K) ⟶ U) (f : A →+* K)
    (hf : Function.Injective f)
    (h : Spec.map (CommRingCat.ofHom f) ≫ σ = b ≫ j) :
    Spec.map (CommRingCat.ofHom (IsFractionRing.lift hf : FractionRing A →+* K)) ≫ β = b := by
  have hθ : (IsFractionRing.lift hf : FractionRing A →+* K).comp
      (algebraMap A (FractionRing A)) = f := by
    ext a
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hf a
  apply (cancel_mono j).mp
  rw [Category.assoc, hβ, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hθ]
  exact h

/-- Two faithful completed maps preserving intrinsic germ orders preserve
the order of every nonzero element of the same actual fraction field. -/
lemma fraction_lift_order_eq {A : Type} [CommRing A] [IsDomain A]
    (f g : A →+* LaurentSeries k) (hf : Function.Injective f)
    (hg : Function.Injective g)
    (hord : ∀ a : A, a ≠ 0 → (f a).order = (g a).order)
    (c : FractionRing A) (hc : c ≠ 0) :
    (IsFractionRing.lift hf c : LaurentSeries k).order =
      (IsFractionRing.lift hg c : LaurentSeries k).order := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A c
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hc
    rw [← hab, ha, map_zero, zero_div]
  have hfa : f a ≠ 0 := fun hh => ha0 (hf (hh.trans (map_zero f).symm))
  have hfb : f b ≠ 0 := fun hh => hb0 (hf (hh.trans (map_zero f).symm))
  have hga : g a ≠ 0 := fun hh => ha0 (hg (hh.trans (map_zero g).symm))
  have hgb : g b ≠ 0 := fun hh => hb0 (hg (hh.trans (map_zero g).symm))
  rw [← hab, map_div₀, map_div₀,
    IsFractionRing.lift_algebraMap (K := FractionRing A) hf,
    IsFractionRing.lift_algebraMap (K := FractionRing A) hf,
    IsFractionRing.lift_algebraMap (K := FractionRing A) hg,
    IsFractionRing.lift_algebraMap (K := FractionRing A) hg,
    laurent_order_div k _ _ hfa hfb, laurent_order_div k _ _ hga hgb,
    hord a ha0, hord b hb0]

#print axioms fraction_open_lift
#print axioms fraction_open_lift_factor
#print axioms fraction_lift_order_eq
end FractionFieldGeometry

section IntrinsicOrders

/-- Changing an integral disk frame changes its prescribed-generator
coefficient by an integral unit and therefore preserves its Laurent order. -/
lemma disk_coefficient_order_frame_independent
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η ξ : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (hξ : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ ξ)
    (a b : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential)
    (hb : scalar (LaurentSeries k) b • diskRestriction k L H T ξ =
      hodgeGenerator k L T.differential) : a.order = b.order := by
  obtain ⟨c, hc⟩ := (hη ⊤ le_rfl).2 ξ
  rw [InitialHodgeSection.res_self] at hc
  change c • η = ξ at hc
  have hcu : IsUnit c := frame_coefficient_unit η hη c (by rw [hc]; exact hξ)
  let d : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom c
  have hdu : IsUnit d := hcu.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
  have hdc : scalar (PowerSeries k) d = c :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom_inv_id c
  have he : a = b * algebraMap (PowerSeries k) (LaurentSeries k) d := by
    have hh := ha.trans hb.symm
    rw [← hc, ← hdc, diskRestriction_smul, smul_smul] at hh
    have hframe := diskRestriction_frame k L H T η hη ⊤ le_rfl
    rw [InitialHodgeSection.res_self] at hframe
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).1
    apply hframe.1
    simpa only [scalar, map_mul] using hh
  rw [he, HahnSeries.order_mul
    (disk_coefficient_ne_zero k L H T ξ hξ b hb)
    (hdu.map (algebraMap (PowerSeries k) (LaurentSeries k))).ne_zero,
    laurent_order_of_powerSeries k d 0 (PowerSeries.order_zero_of_unit hdu)]
  simp

/-- The equality of centers gives the canonical equality isomorphism of
actual structure-sheaf stalks. -/
def stalkCenterIso (Y : Scheme.{0}) {x y : Y} (h : x = y) :
    Y.presheaf.stalk x ≅ Y.presheaf.stalk y :=
  eqToIso (congrArg (fun z => Y.presheaf.stalk z) h)

lemma stalkCenterIso_ord (Y : Scheme.{0}) {x y : Y} (h : x = y)
    (a : Y.presheaf.stalk x) :
    Ring.ord (Y.presheaf.stalk y) ((stalkCenterIso Y h).hom a) =
      Ring.ord (Y.presheaf.stalk x) a := by
  subst y
  rfl

lemma stalkCenterIso_fromSpecStalk (Y : Scheme.{0}) {x y : Y} (h : x = y) :
    Spec.map (stalkCenterIso Y h).hom ≫ Y.fromSpecStalk x = Y.fromSpecStalk y := by
  subst y
  simp [stalkCenterIso]

/-- Both disks at a common center factor through the same actual local
fraction-field point of the specified open. The two scalar maps preserve the
order of every common nonzero rational germ. -/
lemma disk_shared_center_fraction_maps (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D)
    (T S : DiskTest k L D X)
    (hcenter : T.disk (closedPoint k) = S.disk (closedPoint k)) :
    letI : IsDomain (CuspStalk k L D X T.disk) :=
      (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
    ∃ β : Spec (CommRingCat.of (FractionRing (CuspStalk k L D X T.disk))) ⟶ OpenBase k L D,
    ∃ θT θS : FractionRing (CuspStalk k L D X T.disk) →+* LaurentSeries k,
      β ≫ X.inclusion =
        Spec.map (CommRingCat.ofHom (algebraMap (CuspStalk k L D X T.disk)
          (FractionRing (CuspStalk k L D X T.disk)))) ≫
          X.space.fromSpecStalk (T.disk (closedPoint k)) ∧
      Spec.map (CommRingCat.ofHom θT) ≫ β = T.base ∧
      Spec.map (CommRingCat.ofHom θS) ≫ β = S.base ∧
      (∀ a : CuspStalk k L D X T.disk,
        θT (algebraMap _ _ a) = algebraMap (PowerSeries k) (LaurentSeries k)
          (CompletedLocalParameter.localMap k L D X T.disk a)) ∧
      (∀ a : CuspStalk k L D X T.disk,
        θS (algebraMap _ _ a) = algebraMap (PowerSeries k) (LaurentSeries k)
          (CompletedLocalParameter.localMap k L D X S.disk
            ((stalkCenterIso X.space hcenter).hom a))) ∧
      ∀ c : FractionRing (CuspStalk k L D X T.disk), c ≠ 0 →
        (θT c).order = (θS c).order := by
  letI : IsDomain (CuspStalk k L D X T.disk) :=
    (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
  letI := X.openImmersion
  let A := CuspStalk k L D X T.disk
  let σ := X.space.fromSpecStalk (T.disk (closedPoint k))
  let f : A →+* LaurentSeries k :=
    (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (CompletedLocalParameter.localMap k L D X T.disk)
  let g : A →+* LaurentSeries k :=
    (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      ((CompletedLocalParameter.localMap k L D X S.disk).comp
        (stalkCenterIso X.space hcenter).hom.hom)
  have hf : Function.Injective f :=
    (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
      (disk_localMap_injective k L hL heven D X T)
  have hg : Function.Injective g :=
    (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
      ((disk_localMap_injective k L hL heven D X S).comp
        (ConcreteCategory.bijective_of_isIso (stalkCenterIso X.space hcenter).hom).1)
  have hT : Spec.map (CommRingCat.ofHom f) ≫ σ = T.base ≫ X.inclusion := by
    rw [show f = (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (CompletedLocalParameter.localMap k L D X T.disk) from rfl,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    change genericInclusion k ≫
      (Spec.map (Scheme.stalkClosedPointTo T.disk) ≫
        X.space.fromSpecStalk (T.disk (closedPoint k))) = _
    have hfac : Spec.map (Scheme.stalkClosedPointTo T.disk) ≫
        X.space.fromSpecStalk (T.disk (closedPoint k)) = T.disk :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk T.disk
    exact (congrArg (fun v => genericInclusion k ≫ v) hfac).trans T.extends_eq.2.1
  have hS : Spec.map (CommRingCat.ofHom g) ≫ σ = S.base ≫ X.inclusion := by
    rw [show g = (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      ((CompletedLocalParameter.localMap k L D X S.disk).comp
        (stalkCenterIso X.space hcenter).hom.hom) from rfl,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hc : Spec.map (stalkCenterIso X.space hcenter).hom ≫ σ =
        X.space.fromSpecStalk (S.disk (closedPoint k)) :=
      stalkCenterIso_fromSpecStalk X.space hcenter
    change genericInclusion k ≫ (Spec.map (Scheme.stalkClosedPointTo S.disk) ≫
      (Spec.map (stalkCenterIso X.space hcenter).hom ≫ σ)) = _
    rw [hc]
    have hfac : Spec.map (Scheme.stalkClosedPointTo S.disk) ≫
        X.space.fromSpecStalk (S.disk (closedPoint k)) = S.disk :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk S.disk
    exact (congrArg (fun v => genericInclusion k ≫ v) hfac).trans S.extends_eq.2.1
  obtain ⟨β, hβ, hβT⟩ := fraction_open_lift (A := A) X.inclusion σ T.base f hf hT
  refine ⟨β, IsFractionRing.lift hf, IsFractionRing.lift hg, hβ, hβT,
    fraction_open_lift_factor (A := A) X.inclusion σ β hβ S.base g hg hS,
    ?_, ?_, ?_⟩
  · intro a
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hf a
  · intro a
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hg a
  · intro c hc
    apply fraction_lift_order_eq k f g hf hg _ c hc
    intro a ha
    have hi := (ConcreteCategory.bijective_of_isIso (stalkCenterIso X.space hcenter).hom).1
    have ha' : (stalkCenterIso X.space hcenter).hom a ≠ 0 := by
      intro hh
      exact ha (hi (hh.trans (map_zero _).symm))
    change (algebraMap (PowerSeries k) (LaurentSeries k)
      (CompletedLocalParameter.localMap k L D X T.disk a)).order =
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X S.disk
          ((stalkCenterIso X.space hcenter).hom a))).order
    rw [disk_localMap_laurent_order k L hL heven D X T a ha,
      disk_localMap_laurent_order k L hL heven D X S _ ha', stalkCenterIso_ord]

#print axioms disk_shared_center_fraction_maps

/-- Evaluation of a section through a factorization of field-valued scheme
maps is evaluation by the same ring homomorphism, including non-global sections. -/
lemma field_section_factor {F E : Type} [Field F] [Field E] {Y : Scheme.{0}}
    (θ : F →+* E) (β : Spec (CommRingCat.of F) ⟶ Y)
    (b : Spec (CommRingCat.of E) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom θ) ≫ β = b)
    (U : Y.Opens) (hβ : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤ β ⁻¹ᵁ U)
    (hb : (⊤ : (Spec (CommRingCat.of E)).Opens) ≤ b ⁻¹ᵁ U) (r : Γ(Y, U)) :
    θ ((Scheme.ΓSpecIso (CommRingCat.of F)).hom (β.appLE U ⊤ hβ r)) =
      (Scheme.ΓSpecIso (CommRingCat.of E)).hom (b.appLE U ⊤ hb r) := by
  subst b
  have hh : β.appLE U ⊤ hβ ≫ (Spec.map (CommRingCat.ofHom θ)).appTop =
      (Spec.map (CommRingCat.ofHom θ) ≫ β).appLE U ⊤ hb := by
    change β.appLE U ⊤ hβ ≫
      (Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ (by simp) = _
    rw [Scheme.Hom.appLE_comp_appLE]
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ)) (β.appLE U ⊤ hβ r)
  exact hn.symm.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of E)).hom
    (ConcreteCategory.congr_hom hh r))

/-- Two actual disks at a common cusp assign the same Laurent order to any
section on a common open neighborhood of their generic images. -/
lemma disk_shared_center_open_scalar_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T S : DiskTest k L D X)
    (hcenter : T.disk (closedPoint k) = S.disk (closedPoint k))
    (U : (OpenBase k L D).Opens)
    (hT : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ U)
    (hS : (⊤ : (Puncture k).Opens) ≤ S.base ⁻¹ᵁ U) (r : Γ(OpenBase k L D, U)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (T.base.appLE U ⊤ hT r)).order =
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (S.base.appLE U ⊤ hS r)).order := by
  letI : IsDomain (CuspStalk k L D X T.disk) :=
    (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
  obtain ⟨β, θT, θS, _, hβT, hβS, _, _, ho⟩ :=
    disk_shared_center_fraction_maps k L hL heven D X T S hcenter
  have hβU : (⊤ : (Spec (CommRingCat.of
      (FractionRing (CuspStalk k L D X T.disk)))).Opens) ≤ β ⁻¹ᵁ U := by
    intro z hz
    let w : Puncture k := (⊥ : PrimeSpectrum (LaurentSeries k))
    have he : Spec.map (CommRingCat.ofHom θT) w = z := Subsingleton.elim _ _
    change β z ∈ U
    rw [← he]
    change (Spec.map (CommRingCat.ofHom θT) ≫ β) w ∈ U
    rw [hβT]
    exact hT (Set.mem_univ w)
  let c : FractionRing (CuspStalk k L D X T.disk) :=
    (Scheme.ΓSpecIso (CommRingCat.of
      (FractionRing (CuspStalk k L D X T.disk)))).hom (β.appLE U ⊤ hβU r)
  have hcT := field_section_factor θT β T.base hβT U hβU hT r
  have hcS := field_section_factor θS β S.base hβS U hβU hS r
  rw [← hcT, ← hcS]
  by_cases hc : c = 0
  · change (θT c).order = (θS c).order
    rw [hc, map_zero, map_zero]
  · exact ho c hc

#print axioms disk_shared_center_open_scalar_order

/-- The two actual completion maps at a common center assign the same order
to each fixed nonzero rational germ. The input is a germ, rather than an
arbitrarily chosen scalar-valued expansion. -/
lemma disk_shared_center_rational_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D)
    (T S : DiskTest k L D X)
    (hcenter : T.disk (closedPoint k) = S.disk (closedPoint k))
    (a b : CuspStalk k L D X T.disk) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X T.disk a)) /
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X T.disk b))).order =
    ((algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X S.disk
          ((stalkCenterIso X.space hcenter).hom a))) /
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (CompletedLocalParameter.localMap k L D X S.disk
          ((stalkCenterIso X.space hcenter).hom b)))).order := by
  have hi := (ConcreteCategory.bijective_of_isIso (stalkCenterIso X.space hcenter).hom).1
  have ha' : (stalkCenterIso X.space hcenter).hom a ≠ 0 := by
    intro hh
    exact ha (hi (hh.trans (map_zero _).symm))
  have hb' : (stalkCenterIso X.space hcenter).hom b ≠ 0 := by
    intro hh
    exact hb (hi (hh.trans (map_zero _).symm))
  rw [disk_rational_germ_order k L hL heven D X T a b ha hb,
    disk_rational_germ_order k L hL heven D X S _ _ ha' hb',
    stalkCenterIso_ord, stalkCenterIso_ord]

#print axioms disk_coefficient_order_frame_independent
#print axioms disk_shared_center_rational_order
end IntrinsicOrders

section SharedCenterHodgeOrder
open ArithmeticThetaTensorPower GlobalFamilyDiscriminantR0180
open OpenDiscriminantFullTateExpansionR0182

/-- Tensor transport of a section expressed in one actual local frame. -/
lemma transportSection_local_scalar {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    (M : Y.Modules) (N : Z.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (n : ℕ) (d : Γ(tensorPower Y M n, ⊤))
    (U : Y.Opens) (s : Γ(M, U)) (r : Γ(Y, U))
    (hr : res (tensorPower Y M n) le_top d = r • tensorPowerSection Y M n U s)
    (h : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ U) :
    transportSection p (tensorPower Y M n) (tensorPower Z N n)
      (tensorComparison p M N e n) d =
    p.appLE U ⊤ h r • tensorPowerSection Z N n ⊤
      (res N h (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))) := by
  have ht := transportSection_restrict p (tensorPower Y M n) (tensorPower Z N n)
    (tensorComparison p M N e n) d U ⊤ h
  rw [res_refl, hr, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul, InitialHodgeSection.res_smul,
    tensorComparison_section] at ht
  have hp := tensorPowerSection_restrict Z N n (p ⁻¹ᵁ U) ⊤ h
    (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))
  change res (tensorPower Z N n) h _ = _ at hp
  rw [hp] at ht
  exact ht

/-- The same local open scalar is the complete D2 coefficient at any disk
whose center lies in the chosen ambient frame neighborhood. -/
lemma disk_local_discriminant_scalar (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (U : X.space.Opens) (s : Γ(H.line, U)) (hs : IsFrame H.line U s)
    (hU : T.disk (closedPoint k) ∈ U)
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : res (openPower k L D 24) le_top (pullToOpen k L 24 d) =
      r • tensorPowerSection (OpenBase k L D) (openHodge k L D) 24
        (X.inclusion ⁻¹ᵁ U)
        (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)))
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T
      (res _ (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
        (Scheme.Modules.pullbackLocalSection T.disk s)) = hodgeGenerator k L T.differential) :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ (by
        intro z hz
        change X.inclusion (T.base z) ∈ U
        rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
        exact (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge (Set.mem_univ _)) r) =
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k L * a^24 := by
  let hdisk : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  let hopen : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z hz
    change X.inclusion (T.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hdisk (Set.mem_univ _)
  let η := res ((Scheme.Modules.pullback T.disk).obj H.line) hdisk
    (Scheme.Modules.pullbackLocalSection T.disk s)
  have hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η :=
    frame_restrict _ hdisk _ (pullback_frame _ _ _ hs)
  have ht := transportSection_local_scalar T.base (openHodge k L D)
    (Hodge (LaurentSeries k) (TateCurve k L)) (openTestIso k L T.toTest)
    24 (pullToOpen k L 24 d) (X.inclusion ⁻¹ᵁ U)
    (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)) r hr hopen
  rw [pullToOpen_test, ← diskRestriction_local_section k L H T U s hdisk hopen] at ht
  have he := disk_discriminant_coefficient k L hL heven H T η a ha d hd
  have hf := tensorPower_frame _ (diskRestriction k L H T η)
    (diskRestriction_frame k L H T η hη) 24 ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at hf
  have hc := hf.1 (ht.symm.trans he)
  exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom hc).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id _)

#print axioms transportSection_local_scalar
#print axioms disk_local_discriminant_scalar

/-- The normalized Tate coefficient order depends only on the actual
boundary center, for arbitrary integral frames on the two disks. -/
lemma disk_shared_center_coefficient_order (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T S : DiskTest k L D X)
    (hcenter : T.disk (closedPoint k) = S.disk (closedPoint k))
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (ξ : Γ((Scheme.Modules.pullback S.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (hξ : IsFrame ((Scheme.Modules.pullback S.disk).obj H.line) ⊤ ξ)
    (a b : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential)
    (hb : scalar (LaurentSeries k) b • diskRestriction k L H S ξ =
      hodgeGenerator k L S.differential) : a.order = b.order := by
  obtain ⟨U, s, hU, hs⟩ := local_frame_exists H.invertible (T.disk (closedPoint k))
  have hUS : S.disk (closedPoint k) ∈ U := hcenter ▸ hU
  let hT : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  let hS : (⊤ : (Disk k).Opens) ≤ S.disk ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem S.disk hUS).ge
  let ηT := res ((Scheme.Modules.pullback T.disk).obj H.line) hT
    (Scheme.Modules.pullbackLocalSection T.disk s)
  let ηS := res ((Scheme.Modules.pullback S.disk).obj H.line) hS
    (Scheme.Modules.pullbackLocalSection S.disk s)
  have hfT : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ ηT :=
    frame_restrict _ hT _ (pullback_frame _ _ _ hs)
  have hfS : IsFrame ((Scheme.Modules.pullback S.disk).obj H.line) ⊤ ηS :=
    frame_restrict _ hS _ (pullback_frame _ _ _ hs)
  obtain ⟨aT, haT, _⟩ := disk_coefficient_exists k L H T ηT hfT
  obtain ⟨aS, haS, _⟩ := disk_coefficient_exists k L H S ηS hfS
  have hnT := disk_coefficient_ne_zero k L H T ηT hfT aT haT
  have hnS := disk_coefficient_ne_zero k L H S ηS hfS aS haS
  let V := X.inclusion ⁻¹ᵁ U
  let σ : Γ(openHodge k L D, V) :=
    H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)
  have hfσ : IsFrame (openHodge k L D) V σ :=
    frame_iso H.onOpen _ (pullback_frame _ _ _ hs)
  obtain ⟨d, hd, _⟩ := global_family_discriminant
    k D.atlas.quotient.ring D.atlas.quotient.smooth D.atlas.descent.family
  obtain ⟨r, hr⟩ := (tensorPower_frame _ σ hfσ 24 V le_rfl).2
    (res (openPower k L D 24) le_top (pullToOpen k L 24 d))
  rw [InitialHodgeSection.res_self] at hr
  have hoT : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ V := by
    intro z hz
    change X.inclusion (T.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hT (Set.mem_univ _)
  have hoS : (⊤ : (Puncture k).Opens) ≤ S.base ⁻¹ᵁ V := by
    intro z hz
    change X.inclusion (S.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← S.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hS (Set.mem_univ _)
  have hcT := disk_local_discriminant_scalar k L hL heven H T U s hs hU d hd r hr.symm aT haT
  have hcS := disk_local_discriminant_scalar k L hL heven H S U s hs hUS d hd r hr.symm aS haS
  have ho := disk_shared_center_open_scalar_order k L hL heven D X T S hcenter V hoT hoS r
  rw [hcT, hcS, discriminant_coefficient_order k L (by omega) aT hnT,
    discriminant_coefficient_order k L (by omega) aS hnS] at ho
  have horder : aT.order = aS.order := by omega
  exact (disk_coefficient_order_frame_independent k L H T η ηT hη hfT a aT ha haT).trans
    (horder.trans (disk_coefficient_order_frame_independent k L H S ξ ηS hξ hfS b aS hb haS).symm)

#print axioms disk_shared_center_coefficient_order
end SharedCenterHodgeOrder


section TwistLocalFrames
open ArithmeticThetaSheafTensor ArithmeticThetaPullback

/-- The pure tensor of two actual local frames is a local frame. -/
lemma tensor_section_frame {Y : Scheme.{0}} {M N : Y.Modules}
    {U : Y.Opens} (s : Γ(M, U)) (t : Γ(N, U))
    (hs : IsFrame M U s) (ht : IsFrame N U t) :
    IsFrame (sheafTensor Y M N) U (tensorSection Y M N U s t) := by
  let e := frameTrivialization M s hs
  let f := frameTrivialization N t ht
  let g := tensorFrame Y M N U e f
  intro V hV
  have he : res (sheafTensor Y M N) hV (tensorSection Y M N U s t) = g.equiv V hV 1 := by
    change (sheafTensor Y M N).presheaf.map (homOfLE hV).op _ = _
    rw [tensorSection_restrict]
    have he1 : e.equiv V hV 1 = res M hV s := one_smul _ _
    have hf1 : f.equiv V hV 1 = res N hV t := one_smul _ _
    have hh := tensorSection_frame Y M N U e f V hV 1 1
    rw [he1, hf1, mul_one] at hh
    exact hh
  have hh : (fun a : Γ(Y,V) => a • res (sheafTensor Y M N) hV
      (tensorSection Y M N U s t)) = g.equiv V hV := by
    funext a
    rw [he, ← (g.equiv V hV).map_smul]
    simp only [smul_eq_mul, mul_one]
  rw [hh]
  exact (g.equiv V hV).bijective

lemma tensor_unitor_scalar {Y : Scheme.{0}} (M : Y.Modules) (U : Y.Opens)
    (r : Γ(Y,U)) (s : Γ(M,U)) :
    (tensorLeftUnitIso Y M).hom.app U
      (tensorSection Y (SheafOfModules.unit Y.ringCatSheaf) M U
        (Scheme.Modules.toUnitSection U r) s) = r • s := by
  have h := congrArg (fun f => f.app (Opposite.op U)) (tensorLeftUnitIso_unit Y M)
  have h' := ConcreteCategory.congr_hom h (r ⊗ₜ[Γ(Y,U)] s)
  exact h'

/-- The chosen open identification of a twist multiplies the original
Hodge section by the scalar from the chosen trivialization of the twisting line. -/
lemma twist_open_local {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (J : X.space.Modules)
    (hJ : Scheme.Modules.IsInvertible J)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (U : X.space.Opens) (s : Γ(J,U)) (t : Γ(H.line,U)) :
    (twistExtension k L H J hJ eJ).onOpen.hom.app (X.inclusion ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection X.inclusion (tensorSection X.space J H.line U s t)) =
    Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)) •
      H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion t) := by
  change (tensorLeftUnitIso _ _).hom.app _
    ((sheafTensorCongr _ eJ H.onOpen).hom.app _
      ((pullback_sheafTensor_iso _ _ X.inclusion J H.line).hom.app _ _)) = _
  rw [pullback_sheafTensor_local_section, sheafTensorCongr_section]
  exact tensor_unitor_scalar _ _ _ _


/-- The geometric disk restriction of the twist is multiplication by its
actual open scalar, evaluated along the disk's specified generic map. -/
lemma twist_disk_local {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (J : X.space.Modules)
    (hJ : Scheme.Modules.IsInvertible J)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (s : Γ(J,U)) (t : Γ(H.line,U))
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    diskRestriction k L (twistExtension k L H J hJ eJ) T
      (res _ hd (Scheme.Modules.pullbackLocalSection T.disk
        (tensorSection X.space J H.line U s t))) =
    T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho
      (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))) •
    diskRestriction k L H T
      (res _ hd (Scheme.Modules.pullbackLocalSection T.disk t)) := by
  rw [diskRestriction_local_section, diskRestriction_local_section, twist_open_local,
    Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul]
  rfl

/-- Generic identification of any globally invertible line with its
specified trivialization on the actual open. -/
def trivializedGenericIso {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X) :
    (Scheme.Modules.pullback (genericInclusion k)).obj
      ((Scheme.Modules.pullback T.disk).obj J) ≅
      SheafOfModules.unit (Puncture k).ringCatSheaf :=
  squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion T.extends_eq.2.1 J ≪≫
    (Scheme.Modules.pullback T.base).mapIso eJ ≪≫ Scheme.Modules.pullbackUnitIso T.base

lemma trivialized_local_section {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X) (U : X.space.Opens) (s : Γ(J,U))
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    OpenDiscriminantFullTateExpansionR0182.transportSection (genericInclusion k) _ _
      (trivializedGenericIso k L J eJ T)
      (res _ hd (Scheme.Modules.pullbackLocalSection T.disk s)) =
    Scheme.Modules.toUnitSection ⊤
      (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho
        (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)))) := by
  have hg : (⊤ : (Puncture k).Opens) ≤
      (genericInclusion k) ⁻¹ᵁ (T.disk ⁻¹ᵁ U) := by
    intro z hz
    exact hd (Set.mem_univ _)
  have hh := squarePullbackIso_section (genericInclusion k) T.disk T.base X.inclusion
    T.extends_eq.2.1 J U s ⊤ hg ho
  unfold OpenDiscriminantFullTateExpansionR0182.transportSection
  rw [← InitialSectionNaturality.pullback_res, ← hom_res,
    InitialHodgeSection.res_res]
  change res _ hg ((Scheme.Modules.pullbackUnitIso T.base).hom.app _
    (((Scheme.Modules.pullback T.base).map eJ.hom).app _
      ((squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion
        T.extends_eq.2.1 J).hom.app _
        (Scheme.Modules.pullbackLocalSection (genericInclusion k)
          (Scheme.Modules.pullbackLocalSection T.disk s))))) = _
  rw [hom_res, hom_res, hh, ← hom_res, ← hom_res,
    ← Scheme.Modules.pullbackLocalSection_app]
  change res _ ho ((Scheme.Modules.pullbackUnitIso T.base).hom.app _
    (Scheme.Modules.pullbackLocalSection T.base
      (Scheme.Modules.toUnitSection _
        (Scheme.Modules.ofUnitSection _ (eJ.hom.app _
          (Scheme.Modules.pullbackLocalSection X.inclusion s)))))) = _
  erw [Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection]
  rfl

#print axioms tensor_section_frame
#print axioms twist_disk_local
#print axioms trivialized_local_section

/-- The scalar of an integral disk frame under the specified open
trivialization, evaluated by the fixed Laurent-series structure-sheaf map. -/
def trivializedScalar {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤)) : LaurentSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    (Scheme.Modules.ofUnitSection ⊤
      (OpenDiscriminantFullTateExpansionR0182.transportSection (genericInclusion k) _ _
        (trivializedGenericIso k L J eJ T) η))

lemma trivializedScalar_smul {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤)) (b : PowerSeries k) :
    trivializedScalar k L J eJ T (scalar (PowerSeries k) b • η) =
    algebraMap (PowerSeries k) (LaurentSeries k) b * trivializedScalar k L J eJ T η := by
  unfold trivializedScalar
  rw [OpenDiscriminantFullTateExpansionR0182.transportSection_smul]
  have hb : (genericInclusion k).appLE ⊤ ⊤ (by simp) (scalar (PowerSeries k) b) =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) b) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) b).symm
  rw [hb, Scheme.Modules.ofUnitSection_smul, map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id _

lemma trivializedScalar_ne_zero {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η) :
    trivializedScalar k L J eJ T η ≠ 0 := by
  let θ := OpenDiscriminantFullTateExpansionR0182.transportSection (genericInclusion k) _ _
    (trivializedGenericIso k L J eJ T) η
  have hf : IsFrame (SheafOfModules.unit (Puncture k).ringCatSheaf) ⊤ θ :=
    frame_restrict _ (by simp) _ (GlobalFamilyDiscriminantR0180.frame_iso
      (trivializedGenericIso k L J eJ T) _ (pullback_frame _ _ η hη))
  intro hz
  have hz' : θ = 0 := by
    apply Scheme.Modules.ofUnitSection_injective ⊤
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom).1
    exact hz.trans (map_zero _).symm
  obtain ⟨r, hr⟩ := (hf ⊤ le_rfl).2 (1 : Γ(Puncture k, ⊤))
  rw [InitialHodgeSection.res_self] at hr
  change r • θ = (1 : Γ(Puncture k, ⊤)) at hr
  rw [hz', smul_zero] at hr
  have hh : (0 : Γ(Puncture k, ⊤)) = 1 := hr
  exact zero_ne_one hh

lemma trivializedScalar_frame_order {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η ξ : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η)
    (hξ : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ ξ) :
    (trivializedScalar k L J eJ T η).order = (trivializedScalar k L J eJ T ξ).order := by
  obtain ⟨c, hc⟩ := (hη ⊤ le_rfl).2 ξ
  rw [InitialHodgeSection.res_self] at hc
  change c • η = ξ at hc
  have hu := frame_coefficient_unit η hη c (by rw [hc]; exact hξ)
  let b : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom c
  have hbu : IsUnit b := hu.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
  have hbc : scalar (PowerSeries k) b = c :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom_inv_id c
  rw [← hc, ← hbc, trivializedScalar_smul, HahnSeries.order_mul
    (hbu.map (algebraMap (PowerSeries k) (LaurentSeries k))).ne_zero
    (trivializedScalar_ne_zero k L J eJ T η hη),
    laurent_order_of_powerSeries k b 0 (PowerSeries.order_zero_of_unit hbu)]
  simp

#print axioms trivializedScalar_frame_order

/-- A cusp ideal contributes one to the generic frame order at its center. -/
lemma cuspIdeal_center_scalar_order (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj
      (cuspIdeal k L D X (T.disk (closedPoint k))).module, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj
      (cuspIdeal k L D X (T.disk (closedPoint k))).module) ⊤ η) :
    (trivializedScalar k L (cuspIdeal k L D X (T.disk (closedPoint k))).module
      (cuspIdealOpenIso k L D X _ T.extends_eq.2.2) T η).order = 1 := by
  obtain ⟨e, hf, he⟩ := cuspIdeal_generic_frame k L hL heven D X T
  rw [trivializedScalar_frame_order k L _ _ T η e hη hf]
  have hh := congrArg (fun θ => (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (Scheme.Modules.ofUnitSection ⊤ θ)) he
  change trivializedScalar k L _ (cuspIdealOpenIso k L D X _ T.extends_eq.2.2) T e =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)) at hh
  rw [hh]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    (scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)) =
    algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X from
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id _]
  exact laurent_order_of_powerSeries k PowerSeries.X 1 PowerSeries.order_X

lemma tensor_smul_left {Y : Scheme.{0}} (M N : Y.Modules) (U : Y.Opens)
    (r : Γ(Y,U)) (s : Γ(M,U)) (t : Γ(N,U)) :
    tensorSection Y M N U (r • s) t = r • tensorSection Y M N U s t := by
  unfold tensorSection
  have hh : (r • s) ⊗ₜ[Γ(Y,U)] t = r • (s ⊗ₜ[Γ(Y,U)] t) :=
    TensorProduct.smul_tmul' r s t
  exact (congrArg ((tensorUnitMap Y M N).app (Opposite.op U)) hh).trans
    (((tensorUnitMap Y M N).app (Opposite.op U)).hom.map_smul r _)

/-- The inverse trivialization is defined using the same perfect pairing
as the global inverse line. -/
def inverseTrivialization {Y : Scheme.{0}} (M N : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (pair : sheafTensor Y M N ≅ SheafOfModules.unit Y.ringCatSheaf) :
    N ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (tensorLeftUnitIso Y N).symm ≪≫
    sheafTensorCongr Y e.symm (Iso.refl N) ≪≫ pair

lemma inverseTrivialization_pair {Y : Scheme.{0}} (M N : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (pair : sheafTensor Y M N ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (s : Γ(M,U)) (t : Γ(N,U)) :
    Scheme.Modules.ofUnitSection U (pair.hom.app U (tensorSection Y M N U s t)) =
    Scheme.Modules.ofUnitSection U (e.hom.app U s) *
      Scheme.Modules.ofUnitSection U ((inverseTrivialization M N e pair).hom.app U t) := by
  let u := e.inv.app U (Scheme.Modules.toUnitSection U 1)
  let r := Scheme.Modules.ofUnitSection U (e.hom.app U s)
  have hu : (tensorLeftUnitIso Y N).inv.app U t =
      tensorSection Y (SheafOfModules.unit Y.ringCatSheaf) N U (Scheme.Modules.toUnitSection U 1) t := by
    apply (ConcreteCategory.bijective_of_isIso ((tensorLeftUnitIso Y N).hom.app U)).1
    have h1 := ConcreteCategory.congr_hom
      (congrArg (fun f => f.app U) (tensorLeftUnitIso Y N).inv_hom_id) t
    exact h1.trans (tensorLeftUnitIso_section Y N U t).symm
  have hv : (inverseTrivialization M N e pair).hom.app U t =
      pair.hom.app U (tensorSection Y M N U u t) := by
    change pair.hom.app U ((sheafTensorCongr Y e.symm (Iso.refl N)).hom.app U
      ((tensorLeftUnitIso Y N).inv.app U t)) = _
    rw [hu, sheafTensorCongr_section]
    rfl
  have hs : s = r • u := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
    rw [Scheme.Modules.Hom.app_smul]
    have he : e.hom.app U u = Scheme.Modules.toUnitSection U 1 :=
      ConcreteCategory.congr_hom (congrArg (fun f => f.app U) e.inv_hom_id) _
    rw [he]
    change e.hom.app U s = Scheme.Modules.toUnitSection U (r * 1)
    rw [mul_one]
    rfl
  calc
    _ = r * Scheme.Modules.ofUnitSection U (pair.hom.app U (tensorSection Y M N U u t)) := by
      rw [hs, tensor_smul_left, Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul]
    _ = _ := by rw [hv]

#print axioms cuspIdeal_center_scalar_order
#print axioms inverseTrivialization_pair

end TwistLocalFrames

#print axioms extendsGenerator_unique
#print axioms canonical_iff_exists
#print axioms disk_uniformizer
#print axioms exists_unit_of_pow_eq_unit
#print axioms span_eq_of_pow_eq_unit
#print axioms compactComponent_integral
#print axioms component_extension

section TwistOrders
open ArithmeticThetaSheafTensor ArithmeticThetaPullback OpenDiscriminantFullTateExpansionR0182
open GlobalFamilyDiscriminantR0180 InitialHodgeSection

lemma cuspIdeal_other_scalar_order
    (D : LevelData k L) (X : Compactification k L D) (T : DiskTest k L D X)
    (x : X.space) (hx : x ∈ boundary k L D X)
    (hne : x ≠ T.disk (closedPoint k))
    (η : Γ((Scheme.Modules.pullback T.disk).obj
      (cuspIdeal k L D X x).module, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj
      (cuspIdeal k L D X x).module) ⊤ η) :
    (trivializedScalar k L (cuspIdeal k L D X x).module
      (cuspIdealOpenIso k L D X x hx) T η).order = 0 := by
  let I := cuspIdeal k L D X x
  have hi := cuspIdeal_invertible k L D X x hx
  have ht := cuspIdeal_other_disk_eq_top k L D X T x hx hne
  have hi' : (I.comap T.disk).IsInvertible := by
    rw [show I.comap T.disk = ⊤ from ht]
    exact Scheme.IdealSheafData.isInvertible_top
  letI := hi.isIso_pullbackModuleComparison T.disk hi'
  letI := ideal_module_inclusion_isIso (I.comap T.disk) ht
  let e := asIso (I.pullbackModuleComparison T.disk) ≪≫ asIso (I.comap T.disk).moduleι
  let ξ := e.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
  have hf : IsFrame ((Scheme.Modules.pullback T.disk).obj I.module) ⊤ ξ := iso_one_frame e.symm
  rw [trivializedScalar_frame_order k L _ _ T η ξ hη hf]
  have he : ((Scheme.Modules.pullback T.disk).map I.moduleι ≫
      (Scheme.Modules.pullbackUnitIso T.disk).hom).app ⊤ ξ =
      Scheme.Modules.toUnitSection ⊤ 1 := by
    rw [← ideal_pullback_inclusion]
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤) e.inv_hom_id) _
  have hg := transportSection_to_unit (genericInclusion k) _ _ _
    (cuspIdealGenericIso_hom k L D X T x hx) ξ
  have hh := congrArg (fun θ => (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    (Scheme.Modules.ofUnitSection ⊤ θ)) hg
  change trivializedScalar k L I.module (cuspIdealOpenIso k L D X x hx) T ξ = _ at hh
  rw [he] at hh
  change trivializedScalar k L I.module (cuspIdealOpenIso k L D X x hx) T ξ =
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      ((genericInclusion k).appLE ⊤ ⊤ (by simp) 1) at hh
  rw [map_one, map_one] at hh
  rw [hh, HahnSeries.order_one]

/-- The intrinsic order of the prescribed generic generator in an integral disk lattice. -/
def diskOrder {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) : ℤ :=
  let η := (diskFrame_exists k L H T).choose
  let hη := (diskFrame_exists k L H T).choose_spec
  ((disk_coefficient_exists k L H T η hη).choose).order

lemma diskOrder_eq {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η)
    (a : LaurentSeries k)
    (ha : scalar (LaurentSeries k) a • diskRestriction k L H T η =
      hodgeGenerator k L T.differential) : diskOrder k L H T = a.order := by
  exact disk_coefficient_order_frame_independent k L H T _ η
    (diskFrame_exists k L H T).choose_spec hη _ a
    (disk_coefficient_exists k L H T _ (diskFrame_exists k L H T).choose_spec).choose_spec.1 ha

lemma diskOrder_shared_center (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T S : DiskTest k L D X)
    (hc : T.disk (closedPoint k) = S.disk (closedPoint k)) :
    diskOrder k L H T = diskOrder k L H S := by
  exact disk_shared_center_coefficient_order k L hL heven H T S hc _ _
    (diskFrame_exists k L H T).choose_spec (diskFrame_exists k L H S).choose_spec _ _
    (disk_coefficient_exists k L H T _ (diskFrame_exists k L H T).choose_spec).choose_spec.1
    (disk_coefficient_exists k L H S _ (diskFrame_exists k L H S).choose_spec).choose_spec.1

lemma canonical_iff_diskOrder_zero {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) : Canonical k L H ↔ ∀ T, diskOrder k L H T = 0 := by
  rw [canonical_iff_exists k L H]
  apply forall_congr'
  intro T
  exact extendsGenerator_iff_order_zero k L H T _
    (diskFrame_exists k L H T).choose_spec _
    (disk_coefficient_exists k L H T _ (diskFrame_exists k L H T).choose_spec).choose_spec.1

lemma twist_diskOrder {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (J : X.space.Modules)
    (hJ : Scheme.Modules.IsInvertible J)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η) :
    diskOrder k L (twistExtension k L H J hJ eJ) T =
      diskOrder k L H T - (trivializedScalar k L J eJ T η).order := by
  obtain ⟨U, s, hU, hs⟩ := local_frame_exists hJ (T.disk (closedPoint k))
  obtain ⟨V, t, hV, ht⟩ := local_frame_exists H.invertible (T.disk (closedPoint k))
  let W := U ⊓ V
  let sW := res J (inf_le_left : W ≤ U) s
  let tW := res H.line (inf_le_right : W ≤ V) t
  have hsW : IsFrame J W sW := frame_restrict _ _ _ hs
  have htW : IsFrame H.line W tW := frame_restrict _ _ _ ht
  have hW : T.disk (closedPoint k) ∈ W := ⟨hU,hV⟩
  let hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hW).ge
  have ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ W) := by
    intro z hz
    change X.inclusion (T.base z) ∈ W
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hd (Set.mem_univ _)
  let ξ := res _ hd (Scheme.Modules.pullbackLocalSection T.disk sW)
  let θ := res _ hd (Scheme.Modules.pullbackLocalSection T.disk tW)
  let ζ : Γ((Scheme.Modules.pullback T.disk).obj
      (twistExtension k L H J hJ eJ).line, ⊤) := res _ hd (Scheme.Modules.pullbackLocalSection T.disk
    (tensorSection X.space J H.line W sW tW))
  have hfξ : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ ξ :=
    frame_restrict _ _ _ (pullback_frame _ _ _ hsW)
  have hfθ : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ θ :=
    frame_restrict _ _ _ (pullback_frame _ _ _ htW)
  have hfζ : IsFrame ((Scheme.Modules.pullback T.disk).obj
      (twistExtension k L H J hJ eJ).line) ⊤ ζ :=
    frame_restrict _ _ _ (pullback_frame _ _ _ (tensor_section_frame sW tW hsW htW))
  obtain ⟨a, ha, _⟩ := disk_coefficient_exists k L H T θ hfθ
  obtain ⟨b, hb, _⟩ := disk_coefficient_exists k L (twistExtension k L H J hJ eJ) T ζ hfζ
  let c := trivializedScalar k L J eJ T ξ
  have hc : scalar (LaurentSeries k) c = T.base.appLE (X.inclusion ⁻¹ᵁ W) ⊤ ho
      (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion sW))) := by
    have hh := trivialized_local_section k L J eJ T W sW hd ho
    have hh' := congrArg (fun v : Γ((SheafOfModules.unit (Puncture k).ringCatSheaf : (Puncture k).Modules), ⊤) =>
      scalar (LaurentSeries k) ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (Scheme.Modules.ofUnitSection ⊤ v))) hh
    change scalar (LaurentSeries k) c = scalar (LaurentSeries k)
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (T.base.appLE (X.inclusion ⁻¹ᵁ W) ⊤ ho
          (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion sW))))) at hh'
    exact hh'.trans (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom_inv_id _)
  have he : a = b * c := by
    have hh := ha.trans hb.symm
    change scalar (LaurentSeries k) a • diskRestriction k L H T θ =
      scalar (LaurentSeries k) b • diskRestriction k L (twistExtension k L H J hJ eJ) T ζ at hh
    have hdisk : diskRestriction k L (twistExtension k L H J hJ eJ) T ζ =
        T.base.appLE (X.inclusion ⁻¹ᵁ W) ⊤ ho
          (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion sW))) •
        diskRestriction k L H T θ := twist_disk_local k L H J hJ eJ T W sW tW hd ho
    rw [hdisk, ← hc, smul_smul] at hh
    have hf := diskRestriction_frame k L H T θ hfθ ⊤ le_rfl
    rw [InitialHodgeSection.res_self] at hf
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).1
    apply hf.1
    simpa only [scalar, map_mul] using hh
  have hn := disk_coefficient_ne_zero k L (twistExtension k L H J hJ eJ) T ζ hfζ b hb
  have hcn := trivializedScalar_ne_zero k L J eJ T ξ hfξ
  have heo : a.order = b.order + c.order := by rw [he, HahnSeries.order_mul hn hcn]
  rw [diskOrder_eq k L _ T ζ hfζ b hb, diskOrder_eq k L H T θ hfθ a ha,
    trivializedScalar_frame_order k L J eJ T η ξ hη hfξ]
  dsimp only [c] at heo
  omega

#print axioms twist_diskOrder
#print axioms cuspIdeal_other_scalar_order

def pullbackPair {Y Z : Scheme.{0}} (p : Z ⟶ Y) (J K : Y.Modules)
    (pair : sheafTensor Y J K ≅ SheafOfModules.unit Y.ringCatSheaf) :
    sheafTensor Z ((Scheme.Modules.pullback p).obj J) ((Scheme.Modules.pullback p).obj K) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (pullback_sheafTensor_iso Z Y p J K).symm ≪≫
    (Scheme.Modules.pullback p).mapIso pair ≪≫ Scheme.Modules.pullbackUnitIso p

lemma pullbackPair_local {Y Z : Scheme.{0}} (p : Z ⟶ Y) (J K : Y.Modules)
    (pair : sheafTensor Y J K ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (s : Γ(J,U)) (t : Γ(K,U)) :
    (pullbackPair p J K pair).hom.app (p ⁻¹ᵁ U)
      (tensorSection Z _ _ _ (Scheme.Modules.pullbackLocalSection p s)
        (Scheme.Modules.pullbackLocalSection p t)) =
    Scheme.Modules.toUnitSection _ (p.app U
      (Scheme.Modules.ofUnitSection U (pair.hom.app U (tensorSection Y J K U s t)))) := by
  have hh := pullback_sheafTensor_local_section Z Y p J K U s t
  rw [← hh]
  change (Scheme.Modules.pullbackUnitIso p).hom.app _
    (((Scheme.Modules.pullback p).map pair.hom).app _
      ((pullback_sheafTensor_iso Z Y p J K).inv.app _
        ((pullback_sheafTensor_iso Z Y p J K).hom.app _ _))) = _
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (p ⁻¹ᵁ U)) (pullback_sheafTensor_iso Z Y p J K).hom_inv_id)
    (Scheme.Modules.pullbackLocalSection p (tensorSection Y J K U s t))
  change (pullback_sheafTensor_iso Z Y p J K).inv.app (p ⁻¹ᵁ U)
    ((pullback_sheafTensor_iso Z Y p J K).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (tensorSection Y J K U s t))) =
    Scheme.Modules.pullbackLocalSection p (tensorSection Y J K U s t) at hi
  rw [hi, ← Scheme.Modules.pullbackLocalSection_app]
  exact Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection p U _

lemma unit_section_frame_isUnit {Y : Scheme.{0}} (U : Y.Opens)
    (θ : Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), U))
    (hf : IsFrame (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) U θ) :
    IsUnit (Scheme.Modules.ofUnitSection U θ) := by
  obtain ⟨a, ha⟩ := (hf U le_rfl).2 (Scheme.Modules.toUnitSection U 1)
  rw [InitialHodgeSection.res_self] at ha
  have h := congrArg (Scheme.Modules.ofUnitSection U) ha
  rw [Scheme.Modules.ofUnitSection_smul] at h
  change a * Scheme.Modules.ofUnitSection U θ = 1 at h
  exact ⟨⟨_, a, by rw [mul_comm]; exact h, h⟩, rfl⟩

lemma generic_open_scalar_eq_disk {D : LevelData k L} {X : Compactification k L D}
    (T : DiskTest k L D X) (U : X.space.Opens)
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U))
    (r : Γ(X.space,U)) :
    T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho (X.inclusion.app U r) =
      (genericInclusion k).appLE ⊤ ⊤ (by simp) (T.disk.appLE U ⊤ hd r) := by
  have h : X.inclusion.app U ≫ T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho =
      T.disk.appLE U ⊤ hd ≫ (genericInclusion k).appLE ⊤ ⊤ (by simp) := by
    change X.inclusion.appLE U (X.inclusion ⁻¹ᵁ U) le_rfl ≫ T.base.appLE _ _ ho = _
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact T.extends_eq.2.1.symm
  exact ConcreteCategory.congr_hom h r

lemma trivializedScalar_local {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X) (U : X.space.Opens) (s : Γ(J,U))
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    trivializedScalar k L J eJ T (res _ hd (Scheme.Modules.pullbackLocalSection T.disk s)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho
          (Scheme.Modules.ofUnitSection _ (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)))) := by
  exact congrArg (fun θ : Γ((SheafOfModules.unit (Puncture k).ringCatSheaf : (Puncture k).Modules), ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom (Scheme.Modules.ofUnitSection ⊤ θ))
    (trivialized_local_section k L J eJ T U s hd ho)

lemma inverse_local_scalar_product {D : LevelData k L} {X : Compactification k L D}
    (J K : X.space.Modules)
    (pair : sheafTensor X.space J K ≅ SheafOfModules.unit X.space.ringCatSheaf)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X) (U : X.space.Opens) (s : Γ(J,U)) (t : Γ(K,U))
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U)) :
    trivializedScalar k L J eJ T
      (res _ hd (Scheme.Modules.pullbackLocalSection T.disk s)) *
    trivializedScalar k L K (inverseTrivialization _ _ eJ (pullbackPair X.inclusion J K pair)) T
      (res _ hd (Scheme.Modules.pullbackLocalSection T.disk t)) =
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      ((genericInclusion k).appLE ⊤ ⊤ (by simp)
        (T.disk.appLE U ⊤ hd (Scheme.Modules.ofUnitSection U
          (pair.hom.app U (tensorSection X.space J K U s t))))) := by
  rw [trivializedScalar_local k L J eJ T U s hd ho,
    trivializedScalar_local k L K _ T U t hd ho]
  change (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    (T.base.appLE _ ⊤ ho (Scheme.Modules.ofUnitSection _
      (eJ.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s)))) *
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    (T.base.appLE _ ⊤ ho (Scheme.Modules.ofUnitSection _
      ((inverseTrivialization _ _ eJ (pullbackPair X.inclusion J K pair)).hom.app _
        (Scheme.Modules.pullbackLocalSection X.inclusion t)))) = _
  rw [← map_mul, ← map_mul, ← inverseTrivialization_pair,
    pullbackPair_local]
  congr 1
  exact generic_open_scalar_eq_disk k L T U hd ho _

#print axioms inverse_local_scalar_product

lemma inverse_scalar_order {D : LevelData k L} {X : Compactification k L D}
    (J K : X.space.Modules) (hJ : Scheme.Modules.IsInvertible J)
    (hK : Scheme.Modules.IsInvertible K)
    (pair : sheafTensor X.space J K ≅ SheafOfModules.unit X.space.ringCatSheaf)
    (eJ : (Scheme.Modules.pullback X.inclusion).obj J ≅
      SheafOfModules.unit (OpenBase k L D).ringCatSheaf)
    (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤))
    (ξ : Γ((Scheme.Modules.pullback T.disk).obj K, ⊤))
    (hη : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η)
    (hξ : IsFrame ((Scheme.Modules.pullback T.disk).obj K) ⊤ ξ) :
    (trivializedScalar k L K (inverseTrivialization _ _ eJ
      (pullbackPair X.inclusion J K pair)) T ξ).order =
      -(trivializedScalar k L J eJ T η).order := by
  let eK := inverseTrivialization _ _ eJ (pullbackPair X.inclusion J K pair)
  obtain ⟨U, s, hU, hs⟩ := local_frame_exists hJ (T.disk (closedPoint k))
  obtain ⟨V, t, hV, ht⟩ := local_frame_exists hK (T.disk (closedPoint k))
  let W := U ⊓ V
  let sW := res J (inf_le_left : W ≤ U) s
  let tW := res K (inf_le_right : W ≤ V) t
  have hsW : IsFrame J W sW := frame_restrict _ _ _ hs
  have htW : IsFrame K W tW := frame_restrict _ _ _ ht
  have hW : T.disk (closedPoint k) ∈ W := ⟨hU,hV⟩
  let hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hW).ge
  have ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ W) := by
    intro z hz
    change X.inclusion (T.base z) ∈ W
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hd (Set.mem_univ _)
  let ηW := res _ hd (Scheme.Modules.pullbackLocalSection T.disk sW)
  let ξW := res _ hd (Scheme.Modules.pullbackLocalSection T.disk tW)
  have hfη : IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ ηW :=
    frame_restrict _ _ _ (pullback_frame _ _ _ hsW)
  have hfξ : IsFrame ((Scheme.Modules.pullback T.disk).obj K) ⊤ ξW :=
    frame_restrict _ _ _ (pullback_frame _ _ _ htW)
  let r := Scheme.Modules.ofUnitSection W (pair.hom.app W
    (tensorSection X.space J K W sW tW))
  have hr : IsUnit r := unit_section_frame_isUnit W _
    (frame_iso pair _ (tensor_section_frame sW tW hsW htW))
  let b : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    (T.disk.appLE W ⊤ hd r)
  have hbu : IsUnit b := (hr.map (T.disk.appLE W ⊤ hd).hom).map
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
  have hp : trivializedScalar k L J eJ T ηW * trivializedScalar k L K eK T ξW =
      algebraMap (PowerSeries k) (LaurentSeries k) b := by
    have hp' := inverse_local_scalar_product k L J K pair eJ T W sW tW hd ho
    exact hp'.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))))
        (T.disk.appLE W ⊤ hd r))
  have he : (trivializedScalar k L J eJ T ηW).order +
      (trivializedScalar k L K eK T ξW).order = 0 := by
    rw [← HahnSeries.order_mul (trivializedScalar_ne_zero k L J eJ T ηW hfη)
      (trivializedScalar_ne_zero k L K eK T ξW hfξ), hp,
      laurent_order_of_powerSeries k b 0 (PowerSeries.order_zero_of_unit hbu)]
    rfl
  have h1 := trivializedScalar_frame_order k L J eJ T η ηW hη hfη
  have h2 := trivializedScalar_frame_order k L K eK T ξ ξW hξ hfξ
  change (trivializedScalar k L K eK T ξ).order = _
  omega

#print axioms inverse_scalar_order

open scoped Classical

lemma line_disk_frame_exists {D : LevelData k L} {X : Compactification k L D}
    (J : X.space.Modules) (hJ : Scheme.Modules.IsInvertible J) (T : DiskTest k L D X) :
    ∃ η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤),
      IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η := by
  obtain ⟨e⟩ := (hJ.pullback T.disk).nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨e.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1), iso_one_frame e.symm⟩

/-- Both elementary corrections are actual invertible global sheaves with
specified open identifications. Their change is supported at exactly one cusp. -/
lemma exists_cusp_steps (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (x : X.space) (hx : x ∈ boundary k L D X) :
    (∃ H' : Extension k L D X, ∀ T : DiskTest k L D X,
      diskOrder k L H' T = diskOrder k L H T - if T.disk (closedPoint k) = x then 1 else 0) ∧
    (∃ H' : Extension k L D X, ∀ T : DiskTest k L D X,
      diskOrder k L H' T = diskOrder k L H T + if T.disk (closedPoint k) = x then 1 else 0) := by
  classical
  let J := (cuspIdeal k L D X x).module
  have hJ : Scheme.Modules.IsInvertible J := (cuspIdeal_invertible k L D X x hx).isInvertible_module
  let eJ := cuspIdealOpenIso k L D X x hx
  have horder : ∀ (T : DiskTest k L D X)
      (η : Γ((Scheme.Modules.pullback T.disk).obj J, ⊤)),
      IsFrame ((Scheme.Modules.pullback T.disk).obj J) ⊤ η →
      (trivializedScalar k L J eJ T η).order = if T.disk (closedPoint k) = x then 1 else 0 := by
    intro T η hη
    split_ifs with hc
    · subst x
      exact cuspIdeal_center_scalar_order k L hL heven D X T η hη
    · exact cuspIdeal_other_scalar_order k L D X T x hx (Ne.symm hc) η hη
  constructor
  · refine ⟨twistExtension k L H J hJ eJ, ?_⟩
    intro T
    obtain ⟨η,hη⟩ := line_disk_frame_exists k L J hJ T
    rw [twist_diskOrder k L H J hJ eJ T η hη, horder T η hη]
  · obtain ⟨K, hK, ⟨p⟩⟩ := hJ.exists_tensor_inverse_monoidalV2
    let pair : sheafTensor X.space J K ≅ SheafOfModules.unit X.space.ringCatSheaf :=
      Scheme.Modules.tensorIsoSheafify J K ≪≫ p
    let eK := inverseTrivialization _ _ eJ (pullbackPair X.inclusion J K pair)
    refine ⟨twistExtension k L H K hK eK, ?_⟩
    intro T
    obtain ⟨η,hη⟩ := line_disk_frame_exists k L J hJ T
    obtain ⟨ξ,hξ⟩ := line_disk_frame_exists k L K hK T
    have hi := inverse_scalar_order k L J K hJ hK pair eJ T η ξ hη hξ
    rw [twist_diskOrder k L H K hK eK T ξ hξ]
    change (trivializedScalar k L K eK T ξ).order = _ at hi
    rw [hi, horder T η hη]
    omega

/-- Repeated elementary twists realize every integral order change at one cusp. -/
lemma exists_cusp_shift (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (x : X.space) (hx : x ∈ boundary k L D X) (n : ℤ) :
    ∃ H' : Extension k L D X, ∀ T : DiskTest k L D X,
      diskOrder k L H' T = diskOrder k L H T + n *
        (if T.disk (closedPoint k) = x then 1 else 0) := by
  classical
  induction n using Int.induction_on with
  | zero => exact ⟨H, fun T => by simp⟩
  | succ n ih =>
    obtain ⟨H',hH'⟩ := ih
    obtain ⟨H'',hH''⟩ := (exists_cusp_steps k L hL heven H' x hx).2
    refine ⟨H'', fun T => ?_⟩
    rw [hH'', hH']
    split_ifs <;> simp <;> omega
  | pred n ih =>
    obtain ⟨H',hH'⟩ := ih
    obtain ⟨H'',hH''⟩ := (exists_cusp_steps k L hL heven H' x hx).1
    refine ⟨H'', fun T => ?_⟩
    rw [hH'', hH']
    split_ifs <;> simp <;> omega

/-- Normalize a finite set of actual boundary centers; all disks at any one
center have the same intrinsic order. -/
lemma exists_normalized_on_finset (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} [IsAlgClosed k] {X : Compactification k L D}
    (S : Finset X.space) (hS : ∀ x ∈ S, x ∈ boundary k L D X)
    (H : Extension k L D X) :
    ∃ H' : Extension k L D X, ∀ T : DiskTest k L D X,
      T.disk (closedPoint k) ∈ S → diskOrder k L H' T = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨H, fun T h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert x S hxS ih =>
    have hx := hS x (Finset.mem_insert_self x S)
    have hS' : ∀ y ∈ S, y ∈ boundary k L D X := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    obtain ⟨H',hH'⟩ := ih hS'
    obtain ⟨T0,hT0⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X x hx
    obtain ⟨H'',hH''⟩ := exists_cusp_shift k L hL heven H' x hx (-diskOrder k L H' T0)
    refine ⟨H'', fun T hT => ?_⟩
    rw [hH'']
    rcases Finset.mem_insert.mp hT with hc | hc
    · rw [if_pos hc, mul_one]
      have he := diskOrder_shared_center k L hL heven H' T T0 (hc.trans hT0.symm)
      omega
    · have hne : T.disk (closedPoint k) ≠ x := fun he => hxS (he ▸ hc)
      rw [if_neg hne, mul_zero, add_zero]
      exact hH' T hc

#print axioms exists_normalized_on_finset

end TwistOrders

end ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

namespace ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open CompactHodgeLatticeExtensionR0182

/-- The actual open Hodge line admits an invertible extension calibrated to
the prescribed normalized Tate differential on every actual boundary disk. -/
theorem compact_hodge_lattice_extension
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) [IsAlgClosed k] (X : Compactification k L D) :
    ∃ H : Extension k L D X, Canonical k L H := by
  classical
  obtain ⟨H⟩ := extension_exists k L D X
  let S := (BoundaryGeometry.boundary_finite k L D X).toFinset
  have hS : ∀ x ∈ S, x ∈ boundary k L D X := by
    intro x hx
    exact (BoundaryGeometry.boundary_finite k L D X).mem_toFinset.mp hx
  obtain ⟨H',hH'⟩ := exists_normalized_on_finset k L hL heven S hS H
  refine ⟨H', (canonical_iff_diskOrder_zero k L H').2 ?_⟩
  intro T
  exact hH' T ((BoundaryGeometry.boundary_finite k L D X).mem_toFinset.mpr T.extends_eq.2.2)

#print axioms compact_hodge_lattice_extension
end ArithmeticThetaBoundaryHodgeR0182
