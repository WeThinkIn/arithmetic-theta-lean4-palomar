module

public import SimultaneousUnaryRootsDefinitionsR0187
public import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
public import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalization
open ArithmeticThetaNormalizedSections ArithmeticThetaKummerCover

/-- Dominance of the specified puncture determines its image point. -/
lemma field_point_generic (E : Type) [Field E] {Z : Scheme.{0}} [IsIntegral Z]
    (q : Spec (CommRingCat.of E) ⟶ Z) [IsDominant q] :
    q (IsLocalRing.closedPoint E) = genericPoint Z := by
  have hr : Set.range q = {q (IsLocalRing.closedPoint E)} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg q (Subsingleton.elim _ _)
    · intro hz
      exact ⟨_, hz.symm⟩
  apply IsGenericPoint.eq _ (genericPoint_spec Z)
  rw [isGenericPoint_def, ← hr]
  exact q.denseRange.closure_range

/-- The field embedding is induced by the actual punctured disk morphism. -/
lemma disk_field_map (k : Type) [Field k] {Z : Scheme.{0}} [IsIntegral Z]
    (f : Disk k ⟶ Z) [IsDominant (genericInclusion k ≫ f)] :
    ∃ φ : Z.functionField →+* LaurentSeries k,
      Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (genericPoint Z) =
        genericInclusion k ≫ f := by
  have hgeneral {X : Scheme.{0}} (E : Type) [Field E]
      (q : Spec (CommRingCat.of E) ⟶ X) (x : X)
      (hx : q (IsLocalRing.closedPoint E) = x) :
      ∃ φ : X.presheaf.stalk x →+* E,
        Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x = q := by
    subst x
    exact ⟨(Scheme.stalkClosedPointTo q).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk q⟩
  exact hgeneral (LaurentSeries k) (genericInclusion k ≫ f) _
    (field_point_generic _ _)

/-- Present the power-series disk as the valuation subring of its own
Laurent-series fraction field, preserving the literal inclusion. -/
def diskValuation (k : Type) [Field k] : ValuationSubring (LaurentSeries k) :=
  (ValuationRing.valuation (PowerSeries k) (LaurentSeries k)).valuationSubring

def diskValuationEquiv (k : Type) [Field k] :
    PowerSeries k ≃+* diskValuation k :=
  ValuationRing.equivInteger (PowerSeries k) (LaurentSeries k)

lemma diskValuationEquiv_coe (k : Type) [Field k] (a : PowerSeries k) :
    (diskValuationEquiv k a : LaurentSeries k) =
      algebraMap (PowerSeries k) (LaurentSeries k) a := rfl

/-- Apply the accepted valuative normalization theorem to this same disk.
Both the base triangle and the selected generated-field branch are retained. -/
lemma disk_normalization_branch
    (k : Type) [Field k] (Z : Scheme.{0}) [IsIntegral Z]
    [IsLocallyNoetherian Z] [CharZero Z.functionField]
    (hZ : NormalAffine Z) [Algebra Z.functionField (LaurentSeries k)]
    (K s : ℕ) (hK : 0 < K) (r : Fin s → LaurentSeries k)
    (c : Fin s → Z.functionField)
    (hr : ∀ j, r j ^ K = algebraMap Z.functionField (LaurentSeries k) (c j))
    (f : Disk k ⟶ Z)
    (hf : genericInclusion k ≫ f = genericExtensionMap Z (LaurentSeries k)) :
    ∃ g : Disk k ⟶ rootCover Z (LaurentSeries k) s r,
      g ≫ rootCoverMap Z (LaurentSeries k) s r = f ∧
      genericInclusion k ≫ g =
        Spec.map (CommRingCat.ofHom (generatedRootField Z (LaurentSeries k) s r).subtype) ≫
          extensionToNormalization Z (generatedRootField Z (LaurentSeries k) s r) := by
  let e := diskValuationEquiv k
  let d : Spec (CommRingCat.of (diskValuation k)) ⟶ Disk k :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  let di : Disk k ⟶ Spec (CommRingCat.of (diskValuation k)) :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hid : di ≫ d = 𝟙 (Disk k) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp e.toRingHom)) = _
    simp
  have hinc : Spec.map (CommRingCat.ofHom
      (algebraMap (diskValuation k) (LaurentSeries k))) ≫ d = genericInclusion k := by
    rw [← Spec.map_comp]
    rfl
  have hinc' : genericInclusion k ≫ di =
      Spec.map (CommRingCat.ofHom
        (algebraMap (diskValuation k) (LaurentSeries k))) := by
    rw [← hinc, Category.assoc]
    have : d ≫ di = 𝟙 _ := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (e.toRingHom.comp e.symm.toRingHom)) = _
      simp
    rw [this, Category.comp_id]
  obtain ⟨g, hg, _⟩ :=
    ArithmeticThetaCoverComparison.normalization_prescribed_valuative_branch
      Z hZ (LaurentSeries k) K s hK r c hr (diskValuation k) (d ≫ f)
      (by rw [← Category.assoc, hinc, hf])
  refine ⟨di ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg.1, ← Category.assoc, hid, Category.id_comp]
  · rw [← Category.assoc, hinc', hg.2]

open ArithmeticThetaNormalizationField ArithmeticThetaLineRoot
open ArithmeticThetaPullback ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185

/-- Evaluate a regular scalar through an actual affine-spectrum map. -/
def specScalar {A : Type} [CommRing A] {Z : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Z) (U : Z.Opens)
    (hU : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U) : Γ(Z,U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (f.appLE U ⊤ hU).hom

lemma specScalar_comp {A B : Type} [CommRing A] [CommRing B] {Z : Scheme.{0}}
    (ρ : A →+* B) (f : Spec (CommRingCat.of A) ⟶ Z) (U : Z.Opens)
    (hU : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U)
    (hV : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤
      (Spec.map (CommRingCat.ofHom ρ) ≫ f) ⁻¹ᵁ U) (a : Γ(Z,U)) :
    specScalar (Spec.map (CommRingCat.ofHom ρ) ≫ f) U hV a =
      ρ (specScalar f U hU a) := by
  have hc := (Spec.map (CommRingCat.ofHom ρ)).appLE_comp_appLE f U ⊤ ⊤ hU (by simp)
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ)
  unfold specScalar
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    (((Spec.map (CommRingCat.ofHom ρ) ≫ f).appLE U ⊤ hV) a) = _
  rw [← hc]
  exact congrArg (fun q => q (f.appLE U ⊤ hU a)) hn

lemma specScalar_generic {Z : Scheme.{0}} [IsIntegral Z]
    (E : Type) [Field E] [Algebra Z.functionField E]
    (U : Z.Opens) [Nonempty U]
    (hU : (⊤ : (Spec (CommRingCat.of E)).Opens) ≤ genericExtensionMap Z E ⁻¹ᵁ U)
    (a : Γ(Z,U)) :
    specScalar (genericExtensionMap Z E) U hU a =
      algebraMap Z.functionField E (Z.germToFunctionField U a) := by
  have he := congrArg (fun q => q a) (genericSectionsIso_base_compat Z E U)
  calc
    _ = (genericSectionsIso Z E U).hom ((genericExtensionMap Z E).app U a) := by
      change (Scheme.ΓSpecIso (CommRingCat.of E)).hom
        ((Spec (CommRingCat.of E)).presheaf.map (homOfLE hU).op
          ((genericExtensionMap Z E).app U a)) =
        (Scheme.ΓSpecIso (CommRingCat.of E)).hom
          ((Spec (CommRingCat.of E)).presheaf.map _
            ((genericExtensionMap Z E).app U a))
      congr 2
    _ = _ := he

/-- The Laurent value of a chart scalar is the image of its actual generic germ. -/
lemma diskScalar_generic (k : Type) [Field k] {Z : Scheme.{0}} [IsIntegral Z]
    [Algebra Z.functionField (LaurentSeries k)] (f : Disk k ⟶ Z)
    (hf : genericInclusion k ≫ f = genericExtensionMap Z (LaurentSeries k))
    (U : Z.Opens) [Nonempty U]
    (hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U) (a : Γ(Z,U)) :
    algebraMap (PowerSeries k) (LaurentSeries k) (specScalar f U hU a) =
      algebraMap Z.functionField (LaurentSeries k) (Z.germToFunctionField U a) := by
  have hV : (⊤ : (Puncture k).Opens) ≤ (genericInclusion k ≫ f) ⁻¹ᵁ U := by
    rw [hf, genericExtensionMap_preimage]
  have hc := specScalar_comp (algebraMap (PowerSeries k) (LaurentSeries k)) f U hU hV a
  change specScalar (genericInclusion k ≫ f) U hV a = _ at hc
  simp only [hf] at hc
  exact hc.symm.trans (specScalar_generic (LaurentSeries k) U _ a)

/-- Finite surjective covers preserve dimension; on an integral smooth cover
this identifies the relative dimension of the actual composite as one. -/
lemma finite_smooth_curve_dimension (k : Type) [Field k]
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
    (b : Z ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 b]
    (p : Y ⟶ Z) [IsFinite p] [Surjective p] [Smooth (p ≫ b)] :
    SmoothOfRelativeDimension 1 (p ≫ b) := by
  obtain ⟨n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace (p ≫ b)
  letI := hn
  have hd := topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
    (p ≫ b) b p rfl (IsLocalRing.closedPoint k)
  have hb : b.base ⁻¹' {IsLocalRing.closedPoint k} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  have hp : (p ≫ b).base ⁻¹' {IsLocalRing.closedPoint k} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [hb, hp, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Z).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph] at hd
  have hZ := le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le b 1)
    (SmoothOfRelativeDimension.le_topologicalKrullDim b 1)
  have hY := le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le (p ≫ b) n)
    (SmoothOfRelativeDimension.le_topologicalKrullDim (p ≫ b) n)
  have hn1 : n = 1 := by
    have he : (n : WithBot ℕ∞) = 1 := hY.symm.trans (hd.symm.trans hZ)
    exact_mod_cast he
  subst n
  infer_instance

open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

lemma scalar_specScalar {A : Type} [CommRing A] {Z : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Z) (U : Z.Opens)
    (hU : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U) (a : Γ(Z,U)) :
    scalar A (specScalar f U hU a) = f.appLE U ⊤ hU a := by
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm_apply_apply _

lemma coordinate_spec {Z : Scheme.{0}} (J : Z.Modules) (U : Z.Opens)
    (e : LocalFrame Z J U) (t : Sections Z J) :
    res J le_top t = sectionCoordinate Z J U e t • e.equiv U le_rfl 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]
  exact ((e.equiv U le_rfl).apply_symm_apply _).symm

lemma power_coordinate_spec {Z : Scheme.{0}} (J : Z.Modules) (U : Z.Opens)
    (e : LocalFrame Z J U) (K : ℕ) (F : Sections Z (tensorPower Z J K)) :
    res (tensorPower Z J K) le_top F =
      sectionCoordinate Z (tensorPower Z J K) U (tensorPowerFrame Z J U e K) F •
        tensorPowerSection Z J K U (e.equiv U le_rfl 1) := by
  rw [tensorPowerSection_frame, one_pow]
  exact coordinate_spec _ _ _ _

/-- A chart coefficient computes the actual global pullback whenever the
whole source lies in that chart. -/
lemma pullback_coordinate {A : Type} [CommRing A] {Z : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Z) (J : Z.Modules) (U : Z.Opens)
    (e : LocalFrame Z J U)
    (hU : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U) (t : Sections Z J) :
    pullbackGlobalSection f J t =
      scalar A (specScalar f U hU (sectionCoordinate Z J U e t)) •
        res ((Scheme.Modules.pullback f).obj J) hU
          (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) := by
  have ht := transportSection_restrict f J _ (Iso.refl _) t U ⊤ hU
  simp only [transport_as_app, id_app_apply, InitialHodgeSection.res_self] at ht
  rw [coordinate_spec J U e t, Scheme.Modules.pullbackLocalSection_smul,
    InitialHodgeSection.res_smul] at ht
  rw [scalar_specScalar]
  exact ht

lemma pullback_power_coordinate {A : Type} [CommRing A] {Z : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Z) (J : Z.Modules) (U : Z.Opens)
    (e : LocalFrame Z J U)
    (hU : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U)
    (K : ℕ) (F : Sections Z (tensorPower Z J K)) :
    pullbackPowerSection f J K F =
      scalar A (specScalar f U hU
        (sectionCoordinate Z (tensorPower Z J K) U (tensorPowerFrame Z J U e K) F)) •
      tensorPowerSection (Spec (CommRingCat.of A)) ((Scheme.Modules.pullback f).obj J) K ⊤
        (res ((Scheme.Modules.pullback f).obj J) hU
          (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1))) := by
  have ht := pull_power_scalar_local f J K F U (e.equiv U le_rfl 1)
    (sectionCoordinate Z (tensorPower Z J K) U (tensorPowerFrame Z J U e K) F)
    (power_coordinate_spec J U e K F)
  have hh := congrArg (res (tensorPower (Spec (CommRingCat.of A))
    ((Scheme.Modules.pullback f).obj J) K) hU) ht
  rw [InitialHodgeSection.res_res, InitialHodgeSection.res_self,
    InitialHodgeSection.res_smul, power_res] at hh
  rw [scalar_specScalar]
  exact hh

lemma specScalar_normalization {Z : Scheme.{0}} [IsIntegral Z]
    (E : Type) [Field E] [Algebra Z.functionField E]
    (V : (extensionNormalization Z E).Opens) [Nonempty V]
    (hV : (⊤ : (Spec (CommRingCat.of E)).Opens) ≤ extensionToNormalization Z E ⁻¹ᵁ V)
    (a : Γ(extensionNormalization Z E,V)) :
    specScalar (extensionToNormalization Z E) V hV a =
      normalizationFunctionFieldMap Z E ((extensionNormalization Z E).germToFunctionField V a) := by
  have he := congrArg (fun q => q a) (normalizationFunctionFieldMap_germ Z E V)
  calc
    _ = (normalizationSourceSectionsIso Z E V).hom ((extensionToNormalization Z E).app V a) := by
      change (Scheme.ΓSpecIso (CommRingCat.of E)).hom
        ((Spec (CommRingCat.of E)).presheaf.map (homOfLE hV).op
          ((extensionToNormalization Z E).app V a)) =
        (Scheme.ΓSpecIso (CommRingCat.of E)).hom
          ((Spec (CommRingCat.of E)).presheaf.map _
            ((extensionToNormalization Z E).app V a))
      congr 2
    _ = _ := he.symm

/-- Scalar evaluation through a prescribed normalization triangle. All ring
maps are explicit so this general naturality proof avoids unfolding concrete
Laurent-series presentations. -/
lemma normalization_scalar_triangle (A Ω E : Type) [CommRing A] [Field Ω] [Field E]
    {Z : Scheme.{0}} [IsIntegral Z] [Algebra Z.functionField E]
    (ρ : A →+* Ω) (ι : E →+* Ω)
    (g : Spec (CommRingCat.of A) ⟶ extensionNormalization Z E)
    (hg : Spec.map (CommRingCat.ofHom ρ) ≫ g =
      Spec.map (CommRingCat.ofHom ι) ≫ extensionToNormalization Z E)
    (V : (extensionNormalization Z E).Opens) [Nonempty V]
    (hV : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ g ⁻¹ᵁ V)
    (a : Γ(extensionNormalization Z E,V)) :
    ρ (specScalar g V hV a) =
      ι (normalizationFunctionFieldMap Z E
        ((extensionNormalization Z E).germToFunctionField V a)) := by
  have he : (⊤ : (Spec (CommRingCat.of E)).Opens) ≤
      extensionToNormalization Z E ⁻¹ᵁ V :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (extensionToNormalization Z E)
      (toNormalization_closedPoint_mem Z E V)).ge
  have hi : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ≤
      (Spec.map (CommRingCat.ofHom ι) ≫ extensionToNormalization Z E) ⁻¹ᵁ V := by
    intro z _
    exact he (by trivial)
  have hq : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ≤
      (Spec.map (CommRingCat.ofHom ρ) ≫ g) ⁻¹ᵁ V := by
    simpa only [hg] using hi
  have hc := specScalar_comp ρ g V hV hq a
  simp only [hg] at hc
  exact hc.symm.trans ((specScalar_comp ι (extensionToNormalization Z E) V he hi a).trans
    (congrArg ι (specScalar_normalization E V he a)))

open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CuspHalfDivisorLineR0185
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

lemma line_of_invertible {Z : Scheme.{0}} (J : Z.Modules)
    (hJ : Scheme.Modules.IsInvertible J) : IsLineBundle Z J := by
  intro z
  obtain ⟨U, u, hz, hu⟩ := local_frame_exists hJ z
  exact ⟨U, hz, ⟨localFrameIso Z J U (InitialHodgeSection.frame J u hu)⟩⟩

lemma powerCoefficient_ne_zero {Z : Scheme.{0}} [IsIntegral Z]
    (J : Z.Modules) (hJ : Scheme.Modules.IsInvertible J)
    (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (K : ℕ) (F : Sections Z (tensorPower Z J K)) (hF : F ≠ 0) :
    powerCoefficient Z J U e K F ≠ 0 := by
  intro hc
  apply hF
  apply sectionCoefficient_injective Z (tensorPower Z J K)
    (line_of_invertible _ (tensorPower_invertible J hJ K)) U (tensorPowerFrame Z J U e K)
  simpa only [powerCoefficient, sectionCoefficient, sectionCoordinate, map_zero] using hc

/-- Express the prescribed disk frame in the pulled-back chart frame.
The resulting roots all lie in the same power-series ring. -/
lemma prescribed_series_roots (k : Type) [Field k] {Z : Scheme.{0}} [IsIntegral Z]
    [Algebra Z.functionField (LaurentSeries k)]
    (f : Disk k ⟶ Z)
    (hf : genericInclusion k ≫ f = genericExtensionMap Z (LaurentSeries k))
    (J : Z.Modules) (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U)
    (K s : ℕ) (F : Fin s → Sections Z (tensorPower Z J K))
    (h : Sections (Disk k) ((Scheme.Modules.pullback f).obj J))
    (a : Fin s → PowerSeries k)
    (ha : ∀ j, pullbackPowerSection f J K (F j) =
      scalar (PowerSeries k) ((a j)^K) • tensorPowerSection (Disk k)
        ((Scheme.Modules.pullback f).obj J) K ⊤ h) :
    ∃ c : PowerSeries k,
      h = scalar (PowerSeries k) c •
        res ((Scheme.Modules.pullback f).obj J) hU
          (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) ∧
      ∀ j, (algebraMap (PowerSeries k) (LaurentSeries k) (a j * c)) ^ K =
        algebraMap Z.functionField (LaurentSeries k) (powerCoefficient Z J U e K (F j)) := by
  let w := res ((Scheme.Modules.pullback f).obj J) hU
    (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1))
  have hw : IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ w :=
    frame_restrict _ hU _ (pullback_frame f J _ (frame_generator Z J U e))
  obtain ⟨C, hC⟩ := (hw ⊤ le_rfl).surjective h
  rw [InitialHodgeSection.res_self] at hC
  change C • w = h at hC
  let c : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom C
  have hc : scalar (PowerSeries k) c = C :=
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm_apply_apply C
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    exact hC.symm
  · intro j
    let d := sectionCoordinate Z (tensorPower Z J K) U (tensorPowerFrame Z J U e K) (F j)
    have ht := pullback_power_coordinate f J U e hU K (F j)
    have he : scalar (PowerSeries k) (specScalar f U hU d) =
        scalar (PowerSeries k) ((a j)^K) * C^K := by
      apply (InitialHodgeSection.tensor_frame _ w hw K ⊤ le_rfl).injective
      simp only [InitialHodgeSection.res_self]
      rw [mul_smul]
      change _ = scalar (PowerSeries k) ((a j)^K) • (C^K •
        tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj J) K ⊤ w)
      rw [← InitialHodgeSection.tensor_smul, hC]
      exact ht.symm.trans (ha j)
    have hd : specScalar f U hU d = (a j * c)^K := by
      have he' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom he
      simpa only [scalar, map_mul, map_pow, Iso.inv_hom_id_apply,
        CommRingCat.hom_comp, RingHom.comp_apply, mul_pow] using he'
    rw [← map_pow, ← hd]
    exact diskScalar_generic k f hf U hU d

/-- The prescribed generic scalar determines the entire regular disk section,
using the canonical pullback triangle and the accepted compatible frame. -/
lemma normalization_section_value (k : Type) [Field k]
    {Z : Scheme.{0}} [IsIntegral Z] [Algebra Z.functionField (LaurentSeries k)]
    (E : IntermediateField Z.functionField (LaurentSeries k))
    (J : Z.Modules) (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (eY : LocalFrame (extensionNormalization Z E)
      ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J)
      (extensionFromNormalization Z E ⁻¹ᵁ U))
    (heY : FramePullbackCompatible (extensionFromNormalization Z E) J U e eY)
    (f : Disk k ⟶ Z) (hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U)
    (g : Disk k ⟶ extensionNormalization Z E)
    (hg : g ≫ extensionFromNormalization Z E = f)
    (hbranch : genericInclusion k ≫ g =
      Spec.map (CommRingCat.ofHom E.subtype) ≫ extensionToNormalization Z E)
    (t : Sections (extensionNormalization Z E)
      ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J))
    (v : PowerSeries k)
    (hv : (normalizationFunctionFieldMap Z E
      (sectionCoefficient (extensionNormalization Z E)
        ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J)
        (extensionFromNormalization Z E ⁻¹ᵁ U) eY t) : LaurentSeries k) =
      algebraMap (PowerSeries k) (LaurentSeries k) v) :
    (along g (extensionFromNormalization Z E) f hg J).hom.app ⊤
      (pullbackGlobalSection g ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J) t) =
      scalar (PowerSeries k) v • res ((Scheme.Modules.pullback f).obj J) hU
        (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) := by
  let p := extensionFromNormalization Z E
  let V := p ⁻¹ᵁ U
  let d := sectionCoordinate (extensionNormalization Z E) ((Scheme.Modules.pullback p).obj J) V eY t
  have hV : (⊤ : (Disk k).Opens) ≤ g ⁻¹ᵁ V := by
    change ⊤ ≤ (g ≫ p) ⁻¹ᵁ U
    simpa only [p, hg] using hU
  have hs := normalization_scalar_triangle (PowerSeries k) (LaurentSeries k) E
    (algebraMap (PowerSeries k) (LaurentSeries k)) E.subtype g hbranch V hV d
  have hd : specScalar g V hV d = v := by
    apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
    exact hs.trans hv
  have hlocal := coordinate_spec ((Scheme.Modules.pullback p).obj J) V eY t
  have he := heY U le_rfl 1
  simp only [map_one] at he
  change Scheme.Modules.pullbackLocalSection p (e.equiv U le_rfl 1) = eY.equiv V le_rfl 1 at he
  rw [← he] at hlocal
  have ht := along_local_scalar p g f hg J t U (e.equiv U le_rfl 1) d hlocal hU hV
  rw [← scalar_specScalar, hd, transport_as_app] at ht
  exact ht

lemma normalization_branch_dominant (k : Type) [Field k]
    {Z : Scheme.{0}} [IsIntegral Z] [Algebra Z.functionField (LaurentSeries k)]
    (E : IntermediateField Z.functionField (LaurentSeries k))
    (g : Disk k ⟶ extensionNormalization Z E)
    (hg : genericInclusion k ≫ g =
      Spec.map (CommRingCat.ofHom E.subtype) ≫ extensionToNormalization Z E) :
    IsDominant (genericInclusion k ≫ g) := by
  have hpt (x : Puncture k) : (genericInclusion k ≫ g) x =
      genericPoint (extensionNormalization Z E) := by
    rw [hg, Scheme.Hom.comp_apply]
    exact (congrArg (extensionToNormalization Z E) (Subsingleton.elim _ _)).trans
      (toNormalization_genericPoint Z E)
  have hr : Set.range (genericInclusion k ≫ g) =
      {genericPoint (extensionNormalization Z E)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hpt x
    · intro hy
      exact ⟨IsLocalRing.closedPoint (LaurentSeries k), (hpt _).trans hy.symm⟩
  constructor
  rw [denseRange_iff_closure_range, hr]
  exact (genericPoint_spec (extensionNormalization Z E)).def

#print axioms disk_field_map
#print axioms disk_normalization_branch
#print axioms diskScalar_generic
#print axioms finite_smooth_curve_dimension
#print axioms pullback_coordinate
#print axioms pullback_power_coordinate
#print axioms normalization_scalar_triangle
#print axioms prescribed_series_roots
#print axioms powerCoefficient_ne_zero
#print axioms normalization_section_value
#print axioms normalization_branch_dominant
end ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187

namespace ArithmeticThetaSimultaneousUnaryR0187
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalization ArithmeticThetaNormalizationField
open ArithmeticThetaNormalizedSections ArithmeticThetaKummerCover ArithmeticThetaGeometricDegree
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLineRoot
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open SimultaneousDiskRootSectionsR0187

/-- Simultaneous global roots on one actual finite cover, with the prescribed
complete disk expansions and positive pointwise degree bounded by `K^s`. -/
theorem simultaneous_disk_root_sections :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (b : Quiver.Hom Z (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.IsProper b] [AlgebraicGeometry.SmoothOfRelativeDimension 1 b] (J : Z.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (K s : ℕ), 0 < K → ∀ (F : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections Z (ArithmeticThetaTensorPower.tensorPower Z (J) (K))), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z), CategoryTheory.CategoryStruct.comp f b = ArithmeticThetaTateCuspsR0181.diskStructure k → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion k) f) → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J))), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) ⊤ h → ∀ (a : Fin s → PowerSeries k), (∀ j, ArithmeticThetaNormalizedSections.pullbackPowerSection f J (K) (F j) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) ((a j)^K) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) (K) ⊤ h) → ∃ R : ArithmeticThetaSimultaneousUnaryR0187.RootCover k Z b (K^s), ArithmeticThetaSimultaneousUnaryR0187.RealizesRoots k R J K s F f h a := by
  intro k _ _ _ Z _ b _ _ J hJ K s hK F hF f hfb hdom h hh a ha
  letI := hdom
  obtain ⟨φ, hφ⟩ := disk_field_map k f
  letI : Algebra Z.functionField (LaurentSeries k) := φ.toAlgebra
  have hf : genericInclusion k ≫ f = genericExtensionMap Z (LaurentSeries k) := hφ.symm
  obtain ⟨U, u, hz, hu⟩ := local_frame_exists hJ (f (closedPoint k))
  let e := InitialHodgeSection.frame J u hu
  letI : Nonempty U := ⟨⟨_, hz⟩⟩
  have hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hz).ge
  obtain ⟨c, hc, hr⟩ := prescribed_series_roots k f hf J U e hU K s F h a ha
  let r : Fin s → LaurentSeries k := fun j => algebraMap (PowerSeries k) (LaurentSeries k) (a j * c)
  let coeff : Fin s → Z.functionField := fun j => powerCoefficient Z J U e K (F j)
  obtain ⟨hnoeth, hchar, hnormal⟩ :=
    ArithmeticThetaSmoothNormality.smooth_normalization_prerequisites Z k b
  letI := hnoeth
  letI := hchar
  obtain ⟨hgeom, eY, heY, t, ht, _⟩ := smooth_proper_root_sections Z k b
    (smooth_relative_curve_dimension Z k b) J (line_of_invertible J hJ)
    U e (LaurentSeries k) K s hK F r hr
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  let p := rootCoverMap Z (LaurentSeries k) s r
  let Y := rootCover Z (LaurentSeries k) s r
  let R : RootCover k Z b (K^s) :=
    { space := Y
      map := p
      integral := inferInstance
      finite := hgeom.1
      flat := rootCover_finite_flat Z k b (LaurentSeries k) K s hK r coeff hr
      surjective := hgeom.2.1
      proper := hgeom.2.2.2.1
      smooth := finite_smooth_curve_dimension k b p
      degree := fun x => ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one (rootCover_geometric_degree_positive
          Z k b (LaurentSeries k) K s hK r coeff hr x),
        rootCover_geometric_degree_bound Z k b (LaurentSeries k) K s hK r coeff hr x⟩ }
  obtain ⟨g, hg, hbranch⟩ := disk_normalization_branch k Z hnormal K s hK r coeff hr f hf
  refine ⟨R, g, hg, normalization_branch_dominant k _ g hbranch, t, ?_⟩
  intro j
  have hvalue := coverRoot_prescribed Z (LaurentSeries k) K s hK r coeff hr j
  have htv : (normalizationFunctionFieldMap Z (generatedRootField Z (LaurentSeries k) s r)
      (sectionCoefficient Y ((Scheme.Modules.pullback p).obj J) (p ⁻¹ᵁ U) eY (t j)) :
        LaurentSeries k) = r j := by
    rw [(ht j).1]
    exact hvalue
  refine ⟨?_, (ht j).2, ?_⟩
  · intro hz
    have rz : r j = 0 := by
      rw [hz] at htv
      simpa only [sectionCoefficient, sectionCoordinate, map_zero, ZeroMemClass.coe_zero] using htv.symm
    apply powerCoefficient_ne_zero J hJ U e K (F j) (hF j)
    apply (algebraMap Z.functionField (LaurentSeries k)).injective
    have hp : algebraMap Z.functionField (LaurentSeries k)
        (powerCoefficient Z J U e K (F j)) = r j ^ K := (hr j).symm
    simpa only [rz, zero_pow (Nat.ne_of_gt hK), map_zero] using hp
  · have htDisk := normalization_section_value k (generatedRootField Z (LaurentSeries k) s r)
      J U e eY heY f hU g hg hbranch (t j) (a j * c) htv
    change _ = scalar (PowerSeries k) (a j) • h
    rw [htDisk, hc, ← mul_smul]
    congr 1
    exact map_mul (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom _ _

#print axioms simultaneous_disk_root_sections
end ArithmeticThetaSimultaneousUnaryR0187
