module

public import SimultaneousUnaryRootsDefinitionsR0187
public import CompactUnaryHodgeRealizationR0183

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace ArithmeticThetaSimultaneousUnaryR0187
namespace UnaryPowersInCommonSquareLineR0187
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaComponentDegreeR0184.ComponentHodgePowerDegreeR0184
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

local instance (Y : Scheme) : MonoidalCategory Y.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := Y.presheaf)

lemma counit_section (Y : Scheme) (M : Y.Modules) (U : Y.Opens) (s : Γ(M,U)) :
    (sheafCounit Y M).hom.val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M.val).app
        (op U) s) = s := by
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app (op U))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).right_triangle_components M)) (show M.val.obj (op U) from s)

lemma counit_inv_section (Y : Scheme) (M : Y.Modules) (U : Y.Opens) (s : Γ(M,U)) :
    (sheafCounit Y M).inv.val.app (op U) s =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M.val).app
        (op U) s) := by
  have h := congrArg (fun t => (sheafCounit Y M).inv.val.app (op U) t)
    (counit_section Y M U s)
  have hi := ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op U))
    (sheafCounit Y M).hom_inv_id)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M.val).app (op U) s)
  exact h.symm.trans hi

lemma tensorRightUnit_section (Y : Scheme) (M : Y.Modules) (U : Y.Opens) (s : Γ(M,U)) :
    (tensorRightUnit Y M).hom.app U
      (tensorSection Y M (SheafOfModules.unit Y.ringCatSheaf) U s (1 : Γ(Y,U))) = s := by
  change (sheafCounit Y M).hom.val.app (op U)
    (((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map (ρ_ M.val).hom).val.app
      (op U) (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (M.val ⊗ (SheafOfModules.unit Y.ringCatSheaf).val)).app (op U) (s ⊗ₜ[Γ(Y,U)] (1 : Γ(Y,U))))) = s
  erw [sheafifyMap_unit_apply]
  change (sheafCounit Y M).hom.val.app (op U)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M.val).app
      (op U) ((1 : Γ(Y,U)) • s)) = s
  erw [one_smul, counit_section]

lemma tensorAssoc_section (Y : Scheme) (M N P : Y.Modules) (U : Y.Opens)
    (m : Γ(M,U)) (n : Γ(N,U)) (p : Γ(P,U)) :
    (tensorAssoc Y M N P).hom.app U
      (tensorSection Y (sheafTensor Y M N) P U (tensorSection Y M N U m n) p) =
    tensorSection Y M (sheafTensor Y N P) U m (tensorSection Y N P U n p) := by
  change (sheafTensorCongr Y (sheafCounit Y M) (Iso.refl _)).hom.app U
    ((sheafificationTensorIso Y M.val (N.val ⊗ P.val)).hom.val.app (op U)
      (((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map (α_ M.val N.val P.val).hom).val.app (op U)
        ((sheafificationTensorIso Y (M.val ⊗ N.val) P.val).inv.val.app (op U)
          ((sheafTensorCongr Y (Iso.refl _) (sheafCounit Y P).symm).hom.app U
            (tensorSection Y (sheafTensor Y M N) P U (tensorSection Y M N U m n) p))))) = _
  erw [sheafTensorCongr_section Y (Iso.refl (sheafTensor Y M N))
    (sheafCounit Y P).symm U (tensorSection Y M N U m n) p]
  erw [counit_inv_section Y P U p]
  change (sheafTensorCongr Y (sheafCounit Y M) (Iso.refl _)).hom.app U
    ((sheafificationTensorIso Y M.val (N.val ⊗ P.val)).hom.val.app (op U)
      (((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map (α_ M.val N.val P.val).hom).val.app (op U)
        ((sheafificationTensorIso Y (M.val ⊗ N.val) P.val).inv.val.app (op U)
          (tensorSection Y _ _ U
            (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[Γ(Y,U)] n))
            (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              P.val).app (op U) p))))) = _
  erw [← sheafificationTensorIso_unit_apply Y (M.val ⊗ N.val) P.val U
    (m ⊗ₜ[Γ(Y,U)] n) p]
  have hi := ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op U))
    (sheafificationTensorIso Y (M.val ⊗ N.val) P.val).hom_inv_id)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
      ((M.val ⊗ N.val) ⊗ P.val)).app (op U) ((m ⊗ₜ[Γ(Y,U)] n) ⊗ₜ[Γ(Y,U)] p))
  erw [hi]
  erw [sheafifyMap_unit_apply]
  change (sheafTensorCongr Y (sheafCounit Y M) (Iso.refl _)).hom.app U
    ((sheafificationTensorIso Y M.val (N.val ⊗ P.val)).hom.val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (M.val ⊗ (N.val ⊗ P.val))).app (op U) (m ⊗ₜ[Γ(Y,U)] (n ⊗ₜ[Γ(Y,U)] p)))) = _
  erw [sheafificationTensorIso_unit_apply Y M.val (N.val ⊗ P.val) U m (n ⊗ₜ[Γ(Y,U)] p)]
  erw [sheafTensorCongr_section]
  erw [counit_section]
  rfl

lemma powerAdd_section (Y : Scheme) (M : Y.Modules) (a b : ℕ)
    (U : Y.Opens) (s : Γ(M,U)) :
    (powerAdd Y M a b).hom.app U (tensorPowerSection Y M (a+b) U s) =
      tensorSection Y _ _ U (tensorPowerSection Y M a U s) (tensorPowerSection Y M b U s) := by
  induction b with
  | zero =>
    have ht := tensorRightUnit_section Y (tensorPower Y M a) U (tensorPowerSection Y M a U s)
    have hh := congrArg (fun t => (tensorRightUnit Y (tensorPower Y M a)).inv.app U t) ht
    exact hh.symm.trans (iso_inv_hom_apply _ U _)
  | succ b ih =>
    change (tensorAssoc Y _ _ _).hom.app U
      ((sheafTensorCongr Y (powerAdd Y M a b) (Iso.refl M)).hom.app U
        (tensorSection Y _ _ U (tensorPowerSection Y M (a+b) U s) s)) = _
    rw [sheafTensorCongr_section, ih, tensorAssoc_section]
    rfl

lemma cast_power_section (Y : Scheme) (M : Y.Modules) {a b : ℕ} (h : a = b)
    (U : Y.Opens) (s : Γ(M,U)) :
    (eqToIso (congrArg (tensorPower Y M) h)).hom.app U (tensorPowerSection Y M a U s) =
      tensorPowerSection Y M b U s := by subst b; rfl

lemma powerMul_section (Y : Scheme) (M : Y.Modules) (a b : ℕ)
    (U : Y.Opens) (s : Γ(M,U)) :
    (powerMul Y M a b).hom.app U
      (tensorPowerSection Y (tensorPower Y M a) b U (tensorPowerSection Y M a U s)) =
      tensorPowerSection Y M (a*b) U s := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change (eqToIso (congrArg (tensorPower Y M) (Nat.mul_succ a b).symm)).hom.app U ((powerAdd Y M (a*b) a).inv.app U
      ((sheafTensorCongr Y (powerMul Y M a b) (Iso.refl _)).hom.app U
        (tensorSection Y _ _ U
          (tensorPowerSection Y (tensorPower Y M a) b U (tensorPowerSection Y M a U s))
          (tensorPowerSection Y M a U s)))) = _
    rw [sheafTensorCongr_section, ih]
    change (eqToIso (congrArg (tensorPower Y M) (Nat.mul_succ a b).symm)).hom.app U ((powerAdd Y M (a*b) a).inv.app U
      (tensorSection Y _ _ U (tensorPowerSection Y M (a*b) U s)
        (tensorPowerSection Y M a U s))) = _
    rw [← powerAdd_section, iso_inv_hom_apply]
    exact cast_power_section Y M (Nat.mul_succ a b).symm U s


lemma exponent_twice_weight (N : ℕ) : exponent N = 2 * weight N := by
  have he : 2 ∣ exponent N := by
    rw [ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.exponent_formula]
    exact ⟨12*N + 72*N^2, by ring⟩
  exact (Nat.mul_div_cancel' he).symm

/-- The specified square map determines the power comparison. -/
def comparison (Y : Scheme) (J H : Y.Modules)
    (β : tensorPower Y J 2 ≅ H) (N : ℕ) :
    tensorPower Y J (exponent N) ≅ tensorPower Y H (weight N) :=
  eqToIso (congrArg (tensorPower Y J) (exponent_twice_weight N)) ≪≫
    (powerMul Y J 2 (weight N)).symm ≪≫ powerCongr Y β (weight N)

lemma comparison_section (Y : Scheme) (J H : Y.Modules)
    (β : tensorPower Y J 2 ≅ H) (N : ℕ) (U : Y.Opens) (s : Γ(J,U)) :
    (comparison Y J H β N).hom.app U (tensorPowerSection Y J (exponent N) U s) =
      tensorPowerSection Y H (weight N) U (β.hom.app U (tensorPowerSection Y J 2 U s)) := by
  change (powerCongr Y β (weight N)).hom.app U
    ((powerMul Y J 2 (weight N)).inv.app U
      ((eqToIso (congrArg (tensorPower Y J) (exponent_twice_weight N))).hom.app U
        (tensorPowerSection Y J (exponent N) U s))) = _
  rw [cast_power_section Y J (exponent_twice_weight N)]
  rw [← powerMul_section, iso_inv_hom_apply, powerCongr_section]

open ArithmeticThetaTateCuspsR0181

lemma squareOnDisk_local (k : Type) [Field k] {B X : Scheme}
    (p : B ⟶ X) (J : B.Modules) (H : X.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H)
    (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d)
    (U : B.Opens) (s : Γ(J,U)) :
    (squareOnDisk k p J H β f d hf).hom.app (f ⁻¹ᵁ U)
      (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj J) 2 (f ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection f s)) =
    (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H).hom.app (f ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection f (β.hom.app U (tensorPowerSection B J 2 U s))) := by
  change (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullback f).map β.hom).app (f ⁻¹ᵁ U)
      ((pullback_tensorPower_iso (Disk k) B f J 2).inv.app (f ⁻¹ᵁ U)
        (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj J) 2 (f ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection f s)))) = _
  rw [← pullback_tensorPower_local_section, iso_inv_hom_apply,
    ← Scheme.Modules.pullbackLocalSection_app]

/-- Naturality uses actual local frames of J to compare the sheaf maps. -/
lemma comparison_pullback (k : Type) [Field k] {B X : Scheme}
    (p : B ⟶ X) (J : B.Modules) (hJ : Scheme.Modules.IsInvertible J) (H : X.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H)
    (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) (N : ℕ) :
    (Scheme.Modules.pullback f).mapIso (comparison B J ((Scheme.Modules.pullback p).obj H) β N) ≪≫
      tensorComparison f ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback d).obj H)
        (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H) (weight N) =
    pullback_tensorPower_iso (Disk k) B f J (exponent N) ≪≫
      comparison (Disk k) ((Scheme.Modules.pullback f).obj J) ((Scheme.Modules.pullback d).obj H)
        (squareOnDisk k p J H β f d hf) N := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  obtain ⟨U, v, hx, hv⟩ := local_frame_exists hJ (f x)
  refine ⟨f ⁻¹ᵁ U, Scheme.Modules.pullbackLocalSection f
    (tensorPowerSection B J (exponent N) U v), hx,
    pullback_frame _ _ _ (tensorPower_frame J v hv (exponent N)), ?_⟩
  change (tensorComparison f ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback d).obj H)
    (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H) (weight N)).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullback f).map (comparison B J _ β N).hom).app _
      (Scheme.Modules.pullbackLocalSection f (tensorPowerSection B J (exponent N) U v))) =
    (comparison (Disk k) _ _ (squareOnDisk k p J H β f d hf) N).hom.app _
      ((pullback_tensorPower_iso (Disk k) B f J (exponent N)).hom.app _
        (Scheme.Modules.pullbackLocalSection f (tensorPowerSection B J (exponent N) U v)))
  rw [← Scheme.Modules.pullbackLocalSection_app, comparison_section,
    tensorComparison_section, pullback_tensorPower_local_section, comparison_section,
    squareOnDisk_local]

/-- The disk comparison of the transported global section follows the same
commuting triangle as the original compact Hodge section. -/
lemma comparison_transport (k : Type) [Field k] {B X : Scheme}
    (p : B ⟶ X) (J : B.Modules) (hJ : Scheme.Modules.IsInvertible J)
    (H : X.Modules) (hH : Scheme.Modules.IsInvertible H)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H)
    (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) (N : ℕ)
    (F : Γ(tensorPower B J (exponent N),⊤))
    (t : Γ(tensorPower X H (weight N),⊤))
    (hF : (comparison B J ((Scheme.Modules.pullback p).obj H) β N).hom.app ⊤ F =
      pullbackPowerSection p H (weight N) t) :
    (comparison (Disk k) ((Scheme.Modules.pullback f).obj J) ((Scheme.Modules.pullback d).obj H)
      (squareOnDisk k p J H β f d hf) N).hom.app ⊤
        (pullbackPowerSection f J (exponent N) F) = pullbackPowerSection d H (weight N) t := by
  have hn := congrArg (fun e => transportSection f _ _ e F)
    (comparison_pullback k p J hJ H β f d hf N)
  have hl : transportSection f _ _
      ((Scheme.Modules.pullback f).mapIso (comparison B J ((Scheme.Modules.pullback p).obj H) β N) ≪≫
        tensorComparison f ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback d).obj H)
          (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H) (weight N)) F =
      transportSection f _ _ (tensorComparison f _ _
        (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H) (weight N))
        ((comparison B J ((Scheme.Modules.pullback p).obj H) β N).hom.app ⊤ F) := by
    unfold transportSection
    change res _ _ ((tensorComparison f ((Scheme.Modules.pullback p).obj H)
      ((Scheme.Modules.pullback d).obj H) (ArithmeticThetaCommonHalfHodgeR0185.along f p d hf H)
      (weight N)).hom.app (f ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullback f).map (comparison B J _ β N).hom).app _
        (Scheme.Modules.pullbackLocalSection f F))) = _
    rw [← Scheme.Modules.pullbackLocalSection_app]
  rw [hl, hF, along_power p f d hf H hH] at hn
  rw [hn]
  unfold transportSection pullbackPowerSection
  rw [hom_res, InitialHodgeSection.res_self]
  rfl


lemma diskPower_eq (k : Type) [Field k] [CharZero k] (N : ℕ)
    {D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N)}
    {X : ArithmeticThetaLevelCompactificationR0179.Compactification k (level N) D}
    (H : Extension k (level N) D X) (V : DiskTest k (level N) D X)
    (t : Γ(tensorPower X.space H.line (weight N),⊤)) :
    diskPower k (level N) H V (weight N) t = pullbackPowerSection V.disk H.line (weight N) t := by
  exact InitialHodgeSection.res_self _ _

lemma coefficient_identification (k : Type) [Field k] (N m : ℕ) (ν : ℤ)
    (a : PowerSeries k)
    (ha : algebraMap (PowerSeries k) (LaurentSeries k) a =
      ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N) :
    a = unarySeries k N m ν ^ exponent N := by
  apply HahnSeries.ofPowerSeries_injective (R := k) (Γ := ℤ)
  change algebraMap (PowerSeries k) (LaurentSeries k) a = _
  rw [ha, map_pow]
  rfl

/-- Nonvanishing is detected by a genuine frame on the actual disk. -/
lemma nonzero_of_disk (k : Type) [Field k] {B : Scheme} (J : B.Modules) (f : Disk k ⟶ B)
    (K : ℕ) (F : Γ(tensorPower B J K,⊤))
    (M : (Disk k).Modules) (e : tensorPower (Disk k) ((Scheme.Modules.pullback f).obj J) K ≅ M)
    (v : Γ(M,⊤)) (hv : IsFrame M ⊤ v) (a : PowerSeries k) (ha : a ≠ 0)
    (he : e.hom.app ⊤ (pullbackPowerSection f J K F) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) a • v) : F ≠ 0 := by
  intro hz
  have hz' : pullbackPowerSection f J K F = 0 := by
    subst F
    simp only [pullbackPowerSection, pullbackGlobalSection, map_zero]
  rw [hz', map_zero] at he
  have hc := (hv ⊤ le_rfl).injective (show
      (0 : Γ(Disk k,⊤)) • res M le_rfl v =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) a • res M le_rfl v by
    simpa only [InitialHodgeSection.res_self, zero_smul] using he)
  apply ha
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv).injective
  exact hc.symm.trans (map_zero _).symm

end UnaryPowersInCommonSquareLineR0187

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaCompactUnaryR0183
open UnaryPowersInCommonSquareLineR0187
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185

theorem unary_powers_in_common_square_line :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin s → ℕ) (ν : Fin s → ℤ), (∀ j, 0 < m j ∧ Even (m j) ∧ m j ∣ N ∧ (-(m j : ℤ) ≤ 2*ν j ∧ 2*ν j < (m j : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (p : Quiver.Hom Z X.space) (J : Z.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower Z (J) (2)) ((AlgebraicGeometry.Scheme.Modules.pullback p).obj (H.line))) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z) (hf : CategoryTheory.CategoryStruct.comp f p = V.disk) (η : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback V.disk).obj (H.line))), ArithmeticThetaBoundaryHodgeR0182.ExtendsGenerator k (ArithmeticThetaCompactUnaryR0183.level N) H V η → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J))), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) ⊤ h → (ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H.line β f V.disk hf).hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) 2 ⊤ h) = η → ∃ F : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections Z (ArithmeticThetaTensorPower.tensorPower Z (J) (ArithmeticThetaCompactUnaryR0183.exponent N)), ArithmeticThetaSimultaneousUnaryR0187.UnaryPowers k N s m ν H p J β F ∧ ∀ j, ArithmeticThetaNormalizedSections.pullbackPowerSection f J (ArithmeticThetaCompactUnaryR0183.exponent N) (F j) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaSimultaneousUnaryR0187.unarySeries k N (m j) (ν j) ^ (ArithmeticThetaCompactUnaryR0183.exponent N)) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) (ArithmeticThetaCompactUnaryR0183.exponent N) ⊤ h := by
  intro k _ _ _ N s hN hNeven m ν hm D X H hH V ζ hζ hmark Z _ p J hJ β f hf η hη h hh hsquare
  classical
  have hc (j : Fin s) := compact_unary_hodge_realization k (m j) N
    (hm j).1 (hm j).2.1 hN hNeven (hm j).2.2.1 D X H hH (ν j) (hm j).2.2.2
  choose a b ha hb A t ht using hc
  let e := comparison Z J ((Scheme.Modules.pullback p).obj H.line) β N
  let F : Fin s → Sections Z (tensorPower Z J (exponent N)) :=
    fun j => e.inv.app ⊤ (pullbackPowerSection p H.line (weight N) (t j))
  have hF (j : Fin s) : e.hom.app ⊤ (F j) =
      pullbackPowerSection p H.line (weight N) (t j) :=
    iso_inv_hom_apply e.symm ⊤ _
  let ed := comparison (Disk k) ((Scheme.Modules.pullback f).obj J)
    ((Scheme.Modules.pullback V.disk).obj H.line) (squareOnDisk k p J H.line β f V.disk hf) N
  have hd (j : Fin s) : ed.hom.app ⊤ (pullbackPowerSection f J (exponent N) (F j)) =
      pullbackPowerSection V.disk H.line (weight N) (t j) :=
    comparison_transport k p J hJ H.line H.invertible β f V.disk hf N (F j) (t j) (hF j)
  have hn (j : Fin s) : F j ≠ 0 := by
    obtain ⟨c, hc, he⟩ := (ht j).1.2.2.1 V
    apply nonzero_of_disk k J f (exponent N) (F j) _ ed
      (tensorPowerSection (Disk k) _ (weight N) ⊤ η)
      (HodgeBaseChange.tensorPower_frame _ η hη.1 (weight N)) c hc
    rw [hd, ← diskPower_eq k N H V]
    exact he η hη
  refine ⟨F, ⟨e, comparison_section Z J _ β N, ?_⟩, ?_⟩
  · intro j
    exact ⟨hn j, a j, b j, ha j, hb j, A j, t j, (ht j).1, hF j⟩
  · intro j
    obtain ⟨c, hc, he⟩ := (ht j).1.2.2.2 V ζ hζ hmark
    have hc' := coefficient_identification k N (m j) (ν j) c hc
    apply (ConcreteCategory.bijective_of_isIso (ed.hom.app ⊤)).injective
    rw [hd, ← diskPower_eq k N H V, he η hη, hc', Scheme.Modules.Hom.app_smul]
    change _ = _ • (comparison (Disk k) _ _ (squareOnDisk k p J H.line β f V.disk hf) N).hom.app ⊤ _
    rw [comparison_section, hsquare]

#print axioms unary_powers_in_common_square_line
end ArithmeticThetaSimultaneousUnaryR0187
