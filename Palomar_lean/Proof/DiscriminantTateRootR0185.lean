module

public import CuspHalfDivisorLineR0185
public import DiscriminantTwistUnitR0185

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section

namespace ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184

open CompactHodgeLatticeExtensionR0182
open DiscriminantTwistUnitR0185
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

lemma tensor_smul_right {Y : Scheme.{0}} (M N : Y.Modules) (U : Y.Opens)
    (r : Γ(Y,U)) (s : Γ(M,U)) (t : Γ(N,U)) :
    tensorSection Y M N U s (r • t) = r • tensorSection Y M N U s t := by
  simp only [tensorSection, TensorProduct.tmul_smul, map_smul]

/-- Multiplication by a fixed frame is a bijection on actual sections. -/
lemma tensor_frame_bijective {Y : Scheme.{0}} {M B H : Y.Modules}
    (m : sheafTensor Y M B ≅ H)
    (u : Γ(M, ⊤)) (hu : IsFrame M ⊤ u)
    (b : Γ(B, ⊤)) (hb : IsFrame B ⊤ b) :
    Function.Bijective (fun v : Γ(M, ⊤) =>
      m.hom.app ⊤ (tensorSection Y M B ⊤ v b)) := by
  let μ := InitialHodgeSection.frame M u hu
  let ν := InitialHodgeSection.frame B b hb
  let ζ := productFrame m μ ν
  have hμ : ∀ r, μ.equiv ⊤ le_rfl r = r • u := by
    intro r
    change r • res M le_rfl u = r • u
    rw [InitialHodgeSection.res_self]
  have hν : ν.equiv ⊤ le_rfl 1 = b := by
    change (1 : Γ(Y,⊤)) • res B le_rfl b = b
    rw [InitialHodgeSection.res_self, one_smul]
  have heq : (fun v : Γ(M,⊤) => m.hom.app ⊤ (tensorSection Y M B ⊤ v b)) =
      (μ.equiv ⊤ le_rfl).symm.trans (ζ.equiv ⊤ le_rfl) := by
    funext v
    obtain ⟨r, rfl⟩ := (μ.equiv ⊤ le_rfl).surjective v
    rw [← hν, productFrame_apply, mul_one]
    change ζ.equiv ⊤ le_rfl r = ζ.equiv ⊤ le_rfl
      ((μ.equiv ⊤ le_rfl).symm ((μ.equiv ⊤ le_rfl) r))
    rw [LinearEquiv.symm_apply_apply]
  rw [heq]
  exact LinearEquiv.bijective _

/-- The inverse image of a frame under multiplication by a frame is a frame. -/
lemma tensor_frame_preimage {Y : Scheme.{0}} {M B H : Y.Modules}
    (m : sheafTensor Y M B ≅ H)
    (u : Γ(M, ⊤)) (hu : IsFrame M ⊤ u)
    (b : Γ(B, ⊤)) (hb : IsFrame B ⊤ b)
    (η : Γ(H, ⊤)) (hη : IsFrame H ⊤ η) :
    ∃ v : Γ(M, ⊤), IsFrame M ⊤ v ∧
      m.hom.app ⊤ (tensorSection Y M B ⊤ v b) = η := by
  obtain ⟨v, hv⟩ := (tensor_frame_bijective m u hu b hb).surjective η
  have hu' : Function.Bijective (fun r : Γ(Y,⊤) => r • u) := by
    simpa only [InitialHodgeSection.res_self] using hu ⊤ le_rfl
  obtain ⟨r, rfl⟩ := hu'.surjective v
  have hprod := frame_iso m _ (tensor_section_frame u b hu hb)
  have hr : IsUnit r := frame_coefficient_unit _ hprod r (by
    dsimp only at hv
    rw [tensor_smul_left, Scheme.Modules.Hom.app_smul] at hv
    rwa [hv])
  exact ⟨r • u, by
    obtain ⟨r, rfl⟩ := hr
    exact InitialHodgeSection.unit_frame M u hu r, hv⟩

lemma disk_frame (k : Type) [Field k] {Y : Scheme.{0}} (f : Disk k ⟶ Y)
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ u : Γ((Scheme.Modules.pullback f).obj M, ⊤),
      IsFrame ((Scheme.Modules.pullback f).obj M) ⊤ u := by
  obtain ⟨U, u, hy, hu⟩ := local_frame_exists hM (f (closedPoint k))
  let h : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hy).ge
  exact ⟨res _ h (Scheme.Modules.pullbackLocalSection f u),
    HodgeBaseChange.frame_restrict _ h _ (HodgeBaseChange.pullback_frame f M u hu)⟩

lemma euler_unit (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 0 < L) :
    IsUnit (euler k L) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  have hc : PowerSeries.constantCoeff (euler k L) = 1 := by
    unfold euler
    rw [PowerSeries.constantCoeff_subst_X_pow (Nat.ne_of_gt hL),
      ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, ArithmeticThetaDiscriminant.P_constant, map_one, map_one]
  rw [hc]
  exact isUnit_one


open ArithmeticThetaOpenHodgeR0180 (scalar)

lemma scalar_mul (k : Type) [Field k] (r s : PowerSeries k) :
    scalar (PowerSeries k) (r * s) = scalar (PowerSeries k) r * scalar (PowerSeries k) s :=
  map_mul (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom r s

lemma scalar_pow (k : Type) [Field k] (r : PowerSeries k) (n : ℕ) :
    scalar (PowerSeries k) (r ^ n) = scalar (PowerSeries k) r ^ n :=
  map_pow (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom r n

variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- The prescribed complete branch has a regular frame representative.
This construction uses the actual multiplication, without a chosen root. -/
lemma branch_frame (hL : 0 < L) (h24 : 24 ∣ L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A)
    (W : Twist k L D X x A H) (hW : Scheme.Modules.IsInvertible W.line)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk) :
    ∃ v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤),
      IsFrame ((Scheme.Modules.pullback f).obj W.line) ⊤ v ∧
      ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤), ExtendsGenerator k L H V η →
        (diskHodgeIso k L D X x H V f hf).hom.app ⊤
          ((pullMultiply k L D X x W f).hom.app ⊤
            (tensorSection (Disk k) ((Scheme.Modules.pullback f).obj W.line)
              (tensorPower (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2) ⊤ v
              (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤
                (pullbackGlobalSection f A.line A.section_)))) =
          scalar (PowerSeries k) (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η := by
  have hlev : 3 ≤ L := le_trans (by decide) (Nat.le_of_dvd hL h24)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) h24)
  have hn : 0 < L / 24 := Nat.div_pos (Nat.le_of_dvd hL h24) (by decide)
  have hdiv : L / 24 * 2 = L / 12 := by omega
  obtain ⟨a, ha, hasec⟩ := CuspHalfDivisorLineR0185.cusp_half_line_disk
    k L D X x hlev heven hn A hA V f hf
  obtain ⟨η, hη, huniq⟩ := hH V
  obtain ⟨u, hu⟩ := disk_frame k f W.line hW
  let m := pullMultiply k L D X x W f ≪≫ diskHodgeIso k L D X x H V f hf
  let b := tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ a
  have hb : IsFrame _ ⊤ b := InitialHodgeSection.tensor_frame _ a ha 2
  obtain ⟨e, he, hmul⟩ := tensor_frame_preimage m u hu b hb η hη.1
  let q := scalar (PowerSeries k) (euler k L ^ 2)
  have hq : IsUnit q := (euler_unit k L hL).pow 2 |>.map
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom
  refine ⟨q • e, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hq
    rw [← hq]
    exact InitialHodgeSection.unit_frame _ e he q
  · intro η' hη'
    rw [huniq η' hη']
    change m.hom.app ⊤ (tensorSection _ _ _ ⊤ (q • e) _) = _
    rw [hasec, InitialHodgeSection.tensor_smul, tensor_smul_right, tensor_smul_left,
      Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
    change _ • (q • m.hom.app ⊤ (tensorSection _ _ _ ⊤ e b)) = _
    rw [hmul, smul_smul]
    congr 1
    rw [← scalar_pow, ← pow_mul, hdiv, scalar_mul]
    exact mul_comm _ _


lemma frame_smul_cancel {Y : Scheme.{0}} {M : Y.Modules}
    [NoZeroDivisors Γ(Y,⊤)] (u : Γ(M,⊤)) (hu : IsFrame M ⊤ u)
    (c : Γ(Y,⊤)) (hc : c ≠ 0) {v w : Γ(M,⊤)} (h : c • v = c • w) : v = w := by
  have hb : Function.Bijective (fun r : Γ(Y,⊤) => r • u) := by
    simpa only [InitialHodgeSection.res_self] using hu ⊤ le_rfl
  obtain ⟨r, rfl⟩ := hb.surjective v
  obtain ⟨s, rfl⟩ := hb.surjective w
  have hrs : c * r = c * s := hb.injective (by simpa only [mul_smul] using h)
  rw [mul_left_cancel₀ hc hrs]

lemma scalar_X_pow_ne_zero (k : Type) [Field k] (n : ℕ) :
    scalar (PowerSeries k) (PowerSeries.X ^ n) ≠ 0 := by
  exact ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm.map_ne_zero_iff).mpr
    (pow_ne_zero n PowerSeries.X_ne_zero)

/-- The full multiplication identity determines the branch uniquely. -/
lemma branch_unique (hL : 0 < L) (h24 : 24 ∣ L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A)
    (W : Twist k L D X x A H) (hW : Scheme.Modules.IsInvertible W.line)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk)
    (v w : Γ((Scheme.Modules.pullback f).obj W.line, ⊤))
    (hv : IsTateRoot k L D X x W V f hf v)
    (hw : IsTateRoot k L D X x W V f hf w) : v = w := by
  have hlev : 3 ≤ L := le_trans (by decide) (Nat.le_of_dvd hL h24)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) h24)
  have hn : 0 < L / 24 := Nat.div_pos (Nat.le_of_dvd hL h24) (by decide)
  obtain ⟨a, ha, hasec⟩ := CuspHalfDivisorLineR0185.cusp_half_line_disk
    k L D X x hlev heven hn A hA V f hf
  obtain ⟨η, hη, _⟩ := hH V
  obtain ⟨u, hu⟩ := disk_frame k f W.line hW
  let m := pullMultiply k L D X x W f ≪≫ diskHodgeIso k L D X x H V f hf
  let b := tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ a
  have hb : IsFrame _ ⊤ b := InitialHodgeSection.tensor_frame _ a ha 2
  have heq := (hv.2.2 η hη).trans (hw.2.2 η hη).symm
  change m.hom.app ⊤ (tensorSection _ _ _ ⊤ v _) =
    m.hom.app ⊤ (tensorSection _ _ _ ⊤ w _) at heq
  rw [hasec, InitialHodgeSection.tensor_smul, tensor_smul_right, tensor_smul_right,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at heq
  apply (tensor_frame_bijective m u hu b hb).injective
  apply frame_smul_cancel η hη.1 _ _ heq
  exact pow_ne_zero 2 (scalar_X_pow_ne_zero k (L / 24))

open HodgeBaseChange OpenDiscriminantFullTateExpansionR0182

/-- The component comparison and ambient disk comparison are the same
geometric pullback, including their action on tensor-power sections. -/
lemma disk_restrict_power (H : Extension k L D X)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk)
    (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) :
    transportSection f _ _
      (tensorComparison f (hodge k L D X x H) _ (diskHodgeIso k L D X x H V f hf) n)
      (restrict k L D X x H n s) = diskPower k L H V n s := by
  have hc : composeComparison (inclusion k L D X x) f V.disk hf.symm H.line
      (hodge k L D X x H) ((Scheme.Modules.pullback V.disk).obj H.line)
      (Iso.refl _) (diskHodgeIso k L D X x H V f hf) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, diskHodgeIso, pullbackEqIso, Scheme.Modules.pullbackCongr]
  have ht := CompactDiscriminantSectionR0182.transportSection_comp_eq
    (inclusion k L D X x) f V.disk hf.symm
    (tensorPower X.space H.line n) (power k L D X x H n)
    (tensorPower (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line) n)
    (tensorComparison (inclusion k L D X x) H.line _ (Iso.refl _) n)
    (tensorComparison f (hodge k L D X x H) _ (diskHodgeIso k L D X x H V f hf) n) s
  rw [← CompactDiscriminantSectionR0182.tensorComparison_comp_eq
    (inclusion k L D X x) f V.disk hf.symm H.line _ _ H.invertible, hc,
    tensorComparison_refl _ _ H.invertible,
    tensorComparison_refl _ _ H.invertible] at ht
  simpa only [transportSection, restrict, diskPower, pullbackPowerSection,
    pullbackGlobalSection, Scheme.Modules.pullbackLocalSection, res_refl] using ht.symm


lemma iso_inv_hom_apply {Y : Scheme.{0}} {M N : Y.Modules} (e : M ≅ N)
    (U : Y.Opens) (s : Γ(M,U)) : e.inv.app U (e.hom.app U s) = s :=
  ConcreteCategory.congr_hom (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) s

lemma pull_multiply_local {H : Extension k L D X}
    {A : DivisorLine (Component k L D X x)} (W : Twist k L D X x A H)
    {Z : Scheme.{0}} (f : Z ⟶ Component k L D X x)
    (U : (Component k L D X x).Opens) (u : Γ(W.line,U)) (a : Γ(A.line,U)) :
    (pullMultiply k L D X x W f).hom.app (f ⁻¹ᵁ U)
      (tensorSection Z _ _ (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f u)
        (tensorPowerSection Z _ 2 (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f a))) =
    Scheme.Modules.pullbackLocalSection f
      (W.multiply.hom.app U (tensorSection _ _ _ U u (tensorPowerSection _ _ 2 U a))) := by
  rw [Scheme.Modules.pullbackLocalSection_app]
  change ((Scheme.Modules.pullback f).map W.multiply.hom).app _
    ((pullback_sheafTensor_iso _ _ f W.line (tensorPower _ A.line 2)).inv.app _
      ((sheafTensorCongr Z (Iso.refl _) (pullback_tensorPower_iso Z _ f A.line 2).symm).hom.app _
        (tensorSection Z _ _ _ _ _))) = _
  rw [sheafTensorCongr_section]
  change ((Scheme.Modules.pullback f).map W.multiply.hom).app _
    ((pullback_sheafTensor_iso _ _ f W.line (tensorPower _ A.line 2)).inv.app _
      (tensorSection Z _ _ _ (Scheme.Modules.pullbackLocalSection f u)
        ((pullback_tensorPower_iso Z _ f A.line 2).inv.app _
          (tensorPowerSection Z _ 2 _ (Scheme.Modules.pullbackLocalSection f a))))) = _
  rw [← HodgeBaseChange.pullback_tensorPower_local_section, iso_inv_hom_apply,
    ← HodgeBaseChange.pullback_sheafTensor_local_section, iso_inv_hom_apply]


lemma tensor_res {Y : Scheme.{0}} (M N : Y.Modules) {U V : Y.Opens}
    (h : V ≤ U) (s : Γ(M,U)) (t : Γ(N,U)) :
    res (sheafTensor Y M N) h (tensorSection Y M N U s t) =
      tensorSection Y M N V (res M h s) (res N h t) :=
  tensorSection_restrict Y M N U V h s t

lemma power_res {Y : Scheme.{0}} (M : Y.Modules) (n : ℕ) {U V : Y.Opens}
    (h : V ≤ U) (s : Γ(M,U)) :
    res (tensorPower Y M n) h (tensorPowerSection Y M n U s) =
      tensorPowerSection Y M n V (res M h s) :=
  tensorPowerSection_restrict Y M n U V h s

lemma transport_power_refl {Y Z : Scheme.{0}} (f : Z ⟶ Y) (M : Y.Modules)
    (n : ℕ) (s : Γ(tensorPower Y M n,⊤)) :
    transportSection f _ _ (pullback_tensorPower_iso Z Y f M n) s =
      pullbackPowerSection f M n s := by
  exact InitialHodgeSection.res_self _ _

lemma id_app_apply {Y : Scheme.{0}} (M : Y.Modules) (U : Y.Opens) (s : Γ(M,U)) :
    (Iso.refl M).hom.app U s = s := rfl

lemma power_coordinate {Y : Scheme.{0}} (M : Y.Modules) (U : Y.Opens)
    (μ : LocalFrame Y M U) (n : ℕ) (s : Γ(tensorPower Y M n,⊤)) :
    res (tensorPower Y M n) le_top s =
      sectionCoordinate Y (tensorPower Y M n) U (tensorPowerFrame Y M U μ n) s •
      tensorPowerSection Y M n U (μ.equiv U le_rfl 1) := by
  rw [tensorPowerSection_frame, one_pow, ← map_smul, smul_eq_mul, mul_one]
  exact ((tensorPowerFrame Y M U μ n).equiv U le_rfl).apply_symm_apply _ |>.symm

/-- A single actual local frame gives compatible coefficients for the
pulled discriminant and the pulled twist section on the entire disk. -/
lemma twist_disk_local_data (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤))
    (A : DivisorLine (Component k L D X x)) (W : Twist k L D X x A H)
    (hW : IsTwist k L D X x s W)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk) :
    ∃ (u : Γ((Scheme.Modules.pullback f).obj W.line, ⊤)) (r : Γ(Disk k,⊤)),
      IsFrame ((Scheme.Modules.pullback f).obj W.line) ⊤ u ∧
      pullbackPowerSection f W.line 24 W.section_ =
        r • tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj W.line) 24 ⊤ u ∧
      diskPower k L H V 24 s = r • tensorPowerSection (Disk k)
        ((Scheme.Modules.pullback V.disk).obj H.line) 24 ⊤
        ((diskHodgeIso k L D X x H V f hf).hom.app ⊤
          ((pullMultiply k L D X x W f).hom.app ⊤
            (tensorSection (Disk k) _ _ ⊤ u
              (tensorPowerSection (Disk k) _ 2 ⊤ (pullbackGlobalSection f A.line A.section_))))) := by
  let Y := Component k L D X x
  obtain ⟨U, u, hy, hu⟩ := local_frame_exists hW.1 (f (closedPoint k))
  let μ := InitialHodgeSection.frame W.line u hu
  have hμ : μ.equiv U le_rfl 1 = u := by
    change (1 : Γ(Y,U)) • res W.line le_rfl u = u
    rw [InitialHodgeSection.res_self, one_smul]
  let r := sectionCoordinate Y (tensorPower Y W.line 24) U
    (tensorPowerFrame Y W.line U μ 24) W.section_
  let h : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hy).ge
  let ud := res ((Scheme.Modules.pullback f).obj W.line) h (Scheme.Modules.pullbackLocalSection f u)
  have hud : IsFrame ((Scheme.Modules.pullback f).obj W.line) ⊤ ud :=
    frame_restrict _ h _ (pullback_frame f W.line u hu)
  have hr : res (tensorPower Y W.line 24) le_top W.section_ =
      r • tensorPowerSection Y W.line 24 U u := by
    simpa only [hμ] using power_coordinate W.line U μ 24 W.section_
  have hd := transportSection_local_scalar f W.line _ (Iso.refl _) 24 W.section_ U u r hr h
  rw [tensorComparison_refl _ _ hW.1, transport_power_refl, id_app_apply] at hd
  have hd' : pullbackPowerSection f W.line 24 W.section_ =
      f.appLE U ⊤ h r • tensorPowerSection (Disk k) _ 24 ⊤ ud := hd
  have hs := hW.2.2 U μ
  change res (power k L D X x H 24) le_top (restrict k L D X x H 24 s) =
    r • tensorPowerSection Y (hodge k L D X x H) 24 U
      (W.multiply.hom.app U (tensorSection Y _ _ U (μ.equiv U le_rfl 1)
        (tensorPowerSection Y A.line 2 U (res A.line le_top A.section_)))) at hs
  rw [hμ] at hs
  have hs' := transportSection_local_scalar f (hodge k L D X x H) _
    (diskHodgeIso k L D X x H V f hf) 24 (restrict k L D X x H 24 s) U _ r hs h
  rw [disk_restrict_power] at hs'
  have ha : res ((Scheme.Modules.pullback f).obj A.line) h
      (Scheme.Modules.pullbackLocalSection f (res A.line le_top A.section_)) =
        pullbackGlobalSection f A.line A.section_ := by
    rw [← InitialSectionNaturality.pullback_res, InitialHodgeSection.res_res,
      InitialHodgeSection.res_self]
    rfl
  have hm : res ((Scheme.Modules.pullback V.disk).obj H.line) h
      ((diskHodgeIso k L D X x H V f hf).hom.app _
        (Scheme.Modules.pullbackLocalSection f
          (W.multiply.hom.app U (tensorSection Y _ _ U u
            (tensorPowerSection Y A.line 2 U (res A.line le_top A.section_)))))) =
    (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      ((pullMultiply k L D X x W f).hom.app ⊤
        (tensorSection (Disk k) _ _ ⊤ ud
          (tensorPowerSection (Disk k) _ 2 ⊤ (pullbackGlobalSection f A.line A.section_)))) := by
    rw [← pull_multiply_local, hom_res, hom_res]
    congr 2
    rw [tensor_res, power_res, ha]
  rw [hm] at hs'
  exact ⟨ud, f.appLE U ⊤ h r, hud, hd', hs'⟩

lemma discriminant_branch_series (k : Type) [Field k] [CharZero k]
    (L : ℕ) (hL : 0 < L) (h24 : 24 ∣ L) :
    (euler k L ^ 2 * (PowerSeries.X : PowerSeries k) ^ (L / 12)) ^ 24 =
      ArithmeticThetaHodgeInitialR0163.discriminantSeries k L := by
  have he : L / 12 * 24 = L * 2 := by omega
  have hp : PowerSeries.HasSubst (PowerSeries.X ^ L : PowerSeries k) :=
    PowerSeries.HasSubst.X_pow (Nat.ne_of_gt hL)
  unfold ArithmeticThetaHodgeInitialR0163.discriminantSeries
  rw [map_mul, map_pow, PowerSeries.map_X, map_pow,
    PowerSeries.subst_mul hp, PowerSeries.subst_pow hp,
    PowerSeries.subst_X hp, PowerSeries.subst_pow hp]
  change (euler k L ^ 2 * (PowerSeries.X : PowerSeries k) ^ (L / 12)) ^ 24 =
    (PowerSeries.X ^ L) ^ 2 * euler k L ^ 48
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, he]
  exact mul_comm _ _

lemma tensor_power_of_branch {Y : Scheme.{0}} {M B H : Y.Modules}
    [NoZeroDivisors Γ(Y,⊤)] (m : sheafTensor Y M B ≅ H)
    (u : Γ(M,⊤)) (hu : IsFrame M ⊤ u)
    (b : Γ(B,⊤)) (hb : IsFrame B ⊤ b)
    (η : Γ(H,⊤)) (v : Γ(M,⊤)) (n : ℕ)
    (t q r : Γ(Y,⊤)) (ht : t ≠ 0)
    (hn : r • tensorPowerSection Y H n ⊤
      (t • m.hom.app ⊤ (tensorSection Y M B ⊤ u b)) =
      q^n • tensorPowerSection Y H n ⊤ η)
    (hv : t • m.hom.app ⊤ (tensorSection Y M B ⊤ v b) = q • η) :
    tensorPowerSection Y M n ⊤ v = r • tensorPowerSection Y M n ⊤ u := by
  have hu' : Function.Bijective (fun c : Γ(Y,⊤) => c • u) := by
    simpa only [InitialHodgeSection.res_self] using hu ⊤ le_rfl
  obtain ⟨c, hc⟩ := hu'.surjective v
  rw [← hc, tensor_smul_left, Scheme.Modules.Hom.app_smul, smul_smul] at hv
  have hvn := congrArg (tensorPowerSection Y H n ⊤) hv
  rw [InitialHodgeSection.tensor_smul, InitialHodgeSection.tensor_smul] at hvn
  rw [InitialHodgeSection.tensor_smul, smul_smul] at hn
  have hf := InitialHodgeSection.tensor_frame H _
    (frame_iso m _ (tensor_section_frame u b hu hb)) n
  have hf' : Function.Injective (fun a : Γ(Y,⊤) => a •
      tensorPowerSection Y H n ⊤ (m.hom.app ⊤ (tensorSection Y M B ⊤ u b))) := by
    simpa only [InitialHodgeSection.res_self] using (hf ⊤ le_rfl).injective
  have heq : (t*c)^n = r * t^n := hf' (hvn.trans hn.symm)
  rw [mul_pow, mul_comm r] at heq
  have hcr : c^n = r := mul_left_cancel₀ (pow_ne_zero n ht) heq
  rw [← hc, InitialHodgeSection.tensor_smul, hcr]

/-- The actual normalized discriminant and the full branch equality force
the twenty-fourth power of the constructed regular frame. -/
lemma branch_power (hL : 0 < L) (h24 : 24 ∣ L)
    (H : Extension k L D X) (hH : Canonical k L H)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (hs : IsCompactD2 k L D X H s)
    (A : DivisorLine (Component k L D X x)) (hA : IsCuspHalfLine k L D X x A)
    (W : Twist k L D X x A H) (hW : IsTwist k L D X x s W)
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk)
    (v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤))
    (hv : ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤), ExtendsGenerator k L H V η →
        (diskHodgeIso k L D X x H V f hf).hom.app ⊤
          ((pullMultiply k L D X x W f).hom.app ⊤
            (tensorSection (Disk k) ((Scheme.Modules.pullback f).obj W.line)
              (tensorPower (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2) ⊤ v
              (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤
                (pullbackGlobalSection f A.line A.section_)))) =
          scalar (PowerSeries k) (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η) :
    tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj W.line) 24 ⊤ v =
      pullbackPowerSection f W.line 24 W.section_ := by
  have hlev : 3 ≤ L := le_trans (by decide) (Nat.le_of_dvd hL h24)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) h24)
  have hn : 0 < L / 24 := Nat.div_pos (Nat.le_of_dvd hL h24) (by decide)
  obtain ⟨a, ha, hasec⟩ := CuspHalfDivisorLineR0185.cusp_half_line_disk
    k L D X x hlev heven hn A hA V f hf
  obtain ⟨η, hη, _⟩ := hH V
  obtain ⟨u, r, hu, hd, he⟩ := twist_disk_local_data k L D X x H s A W hW V f hf
  let m := pullMultiply k L D X x W f ≪≫ diskHodgeIso k L D X x H V f hf
  let b := tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ a
  have hb : IsFrame _ ⊤ b := InitialHodgeSection.tensor_frame _ a ha 2
  let t := scalar (PowerSeries k) (PowerSeries.X ^ (L / 24)) ^ 2
  let q := scalar (PowerSeries k) (euler k L ^ 2 * PowerSeries.X ^ (L / 12))
  have ht : t ≠ 0 := pow_ne_zero 2 (scalar_X_pow_ne_zero k (L / 24))
  have hv' := hv η hη
  change m.hom.app ⊤ (tensorSection _ _ _ ⊤ v _) = q • η at hv'
  rw [hasec, InitialHodgeSection.tensor_smul, tensor_smul_right,
    Scheme.Modules.Hom.app_smul] at hv'
  have he' : r • tensorPowerSection (Disk k) _ 24 ⊤
      (t • m.hom.app ⊤ (tensorSection _ _ _ ⊤ u b)) =
      q ^ 24 • tensorPowerSection (Disk k) _ 24 ⊤ η := by
    obtain ⟨d, hd, hs⟩ := hs
    have hex := CompactDiscriminantSectionR0182.disk_expansion_of_restrict
      k L hlev heven H d hd s hs V η hη
    change diskPower k L H V 24 s = r • tensorPowerSection (Disk k) _ 24 ⊤
      (m.hom.app ⊤ (tensorSection _ _ _ ⊤ u _)) at he
    rw [hasec, InitialHodgeSection.tensor_smul, tensor_smul_right,
      Scheme.Modules.Hom.app_smul] at he
    have hq : q ^ 24 = scalar (PowerSeries k)
        (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) := by
      rw [← scalar_pow, discriminant_branch_series k L hL h24]
    rw [hq]
    exact he.symm.trans hex
  rw [hd]
  exact tensor_power_of_branch m u hu b hb η v 24 t q r ht he' hv'

end ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185






namespace ArithmeticThetaCommonHalfHodgeR0185
/-- The prescribed complete Tate root of the actual normalized twist. -/
theorem discriminant_tate_root :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∀ (W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H), ArithmeticThetaCommonHalfHodgeR0185.IsTwist k L D X x s W → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (hf : CategoryTheory.CategoryStruct.comp f (ArithmeticThetaComponentDegreeR0184.inclusion k L D X x) = V.disk), ∃! v : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCommonHalfHodgeR0185.IsTateRoot k L D X x W V f hf v := by
  intro k _ _ _ L hL h24 D X x H hH s hs A hA W hW V f hf
  obtain ⟨v, hv, hbranch⟩ := DiscriminantTateRootR0185.branch_frame
    k L D X x hL h24 H hH A hA W hW.1 V f hf
  have hroot : IsTateRoot k L D X x W V f hf v :=
    ⟨hv, DiscriminantTateRootR0185.branch_power
      k L D X x hL h24 H hH s hs A hA W hW V f hf v hbranch, hbranch⟩
  refine ⟨v, hroot, ?_⟩
  intro w hw
  exact DiscriminantTateRootR0185.branch_unique
    k L D X x hL h24 H hH A hA W hW.1 V f hf w v hw hroot

#print axioms discriminant_tate_root
end ArithmeticThetaCommonHalfHodgeR0185
