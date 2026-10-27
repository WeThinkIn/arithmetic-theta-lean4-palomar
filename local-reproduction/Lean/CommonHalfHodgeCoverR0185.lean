import DiscriminantTateRootR0185

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaGlobalization ArithmeticThetaRootTorsor
open CompactHodgeLatticeExtensionR0182
open DiscriminantTateRootR0185
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Any disk map factors through an open containing its closed point. -/
lemma disk_factor (k : Type) [Field k] {Y : Scheme.{0}}
    (f : Disk k ⟶ Y) (U : Y.Opens) (hU : f (closedPoint k) ∈ U) :
    ∃ g : Disk k ⟶ U, g ≫ U.ι = f := by
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have h := Scheme.preimage_eq_top_of_closedPoint_mem f hU
    change z ∈ f ⁻¹ᵁ U
    rw [h]
    trivial
  exact ⟨IsOpenImmersion.lift U.ι f hr, IsOpenImmersion.lift_fac U.ι f hr⟩

/-- A section which generates locally is a frame on the whole scheme. -/
lemma generating_frame {Y : Scheme.{0}} {M : Y.Modules} (v : Γ(M,⊤))
    (hv : IsGeneratingSection Y M v) : IsFrame M ⊤ v := by
  classical
  choose U hy e he using hv
  have hc : (⨆ y, U y) = ⊤ := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
  apply InitialHodgeSection.frame_glue M U hc v
  intro y
  obtain ⟨r, hr⟩ := he y
  have hb := CuspHalfDivisorLineR0185.frame_generator Y M (U y) (e y)
  have heq : res M le_top v = (r : Γ(Y,U y)) • (e y).equiv (U y) le_rfl 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, hr]
    exact ((e y).equiv (U y) le_rfl).apply_symm_apply _ |>.symm
  rw [heq]
  exact InitialHodgeSection.unit_frame M _ hb r

/-- Trivializing the first tensor factor by the specified frame. -/
def multiplyFrame {Y : Scheme.{0}} {M B H : Y.Modules}
    (m : sheafTensor Y M B ≅ H) (v : Γ(M,⊤)) (hv : IsFrame M ⊤ v) : B ≅ H :=
  (tensorLeftUnitIso Y B).symm ≪≫
    sheafTensorCongr Y
      (DiscriminantTwistUnitR0185.globalFrameIso Y M (InitialHodgeSection.frame M v hv))
      (Iso.refl B) ≪≫ m

lemma multiplyFrame_apply {Y : Scheme.{0}} {M B H : Y.Modules}
    (m : sheafTensor Y M B ≅ H) (v : Γ(M,⊤)) (hv : IsFrame M ⊤ v)
    (U : Y.Opens) (b : Γ(B,U)) :
    (multiplyFrame m v hv).hom.app U b =
      m.hom.app U (tensorSection Y M B U (res M le_top v) b) := by
  have ht := tensorLeftUnitIso_section Y B U b
  have hi : (tensorLeftUnitIso Y B).inv.app U b =
      tensorSection Y (SheafOfModules.unit Y.ringCatSheaf) B U (1 : Γ(Y,U)) b := by
    calc
      _ = (tensorLeftUnitIso Y B).inv.app U
          ((tensorLeftUnitIso Y B).hom.app U
            (tensorSection Y (SheafOfModules.unit Y.ringCatSheaf) B U (1 : Γ(Y,U)) b)) :=
        congrArg ((tensorLeftUnitIso Y B).inv.app U) ht.symm
      _ = _ := iso_inv_hom_apply (tensorLeftUnitIso Y B) U _
  change m.hom.app U ((sheafTensorCongr Y _ _).hom.app U
    ((tensorLeftUnitIso Y B).inv.app U b)) = _
  rw [hi, sheafTensorCongr_section]
  change m.hom.app U (tensorSection Y M B U ((1 : Γ(Y,U)) • res M le_top v) b) = _
  rw [one_smul]


/-- The actual specified disk lies on its closed point's accepted component. -/
lemma component_disk_factor (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (V : DiskTest k L D X) :
    ∃ f : Disk k ⟶ Component k L D X (V.disk (closedPoint k)),
      f ≫ inclusion k L D X (V.disk (closedPoint k)) = V.disk :=
  disk_factor k V.disk _ mem_irreducibleComponent

/-- The integer 24 is invertible on the actual component in characteristic zero. -/
lemma twentyfour_unit (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space) :
    IsUnit (24 : Γ(Component k L D X x, ⊤)) := by
  let a : k →+* Γ(Component k L D X x, ⊤) :=
    (projection k L D X x).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h : IsUnit (24 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map a

/-- The accepted global root torsor, instantiated with the constructed twist
and the literal complete Tate root. -/
lemma twist_torsor (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤))
    (A : DivisorLine (Component k L D X x))
    (W : Twist k L D X x A H) (hW : IsTwist k L D X x s W)
    (f : Disk k ⟶ Component k L D X x)
    (v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤))
    (hv : tensorPowerSection (Disk k) _ 24 ⊤ v = pullbackPowerSection f W.line 24 W.section_) :
    ∃ (T : Scheme.{0}) (p : T ⟶ Component k L D X x)
      (u : Γ((Scheme.Modules.pullback p).obj W.line, ⊤)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      (∀ y, p.finrank y = 24) ∧ IsFrame ((Scheme.Modules.pullback p).obj W.line) ⊤ u ∧
      tensorPowerSection T _ 24 ⊤ u = pullbackPowerSection p W.line 24 W.section_ ∧
      ∃ g : {g : Disk k ⟶ T // g ≫ p = f}, pullbackSectionOver p f W.line g u = v := by
  have hline : IsLineBundle (Component k L D X x) W.line := by
    intro y
    obtain ⟨U, u, hy, hu⟩ := local_frame_exists hW.1 y
    exact ⟨U, hy, ⟨localFrameIso _ W.line U (InitialHodgeSection.frame W.line u hu)⟩⟩
  obtain ⟨T, p, u, hfin, het, hsur, hr, hgen, hpow, huniv⟩ :=
    global_root_torsor _ W.line hline 24 (by decide)
      (twentyfour_unit k L D X x) W.section_ hW.2.1
  obtain ⟨g, hg, _⟩ := huniv (Disk k) f ⟨v, hv⟩
  exact ⟨T, p, u, hfin, het, hsur, hr, generating_frame u hgen, hpow, g, hg⟩

/-- Selection is made on the actual root torsor through the prescribed disk.
The degree bounds are those of the selected finite etale morphism. -/
lemma selected_geometry (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (T : Scheme.{0}) (p : T ⟶ Component k L D X x) [IsFinite p] [Etale p]
    (hr : ∀ y, p.finrank y = 24) (g : Disk k ⟶ T) :
    ∃ (U : T.Opens) (b : Disk k ⟶ U), b ≫ U.ι = g ∧
      IsIntegral U ∧ IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) ∧ Surjective (U.ι ≫ p) ∧
      IsProper ((U.ι ≫ p) ≫ projection k L D X x) ∧
      SmoothOfRelativeDimension 1 ((U.ι ≫ p) ≫ projection k L D X x) ∧
      ∀ y, 0 < (U.ι ≫ p).finrank y ∧ (U.ι ≫ p).finrank y ≤ 24 := by
  letI := compact_noetherian k L D X
  have hc := component_curve_frames k L hL heven D X x
  letI := hc.1
  letI := hc.2.1
  letI : CompactSpace (Component k L D X x) :=
    QuasiCompact.compactSpace_of_compactSpace (projection k L D X x)
  haveI : IsNoetherian (Component k L D X x) := {}
  have hn : ∀ y : Component k L D X x,
      IsIntegrallyClosed ((Component k L D X x).presheaf.stalk y) := by
    intro y
    letI := (compact_stalk_normal k L D X (inclusion k L D X x y)).2
    exact IsIntegrallyClosed.of_equiv
      (asIso ((inclusion k L D X x).stalkMap y)).commRingCatIsoToRingEquiv
  obtain ⟨U, hU, hi, hfin, het, hsur, hrank⟩ :=
    finite_etale_selected_component _ T hn p (g (closedPoint k))
  have hmem : g (closedPoint k) ∈ U := by
    change g (closedPoint k) ∈ (U : Set T)
    rw [hU]
    exact mem_connectedComponent
  obtain ⟨b, hb⟩ := disk_factor k g U hmem
  letI := hfin
  letI := het
  refine ⟨U, b, hb, hi, hfin, het, hsur, inferInstance, ?_, ?_⟩
  · exact smoothOfRelativeDimension_comp 0 1 (U.ι ≫ p) (projection k L D X x)
  · intro y
    simpa only [hr y] using hrank y


open HodgeBaseChange OpenDiscriminantFullTateExpansionR0182

lemma transport_frame {Y Z : Scheme.{0}} (f : Z ⟶ Y) (M : Y.Modules) (N : Z.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (v : Γ(M,⊤)) (hv : IsFrame M ⊤ v) :
    IsFrame N ⊤ (transportSection f M N e v) := by
  exact frame_restrict N _ _ (frame_iso e _ (pullback_frame f M v hv))

/-- Tensor transport along a commuting triangle preserves the original
power section, using the accepted composition theorem. -/
lemma along_power {Y Z B : Scheme.{0}} (p : Y ⟶ B) (j : Z ⟶ Y) (q : Z ⟶ B)
    (hq : j ≫ p = q) (M : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    (n : ℕ) (d : Γ(tensorPower B M n,⊤)) :
    transportSection j _ _
      (tensorComparison j ((Scheme.Modules.pullback p).obj M)
        ((Scheme.Modules.pullback q).obj M) (along j p q hq M) n)
      (pullbackPowerSection p M n d) = pullbackPowerSection q M n d := by
  have hc : composeComparison p j q hq.symm M
      ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback q).obj M)
      (Iso.refl _) (along j p q hq M) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, along, pullbackEqIso, Scheme.Modules.pullbackCongr]
  have ht := CompactDiscriminantSectionR0182.transportSection_comp_eq p j q hq.symm
    (tensorPower B M n) (tensorPower Y ((Scheme.Modules.pullback p).obj M) n)
    (tensorPower Z ((Scheme.Modules.pullback q).obj M) n)
    (tensorComparison p M _ (Iso.refl _) n)
    (tensorComparison j _ _ (along j p q hq M) n) d
  rw [← CompactDiscriminantSectionR0182.tensorComparison_comp_eq
      p j q hq.symm M _ _ hM (Iso.refl _) (along j p q hq M) n,
    hc, tensorComparison_refl _ _ hM, tensorComparison_refl _ _ hM,
    transport_power_refl, transport_power_refl] at ht
  exact ht.symm

/-- The tautological root retains its exact power on the selected component. -/
lemma along_root {Y Z B : Scheme.{0}} (p : Y ⟶ B) (j : Z ⟶ Y) (q : Z ⟶ B)
    (hq : j ≫ p = q) (M : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    (n : ℕ) (d : Γ(tensorPower B M n,⊤))
    (v : Γ((Scheme.Modules.pullback p).obj M,⊤))
    (hv : tensorPowerSection Y _ n ⊤ v = pullbackPowerSection p M n d) :
    tensorPowerSection Z _ n ⊤
      (transportSection j _ _ (along j p q hq M) v) = pullbackPowerSection q M n d := by
  rw [← transportSection_tensor, hv]
  exact along_power p j q hq M hM n d

/-- The actual finite-etale lifting theorem gives uniqueness over the
whole power-series disk for its prescribed residual restriction. -/
lemma disk_lift_unique (k : Type) [Field k] {B Y : Scheme.{0}}
    (p : Y ⟶ B) [IsFinite p] [Etale p] (f : Disk k ⟶ B)
    (g : Disk k ⟶ Y) (hg : g ≫ p = f) :
    ∃! b : Disk k ⟶ Y, b ≫ p = f ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries k)}))) ≫ b =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries k)}))) ≫ g := by
  exact finite_etale_formal_disk_lift (PowerSeries k) (Ideal.span {PowerSeries.X})
    B Y p f _ (by rw [Category.assoc, hg])

/-- A local power equality gives the same equality after multiplying
by any section of the second tensor factor. -/
lemma root_multiply_power {Y : Scheme.{0}} {M B H : Y.Modules}
    (m : sheafTensor Y M B ≅ H) (U : Y.Opens)
    (u : Γ(M,U)) (hu : IsFrame M U u) (v : Γ(M,U)) (b : Γ(B,U))
    (n : ℕ) (r : Γ(Y,U))
    (hv : tensorPowerSection Y M n U v = r • tensorPowerSection Y M n U u) :
    tensorPowerSection Y H n U (m.hom.app U (tensorSection Y M B U v b)) =
      r • tensorPowerSection Y H n U (m.hom.app U (tensorSection Y M B U u b)) := by
  have hbij : Function.Bijective (fun c : Γ(Y,U) => c • u) := by
    simpa only [InitialHodgeSection.res_self] using hu U le_rfl
  obtain ⟨c, rfl⟩ := hbij.surjective v
  have hpow := InitialHodgeSection.tensor_frame M u hu n
  have hinj : Function.Injective (fun c : Γ(Y,U) => c • tensorPowerSection Y M n U u) := by
    simpa only [InitialHodgeSection.res_self] using (hpow U le_rfl).injective
  have hc : c^n = r := hinj (by simpa only [InitialHodgeSection.tensor_smul] using hv)
  rw [tensor_smul_left, Scheme.Modules.Hom.app_smul, InitialHodgeSection.tensor_smul, hc]

lemma pull_power_scalar_local {Y Z : Scheme.{0}} (p : Z ⟶ Y) (M : Y.Modules)
    (n : ℕ) (d : Γ(tensorPower Y M n,⊤)) (U : Y.Opens) (u : Γ(M,U)) (r : Γ(Y,U))
    (hd : res (tensorPower Y M n) le_top d = r • tensorPowerSection Y M n U u) :
    res (tensorPower Z ((Scheme.Modules.pullback p).obj M) n) le_top
      (pullbackPowerSection p M n d) =
    p.app U r • tensorPowerSection Z ((Scheme.Modules.pullback p).obj M) n (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p u) := by
  rw [show res (tensorPower Z ((Scheme.Modules.pullback p).obj M) n) le_top
      (pullbackPowerSection p M n d) =
    (pullback_tensorPower_iso Z Y p M n).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (res (tensorPower Y M n) le_top d)) from
        pullbackPowerSection_restrict Z Y p M n U d]
  rw [hd, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    HodgeBaseChange.pullback_tensorPower_local_section]

/-- Multiplication by a global root of the constructed twisted unit has
24th power equal to the pullback of the same original compact D2. -/
lemma twist_pullback_discriminant
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24,⊤))
    (A : DivisorLine (Component k L D X x)) (W : Twist k L D X x A H)
    (hW : IsTwist k L D X x s W) {Z : Scheme.{0}} (p : Z ⟶ Component k L D X x)
    (v : Γ((Scheme.Modules.pullback p).obj W.line,⊤))
    (hv : tensorPowerSection Z _ 24 ⊤ v = pullbackPowerSection p W.line 24 W.section_) :
    tensorPowerSection Z ((Scheme.Modules.pullback p).obj (hodge k L D X x H)) 24 ⊤
      ((pullMultiply k L D X x W p).hom.app ⊤
        (tensorSection Z _ _ ⊤ v
          (tensorPowerSection Z _ 2 ⊤ (pullbackGlobalSection p A.line A.section_)))) =
    pullbackPowerSection p (hodge k L D X x H) 24 (restrict k L D X x H 24 s) := by
  let Y := Component k L D X x
  let M := (Scheme.Modules.pullback p).obj W.line
  let B := tensorPower Z ((Scheme.Modules.pullback p).obj A.line) 2
  let J := (Scheme.Modules.pullback p).obj (hodge k L D X x H)
  let m := pullMultiply k L D X x W p
  apply (tensorPower Z J 24).isSheaf.section_ext
  intro z hz
  obtain ⟨U, u, hu, huf⟩ := local_frame_exists hW.1 (p z)
  let μ := InitialHodgeSection.frame W.line u huf
  have hμ : μ.equiv U le_rfl 1 = u := by
    change (1 : Γ(Y,U)) • res W.line le_rfl u = u
    rw [InitialHodgeSection.res_self, one_smul]
  let r := sectionCoordinate Y (tensorPower Y W.line 24) U
    (tensorPowerFrame Y W.line U μ 24) W.section_
  let ud := Scheme.Modules.pullbackLocalSection p u
  let vd := res M (show p ⁻¹ᵁ U ≤ ⊤ from le_top) v
  let ad := Scheme.Modules.pullbackLocalSection p
    (res A.line (show U ≤ ⊤ from le_top) A.section_)
  have hud : IsFrame M (p ⁻¹ᵁ U) ud := pullback_frame p W.line u huf
  have hd : res (tensorPower Y W.line 24) le_top W.section_ =
      r • tensorPowerSection Y W.line 24 U u := by
    simpa only [hμ] using power_coordinate W.line U μ 24 W.section_
  have hvd : tensorPowerSection Z M 24 (p ⁻¹ᵁ U) vd =
      p.app U r • tensorPowerSection Z M 24 (p ⁻¹ᵁ U) ud := by
    rw [← power_res, hv]
    exact pull_power_scalar_local p W.line 24 W.section_ U u r hd
  have hd2 := hW.2.2 U μ
  change res (power k L D X x H 24) le_top (restrict k L D X x H 24 s) =
    r • tensorPowerSection Y (hodge k L D X x H) 24 U
      (W.multiply.hom.app U (tensorSection Y _ _ U (μ.equiv U le_rfl 1)
        (tensorPowerSection Y A.line 2 U (res A.line le_top A.section_)))) at hd2
  rw [hμ] at hd2
  have hpb := pull_power_scalar_local p (hodge k L D X x H) 24
    (restrict k L D X x H 24 s) U _ r hd2
  rw [← pull_multiply_local] at hpb
  refine ⟨p ⁻¹ᵁ U, le_top, hu, ?_⟩
  change res (tensorPower Z J 24) le_top _ = res (tensorPower Z J 24) le_top _
  rw [power_res, hom_res, tensor_res, power_res]
  have ha : res ((Scheme.Modules.pullback p).obj A.line) le_top
      (pullbackGlobalSection p A.line A.section_) = ad :=
    pullbackGlobalSection_restrict p A.line U A.section_
  rw [ha, hpb]
  exact root_multiply_power m (p ⁻¹ᵁ U) ud hud vd
    (tensorPowerSection Z ((Scheme.Modules.pullback p).obj A.line) 2 (p ⁻¹ᵁ U) ad)
    24 (p.app U r) hvd

open ArithmeticThetaOpenHodgeR0180 (scalar)

/-- The complete Euler product fixes the regular common frame from the
canonical effective section, once the same square map has the branch identity. -/
lemma common_frame_from_branch (k : Type) [Field k] [CharZero k] (L : ℕ)
    (hL : 0 < L) (h24 : 24 ∣ L) (M N : (Disk k).Modules)
    (a s : Γ(M,⊤)) (ha : IsFrame M ⊤ a)
    (hs : s = scalar (PowerSeries k) (PowerSeries.X ^ (L / 24)) • a)
    (β : tensorPower (Disk k) M 2 ≅ N) (η : Γ(N,⊤)) (hη : IsFrame N ⊤ η)
    (hβ : β.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤ s) =
      scalar (PowerSeries k) (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η) :
    ∃ h : Γ(M,⊤), IsFrame M ⊤ h ∧
      s = scalar (PowerSeries k) (euler k L * PowerSeries.X ^ (L / 24)) • h ∧
      β.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤ h) = η := by
  obtain ⟨e, he⟩ := (euler_unit k L hL).map
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom
  change (e : Γ(Disk k,⊤)) = scalar (PowerSeries k) (euler k L) at he
  let h : Γ(M,⊤) := (e⁻¹ : Γ(Disk k,⊤)ˣ) • a
  let c := scalar (PowerSeries k) (euler k L * PowerSeries.X ^ (L / 24))
  have hc : c * (↑(e⁻¹) : Γ(Disk k,⊤)) =
      scalar (PowerSeries k) (PowerSeries.X ^ (L / 24)) := by
    dsimp [c]
    rw [scalar_mul, ← he]
    rw [mul_comm (e : Γ(Disk k,⊤)), Units.mul_inv_cancel_right]
  have hsc : s = c • h := by
    rw [hs]
    change _ = c • ((↑(e⁻¹) : Γ(Disk k,⊤)) • a)
    rw [smul_smul, hc]
  have hc0 : c ≠ 0 := by
    dsimp [c]
    rw [scalar_mul, ← he]
    exact mul_ne_zero e.ne_zero (scalar_X_pow_ne_zero k (L / 24))
  have hc2 : c ^ 2 = scalar (PowerSeries k)
      (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) := by
    dsimp [c]
    rw [← scalar_pow, mul_pow, ← pow_mul, show L / 24 * 2 = L / 12 from by omega]
  refine ⟨h, InitialHodgeSection.unit_frame M a ha e⁻¹, hsc, ?_⟩
  apply frame_smul_cancel η hη (c^2) (pow_ne_zero 2 hc0)
  rw [hsc, InitialHodgeSection.tensor_smul, Scheme.Modules.Hom.app_smul, ← hc2] at hβ
  exact hβ

/-- The supplied geometric map and its constructed tautological frame
produce the actual square isomorphism and its discriminant equality. -/
def halfCoverOfRoot
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24,⊤))
    (A : DivisorLine (Component k L D X x)) (W : Twist k L D X x A H)
    (hW : IsTwist k L D X x s W) (Z : Scheme.{0}) (p : Z ⟶ Component k L D X x)
    (hi : IsIntegral Z) (hfin : IsFinite p) (het : Etale p) (hsur : Surjective p)
    (hproper : IsProper (p ≫ projection k L D X x))
    (hsmooth : SmoothOfRelativeDimension 1 (p ≫ projection k L D X x))
    (hr : ∀ y, 0 < p.finrank y ∧ p.finrank y ≤ 24)
    (v : Γ((Scheme.Modules.pullback p).obj W.line,⊤))
    (hv : IsFrame ((Scheme.Modules.pullback p).obj W.line) ⊤ v)
    (hpow : tensorPowerSection Z _ 24 ⊤ v = pullbackPowerSection p W.line 24 W.section_) :
    HalfCover k L D X x A H s where
  space := Z
  map := p
  integral := hi
  finite := hfin
  etale := het
  surjective := hsur
  proper := hproper
  smooth := hsmooth
  rank := hr
  square := multiplyFrame (pullMultiply k L D X x W p) v hv
  discriminant := by
    rw [multiplyFrame_apply, InitialHodgeSection.res_self]
    exact twist_pullback_discriminant k L D X x H s A W hW p v hpow

lemma transport_along_eq {Y Z B : Scheme.{0}} (p : Y ⟶ B) (j : Z ⟶ Y) (q : Z ⟶ B)
    (hq : j ≫ p = q) (M : B.Modules) (v : Γ((Scheme.Modules.pullback p).obj M,⊤)) :
    transportSection j _ _ (along j p q hq M) v =
      pullbackSectionOver p q M ⟨j,hq⟩ v := by
  unfold transportSection
  rw [hom_res, InitialHodgeSection.res_self]
  rfl

/-- Coherence for transporting the tautological section through the
selected open component and then along its disk lift. -/
lemma along_comp_section {B T Y Z : Scheme.{0}}
    (p : T ⟶ B) (j : Y ⟶ T) (q : Z ⟶ Y)
    (r : Y ⟶ B) (g : Z ⟶ T) (f : Z ⟶ B)
    (hjp : j ≫ p = r) (hqj : q ≫ j = g) (hgp : g ≫ p = f) (hqr : q ≫ r = f)
    (M : B.Modules) (v : Γ((Scheme.Modules.pullback p).obj M,⊤)) :
    transportSection q _ _ (along q r f hqr M)
      (transportSection j _ _ (along j p r hjp M) v) =
      transportSection g _ _ (along g p f hgp M) v := by
  have hc := ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.compIso_assoc
    q j p g r f hqj hjp hgp hqr M
  have he : composeComparison j q g hqj.symm
      ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback r).obj M)
      ((Scheme.Modules.pullback f).obj M) (along j p r hjp M) (along q r f hqr M) =
      along g p f hgp M := by
    apply Iso.ext
    have hleft : (composeComparison j q g hqj.symm
        ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback r).obj M)
        ((Scheme.Modules.pullback f).obj M) (along j p r hjp M) (along q r f hqr M)).hom =
        (along q j g hqj ((Scheme.Modules.pullback p).obj M)).inv ≫
          ((Scheme.Modules.pullback q).map (along j p r hjp M).hom ≫
            (along q r f hqr M).hom) := by
      simp [composeComparison, along, pullbackEqIso, Scheme.Modules.pullbackCongr, Category.assoc]
    rw [hleft]
    rw [show (Scheme.Modules.pullback q).map (along j p r hjp M).hom ≫
      (along q r f hqr M).hom =
      (along q j g hqj ((Scheme.Modules.pullback p).obj M)).hom ≫
        (along g p f hgp M).hom from hc]
    simp
  rw [← CompactDiscriminantSectionR0182.transportSection_comp_eq j q g hqj.symm
    _ _ _ (along j p r hjp M) (along q r f hqr M) v, he]

lemma transport_as_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) (M : Y.Modules) (N : Z.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (v : Γ(M,⊤)) :
    transportSection f M N e v = e.hom.app ⊤ (pullbackGlobalSection f M v) := by
  unfold transportSection
  rw [hom_res, InitialHodgeSection.res_self]
  rfl

lemma along_global {Y Z B : Scheme.{0}} (p : Y ⟶ B) (j : Z ⟶ Y) (q : Z ⟶ B)
    (hq : j ≫ p = q) (M : B.Modules) (a : Γ(M,⊤)) :
    transportSection j _ _ (along j p q hq M) (pullbackGlobalSection p M a) =
      pullbackGlobalSection q M a := by
  have hc : composeComparison p j q hq.symm M
      ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback q).obj M)
      (Iso.refl _) (along j p q hq M) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, along, pullbackEqIso, Scheme.Modules.pullbackCongr]
  have ht := CompactDiscriminantSectionR0182.transportSection_comp_eq p j q hq.symm
    M _ _ (Iso.refl _) (along j p q hq M) a
  simp only [hc, transport_as_app, id_app_apply] at ht
  simpa only [transport_as_app] using ht.symm

lemma pullback_global_app {Y Z : Scheme.{0}} (g : Z ⟶ Y) {M N : Y.Modules}
    (β : M ⟶ N) (s : Γ(M,⊤)) :
    pullbackGlobalSection g N (β.app ⊤ s) =
      ((Scheme.Modules.pullback g).map β).app ⊤ (pullbackGlobalSection g M s) := by
  exact Scheme.Modules.pullbackLocalSection_app g β s

/-- The frozen square comparison transports tensor-square sections through
exactly the displayed commuting triangle. -/
lemma pullSquare_transport {Z Y B : Scheme.{0}} (g : Z ⟶ Y) (p : Y ⟶ B)
    (f : Z ⟶ B) (hg : g ≫ p = f) (A J : B.Modules)
    (β : tensorPower Y ((Scheme.Modules.pullback p).obj A) 2 ≅
      (Scheme.Modules.pullback p).obj J)
    (a : Γ((Scheme.Modules.pullback p).obj A,⊤)) :
    (pullSquare g p f hg A J β).hom.app ⊤
      (tensorPowerSection Z ((Scheme.Modules.pullback f).obj A) 2 ⊤
        (transportSection g _ _ (along g p f hg A) a)) =
      transportSection g _ _ (along g p f hg J)
        (β.hom.app ⊤ (tensorPowerSection Y _ 2 ⊤ a)) := by
  have ht := transportSection_tensor g _ _ (along g p f hg A) 2 a
  rw [transport_as_app] at ht
  rw [← ht]
  change (along g p f hg J).hom.app ⊤
    (((Scheme.Modules.pullback g).map β.hom).app ⊤
      ((tensorComparison g _ _ (along g p f hg A) 2).inv.app ⊤
        ((tensorComparison g _ _ (along g p f hg A) 2).hom.app ⊤ _))) = _
  rw [iso_inv_hom_apply, transport_as_app, pullback_global_app]

lemma along_local {Y Z B : Scheme.{0}} (p : Y ⟶ B) (g : Z ⟶ Y) (f : Z ⟶ B)
    (hg : g ≫ p = f) (M : B.Modules) (U : B.Opens) (a : Γ(M,U))
    (V : Z.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hgp : V ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback f).obj M) hgp
      ((along g p f hg M).hom.app _ (Scheme.Modules.pullbackLocalSection g
        (Scheme.Modules.pullbackLocalSection p a))) =
    res ((Scheme.Modules.pullback f).obj M) hf (Scheme.Modules.pullbackLocalSection f a) := by
  have hc : composeComparison p g f hg.symm M
      ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback f).obj M)
      (Iso.refl _) (along g p f hg M) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, along, pullbackEqIso, Scheme.Modules.pullbackCongr]
  have ht := composeComparison_section p g f hg.symm M _ _
    (Iso.refl _) (along g p f hg M) U a V hf hgp
  rw [hc] at ht
  exact ht.symm

lemma along_local_scalar {Y Z B : Scheme.{0}} (p : Y ⟶ B) (g : Z ⟶ Y) (f : Z ⟶ B)
    (hg : g ≫ p = f) (M : B.Modules) (v : Γ((Scheme.Modules.pullback p).obj M,⊤))
    (U : B.Opens) (a : Γ(M,U)) (c : Γ(Y,p ⁻¹ᵁ U))
    (hv : res ((Scheme.Modules.pullback p).obj M) le_top v =
      c • Scheme.Modules.pullbackLocalSection p a)
    (hf : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ U) (hgp : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    transportSection g _ _ (along g p f hg M) v =
      g.appLE (p ⁻¹ᵁ U) ⊤ hgp c •
        res ((Scheme.Modules.pullback f).obj M) hf (Scheme.Modules.pullbackLocalSection f a) := by
  have ht := transportSection_restrict g _ _ (along g p f hg M) v (p ⁻¹ᵁ U) ⊤ hgp
  rw [InitialHodgeSection.res_self, hv, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul, InitialHodgeSection.res_smul, along_local] at ht
  exact ht

/-- On the complete disk, multiplication by the tautological section
commutes with the actual geometric pullback triangle. -/
lemma disk_multiply_transport
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (A : DivisorLine (Component k L D X x))
    (W : Twist k L D X x A H) (hW : Scheme.Modules.IsInvertible W.line)
    {Z : Scheme.{0}} (p : Z ⟶ Component k L D X x)
    (g : Disk k ⟶ Z) (f : Disk k ⟶ Component k L D X x) (hg : g ≫ p = f)
    (v : Γ((Scheme.Modules.pullback p).obj W.line,⊤)) :
    transportSection g _ _ (along g p f hg (hodge k L D X x H))
      ((pullMultiply k L D X x W p).hom.app ⊤
        (tensorSection Z _ _ ⊤ v (tensorPowerSection Z _ 2 ⊤
          (pullbackGlobalSection p A.line A.section_)))) =
    (pullMultiply k L D X x W f).hom.app ⊤
      (tensorSection (Disk k) _ _ ⊤
        (transportSection g _ _ (along g p f hg W.line) v)
        (tensorPowerSection (Disk k) _ 2 ⊤ (pullbackGlobalSection f A.line A.section_))) := by
  let J := hodge k L D X x H
  let ε := (pullMultiply k L D X x W p).hom.app ⊤
    (tensorSection Z _ _ ⊤ v (tensorPowerSection Z _ 2 ⊤
      (pullbackGlobalSection p A.line A.section_)))
  obtain ⟨U, u, hu, huf⟩ := local_frame_exists hW (f (closedPoint k))
  have hfU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hu).ge
  have hgU : (⊤ : (Disk k).Opens) ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    change (⊤ : (Disk k).Opens) ≤ (g ≫ p) ⁻¹ᵁ U
    rw [hg]
    exact hfU
  have hup := pullback_frame p W.line u huf
  obtain ⟨c, hc⟩ := (hup (p ⁻¹ᵁ U) le_rfl).surjective
    (res ((Scheme.Modules.pullback p).obj W.line) le_top v)
  rw [InitialHodgeSection.res_self] at hc
  let a := res A.line (show U ≤ ⊤ from le_top) A.section_
  let e := W.multiply.hom.app U (tensorSection _ _ _ U u
    (tensorPowerSection _ A.line 2 U a))
  have hε : res ((Scheme.Modules.pullback p).obj J) le_top ε =
      c • Scheme.Modules.pullbackLocalSection p e := by
    dsimp only [ε]
    rw [hom_res, tensor_res, power_res]
    have ha : res ((Scheme.Modules.pullback p).obj A.line) le_top
        (pullbackGlobalSection p A.line A.section_) = Scheme.Modules.pullbackLocalSection p a :=
      pullbackGlobalSection_restrict p A.line U A.section_
    rw [← hc, ha, tensor_smul_left, Scheme.Modules.Hom.app_smul, pull_multiply_local]
  change transportSection g _ _ (along g p f hg J) ε = _
  rw [along_local_scalar p g f hg J ε U e c hε hfU hgU,
    along_local_scalar p g f hg W.line v U u c hc.symm hfU hgU,
    tensor_smul_left, Scheme.Modules.Hom.app_smul]
  congr 1
  dsimp only [e]
  rw [← pull_multiply_local, hom_res, tensor_res, power_res]
  have ha : res ((Scheme.Modules.pullback f).obj A.line) hfU
      (Scheme.Modules.pullbackLocalSection f a) = pullbackGlobalSection f A.line A.section_ := by
    dsimp only [a]
    rw [← InitialSectionNaturality.pullback_res, InitialHodgeSection.res_res,
      InitialHodgeSection.res_self]
    rfl
  rw [ha]

/-- The square map built from the root pulls back to multiplication by the
prescribed full disk root, through the frozen square comparison. -/
lemma root_square_branch
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
    (H : Extension k L D X) (A : DivisorLine (Component k L D X x))
    (W : Twist k L D X x A H) (hW : Scheme.Modules.IsInvertible W.line)
    {Z : Scheme.{0}} (p : Z ⟶ Component k L D X x)
    (g : Disk k ⟶ Z) (f : Disk k ⟶ Component k L D X x) (hg : g ≫ p = f)
    (v : Γ((Scheme.Modules.pullback p).obj W.line,⊤))
    (hv : IsFrame ((Scheme.Modules.pullback p).obj W.line) ⊤ v)
    (w : Γ((Scheme.Modules.pullback f).obj W.line,⊤))
    (hw : pullbackSectionOver p f W.line ⟨g,hg⟩ v = w) :
    (pullSquare g p f hg A.line (hodge k L D X x H)
      (multiplyFrame (pullMultiply k L D X x W p) v hv)).hom.app ⊤
      (tensorPowerSection (Disk k) _ 2 ⊤ (pullbackGlobalSection f A.line A.section_)) =
    (pullMultiply k L D X x W f).hom.app ⊤
      (tensorSection (Disk k) _ _ ⊤ w
        (tensorPowerSection (Disk k) _ 2 ⊤ (pullbackGlobalSection f A.line A.section_))) := by
  have ht := pullSquare_transport g p f hg A.line (hodge k L D X x H)
    (multiplyFrame (pullMultiply k L D X x W p) v hv)
    (pullbackGlobalSection p A.line A.section_)
  rw [along_global, multiplyFrame_apply, InitialHodgeSection.res_self,
    disk_multiply_transport k L D X x H A W hW p g f hg v,
    transport_along_eq, hw] at ht
  exact ht

#print axioms component_disk_factor
#print axioms twist_torsor
#print axioms selected_geometry
#print axioms twist_pullback_discriminant
#print axioms common_frame_from_branch
#print axioms halfCoverOfRoot
#print axioms along_comp_section
#print axioms root_square_branch
#print axioms along_root
#print axioms disk_lift_unique

end ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185




namespace ArithmeticThetaCommonHalfHodgeR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaRootTorsor CommonHalfHodgeCoverR0185
open OpenDiscriminantFullTateExpansionR0182

/-- The common half-Hodge cover, with the prescribed complete Tate branch,
constructed on the actual accepted geometric component. -/
theorem common_half_hodge_cover :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X, ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodge k L D X H s V := by
  intro k _ _ _ L hL h24 D X H hH s hs V
  have hlev : 3 ≤ L := le_trans (by decide) (Nat.le_of_dvd hL h24)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 24) h24)
  let x := V.disk (closedPoint k)
  obtain ⟨f, hf⟩ := component_disk_factor k L D X V
  obtain ⟨A, hA, hAdisk⟩ := cusp_half_divisor_line k L hL h24 D X x
  obtain ⟨W, hW⟩ := discriminant_twist_unit k L hL h24 D X x H hH s hs A hA
  obtain ⟨w, hw, _⟩ := discriminant_tate_root k L hL h24 D X x H hH s hs A hA W hW V f hf
  obtain ⟨T, p, u, hfin, het, hsur, hrank, huf, hupow, gf, hgf⟩ :=
    twist_torsor k L D X x H s A W hW f w hw.2.1
  letI := hfin
  letI := het
  obtain ⟨U, b, hb, hint, hqfin, hqet, hqsur, hqproper, hqsmooth, hqrank⟩ :=
    selected_geometry k L hlev heven D X x T p hrank gf.val
  let q : U.toScheme ⟶ Component k L D X x := U.ι ≫ p
  have hbq : b ≫ q = f := by
    change b ≫ (U.ι ≫ p) = f
    rw [← Category.assoc, hb]
    exact gf.property
  let v := transportSection U.ι _ _ (along U.ι p q rfl W.line) u
  have hvf : IsFrame ((Scheme.Modules.pullback q).obj W.line) ⊤ v :=
    transport_frame U.ι _ _ (along U.ι p q rfl W.line) u huf
  have hvpow : tensorPowerSection U.toScheme _ 24 ⊤ v =
      pullbackPowerSection q W.line 24 W.section_ :=
    along_root p U.ι q rfl W.line hW.1 24 W.section_ u hupow
  let C := halfCoverOfRoot k L D X x H s A W hW U.toScheme q hint hqfin hqet hqsur
    hqproper hqsmooth hqrank v hvf hvpow
  refine ⟨f, hf, A, hA, C, ?_⟩
  letI : IsFinite q := hqfin
  letI : Etale q := hqet
  obtain ⟨g, hg, huniq⟩ := disk_lift_unique k q f b hbq
  have hbg : b = g := huniq b ⟨hbq, rfl⟩
  have hvg : pullbackSectionOver q f W.line ⟨g, hg.1⟩ v = w := by
    subst g
    rw [← transport_along_eq]
    change transportSection b _ _ (along b q f hg.1 W.line)
      (transportSection U.ι _ _ (along U.ι p q rfl W.line) u) = w
    rw [along_comp_section p U.ι b q gf.val f rfl hb gf.property hg.1 W.line u,
      transport_along_eq]
    exact hgf
  refine ⟨g, hg.1, ?_⟩
  intro η hη
  obtain ⟨a, haf, has⟩ := hAdisk V f hf
  let β := pullSquare g q f hg.1 A.line (hodge k L D X x H) C.square ≪≫
    diskHodgeIso k L D X x H V f hf
  have hβ : β.hom.app ⊤
      (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤
        (pullbackGlobalSection f A.line A.section_)) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η := by
    have he := root_square_branch k L D X x H A W hW.1 q g f hg.1 v hvf w hvg
    exact (congrArg ((diskHodgeIso k L D X x H V f hf).hom.app ⊤) he).trans (hw.2.2 η hη)
  exact common_frame_from_branch k L hL h24 _ _ a
    (pullbackGlobalSection f A.line A.section_) haf has β η hη.1 hβ

#print axioms common_half_hodge_cover
end ArithmeticThetaCommonHalfHodgeR0185
