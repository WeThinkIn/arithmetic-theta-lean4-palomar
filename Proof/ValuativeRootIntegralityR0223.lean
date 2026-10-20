module

public import ValuativeRootSectionsDefinitionsR0223

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaValuativeRootsR0223
namespace ValuativeRootIntegralityR0223
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaSheafTensor ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

lemma pullback_hom_ext {X Y : Scheme.{0}} (p : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (a b : (Scheme.Modules.pullback p).obj M ⟶ N)
    (h : ∀ (U : Y.Opens) (s : Γ(M,U)),
      a.app _ (Scheme.Modules.pullbackLocalSection p s) =
      b.app _ (Scheme.Modules.pullbackLocalSection p s)) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  exact h U.unop s

lemma pullback_tensor_hom_ext {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M N : Y.Modules) (P : X.Modules)
    (a b : (Scheme.Modules.pullback p).obj (sheafTensor Y M N) ⟶ P)
    (h : ∀ (U : Y.Opens) (s : Γ(M,U)) (t : Γ(N,U)),
      a.app _ (Scheme.Modules.pullbackLocalSection p (tensorSection Y M N U s t)) =
      b.app _ (Scheme.Modules.pullbackLocalSection p (tensorSection Y M N U s t))) :
    a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ P).injective
  apply tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

def binaryComparison {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M N : Y.Modules) (P Q : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ P)
    (d : (Scheme.Modules.pullback p).obj N ≅ Q) :
    (Scheme.Modules.pullback p).obj (sheafTensor Y M N) ≅ sheafTensor X P Q :=
  pullback_sheafTensor_iso X Y p M N ≪≫ sheafTensorCongr X e d

lemma binaryComparison_section {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M N : Y.Modules) (P Q : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ P)
    (d : (Scheme.Modules.pullback p).obj N ≅ Q)
    (U : Y.Opens) (s : Γ(M,U)) (t : Γ(N,U)) :
    (binaryComparison p M N P Q e d).hom.app _
      (Scheme.Modules.pullbackLocalSection p (tensorSection Y M N U s t)) =
    tensorSection X P Q (p ⁻¹ᵁ U)
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))
      (d.hom.app _ (Scheme.Modules.pullbackLocalSection p t)) := by
  change (sheafTensorCongr X e d).hom.app _
    ((pullback_sheafTensor_iso X Y p M N).hom.app _ _) = _
  rw [HodgeBaseChange.pullback_sheafTensor_local_section, sheafTensorCongr_section]

lemma binaryComparison_comp {X Y Z : Scheme.{0}} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M₁ M₂ : X.Modules) (N₁ N₂ : Y.Modules) (P₁ P₂ : Z.Modules)
    (e₁ : (Scheme.Modules.pullback p).obj M₁ ≅ N₁)
    (e₂ : (Scheme.Modules.pullback p).obj M₂ ≅ N₂)
    (d₁ : (Scheme.Modules.pullback q).obj N₁ ≅ P₁)
    (d₂ : (Scheme.Modules.pullback q).obj N₂ ≅ P₂) :
    binaryComparison (q ≫ p) M₁ M₂ P₁ P₂
      (composeComparison p q (q ≫ p) rfl M₁ N₁ P₁ e₁ d₁)
      (composeComparison p q (q ≫ p) rfl M₂ N₂ P₂ e₂ d₂) =
    composeComparison p q (q ≫ p) rfl
      (sheafTensor X M₁ M₂) (sheafTensor Y N₁ N₂) (sheafTensor Z P₁ P₂)
      (binaryComparison p M₁ M₂ N₁ N₂ e₁ e₂)
      (binaryComparison q N₁ N₂ P₁ P₂ d₁ d₂) := by
  apply Iso.ext
  apply pullback_tensor_hom_ext
  intro U s t
  rw [binaryComparison_section, composeComparison_section_comp,
    composeComparison_section_comp, composeComparison_section_comp,
    binaryComparison_section, binaryComparison_section]
  rfl

lemma tensorCongr_trans (X : Scheme.{0}) {M N P M' N' P' : X.Modules}
    (e : M ≅ N) (f : N ≅ P) (e' : M' ≅ N') (f' : N' ≅ P') :
    sheafTensorCongr X e e' ≪≫ sheafTensorCongr X f f' =
      sheafTensorCongr X (e ≪≫ f) (e' ≪≫ f') := by
  apply Iso.ext
  apply tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change (sheafTensorCongr X f f').hom.app U.unop
    ((sheafTensorCongr X e e').hom.app U.unop (tensorSection X M M' U.unop s t)) =
    (sheafTensorCongr X (e ≪≫ f) (e' ≪≫ f')).hom.app U.unop
      (tensorSection X M M' U.unop s t)
  rw [sheafTensorCongr_section, sheafTensorCongr_section, sheafTensorCongr_section]
  rfl

lemma tensorCongr_refl (X : Scheme.{0}) (M N : X.Modules) :
    sheafTensorCongr X (Iso.refl M) (Iso.refl N) = Iso.refl _ := by
  apply Iso.ext
  apply tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change (sheafTensorCongr X (Iso.refl M) (Iso.refl N)).hom.app U.unop
    (tensorSection X M N U.unop s t) = tensorSection X M N U.unop s t
  rw [sheafTensorCongr_section]
  rfl

lemma tensorComparison_succ {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (n : ℕ) :
    tensorComparison p M N e (n+1) =
      binaryComparison p (tensorPower Y M n) M (tensorPower X N n) N
        (tensorComparison p M N e n) e := by
  change (pullback_sheafTensor_iso X Y p (tensorPower Y M n) M ≪≫
    sheafTensorCongr X (pullback_tensorPower_iso X Y p M n) (Iso.refl _)) ≪≫
      sheafTensorCongr X (powerCongr X e n) e = _
  rw [Iso.trans_assoc, tensorCongr_trans]
  rfl

lemma powerCongr_refl (X : Scheme.{0}) (M : X.Modules) (n : ℕ) :
    powerCongr X (Iso.refl M) n = Iso.refl _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sheafTensorCongr X (powerCongr X (Iso.refl M) n) (Iso.refl M) = _
    rw [ih, tensorCongr_refl]
    rfl

lemma tensorComparison_refl_general {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M : Y.Modules) (n : ℕ) :
    tensorComparison p M _ (Iso.refl _) n = pullback_tensorPower_iso X Y p M n := by
  unfold tensorComparison
  rw [powerCongr_refl, Iso.trans_refl]

lemma unit_section {X Y : Scheme.{0}} (p : X ⟶ Y) (U : Y.Opens) (a : Γ(Y,U)) :
    (pullback_unit_iso X Y p).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (L := SheafOfModules.unit Y.ringCatSheaf) a) =
      p.app U a :=
  ArithmeticThetaNormalizedSections.pullback_unit_local_section X Y p U a

lemma tensorComparison_comp_general {X Y Z : Scheme.{0}}
    (p : Y ⟶ X) (q : Z ⟶ Y) (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (d : (Scheme.Modules.pullback q).obj N ≅ P) (n : ℕ) :
    tensorComparison (q ≫ p) M P
      (composeComparison p q (q ≫ p) rfl M N P e d) n =
    composeComparison p q (q ≫ p) rfl
      (tensorPower X M n) (tensorPower Y N n) (tensorPower Z P n)
      (tensorComparison p M N e n) (tensorComparison q N P d n) := by
  induction n with
  | zero =>
    apply Iso.ext
    apply pullback_hom_ext
    intro U s
    rw [composeComparison_section_comp]
    change (pullback_unit_iso Z X (q ≫ p)).hom.app _
      (Scheme.Modules.pullbackLocalSection (q ≫ p) s) =
      (pullback_unit_iso Z Y q).hom.app _ (Scheme.Modules.pullbackLocalSection q
        ((pullback_unit_iso Y X p).hom.app _ (Scheme.Modules.pullbackLocalSection p s)))
    change Γ(X,U) at s
    erw [unit_section, unit_section, unit_section]
    rfl
  | succ n ih =>
    rw [tensorComparison_succ, tensorComparison_succ, tensorComparison_succ, ih]
    exact binaryComparison_comp p q _ _ _ _ _ _ _ _ _ _

open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaSimultaneousUnaryR0187

lemma comp_power {X Y Z : Scheme.{0}} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : X.Modules) (n : ℕ) (s : Γ(tensorPower X M n,⊤)) :
    transportSection q _ _
      (tensorComparison q ((Scheme.Modules.pullback p).obj M)
        ((Scheme.Modules.pullback (q ≫ p)).obj M) ((Scheme.Modules.pullbackComp q p).app M) n)
      (pullbackPowerSection p M n s) = pullbackPowerSection (q ≫ p) M n s := by
  have hc : composeComparison p q (q ≫ p) rfl M
      ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback (q ≫ p)).obj M)
      (Iso.refl _) ((Scheme.Modules.pullbackComp q p).app M) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, pullbackEqIso]
  have ht := transportSection_comp p q (tensorPower X M n)
    (tensorPower Y ((Scheme.Modules.pullback p).obj M) n)
    (tensorPower Z ((Scheme.Modules.pullback (q ≫ p)).obj M) n)
    (tensorComparison p M _ (Iso.refl _) n)
    (tensorComparison q _ _ ((Scheme.Modules.pullbackComp q p).app M) n) s
  rw [← tensorComparison_comp_general, hc, tensorComparison_refl_general,
    tensorComparison_refl_general, transport_power_refl, transport_power_refl] at ht
  exact ht.symm

lemma scalar_generic (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (a : A) :
    (genericInclusion Ω A).appLE ⊤ ⊤ (by simp) (scalar A a) =
      scalar Ω (algebraMap A Ω a) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap A Ω))) a).symm

lemma genericFrame_transport (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules)
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J)) :
    transportSection (genericInclusion Ω A) _ _
      ((Scheme.Modules.pullbackComp (genericInclusion Ω A) f).app J) h =
      genericFrame Ω A f J h := by
  rw [transport_as_app]
  rfl

/-- The given integral frame extracts a regular coefficient, whose generic
value is the prescribed power. No invertibility of J on Z is assumed. -/
lemma coefficient (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules) (K : ℕ)
    (F : Sections Z (tensorPower Z J K))
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (hh : IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ h)
    (r : Ω) (hr : FieldEquation Ω A f J K F h r) :
    ∃ c : A, algebraMap A Ω c = r^K ∧
      pullbackPowerSection f J K F = scalar A c •
        tensorPowerSection (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J) K ⊤ h := by
  have hp := InitialHodgeSection.tensor_frame _ h hh K
  obtain ⟨C, hC⟩ := (hp ⊤ le_rfl).surjective (pullbackPowerSection f J K F)
  simp only [InitialHodgeSection.res_self] at hC
  let c : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom C
  have hc : scalar A c = C :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm_apply_apply C
  have he : pullbackPowerSection f J K F = scalar A c •
      tensorPowerSection (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J) K ⊤ h := by
    rw [hc]
    exact hC.symm
  refine ⟨c, ?_, he⟩
  let e := (Scheme.Modules.pullbackComp (genericInclusion Ω A) f).app J
  have ht := congrArg (transportSection (genericInclusion Ω A) _ _
    (tensorComparison (genericInclusion Ω A) _ _ e K)) he
  rw [comp_power, transportSection_smul, transportSection_tensor,
    scalar_generic, genericFrame_transport] at ht
  have hg : IsFrame _ ⊤ (genericFrame Ω A f J h) := by
    rw [← genericFrame_transport]
    exact transport_frame _ _ _ e h hh
  have hinj := (InitialHodgeSection.tensor_frame _ _ hg K ⊤ le_rfl).injective
  have hs : scalar Ω (algebraMap A Ω c) = scalar Ω (r^K) := by
    apply hinj
    simp only [InitialHodgeSection.res_self]
    exact ht.symm.trans hr
  exact (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.injective hs

end ValuativeRootIntegralityR0223

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180

/-- A prescribed field root has a unique integral lift in the original frame. -/
theorem valuative_root_integrality
    (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (Z : Scheme.{0})
    (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules) (K : ℕ) (hK : 0 < K)
    (F : Sections Z (tensorPower Z J K))
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (hh : IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ h)
    (r : Ω) (hr : FieldEquation Ω A f J K F h r) :
    ∃! a : A, algebraMap A Ω a = r ∧ IntegralEquation Ω A f J K F h a := by
  obtain ⟨c, hc, he⟩ := ValuativeRootIntegralityR0223.coefficient Ω A f J K F h hh r hr
  have hi : IsIntegral A (r^K) := hc ▸ isIntegral_algebraMap
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hK hi
  have hap : a^K = c := by
    apply (IsFractionRing.injective A Ω)
    rw [map_pow, ha, hc]
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · unfold IntegralEquation
    rw [hap]
    exact he
  · intro b hb
    apply (IsFractionRing.injective A Ω)
    exact hb.1.trans ha.symm

#print axioms valuative_root_integrality
end ArithmeticThetaValuativeRootsR0223
