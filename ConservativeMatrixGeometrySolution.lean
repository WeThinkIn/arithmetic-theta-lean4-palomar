module
public import ArithmeticGeometricFamilyExistenceR0189
public import GeometricFamilyConservativeCutoffR0189
public import SchemeDiscriminantExistenceR0244
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
namespace ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaSheafTensor
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) =
      tensorSection X M N (f ⁻¹ᵁ U)
        (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) : ∃! q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N, Compatible f H K M N e d q := by
  let q := ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
    ArithmeticThetaPullback.sheafTensorCongr X e d
  have hq : Compatible f H K M N e d q := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (pullSection f (tensorSection Y H K U s t))) = _
    rw [show pullSection f (tensorSection Y H K U s t) =
      Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t) from rfl]
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ArithmeticThetaSheafTensor.tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change q'.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t)) =
    q.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t))
  exact (hq' U.unop s t).trans (hq U.unop s t).symm
theorem compatible_iff_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Compatible f H K M N e d q ↔ q = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫ ArithmeticThetaPullback.sheafTensorCongr X e d := by
  have h : Compatible f H K M N e d (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
      ArithmeticThetaPullback.sheafTensorCongr X e d) := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t))) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  constructor
  · intro hq
    exact (canonicalBinaryTensor f H K M N e d).unique hq h
  · rintro rfl
    exact h
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) :=
  Classical.choose (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end ArithmeticThetaPalomarComponent485
namespace ArithmeticThetaPalomarHalf505
theorem binary_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : binary f H K = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K := by
  have h := Classical.choose_spec (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
  have hq : ArithmeticThetaPalomarBinaryTensor458.Compatible f H K _ _ (Iso.refl _) (Iso.refl _) (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K) := by
    intro U s t
    change (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _ (Scheme.Modules.pullbackLocalSection f (ArithmeticThetaSheafTensor.tensorSection Y H K U s t)) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section]
    rfl
  exact (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).unique h hq
theorem powerComparison_eq_original (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) (n : ℕ) : powerComparison X Y f H n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerComparison, ArithmeticThetaPullback.pullback_tensorPower_iso, binary_eq_original, ih]
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarConservative530
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185
def squareOnDisk (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : tensorPower (Disk k) ((Scheme.Modules.pullback f).obj J) 2 ≅ (Scheme.Modules.pullback d).obj H := (ArithmeticThetaPalomarHalf505.powerComparison (Disk k) B f J 2).symm ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ along f p d hf H
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) := (ArithmeticThetaPalomarHalf505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens)) (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
def GeometricFamily {n h : ℕ} (A : Matrices n h) (U : Indexing A) {D : LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A))} {X : Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D} (H : Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D X) (V : DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (commonN A)) D X) : Prop :=
  let N := commonN A
  let L := ArithmeticThetaCompactUnaryR0183.level N
  let x := V.disk (closedPoint ℂ)
  ∃ (J : DivisorLine (Component ℂ L D X x)), IsCuspHalfLine ℂ L D X x J ∧
    ∃ R : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x)
        (24 * (exponent N)^U.count),
      CoverDegree ℂ L D X x J (24 * (exponent N)^U.count) n R ∧
      ∃ (g : Disk ℂ ⟶ R.space)
        (hg : g ≫ (R.map ≫ inclusion ℂ L D X x) = V.disk),
        IsDominant (genericInclusion ℂ ≫ g) ∧
        ∃ (β : tensorPower R.space (coverLine J R) 2 ≅
            (Scheme.Modules.pullback (R.map ≫ inclusion ℂ L D X x)).obj H.line)
          (η : Sections (Disk ℂ) ((Scheme.Modules.pullback V.disk).obj H.line))
          (e : Sections (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R))),
          ExtendsGenerator ℂ L H V η ∧
          ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ e ∧
          (squareOnDisk ℂ (R.map ≫ inclusion ℂ L D X x) (coverLine J R) H.line
            β g V.disk hg).hom.app ⊤
            (tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R)) 2 ⊤ e) = η ∧
          ∃ (t : Fin U.count → Sections R.space (coverLine J R))
            (σ : Fin h → Sections R.space (tensorPower R.space (coverLine J R) n)),
            (∀ j, t j ≠ 0 ∧ pullbackGlobalSection g (coverLine J R) (t j) =
              ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ)
                (unarySeries ℂ N (U.pair j).1 (U.pair j).2) • e) ∧
            (∀ i, σ i = ∑ a : Cosets A i,
              tensorProductSection R.space (coverLine J R) n ⊤ (fun j => t (U.index i a j))) ∧
            (∀ c : Fin h → ℂ,
              pullbackPowerSection g (coverLine J R) n
                (∑ i : Fin h, baseScalar ℂ (R.map ≫ projection ℂ L D X x) (c i) • σ i) =
                ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (expanded A c) •
                  tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback g).obj (coverLine J R)) n ⊤ e)
end ArithmeticThetaPalomarConservative530
namespace ArithmeticThetaPalomarConservative530
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185
theorem squareOnDisk_eq_original (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : squareOnDisk k p J H β f d hf = ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H β f d hf := by
  simp only [squareOnDisk, ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem pullbackPowerSection_eq_original {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : pullbackPowerSection p H n F = ArithmeticThetaNormalizedSections.pullbackPowerSection p H n F := by
  simp only [pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem geometric_iff_original {n h : ℕ} (A : Matrices n h) (U : Indexing A) {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D} (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : GeometricFamily A U H V ↔ ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by
  simp only [GeometricFamily, ArithmeticThetaLatticeSectionsR0188.GeometricFamily, squareOnDisk_eq_original, pullbackPowerSection_eq_original]
end ArithmeticThetaPalomarConservative530
namespace ArithmeticThetaPalomarConservative530
theorem arithmeticGeometricFamilyExistence : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ∃ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaPalomarConservative530.GeometricFamily A U H V := by
  simpa only [geometric_iff_original] using ArithmeticThetaConservativeKernelR0189.arithmetic_geometric_family_existence
theorem recover_original_035 : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ∃ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by
  simpa only [geometric_iff_original] using arithmeticGeometricFamilyExistence
end ArithmeticThetaPalomarConservative530
namespace ArithmeticThetaPalomarConservative530
theorem geometricFamilyConservativeCutoff : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaPalomarConservative530.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaConservativeKernelR0189.cutoff A U) → ArithmeticThetaComputed.thetaMap A c = 0 := by
  simpa only [geometric_iff_original] using ArithmeticThetaConservativeKernelR0189.geometric_family_conservative_cutoff
theorem recover_original_036 : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaConservativeKernelR0189.cutoff A U) → ArithmeticThetaComputed.thetaMap A c = 0 := by
  simpa only [geometric_iff_original] using geometricFamilyConservativeCutoff
end ArithmeticThetaPalomarConservative530
