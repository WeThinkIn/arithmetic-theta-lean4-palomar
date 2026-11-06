module
public import CompactAlphaCanonicalHalfLineR0192
public import SchemeDiscriminantExistenceR0244
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
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
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaGlobalFourTorsionR0190
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
def AlphaHalfBranch (x : X.space) (A : DivisorLine (Component k L D X x)) (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H) : Prop :=
  ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ V.level →
    ∀ (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Component k L D X x)
      (hf : f ≫ inclusion k L D X x = V.disk)
      (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)),
    ExtendsGenerator k L H V η →
    ∃ h : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
      ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ h ∧
      pullbackGlobalSection f A.line A.section_ =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L) • h ∧
      (diskHodgeIso k L D X x H V f hf).hom.app ⊤
        (((powerComparison _ _ f A.line 2).symm ≪≫
          (Scheme.Modules.pullback f).mapIso β).hom.app ⊤
          (tensorPowerSection _ ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ h)) = η
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarHalf505
theorem branch_iff_original (k : Type) [Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (β : ArithmeticThetaTensorPower.tensorPower _ A.line 2 ≅ ArithmeticThetaComponentDegreeR0184.hodge k L D X x H) : AlphaHalfBranch k L D X H x A β ↔ ArithmeticThetaSquareLinesR0192.AlphaHalfBranch k L D X H x A β := by
  simp only [AlphaHalfBranch, ArithmeticThetaSquareLinesR0192.AlphaHalfBranch, powerComparison_eq_original]
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarHalf505
theorem compactAlphaCanonicalHalfLine :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (a : (H.line).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSquareLinesR0192.IsCompactAlpha k L D X H a → ∀ x : X.space, ∃ (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ) (hE : ∀ y, 0 ≤ E y) (hN : ArithmeticThetaNormalizedSections.NormalAffine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaSquareLinesR0192.HalfAlphaDivisor k L D X H x a E ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line ∧ ∃ β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H), β.hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2 ⊤ (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).section_) = ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ∧ ArithmeticThetaPalomarHalf505.AlphaHalfBranch k L D X H x (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN) β := by
  simpa only [branch_iff_original] using ArithmeticThetaSquareLinesR0192.compact_alpha_canonical_half_line
theorem recover_original_042 :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (a : (H.line).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSquareLinesR0192.IsCompactAlpha k L D X H a → ∀ x : X.space, ∃ (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ) (hE : ∀ y, 0 ≤ E y) (hN : ArithmeticThetaNormalizedSections.NormalAffine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaSquareLinesR0192.HalfAlphaDivisor k L D X H x a E ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line ∧ ∃ β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H), β.hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2 ⊤ (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).section_) = ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ∧ ArithmeticThetaSquareLinesR0192.AlphaHalfBranch k L D X H x (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN) β := by
  simpa only [branch_iff_original] using compactAlphaCanonicalHalfLine
end ArithmeticThetaPalomarHalf505
