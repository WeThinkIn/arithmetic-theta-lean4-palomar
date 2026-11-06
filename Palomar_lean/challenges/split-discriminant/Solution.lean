module
public import SplitDiscriminantDivisorR0239
import all Lean.Meta.Match.Match
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
namespace P458
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
end P458
namespace P505
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) :=
  Classical.choose (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
end P505
namespace P505
open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end P505
namespace P485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end P485
namespace P505
theorem binary_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : binary f H K = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K := by
  have h := Classical.choose_spec (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
  have hq : P458.Compatible f H K _ _ (Iso.refl _) (Iso.refl _) (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K) := by
    intro U s t
    change (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _ (Scheme.Modules.pullbackLocalSection f (ArithmeticThetaSheafTensor.tensorSection Y H K U s t)) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section]
    rfl
  exact (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).unique h hq
theorem powerComparison_eq_original (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) (n : ℕ) : powerComparison X Y f H n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerComparison, ArithmeticThetaPullback.pullback_tensorPower_iso, binary_eq_original, ih]
end P505
namespace P509.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
def tensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X K n :=
  P505.powerComparison X Y p H n ≪≫ powerCongr X e n
end P509.HodgeBaseChange
namespace P509.OpenHodge
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower ArithmeticThetaOpenHodgeR0180
def powerComparison {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) : (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n :=
  P509.HodgeBaseChange.tensorComparison (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n
def pullSection {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤)) : Γ(HodgePower R W n, ⊤) :=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))
def IsD2 {S : Type u} [CommRing S] (E : EllipticFamily S) (d : Γ(power E 24, ⊤)) : Prop :=
  IsFrame (power E 24) ⊤ d ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G →
    ∀ (C : Test S E R W G) (g : (Curve R W).functionField),
    Normalized R W G 5 g → RepresentsInitial R W G 5 g (pullSection C 24 d)
end P509.OpenHodge
namespace P509.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def pullToOpen {D : LevelData k L} (n : ℕ) (s : Γ(power D.atlas.descent.family n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((P505.powerComparison _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (Scheme.Modules.pullbackLocalSection D.quotient.inclusion s))
def restrictPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((P509.HodgeBaseChange.tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))
end P509.BoundaryHodge
namespace P509
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaTensorPower
theorem tensorComparison_eq_original {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : HodgeBaseChange.tensorComparison p H K e n = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison p H K e n := by
  simp only [HodgeBaseChange.tensorComparison, ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison, P505.powerComparison_eq_original]
theorem isD2_iff_original {S : Type u} [CommRing S] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (d : Γ(ArithmeticThetaOpenHodgeR0180.power E 24, ⊤)) : OpenHodge.IsD2 E d ↔ ArithmeticThetaOpenHodgeR0180.IsD2 E d := by
  simp only [OpenHodge.IsD2, ArithmeticThetaOpenHodgeR0180.IsD2, OpenHodge.pullSection, ArithmeticThetaOpenHodgeR0180.pullSection, OpenHodge.powerComparison, ArithmeticThetaOpenHodgeR0180.powerComparison, tensorComparison_eq_original]
end P509
namespace P509.NormalizedSections
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaTensorPower
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) :=
  (P505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens))
    (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
end P509.NormalizedSections
namespace P509.ComponentDegree
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)
def restrict (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(power k L D X x H n, ⊤) :=
  P509.NormalizedSections.pullbackPowerSection (inclusion k L D X x) H.line n s
def IsCompactD2 (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop :=
  ∃ d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤),
    P509.OpenHodge.IsD2 D.atlas.descent.family d ∧
    P509.BoundaryHodge.restrictPower k L H 24 s = P509.BoundaryHodge.pullToOpen k L 24 d
end P509.ComponentDegree
namespace P509
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaTensorPower
theorem compactD2_iff_original (k : Type) [Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤)) : ComponentDegree.IsCompactD2 k L D X H s ↔ ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s := by
  simp only [ComponentDegree.IsCompactD2, ArithmeticThetaComponentDegreeR0184.IsCompactD2, isD2_iff_original, BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, tensorComparison_eq_original, P505.powerComparison_eq_original]
theorem restrict_eq_original (k : Type) [Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : ComponentDegree.restrict k L D X x H n s = ArithmeticThetaComponentDegreeR0184.restrict k L D X x H n s := by
  simp only [ComponentDegree.restrict, ArithmeticThetaComponentDegreeR0184.restrict, NormalizedSections.pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, P505.powerComparison_eq_original]
end P509
namespace ArithmeticThetaPalomarSplit515
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
theorem splitComponentDiscriminantDivisor : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), P509.ComponentDegree.IsCompactD2 k L D X H s → (P509.ComponentDegree.restrict k L D X x H 24 s) ≠ 0 ∧ ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) ι), ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) C (P509.ComponentDegree.restrict k L D X x H 24 s) E ∧ ∀ y : ArithmeticThetaComponentDegreeR0184.Component k L D X x, (y ∈ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = (2*L : ℕ)) ∧ (y ∉ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = 0) := by
  simpa only [P509.compactD2_iff_original, P509.restrict_eq_original] using ArithmeticThetaCyclotomicModularityR0239.split_component_discriminant_divisor
theorem recover_original_073 : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) ≠ 0 ∧ ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) ι), ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) C (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) E ∧ ∀ y : ArithmeticThetaComponentDegreeR0184.Component k L D X x, (y ∈ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = (2*L : ℕ)) ∧ (y ∉ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = 0) := by
  simpa only [P509.compactD2_iff_original, P509.restrict_eq_original] using splitComponentDiscriminantDivisor
end ArithmeticThetaPalomarSplit515
