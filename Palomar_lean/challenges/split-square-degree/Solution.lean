module
public import SplitSquareCoverDegreeR0239
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
namespace P485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end P485
namespace ArithmeticThetaPalomarSplit516
theorem splitSquareCoverDegree : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (x : X.space) (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H)) (b n : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.projection k L D X x) b), ArithmeticThetaSharpCoverR0194.SquareCoverDegree k L D X H x J b n C := by
  exact ArithmeticThetaCyclotomicModularityR0239.split_square_cover_degree
theorem recover_original_074 : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (x : X.space) (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H)) (b n : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.projection k L D X x) b), ArithmeticThetaSharpCoverR0194.SquareCoverDegree k L D X H x J b n C := splitSquareCoverDegree
end ArithmeticThetaPalomarSplit516
