module

public import PullbackTensorSections
public import TensorPowerRootIntegration
public import SmoothRootCurve
public import PullbackTensor
public import PullbackTensorDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower

universe u
noncomputable section

namespace ArithmeticThetaNormalizedSections

/-- The usual rank-one locally trivial module sheaf condition, using actual sheaf isomorphisms. -/
def IsLineBundle (X : Scheme.{u}) (H : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (SheafOfModules.unit (X.ringCatSheaf.over U) ≅ SheafOfModules.over H U)

/-- Normality of the affine charts, as needed by the accepted regular-root theorem. -/
def NormalAffine (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X, U)

/-- The literal coefficient of a global section in one actual local frame. -/
def sectionCoordinate (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) (s : Γ(H, ⊤)) : Γ(X,U) :=
  (e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)

/-- Its generic germ; this is not an assumed expansion map. -/
def sectionCoefficient (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (s : Γ(H, ⊤)) : X.functionField :=
  X.germToFunctionField U (sectionCoordinate X H U e s)

/-- Coefficient of an actual tensor-power section in the power of the chosen frame. -/
def powerCoefficient (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (n : ℕ)
    (F : Γ(tensorPower X H n, ⊤)) : X.functionField :=
  sectionCoefficient X (tensorPower X H n) U (tensorPowerFrame X H U e n) F

/-- Canonical local section pullback is the actual adjunction unit. -/
def pullbackLocalSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (s : Γ(H,U)) : Γ((Scheme.Modules.pullback p).obj H, p ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H).app U s

/-- Pullback of a power section via the accepted genuine tensor comparison. -/
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ)
    (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) :=
  (ArithmeticThetaPullback.pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens))
    (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)

/-- An actual pullback frame must send the pulled local basis to its unit basis.
This is a property to prove for a constructed frame, not a substitute line object. -/
def FramePullbackCompatible {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)) : Prop :=
  ∀ (V : X.Opens) (hVU : V ≤ U) (a : Γ(X,V)),
    pullbackLocalSection p H V (e.equiv V hVU a) =
      eY.equiv (p ⁻¹ᵁ V) (p.preimage_mono hVU) (p.app V a)

end ArithmeticThetaNormalizedSections
