module
public import ProjectiveProviderBridge
import all ProjectiveProviderBridge
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaTateSchemeMarkingR0263
namespace PalomarSquare1209

def Square : Prop :=
  ∀ (X : Scheme.{0}) (N : X.Modules) (r : X ⟶ X) (hr : r ≫ r = 𝟙 X)
    (ρ : (Scheme.Modules.pullback r).obj N ≅ N),
    (∀ (a b : (Scheme.Modules.pullback (r ≫ r)).obj N ≅ N),
      (∀ v, SectionAction.globalAct (r ≫ r) a v =
        SectionAction.globalAct (r ≫ r) b v) → a = b) →
    (∀ v, SectionAction.globalAct r ρ (SectionAction.globalAct r ρ v) = v) →
    (Scheme.Modules.pullback r).mapIso ρ ≪≫ ρ =
      (Scheme.Modules.pullbackComp r r).app N ≪≫
        (Scheme.Modules.pullbackCongr hr).app N ≪≫ (Scheme.Modules.pullbackId X).app N

theorem square : Square := by
  intro X N r hr ρ faithful hs
  have hc : Midpoint.composeLift r r N ρ ρ =
      (Scheme.Modules.pullbackCongr hr).app N ≪≫ (Scheme.Modules.pullbackId X).app N := by
    apply faithful
    intro v
    rw [ScalarLift.globalAct_comp, ScalarLift.globalAct_changeMap,
      ScalarLift.globalAct_identity, hs]
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp r r).app N).inv).mp
  simpa [Midpoint.composeLift, Category.assoc] using congrArg Iso.hom hc

end PalomarSquare1209
