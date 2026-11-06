import TensorPowerDefinitions

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace ArithmeticThetaPullback

/-- The global section map induced by the actual pullback/pushforward adjunction.
It is only an ordinary definition; the compatibility laws are target obligations. -/
def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) :=
  fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s

end ArithmeticThetaPullback
