module

public import CompactUnaryHodgeRealizationR0183
public import TensorLineDegrees
public import MarkingCuspProjectionR0102
public import FiniteFullLevelCount
public import CompactHodgeLatticeExtensionR0182

@[expose] public section

/-! Actual components and Hodge sections of the accepted level compactification.
Only ordinary definitions and direct reuse of the accepted component instance
occur here. No cusp count, divisor identity or degree assertion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaComponentDegreeR0184
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

abbrev componentOpen : X.space.Opens :=
  ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x
abbrev Component : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
abbrev projection : Component k L D X x ⟶ Spec (CommRingCat.of k) :=
  inclusion k L D X x ≫ X.projection

instance componentIntegral : IsIntegral (Component k L D X x) :=
  ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent_integral k L D X x

instance componentLocallyNoetherian : IsLocallyNoetherian (Component k L D X x) := by
  letI := ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compact_noetherian k L D X
  infer_instance

def cuspSet : Set (Component k L D X x) :=
  {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps := {y : Component k L D X x // y ∈ cuspSet k L D X x}

abbrev hodge (H : Extension k L D X) : (Component k L D X x).Modules :=
  (Scheme.Modules.pullback (inclusion k L D X x)).obj H.line
abbrev power (H : Extension k L D X) (n : ℕ) : (Component k L D X x).Modules :=
  tensorPower (Component k L D X x) (hodge k L D X x H) n

def restrict (H : Extension k L D X) (n : ℕ)
    (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(power k L D X x H n, ⊤) :=
  pullbackPowerSection (inclusion k L D X x) H.line n s

/-- The intrinsic open D2 and its already proved unique compact extension.
This predicate does not assert a divisor, a degree, or a cusp count. -/
def IsCompactD2 (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop :=
  ∃ d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤),
    ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d ∧
    restrictPower k L H 24 s = pullToOpen k L 24 d

end ArithmeticThetaComponentDegreeR0184
