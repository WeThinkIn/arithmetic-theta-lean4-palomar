import GlobalizationDefinitions
import GlobalRootTorsor
import EffectiveDivisorLine
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open AlgebraicGeometry CategoryTheory Opposite
universe u
noncomputable section
namespace ArithmeticThetaCoverComparison

/-- The actual functorial morphism on the established sheaf tensor powers. -/
def tensorPowerMap {X : Scheme.{u}} {H J : X.Modules} (a : H ⟶ J) :
    (n : ℕ) → ArithmeticThetaTensorPower.tensorPower X H n ⟶
      ArithmeticThetaTensorPower.tensorPower X J n
  | 0 => 𝟙 _
  | n + 1 => ArithmeticThetaPullback.sheafTensorMap X (tensorPowerMap a n) a

/-- Canonical pullback of a given tensor-power isomorphism. -/
def pullbackPowerIso {X S : Scheme.{u}} (f : S ⟶ X)
    {H W : X.Modules} {n : ℕ}
    (a : ArithmeticThetaTensorPower.tensorPower X H n ≅ W) :
    ArithmeticThetaTensorPower.tensorPower S ((Scheme.Modules.pullback f).obj H) n ≅
      (Scheme.Modules.pullback f).obj W :=
  (ArithmeticThetaPullback.pullback_tensorPower_iso S X f H n).symm ≪≫
    (Scheme.Modules.pullback f).mapIso a

/-- Equality transport on the actual pullback along a commuting triangle. -/
def overPullbackIso {S T X : Scheme.{u}} (p : T ⟶ X) (f : S ⟶ X)
    (g : {g : S ⟶ T // g ≫ p = f}) (H : X.Modules) :
    (Scheme.Modules.pullback g.val).obj ((Scheme.Modules.pullback p).obj H) ≅
      (Scheme.Modules.pullback f).obj H :=
  (Scheme.Modules.pullbackComp g.val p).app H ≪≫
    (Scheme.Modules.pullbackCongr g.property).app H

/-- Pull back an actual isomorphism and transport it over the specified triangle. -/
def pullbackIsoOver {S T X : Scheme.{u}} (p : T ⟶ X) (f : S ⟶ X)
    (H J : X.Modules) (g : {g : S ⟶ T // g ≫ p = f})
    (e : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J) :
    (Scheme.Modules.pullback f).obj H ≅ (Scheme.Modules.pullback f).obj J :=
  (overPullbackIso p f g H).symm ≪≫
    (Scheme.Modules.pullback g.val).mapIso e ≪≫ overPullbackIso p f g J

/-- Square-compatible isomorphisms between two supplied square roots of W.
This is the concrete test-object set, not an assumption of representability. -/
def SquareIsos {X S : Scheme.{u}} {H J W : X.Modules}
    (a : ArithmeticThetaTensorPower.tensorPower X H 2 ≅ W)
    (b : ArithmeticThetaTensorPower.tensorPower X J 2 ≅ W) (f : S ⟶ X) :=
  {e : (Scheme.Modules.pullback f).obj H ≅ (Scheme.Modules.pullback f).obj J //
    tensorPowerMap e.hom 2 ≫ (pullbackPowerIso f b).hom = (pullbackPowerIso f a).hom}

/-- Literal degree-n quotient of powers of the principal Cartier ideal. -/
abbrev PrincipalGradedPiece (R : Type u) [CommRing R] (t : R) (n : ℕ) :=
  (↥((Ideal.span ({t} : Set R)) ^ n)) ⧸
    (Submodule.comap ((Ideal.span ({t} : Set R)) ^ n).subtype
      ((Ideal.span ({t} : Set R)) ^ (n + 1)))

end ArithmeticThetaCoverComparison
