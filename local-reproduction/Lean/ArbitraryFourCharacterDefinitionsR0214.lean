import RelativeAlphaCharacterR0211
import RelativePhaseBaseChangeR0211
import ArbitraryAffineClassificationR0202

/-! Actual arbitrary-base Miller normalization and canonical Hodge pullback.
These definitions assert no new existence or character theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeFourCharacterR0211

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) (G : Law R W)
  (M : FullLevel R W G 4 (𝟙 (Base R)))

/-- The regular normalized Miller ratio on the original ring. Both the
coordinate existence and unit denominator are explicit. Unlike field-fiber
agreement alone, this equation retains information in nilpotent directions. -/
def MillerPhase (z : R) : Prop :=
  (∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y) ∧
  ∀ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y →
    let Y := fun i => completedY R W (x i) (y i)
    IsUnit (RelativeGeometricPhase.denominator e x Y) ∧
      RelativeGeometricPhase.denominator e x Y * z =
        RelativeGeometricPhase.numerator e x Y

section BaseChange
variable (S : Type u) [CommRing S] (V : WeierstrassCurve S)
  (H : Law S V) (ι : R →+* S) (f : Curve S V ⟶ Curve R W)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι f)

/-- The actual differential map, pulled back along the identity square.
No normality assumption is needed to define this map, and no arbitrary
line isomorphism is chosen. Its invertibility is a planned conclusion. -/
def hodgeMap : (Scheme.Modules.pullback (baseMap R S ι)).obj (Hodge R W) ⟶ Hodge S V :=
  letI : Algebra R S := ι.toAlgebra
  (squarePullbackIso (baseMap R S ι) (origin R W) (origin S V) f
    hb.2.1.symm (structureMap R W).kaehler).hom ≫
      (Scheme.Modules.pullback (origin S V)).map
        (differentialMap (structureMap R W) (structureMap S V) f hb.1.w)

def pullAlpha (a : Γ(Hodge R W, ⊤)) : Γ(Hodge S V, ⊤) :=
  (hodgeMap R W G S V H ι f hb).app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (baseMap R S ι) (Hodge R W) a)
end BaseChange
end ArithmeticThetaArbitraryFourCharacterR0214
