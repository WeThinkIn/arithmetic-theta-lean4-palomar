module

public import ArbitraryAlphaCharacterR0214
public import ArbitraryPhaseBaseChangeR0214
public import SchemeThetaEvaluationNaturalityR0213
public import CartesianIdentityIdealR0205
public import SchemeCotangentCoherenceR0205
public import AffineConormalHodgeNaturalityR0205

@[expose] public section

/-! Scheme-valued four-character data. Affine tests retain the actual curve,
marked points, Cartesian map, identity ideal, and its canonical derivative.
No phase, alpha, or descent theorem is assumed in these definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Every actual affine Weierstrass test, not merely geometric field points.
The base map is arbitrary, including nonflat maps and the empty test. -/
structure AffineTest {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4) where
  ring : Type u
  [commRing : CommRing ring]
  [rational : Algebra ℚ ring]
  equation : WeierstrassCurve ring
  elliptic : equation.IsElliptic
  law : ArithmeticThetaRelativeKatoR0169.Law ring equation
  originLaw : ArithmeticThetaRelativeKatoR0169.IsOriginLaw ring equation law
  base : Base ring ⟶ S
  comparison : ArithmeticThetaRelativeKatoR0169.Curve ring equation ⟶ E.curve
  cartesian : IsPullback comparison
    (ArithmeticThetaRelativeKatoR0169.structureMap ring equation) E.p base
  zero_eq : ArithmeticThetaRelativeKatoR0169.origin ring equation ≫ comparison = base ≫ E.zero
  mul_eq : ∀ (T : Scheme.{u}) (t : T ⟶ Base ring)
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap ring equation))
    (x' y' : SchemeHomOver (t ≫ base) E.p),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (E.law.mul _ x' y').val = (law.mul t x y).val ≫ comparison
  level : ArithmeticThetaFullLevelCoverR0175.FullLevel ring equation law 4 (𝟙 (Base ring))
  x_eq : level.x.val ≫ comparison = base ≫ M.x.val
  y_eq : level.y.val ≫ comparison = base ≫ M.y.val

attribute [instance] AffineTest.commRing AffineTest.rational

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- The source right action: columns prescribe the two new actual sections. -/
def Changes (N : FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4) : Prop :=
  N.x = E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 0).val M.x)
    (multiple E (𝟙 S) (A 1 0).val M.y) ∧
  N.y = E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 1).val M.x)
    (multiple E (𝟙 S) (A 1 1).val M.y)

/-- Pull the actual global regular function into the original affine test ring. -/
def affineScalar (P : AffineTest E M) (z : Γ(S, ⊤)) : P.ring :=
  (Scheme.ΓSpecIso (CommRingCat.of P.ring)).hom (P.base.appTop z)

/-- Exact Miller normalization in every test ring, including nilpotents. -/
def MillerPhase (z : Γ(S, ⊤)) : Prop :=
  ∀ P : AffineTest E M,
    ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase
      P.ring P.equation P.law P.level (affineScalar E M P z)

/-- Inclusion compatibility fixes the ideal comparison, not just its carrier. -/
def AffineIdealCompatible (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj E.zero.ker.module ≅
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module) : Prop :=
  i.hom ≫ (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.moduleι =
    (Scheme.Modules.pullback P.comparison).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ P.comparison).hom

/-- The actual cotangent-to-affine-Hodge map: pointed square, ideal comparison,
then the derivative of the identity ideal. No chosen Hodge frame is inserted. -/
def affineHodgeMap (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj E.zero.ker.module ≅
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module) :
    (Scheme.Modules.pullback P.base).obj (Cotangent E) ⟶
      ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation :=
  (squarePullbackIso P.base E.zero
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation) P.comparison
    P.zero_eq.symm E.zero.ker.module).hom ≫
  (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)).map i.hom ≫
  ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap
    (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation)
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)

def affineAlpha (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj E.zero.ker.module ≅
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module)
    (a : Γ(Cotangent E, ⊤)) :
      Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation, ⊤) :=
  (affineHodgeMap E M P i).app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection P.base (Cotangent E) a)

/-- A scheme section realizes precisely the signed alpha on every affine test.
Existence of compatible ideal comparisons is part of the conclusion, not a premise. -/
def RealizesAlpha (a : Γ(Cotangent E, ⊤)) : Prop :=
  ∀ P : AffineTest E M,
    (∃ i, AffineIdealCompatible E M P i) ∧
    ∀ i, AffineIdealCompatible E M P i →
      ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha
        P.ring P.equation P.law 4 P.level (affineAlpha E M P i a)

/-- Pullback along a canonical, inclusion-normalized cotangent comparison. -/
def pullAlpha {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (a : Γ(Cotangent E, ⊤)) : Γ(Cotangent F, ⊤) :=
  e.hom.app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection b (Cotangent E) a)

end ArithmeticThetaSchemeFourCharacterR0215
