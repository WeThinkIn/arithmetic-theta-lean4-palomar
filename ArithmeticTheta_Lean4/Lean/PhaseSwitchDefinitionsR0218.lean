import EvenKeyBaseChangeR0217
import Mathlib.RingTheory.AdjoinRoot

/-! Opposite-pairing comparison data. These definitions contain no existence proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaPullback ArithmeticThetaSheafTensor

/-- Reverse the first half-point, retaining the second half-point. -/
def reversal : ArithmeticThetaFourTorsion.Mat4 := !![-1, 0; 0, 1]
def conjugate (A : ArithmeticThetaFourTorsion.Mat4) : ArithmeticThetaFourTorsion.Mat4 :=
  reversal * A * reversal

variable {S : Scheme.{u}} (E : Family S) (D C : Cover E)
/-- The actual universal-cover comparison reverses the first marked section. -/
def Switches (q : D.space ≅ C.space) : Prop :=
  q.hom ≫ C.projection = D.projection ∧
  q.hom ≫ C.marking.x.val ≫ C.comparison =
    changedX D.family D.marking reversal ≫ D.comparison ∧
  q.hom ≫ C.marking.y.val ≫ C.comparison =
    changedY D.family D.marking reversal ≫ D.comparison

/-- Pull a level frame along the specified cover switch and its actual triangle. -/
def switchPull (q : D.space ≅ C.space) (h : Switches E D C q) (K : S.Modules)
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤)) :
    Γ((Scheme.Modules.pullback D.projection).obj K, ⊤) :=
  (((Scheme.Modules.pullbackComp q.hom C.projection).app K) ≪≫
    (Scheme.Modules.pullbackCongr h.1).app K).hom.app ⊤
      (pullbackGlobalSection q.hom _ n)

def SwitchFrame (q : D.space ≅ C.space) (h : Switches E D C q)
    (L K : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤)) (v : L ≅ K) : Prop :=
  ((Scheme.Modules.pullback D.projection).map v.hom).app ⊤ m =
    switchPull E D C q h K n

/-- The finite algebra adjoining a phase, with no chosen square root in k. -/
def phasePolynomial (k : Type u) [Field k] : Polynomial k := Polynomial.X^2 + 1
abbrev PhaseAlgebra (k : Type u) [Field k] := AdjoinRoot (phasePolynomial k)
def phaseMap (k : Type u) [Field k] :
    Scheme.Spec.obj (Opposite.op (CommRingCat.of (PhaseAlgebra k))) ⟶ Base k :=
  Scheme.Spec.map (CommRingCat.ofHom (AdjoinRoot.of (phasePolynomial k))).op
def phaseSpace (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k) : Scheme.{u} :=
  pullback σ (phaseMap k)
def phaseProjection (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k) :
    phaseSpace k S σ ⟶ S := pullback.fst σ (phaseMap k)
def phaseValue (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k) :
    Γ(phaseSpace k S σ, ⊤) :=
  (pullback.snd σ (phaseMap k)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (PhaseAlgebra k))).inv
      (AdjoinRoot.root (phasePolynomial k)))
end ArithmeticThetaPhaseSwitchR0218
