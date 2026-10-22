module

public import KeyPhaseSwitchR0218
public import PhaseCoverR0218
public import PhaseSwitchDefinitionsR0218
public import MultiplierKeyDefinitionsR0217

@[expose] public section

/-! Frames on every actual full marking, without a chosen global Miller phase.
Existence, descent, uniqueness and naturality are not assumed by these definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaPullback ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

/-- The source even characteristic is fixed, but no phase is prescribed. -/
structure MarkedTest where
  base : Scheme.{u}
  family : Family base
  marking : FullLevel family 4
  map : base ⟶ S
  comparison : family.curve ⟶ E.curve
  cartesian : Cartesian E family map comparison
  characteristic : ArithmeticThetaUniversalEvaluationR0213.evenPoint family marking ≫
    comparison = map ≫ P.point.val

/-- The exact all-scheme universal property of the phase-free marking cover. -/
def RepresentsUnphased (D : Cover E) : Prop :=
  ArithmeticThetaUniversalEvaluationR0213.evenPoint D.family D.marking ≫ D.comparison =
    D.projection ≫ P.point.val ∧
  ∀ A : MarkedTest E P,
    ∃! q : {q : A.base ⟶ D.space // q ≫ D.projection = A.map},
      ∃ h : A.family.curve ⟶ D.family.curve,
        MarkedCartesian D.family A.family D.marking A.marking q.val h ∧
          h ≫ D.comparison = A.comparison

/-- Only the marking changes; all underlying maps and the family are retained. -/
def remark (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) : MarkedTest E P :=
  { A with marking := N, characteristic := hN }

abbrev Frames (L : S.Modules) :=
  (A : MarkedTest E P) → Γ((Scheme.Modules.pullback A.map).obj L, ⊤)

/-- An actual marked Cartesian map between two tests of the same family. -/
structure TestMap (A B : MarkedTest E P) where
  map : A.base ⟶ B.base
  commutes : map ≫ B.map = A.map
  familyMap : A.family.curve ⟶ B.family.curve
  marked : MarkedCartesian B.family A.family B.marking A.marking map familyMap
  triangle : familyMap ≫ B.comparison = A.comparison

def testPull (L : S.Modules) {A B : MarkedTest E P} (H : TestMap E P A B)
    (m : Γ((Scheme.Modules.pullback B.map).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback A.map).obj L, ⊤) :=
  (((Scheme.Modules.pullbackComp H.map B.map).app L) ≪≫
    (Scheme.Modules.pullbackCongr H.commutes).app L).hom.app ⊤
      (pullbackGlobalSection H.map _ m)

/-- A natural system of inverse-character frames, with the necessary reversal law.
The phase in the character is the actual Miller phase of that test marking. -/
def IsMultiplier (L : S.Modules) (m : Frames E P L) : Prop :=
  Scheme.Modules.IsInvertible L ∧
  (∀ A : MarkedTest E P, IsFrame ((Scheme.Modules.pullback A.map).obj L) ⊤ (m A)) ∧
  (∀ (A B : MarkedTest E P) (H : TestMap E P A B), testPull E P L H (m B) = m A) ∧
  (∀ (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)), MillerPhase A.family A.marking z →
    ∀ g : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven g →
    Changes A.family A.marking N g →
    m (remark E P A N hN) = z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) • m A) ∧
  (∀ (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val),
    Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal →
    m (remark E P A N hN) = m A)

def PreservesFrames {L K : S.Modules} (m : Frames E P L) (n : Frames E P K)
    (v : L ≅ K) : Prop :=
  ∀ A : MarkedTest E P, ((Scheme.Modules.pullback A.map).map v.hom).app ⊤ (m A) = n A

/-- The fourth tensor power is trivialized in the actual level frames. -/
def FourthNormalized (L : S.Modules) (m : Frames E P L)
    (t : tensorPower S L 4 ≅ SheafOfModules.unit S.ringCatSheaf) : Prop :=
  ∀ A : MarkedTest E P,
    (Scheme.Modules.pullbackUnitIso A.map).hom.app ⊤
      (((Scheme.Modules.pullback A.map).map t.hom).app ⊤
        ((pullback_tensorPower_iso A.base S A.map L 4).inv.app ⊤
          (tensorPowerSection A.base ((Scheme.Modules.pullback A.map).obj L) 4 ⊤ (m A)))) = (1 : Γ(A.base, ⊤))

/-- Complete alpha tensor equality on every marking test in the specified frames. -/
def Descends (L : S.Modules) (m : Frames E P L)
    (β : Γ(productLine E L, ⊤)) : Prop :=
  ∀ A : MarkedTest E P,
    (∃ c : (Scheme.Modules.pullback A.map).obj (Cotangent E) ≅ Cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c) ∧
    (∃ a : Γ(Cotangent A.family, ⊤), RealizesAlpha A.family A.marking a) ∧
    ∀ c : (Scheme.Modules.pullback A.map).obj (Cotangent E) ≅ Cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c →
      ∀ a : Γ(Cotangent A.family, ⊤), RealizesAlpha A.family A.marking a →
      ((pullback_sheafTensor_iso A.base S A.map (Cotangent E) L) ≪≫
        sheafTensorCongr A.base c (Iso.refl _)).hom.app ⊤
          (pullbackGlobalSection A.map (productLine E L) β) =
        tensorSection A.base (Cotangent A.family)
          ((Scheme.Modules.pullback A.map).obj L) ⊤ a (m A)

variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)

/-- A comparison of arbitrary marked tests across the specified family map. -/
structure RelativeTestMap (A : MarkedTest E P) (B : MarkedTest F Q) where
  map : B.base ⟶ A.base
  commutes : map ≫ A.map = B.map ≫ b
  familyMap : B.family.curve ⟶ A.family.curve
  marked : MarkedCartesian A.family B.family A.marking B.marking map familyMap
  triangle : familyMap ≫ A.comparison = B.comparison ≫ f

def testSquare {A : MarkedTest E P} {B : MarkedTest F Q}
    (H : RelativeTestMap E P F Q b f A B) (L : S.Modules) :
    (Scheme.Modules.pullback B.map).obj ((Scheme.Modules.pullback b).obj L) ≅
    (Scheme.Modules.pullback H.map).obj ((Scheme.Modules.pullback A.map).obj L) :=
  (Scheme.Modules.pullbackComp B.map b).app L ≪≫
    (Scheme.Modules.pullbackCongr H.commutes.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp H.map A.map).app L).symm

def Compatible (L : S.Modules) (K : T.Modules) (m : Frames E P L) (n : Frames F Q K)
    (v : (Scheme.Modules.pullback b).obj L ≅ K) : Prop :=
  ∀ (A : MarkedTest E P) (B : MarkedTest F Q)
    (H : RelativeTestMap E P F Q b f A B),
    ((Scheme.Modules.pullback B.map).map v.hom).app ⊤
      ((testSquare E P F Q b f H L).inv.app ⊤
        (pullbackGlobalSection H.map _ (m A))) = n B

end ArithmeticThetaPhaseFreeKeyR0219
