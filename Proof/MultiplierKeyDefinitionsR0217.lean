module

public import EvenCoverTorsorR0216
public import EvenCoverBaseChangeR0216
public import EvenCoverRightActionR0216
public import SchemeThetaEvaluationNaturalityR0213
public import EvenMarkingTorsorDefinitionsR0216

@[expose] public section

/-! The inverse-character associated line and the actual even theta evaluation.
Only data and predicates are defined here; all existence and descent are targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaPullback ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

/-- The divisor and its canonical section depend on P, not on a full marking. -/
def thetaIdeal : E.curve.IdealSheafData := P.point.val.ker
def thetaLine : E.curve.Modules := (thetaIdeal E P).invModule
def thetaMap : (𝟙_ E.curve.Modules) ⟶ thetaLine E P :=
  (thetaIdeal E P).invModuleSection
def pushforwardLine : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E P)
def generator : (𝟙_ S.Modules) ⟶ pushforwardLine E P :=
  E.p.unitToPushforwardUnit ≫ (Scheme.Modules.pushforward E.p).map (thetaMap E P)
def originGenerator : (𝟙_ S.Modules) ⟶
    (Scheme.Modules.pullback E.zero).obj (thetaLine E P) :=
  (Scheme.Modules.pullbackUnitIso E.zero).inv ≫
    (Scheme.Modules.pullback E.zero).map (thetaMap E P)
def IsRigidification (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅
    (𝟙_ S.Modules)) : Prop := originGenerator E P ≫ e.hom = 𝟙 _
def evaluation (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅
    (𝟙_ S.Modules)) : pushforwardLine E P ⟶ (𝟙_ S.Modules) :=
  (Scheme.Modules.pushforward E.p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction E.zero).unit.app (thetaLine E P) ≫
      (Scheme.Modules.pushforward E.zero).map e.hom) ≫
    (Scheme.Modules.pushforwardComp E.zero E.p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (E.law.one (𝟙 S)).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId S).hom.app _
def evaluationSection (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅
    (𝟙_ S.Modules)) : Γ(Scheme.Modules.dual (pushforwardLine E P), ⊤) :=
  (Scheme.Modules.ihomGlobalSectionsEquiv (pushforwardLine E P)
    (𝟙_ S.Modules)).symm (evaluation E P e)
def inverseSquare : S.Modules := tensorPower S (Scheme.Modules.dual (pushforwardLine E P)) 2
def evaluationSquare (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅
    (𝟙_ S.Modules)) : Γ(inverseSquare E P, ⊤) :=
  tensorPowerSection S (Scheme.Modules.dual (pushforwardLine E P)) 2 ⊤
    (evaluationSection E P e)

variable (D : Cover E)
/-- Transport along the actual equality qπ=π, with no alternative scalar map. -/
def overPull (L : S.Modules) (q : D.space ⟶ D.space)
    (h : q ≫ D.projection = D.projection)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback D.projection).obj L, ⊤) :=
  (((Scheme.Modules.pullbackComp q D.projection).app L) ≪≫
    (Scheme.Modules.pullbackCongr h).app L).hom.app ⊤
      (pullbackGlobalSection q _ m)

/-- The inverse-character frame rule of the isomorphism-to-standard torsor.
For z^4=1, z^(3e) is the inverse of z^e, also over nonreduced rings. -/
def Multiplier (z : Γ(S, ⊤)) (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤)) : Prop :=
  Scheme.Modules.IsInvertible L ∧
  IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ m ∧
  ∀ (A : EvenGroup) (q : D.space ≅ D.space) (h : Acts E D A.val q),
    overPull E D L q.hom h.1 m =
      D.projection.appTop (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent A.val).val)) • m

def PreservesFrame {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤)) (e : L ≅ K) : Prop :=
  ((Scheme.Modules.pullback D.projection).map e.hom).app ⊤ m = n

def productLine (L : S.Modules) : S.Modules := sheafTensor S (Cotangent E) L

/-- Equality of complete global sections after the actual marking cover.
The canonical cotangent comparison and the intrinsic alpha have witnesses. -/
def DescendsAlpha (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (β : Γ(productLine E L, ⊤)) : Prop :=
  (∃ c : (Scheme.Modules.pullback D.projection).obj (Cotangent E) ≅ Cotangent D.family,
    CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 c) ∧
  (∃ a : Γ(Cotangent D.family, ⊤), RealizesAlpha D.family D.marking a) ∧
  ∀ (c : (Scheme.Modules.pullback D.projection).obj (Cotangent E) ≅ Cotangent D.family),
    CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 c →
    ∀ a : Γ(Cotangent D.family, ⊤), RealizesAlpha D.family D.marking a →
    ((pullback_sheafTensor_iso D.space S D.projection (Cotangent E) L) ≪≫
      sheafTensorCongr D.space c (Iso.refl _)).hom.app ⊤
        (pullbackGlobalSection D.projection (productLine E L) β) =
      tensorSection D.space (Cotangent D.family)
        ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m

def IsKey (L : S.Modules)
    (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules))
    (β : Γ(productLine E L, ⊤)) (κ : inverseSquare E P ≅ productLine E L) : Prop :=
  κ.hom.app ⊤ (evaluationSquare E P e) = β

variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)

def PreservesThetaSection
    (q : (Scheme.Modules.pullback f).obj (thetaLine E P) ≅ thetaLine F Q) : Prop :=
  (Scheme.Modules.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (thetaMap E P) ≫ q.hom = thetaMap F Q

def pushforwardComparison (h : f ≫ E.p = F.p ≫ b)
    (q : (Scheme.Modules.pullback f).obj (thetaLine E P) ≅ thetaLine F Q) :
    (Scheme.Modules.pullback b).obj (pushforwardLine E P) ⟶ pushforwardLine F Q :=
  Scheme.Modules.baseChangeHom h (thetaLine E P) ≫
    (Scheme.Modules.pushforward F.p).map q.hom

/-- A cover map with the actual Cartesian marked family and commuting triangle. -/
structure CoverChange (C : Cover F) where
  map : C.space ⟶ D.space
  commutes : map ≫ D.projection = C.projection ≫ b
  familyMap : C.family.curve ⟶ D.family.curve
  marked : ArithmeticThetaSchemeLevelR0204.MarkedCartesian D.family C.family
    D.marking C.marking map familyMap
  triangle : familyMap ≫ D.comparison = C.comparison ≫ f

variable (C : Cover F)

def coverSquare (H : CoverChange E D F b f C) (L : S.Modules) :
    (Scheme.Modules.pullback C.projection).obj ((Scheme.Modules.pullback b).obj L) ≅
    (Scheme.Modules.pullback H.map).obj ((Scheme.Modules.pullback D.projection).obj L) :=
  (Scheme.Modules.pullbackComp C.projection b).app L ≪≫
    (Scheme.Modules.pullbackCongr H.commutes.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp H.map D.projection).app L).symm

def MultiplierCompatible (H : CoverChange E D F b f C) (L : S.Modules) (K : T.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (e : (Scheme.Modules.pullback b).obj L ≅ K) : Prop :=
  ((Scheme.Modules.pullback C.projection).map e.hom).app ⊤
    ((coverSquare E D F b f C H L).inv.app ⊤ (pullbackGlobalSection H.map _ m)) = n

/-- The tensor comparison is induced by precisely the cotangent and multiplier maps. -/
def productComparison (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (e : (Scheme.Modules.pullback b).obj L ≅ K) :
    (Scheme.Modules.pullback b).obj (productLine E L) ≅ productLine F K :=
  pullback_sheafTensor_iso T S b (Cotangent E) L ≪≫ sheafTensorCongr T c e

def AlphaNatural (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (e : (Scheme.Modules.pullback b).obj L ≅ K)
    (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤)) : Prop :=
  (productComparison E F b L K c e).hom.app ⊤
    (pullbackGlobalSection b (productLine E L) β) = γ

/-- Characterization of the inverse-square comparison on the actual evaluation
sections. Its existence, uniqueness and key-map naturality are conclusions. -/
def EvaluationSquareCompatible
    (eS : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules))
    (eT : (Scheme.Modules.pullback F.zero).obj (thetaLine F Q) ≅ (𝟙_ T.Modules))
    (j : (Scheme.Modules.pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q) : Prop :=
  j.hom.app ⊤ (pullbackGlobalSection b (inverseSquare E P) (evaluationSquare E P eS)) =
    evaluationSquare F Q eT
end ArithmeticThetaMultiplierKeyR0217
