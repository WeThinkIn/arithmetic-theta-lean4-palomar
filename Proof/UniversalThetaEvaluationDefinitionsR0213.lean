module

public import ThetaEvaluationBaseChangeR0212
public import SchemeFullLevelUniversalR0204

@[expose] public section

/-! The even theta line and its actual identity evaluation for scheme families.
All constructions retain the original section, ideal and structural maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaUniversalEvaluationR0213
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

variable {S : Scheme.{u}} (E : Family S)
  (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4)

def evenPoint : S ⟶ E.curve :=
  (E.law.mul (𝟙 S)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.x)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.y)).val

def thetaIdeal : E.curve.IdealSheafData := (evenPoint E M).ker
def thetaLine : E.curve.Modules := (thetaIdeal E M).invModule
def thetaSection : Γ(thetaLine E M, ⊤) :=
  (Scheme.Modules.ihomGlobalSectionsEquiv (thetaIdeal E M).module
    (𝟙_ E.curve.Modules)).symm (thetaIdeal E M).moduleι
def thetaMap : (𝟙_ E.curve.Modules) ⟶ thetaLine E M :=
  ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection
    (thetaLine E M) (thetaSection E M)
def pushforwardLine : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E M)
def generator : (𝟙_ S.Modules) ⟶ pushforwardLine E M :=
  E.p.unitToPushforwardUnit ≫ (Scheme.Modules.pushforward E.p).map (thetaMap E M)
def originGenerator : (𝟙_ S.Modules) ⟶
    (Scheme.Modules.pullback E.zero).obj (thetaLine E M) :=
  (Scheme.Modules.pullbackUnitIso E.zero).inv ≫
    (Scheme.Modules.pullback E.zero).map (thetaMap E M)
def IsRigidification (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E M) ≅
    (𝟙_ S.Modules)) : Prop := originGenerator E M ≫ e.hom = 𝟙 _
def evaluation (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E M) ≅
    (𝟙_ S.Modules)) : pushforwardLine E M ⟶ (𝟙_ S.Modules) :=
  (Scheme.Modules.pushforward E.p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction E.zero).unit.app (thetaLine E M) ≫
      (Scheme.Modules.pushforward E.zero).map e.hom) ≫
    (Scheme.Modules.pushforwardComp E.zero E.p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (E.law.one (𝟙 S)).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId S).hom.app _
def evaluationSection (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E M) ≅
    (𝟙_ S.Modules)) : Γ(Scheme.Modules.dual (pushforwardLine E M), ⊤) :=
  (Scheme.Modules.ihomGlobalSectionsEquiv (pushforwardLine E M)
    (𝟙_ S.Modules)).symm (evaluation E M e)

variable {T : Scheme.{u}} (F : Family T)
  (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : T ⟶ S)
  (f : F.curve ⟶ E.curve)
def PreservesThetaSection
    (q : (Scheme.Modules.pullback f).obj (thetaLine E M) ≅ thetaLine F N) : Prop :=
  (Scheme.Modules.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (thetaMap E M) ≫ q.hom = thetaMap F N
def pushforwardComparison (h : f ≫ E.p = F.p ≫ b)
    (q : (Scheme.Modules.pullback f).obj (thetaLine E M) ≅ thetaLine F N) :
    (Scheme.Modules.pullback b).obj (pushforwardLine E M) ⟶ pushforwardLine F N :=
  Scheme.Modules.baseChangeHom h (thetaLine E M) ≫
    (Scheme.Modules.pushforward F.p).map q.hom
end ArithmeticThetaUniversalEvaluationR0213
