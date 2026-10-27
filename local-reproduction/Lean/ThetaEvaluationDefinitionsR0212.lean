import RelativeAlphaCharacterR0211
import Definitions.Def_AlgebraicGeometry_ModulesIhomSectionsV2
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

/-! The actual even-characteristic divisor, its inverse ideal, pushforward,
and evaluation through the origin. No existence or invertibility is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaThetaEvaluationR0212
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
  (M : FullLevel R W G 4 (𝟙 (Base R)))

def evenPoint : Base R ⟶ Curve R W := twoLabel R W G 4 M 2

def thetaIdeal : (Curve R W).IdealSheafData := (evenPoint R W G M).ker

def thetaLine : (Curve R W).Modules := (thetaIdeal R W G M).invModule

def thetaSection : Γ(thetaLine R W G M, ⊤) :=
  (Scheme.Modules.ihomGlobalSectionsEquiv (thetaIdeal R W G M).module
    (𝟙_ (Curve R W).Modules)).symm (thetaIdeal R W G M).moduleι

def thetaMap : (𝟙_ (Curve R W).Modules) ⟶ thetaLine R W G M :=
  ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection
    (thetaLine R W G M) (thetaSection R W G M)

def pushforwardLine : (Base R).Modules :=
  (Scheme.Modules.pushforward (structureMap R W)).obj (thetaLine R W G M)

/-- The actual map on every base open: a maps to pi-sharp(a) times the canonical
section of the effective divisor P3. -/
def generator : (𝟙_ (Base R).Modules) ⟶ pushforwardLine R W G M :=
  (structureMap R W).unitToPushforwardUnit ≫
    (Scheme.Modules.pushforward (structureMap R W)).map (thetaMap R W G M)

/-- Pullback of the canonical divisor section, as a map of sheaves. -/
def originGenerator : (𝟙_ (Base R).Modules) ⟶
    (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) :=
  (Scheme.Modules.pullbackUnitIso (origin R W)).inv ≫
    (Scheme.Modules.pullback (origin R W)).map (thetaMap R W G M)

/-- A rigidification has prescribed value 1 on the canonical divisor section. -/
def IsRigidification
    (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅
      (𝟙_ (Base R).Modules)) : Prop :=
  originGenerator R W G M ≫ e.hom = 𝟙 _

/-- Genuine restriction of sections to the origin, followed by its specified
rigidification; defined by the sheaf pullback/pushforward adjunction. -/
def evaluation
    (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅
      (𝟙_ (Base R).Modules)) : pushforwardLine R W G M ⟶ (𝟙_ (Base R).Modules) :=
  (Scheme.Modules.pushforward (structureMap R W)).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (origin R W)).unit.app
      (thetaLine R W G M) ≫ (Scheme.Modules.pushforward (origin R W)).map e.hom) ≫
    (Scheme.Modules.pushforwardComp (origin R W) (structureMap R W)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr
      (WeierstrassProjModel.kwZeroSect R W).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId (Base R)).hom.app _

/-- The source's e in J inverse is the internal-Hom section of this actual
identity-evaluation morphism, not an independently selected functional. -/
def evaluationSection
    (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅
      (𝟙_ (Base R).Modules)) : Γ(Scheme.Modules.dual (pushforwardLine R W G M), ⊤) :=
  (Scheme.Modules.ihomGlobalSectionsEquiv (pushforwardLine R W G M)
    (𝟙_ (Base R).Modules)).symm (evaluation R W G M e)

section BaseChange
variable (S : Type u) [CommRing S] (V : WeierstrassCurve S) (H : Law S V)
  (N : FullLevel S V H 4 (𝟙 (Base S))) (ι : R →+* S)
  (f : Curve S V ⟶ Curve R W)

/-- Comparison of the actual divisor lines, fixing the canonical section. -/
def PreservesThetaSection
    (q : (Scheme.Modules.pullback f).obj (thetaLine R W G M) ≅ thetaLine S V H N) : Prop :=
  (Scheme.Modules.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (thetaMap R W G M) ≫ q.hom = thetaMap S V H N

/-- The canonical base-change map for J, followed by the actual theta-line
comparison. The commuting square is supplied by the actual Cartesian map. -/
def pushforwardComparison (h : f ≫ structureMap R W = structureMap S V ≫ baseMap R S ι)
    (q : (Scheme.Modules.pullback f).obj (thetaLine R W G M) ≅ thetaLine S V H N) :
    (Scheme.Modules.pullback (baseMap R S ι)).obj (pushforwardLine R W G M) ⟶
      pushforwardLine S V H N :=
  Scheme.Modules.baseChangeHom h (thetaLine R W G M) ≫
    (Scheme.Modules.pushforward (structureMap S V)).map q.hom
end BaseChange
end ArithmeticThetaThetaEvaluationR0212
