import SchemeAlphaCharacterR0215
import SchemePhaseNaturalityR0215
import SchemeAlphaNaturalityR0215
import SchemeFullLevelUniversalR0204
import FullLevelCoverGeometryR0175

/-! Actual four-marking covers before associated-line descent.
No representing cover, phase lift, geometric property or torsor is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215

variable {S : Scheme.{u}} (E : Family S)

/-- The fixed nonidentity two-torsion section defining the even characteristic. -/
structure EvenPoint where
  point : SchemeHomOver (𝟙 S) E.p
  killed : multiple E (𝟙 S) 2 point = E.law.one (𝟙 S)
  avoids : Disjoint (Set.range point.val) (Set.range E.zero)

/-- An actual pointed Cartesian group-family map. -/
def Cartesian {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) : Prop :=
  IsPullback f F.p E.p b ∧ F.zero ≫ f = b ≫ E.zero ∧ Multiplicative E F b f

/-- Data for a proposed universal marking; existence and representation are targets. -/
structure Cover where
  space : Scheme.{u}
  projection : space ⟶ S
  family : Family space
  comparison : family.curve ⟶ E.curve
  cartesian : Cartesian E family projection comparison
  marking : FullLevel family 4

/-- The universal property tests all schemes and actual family maps. -/
def Represents (D : Cover E) : Prop :=
  ∀ (T : Scheme.{u}) (F : Family T) (N : FullLevel F 4)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve), Cartesian E F b f →
    ∃! q : {q : T ⟶ D.space // q ≫ D.projection = b},
      ∃ h : F.curve ⟶ D.family.curve,
        MarkedCartesian D.family F D.marking N q.val h ∧ h ≫ D.comparison = f

/-- Prescribed actual characteristic and exact global Miller phase. -/
def Matches (P : EvenPoint E) (z : Γ(S, ⊤)) {T : Scheme.{u}}
    (F : Family T) (N : FullLevel F 4) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) : Prop :=
  ArithmeticThetaUniversalEvaluationR0213.evenPoint F N ≫ f = b ≫ P.point.val ∧
  MillerPhase F N (b.appTop z)

/-- Representation of precisely the fixed-characteristic, fixed-pairing markings. -/
def RepresentsEven (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E) : Prop :=
  Matches E P z D.family D.marking D.projection D.comparison ∧
  ∀ (T : Scheme.{u}) (F : Family T) (N : FullLevel F 4)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve), Cartesian E F b f →
    Matches E P z F N b f →
    ∃! q : {q : T ⟶ D.space // q ≫ D.projection = b},
      ∃ h : F.curve ⟶ D.family.curve,
        MarkedCartesian D.family F D.marking N q.val h ∧ h ≫ D.comparison = f

/-- Exact geometric degree on every point, using the actual projection. -/
def Geometry (D : Cover E) (n : ℕ) : Prop :=
  IsFinite D.projection ∧ Etale D.projection ∧ Surjective D.projection ∧
    ∀ s : S, D.projection.finrank s = n

abbrev EvenGroup := {A : ArithmeticThetaFourTorsion.Mat4 //
  ArithmeticThetaFourTorsion.PreservesEven A}

def changedX (M : FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4) : S ⟶ E.curve :=
  (E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 0).val M.x)
    (multiple E (𝟙 S) (A 1 0).val M.y)).val

def changedY (M : FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4) : S ⟶ E.curve :=
  (E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 1).val M.x)
    (multiple E (𝟙 S) (A 1 1).val M.y)).val

/-- A locally constant change of marking, with equalities of actual local maps. -/
def LocalChange (M N : FullLevel E 4) (g : LocallyConstant S EvenGroup) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    (∀ t : S, t ∈ U → g t = g s) ∧
    U.ι ≫ N.x.val = U.ι ≫ changedX E M (g s).val ∧
    U.ι ≫ N.y.val = U.ι ≫ changedY E M (g s).val

/-- The right marking action on the actual representing cover. -/
def Acts (D : Cover E) (A : ArithmeticThetaFourTorsion.Mat4)
    (q : D.space ≅ D.space) : Prop :=
  q.hom ≫ D.projection = D.projection ∧
  q.hom ≫ D.marking.x.val ≫ D.comparison =
    changedX D.family D.marking A ≫ D.comparison ∧
  q.hom ≫ D.marking.y.val ≫ D.comparison =
    changedY D.family D.marking A ≫ D.comparison

/-- Full scheme-valued simple transitivity; matrices can vary on clopen components. -/
def LocallyRelated (D : Cover E) {T : Scheme.{u}} (a b : T ⟶ D.space)
    (g : LocallyConstant T EvenGroup) : Prop :=
  ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
    (∀ v : T, v ∈ U → g v = g t) ∧
    U.ι ≫ b ≫ D.marking.x.val ≫ D.comparison =
      U.ι ≫ a ≫ changedX D.family D.marking (g t).val ≫ D.comparison ∧
    U.ι ≫ b ≫ D.marking.y.val ≫ D.comparison =
      U.ι ≫ a ≫ changedY D.family D.marking (g t).val ≫ D.comparison

/-- A marking-preserving map between two covers of the same family. -/
def CoverMap (D C : Cover E) (q : D.space ⟶ C.space)
    (h : D.family.curve ⟶ C.family.curve) : Prop :=
  q ≫ C.projection = D.projection ∧
  MarkedCartesian C.family D.family C.marking D.marking q h ∧
  h ≫ C.comparison = D.comparison

end ArithmeticThetaEvenMarkingTorsorR0216
