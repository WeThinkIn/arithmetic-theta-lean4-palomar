module

public import AdaptiveScalarExtensionImageR0240
public import ScalarExtensionDefinitionsR0240

@[expose] public section

/-! Coefficient-field classification of the same compact arithmetic sections.
Definitions only: every new Cartesian, finite-level and normalization claim is
assigned to the separate proof-worker modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaActualLevelR0208
open ArithmeticThetaMetaplecticStackR0207 ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower ArithmeticThetaPullback

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ}

/-- Classify the target provider's actual universal marked family over k,
using the structure map induced by the specified coefficient homomorphism. -/
def coefficientMap (ι : k →+* l) (P : Provider k L) (Q : Provider l L) :
    (base Q).left ⟶ (base P).left :=
  (P.universal.1.1 (base Q).left
    ((base Q).hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    (model Q (𝟙 (base Q))).family (model Q (𝟙 (base Q))).marking).choose

/-- The old family/root pulled along the actual map of test schemes. -/
def extendedObject (P : Provider k L) (Y : Over (Base k)) (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (T : Over (Base l)) (a : T.left ⟶ Y.left) : (group L T.left).Objects :=
  (pull L a).functor.obj (object P p H)

def classifiedMap (Q : Provider l L) (T : Over (Base l))
    (X : (group L T.left).Objects) : T ⟶ base Q :=
  Over.homMk (ActualFamilyFPQCDescentProof.classifier Q.universal X).val
    (ActualFamilyFPQCDescentProof.classifier Q.universal X).property

def classifiedSquare (Q : Provider l L) (T : Over (Base l))
    (X : (group L T.left).Objects) :
    SquareLine T.left ((Scheme.Modules.pullback (classifiedMap Q T X).left).obj (hodge Q)) :=
  ActualFamilyFPQCDescentProof.classifiedRoot Q.universal X

variable {n h : ℕ} {A : ArithmeticThetaLatticeSectionsR0188.Matrices n h}

abbrev Interior (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  pullback (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)
abbrev inclusion (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  pullback.fst (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)
abbrev toOldInterior (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  pullback.snd (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)
def interiorBase (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    Over (Base l) :=
  Over.mk (inclusion ι G ≫ ArithmeticThetaScalarExtensionR0240.structureMap ι G)
abbrev weightLine (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  (Scheme.Modules.pullback (inclusion ι G)).obj (ArithmeticThetaScalarExtensionR0240.line ι G)

/-- Canonical comparison between the two restrictions of the SAME compact line. -/
def lineComparison (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    weightLine ι G ≅ (Scheme.Modules.pullback (toOldInterior ι G)).obj
      (ArithmeticThetaCompactModularityR0209.openSquare G.root).line :=
  (Scheme.Modules.pullbackComp (inclusion ι G)
    (ArithmeticThetaScalarExtensionR0240.projection ι G)).app _ ≪≫
  (Scheme.Modules.pullbackCongr pullback.condition).app _ ≪≫
  ((Scheme.Modules.pullbackComp (toOldInterior ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)).app _).symm

abbrev oldProvider (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :=
  ArithmeticThetaCompactModularityR0209.provider G.root u
abbrev oldObject (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :=
  object (oldProvider G u) (ArithmeticThetaCompactModularityR0209.levelMap G.root u)
    (ArithmeticThetaCompactModularityR0209.openSquare G.root)
def pulledObject (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :
    (group (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))
      (Interior ι G)).Objects :=
  (pull _ (toOldInterior ι G)).functor.obj (oldObject G u)

def actualLineComparison (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :
    (pulledObject ι G u).root.line ≅ weightLine ι G :=
  (pull _ (toOldInterior ι G)).line (oldObject G u) ≪≫ (lineComparison ι G).symm

/-- The compact square is literally the pullback of the accepted compact square. -/
def compactSquare (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :=
  (pullback_tensorPower_iso _ _ (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.line G.root) 2).symm ≪≫
  (Scheme.Modules.pullback (ArithmeticThetaScalarExtensionR0240.projection ι G)).mapIso
    (ArithmeticThetaCompactModularityR0209.compactSquare G.root)

/-- Hodge comparison fixed by the two Cartesian triangles, old boundary
restriction, old universal-family comparison and actual cotangent pullback. -/
def hodgeComparison (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :=
  (Scheme.Modules.pullbackComp (inclusion ι G)
    (ArithmeticThetaScalarExtensionR0240.projection ι G)).app
      ((Scheme.Modules.pullback (ArithmeticThetaCompactModularityR0209.compactMap G.root)).obj G.hodge.line) ≪≫
  (Scheme.Modules.pullbackCongr pullback.condition).app _ ≪≫
  ((Scheme.Modules.pullbackComp (toOldInterior ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)).app _).symm ≪≫
  (Scheme.Modules.pullback (toOldInterior ι G)).mapIso
    ((Scheme.Modules.pullbackComp (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)
      (ArithmeticThetaCompactModularityR0209.compactMap G.root)).app G.hodge.line ≪≫
    (Scheme.Modules.pullbackCongr pullback.condition).app G.hodge.line ≪≫
    ((Scheme.Modules.pullbackComp (ArithmeticThetaCompactModularityR0209.interiorMap G.root)
      G.compact.inclusion).app G.hodge.line).symm ≪≫
    (Scheme.Modules.pullback (ArithmeticThetaCompactModularityR0209.interiorMap G.root)).mapIso G.hodge.onOpen ≪≫
    (model (oldProvider G u) (ArithmeticThetaCompactModularityR0209.levelMap G.root u)).hodge) ≪≫
  (pull _ (toOldInterior ι G)).cotangent (oldObject G u)

/-- Square map through the compact extension, with its prescribed normalization. -/
def restrictedCompactSquare (ι : k →+* l)
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root) :=
  (pullback_tensorPower_iso _ _ (inclusion ι G) (ArithmeticThetaScalarExtensionR0240.line ι G) 2).symm ≪≫
  (Scheme.Modules.pullback (inclusion ι G)).mapIso (compactSquare ι G) ≪≫ hodgeComparison ι G u

/-- Classify that same actual marked elliptic family over the new field. -/
def targetMap (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root)
    (Q : Provider l (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) :=
  classifiedMap Q (interiorBase ι G) (pulledObject ι G u)

/-- The target root has the LITERAL restriction of the compact line as carrier.
Its square map uses the actual compact Hodge comparison, not a chosen scalar. -/
def targetSquare (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (u : ArithmeticThetaCompactModularityR0209.Universal G.root)
    (Q : Provider l (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) :
    SquareLine (Interior ι G) ((Scheme.Modules.pullback (targetMap ι G u Q).left).obj (hodge Q)) where
  line := weightLine ι G
  invertible := ((G.half.invertible.pullback G.cover.map).pullback
    (ArithmeticThetaScalarExtensionR0240.projection ι G)).pullback (inclusion ι G)
  square := restrictedCompactSquare ι G u ≪≫
    (ActualFamilyFPQCDescentProof.classifiedModel Q.universal (S := interiorBase ι G) (pulledObject ι G u)).hodge.symm

/-- Full target-field moduli level, canonical tautological line and compact
restriction, retaining the marked-family arrow and its exact line comparison. -/
def ExtendedLevel (ι : k →+* l) (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) : Prop :=
  IsOpenImmersion (inclusion ι G) ∧ DenseRange (inclusion ι G).base ∧
  ∃ (u : ArithmeticThetaCompactModularityR0209.Universal G.root)
    (Q : Provider l (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)))
    (C : Coherence (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) (Base l)),
    Nonempty (ForgetData _ (Base l) C) ∧
    Pseudofunctor.IsStack C.functor (ArithmeticThetaRootStackR0198.rootTopology (Base l)) ∧
    (∃ e : Arrow (object Q (targetMap ι G u Q) (targetSquare ι G u Q)) (pulledObject ι G u),
      e.line.hom = (actualLineComparison ι G u).inv) ∧
    Nonempty (PullbackComparison (canonicalMap C (interiorBase ι G)
      (object Q (targetMap ι G u Q) (targetSquare ι G u Q)))) ∧
    FiniteEtaleLevel Q (targetMap ι G u Q) (targetSquare ι G u Q)
      (canonicalMap C (interiorBase ι G) (object Q (targetMap ι G u Q) (targetSquare ι G u Q))) ∧
    (∀ z : (base Q).left, (targetMap ι G u Q).left.finrank z ≤
      2 ^ (ArithmeticThetaSharpKernelR0195.normCount A - 1))

end ArithmeticThetaExtendedMetaplecticR0241
