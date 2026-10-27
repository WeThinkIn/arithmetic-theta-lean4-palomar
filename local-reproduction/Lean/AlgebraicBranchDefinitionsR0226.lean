import PrescribedRootsFiniteConstantExtensionR0225
import ValuedExtensionPrescribedRootsR0223
import Mathlib.RingTheory.Valuation.LocalSubring

/-! Actual algebraic extensions of a punctured formal disk. All construction
records below are outputs, not assumptions of the source-facing constructor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAlgebraicBranchesR0226
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Base Sections)
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaValuativeRootsR0223

/-- The specified power-series inclusion followed by the actual field extension. -/
def seriesMap (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E] :
    PowerSeries k →+* E :=
  (algebraMap (LaurentSeries k) E).comp (algebraMap (PowerSeries k) (LaurentSeries k))

/-- A local extension of the original disk; no residue-field identification is supplied. -/
structure ValuationExtension (k E : Type) [Field k] [Field E]
    [Algebra (LaurentSeries k) E] where
  ring : ValuationSubring E
  inclusion : PowerSeries k →+* ring
  compatible : (algebraMap ring E).comp inclusion = seriesMap k E
  isLocal : IsLocalHom inclusion

/-- A rational centre is constructed by an actual residue homomorphism, with
its exact kernel and its restriction to every original formal series. -/
structure BranchValuation (k E : Type) [Field k] [Field E]
    [Algebra (LaurentSeries k) E] extends ValuationExtension k E where
  residue : ring →+* k
  residue_comp : residue.comp inclusion = (PowerSeries.constantCoeff : PowerSeries k →+* k)
  residue_kernel : RingHom.ker residue = IsLocalRing.maximalIdeal ring

variable {k E : Type} [Field k] [Field E] [Algebra (LaurentSeries k) E]

def BranchValuation.centre (B : BranchValuation k E) :
    Base k ⟶ ValuationPoint E B.ring := Spec.map (CommRingCat.ofHom B.residue)

/-- The field-valued disk uses only the given field inclusion, before any
valuation extension or integral root coefficients have been constructed. -/
def fieldDisk {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) :
    Base E ⟶ Z := Spec.map (CommRingCat.ofHom (seriesMap k E)) ≫ f

def fieldFrame {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z)
    (J : Z.Modules) (h : Sections ((Scheme.Modules.pullback f).obj J)) :
    Sections ((Scheme.Modules.pullback (fieldDisk (E := E) f)).obj J) :=
  ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (seriesMap k E))) f).app J).hom.app ⊤
    (pullbackGlobalSection (Spec.map (CommRingCat.ofHom (seriesMap k E)))
      ((Scheme.Modules.pullback f).obj J) h)

/-- The full prescribed root equation in E, independent of an integral model. -/
def Equation {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z)
    (J : Z.Modules) (n : ℕ) (F : Sections (tensorPower Z J n))
    (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : E) : Prop :=
  pullbackPowerSection (fieldDisk (E := E) f) J n F =
    ArithmeticThetaOpenHodgeR0180.scalar E (r ^ n) •
      tensorPowerSection (Base E) ((Scheme.Modules.pullback (fieldDisk (E := E) f)).obj J)
        n ⊤ (fieldFrame (E := E) f J h)

/-- Output of the construction, retaining the original field roots, disk and
frame, and finite descent of the SAME regular root cover. -/
def Realization (k : Type) [Field k]
    (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k))
    (J : X.space.Modules) (n s : ℕ)
    (F : Fin s → Sections (tensorPower X.space J n))
    (f : ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k) ⟶ X.space)
    (h : Sections ((Scheme.Modules.pullback f).obj J))
    (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E]
    (r : Fin s → E) (K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k) : Prop :=
  ∃ B : BranchValuation (ArithmeticThetaConstantExtensionR0225.Omega k) E,
    B.centre (IsLocalRing.closedPoint (ArithmeticThetaConstantExtensionR0225.Omega k)) =
      IsLocalRing.closedPoint B.ring ∧
    ∃ T : ArithmeticThetaConstantExtensionR0225.RootRealization X J n s F E B.ring
      (extendedDisk (ArithmeticThetaConstantExtensionR0225.Omega k) E B.ring B.inclusion f)
      (extendedFrame (ArithmeticThetaConstantExtensionR0225.Omega k) E B.ring B.inclusion f J h)
      r B.centre,
      Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation
        (ArithmeticThetaConstantExtensionR0225.Omega k) X.space X.map) ∧
      Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation
        (ArithmeticThetaConstantExtensionR0225.Omega k) T.cover.space (T.cover.map ≫ X.map)) ∧
      ArithmeticThetaConstantExtensionR0225.FiniteRealization T K0

end ArithmeticThetaAlgebraicBranchesR0226
