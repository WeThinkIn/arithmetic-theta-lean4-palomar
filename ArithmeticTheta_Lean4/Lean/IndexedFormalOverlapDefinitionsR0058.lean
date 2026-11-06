import TateNodeTorusCharts
import GeometricTorsionChartSectionsR0053

/-! Indexed adjacent opens of the Tate chain. These are ordinary objects and
predicates, not a proper polygon or an asserted gluing theorem. The indices
label copies of the same affine node; their multiplicative coordinates differ.
The source of an adjacent ring map is the y-open of j, its target the x-open
of j+1 (or 0 at the last period boundary). -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaIndexedOverlapsR0058
variable (k : Type u) [Field k] [CharZero k]

abbrev Base := PowerSeries k
abbrev Node (_j : ℕ) := ArithmeticThetaNodeCharts.Node k
abbrev Chart (_j : ℕ) := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
def next (r j : ℕ) : ℕ := (j + 1) % r
def nodeCoord (side : Bool) : Node k 0 :=
  if side then ArithmeticThetaNodeCharts.x k else ArithmeticThetaNodeCharts.y k
abbrev Open (_j : ℕ) (side : Bool) := Localization.Away (nodeCoord k side)

/-- The already defined thickness-one node, identified with the unscaled node. -/
def nodeEquiv : ArithmeticThetaAnnularTorsionPrereqR0053.Node k ≃+* Node k 0 :=
  (Ideal.quotientEquivAlgOfEq (Base k) (show
    ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter])).toRingEquiv

def openMap (j : ℕ) (side : Bool) :
    ArithmeticThetaAnnularTorsionPrereqR0053.Node k →+* Open k j side :=
  (algebraMap (Node k j) (Open k j side)).comp (nodeEquiv k).toRingHom
def openBase (j : ℕ) (side : Bool) : Base k →+* Open k j side :=
  (openMap k j side).comp (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k)
def ox (j : ℕ) (side : Bool) : Open k j side :=
  algebraMap (Node k j) _ (ArithmeticThetaNodeCharts.x k)
def oy (j : ℕ) (side : Bool) : Open k j side :=
  algebraMap (Node k j) _ (ArithmeticThetaNodeCharts.y k)
def ot (j : ℕ) (side : Bool) : Open k j side := openBase k j side PowerSeries.X
def oz (j : ℕ) (side : Bool) : Open k j side := ot k j side ^ j * ox k j side
def xUnit (j : ℕ) : (Open k j true)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (nodeCoord k true)
    (S := Open k j true)).unit
def torusEquiv (j : ℕ) (side : Bool) :
    Open k j side ≃+* ArithmeticThetaNodeCharts.Torus k := by
  cases side with
  | false => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).2
  | true => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
def adjacent (r j : ℕ) : Open k j false ≃+* Open k (next r j) true :=
  ((torusEquiv k j false).trans LaurentPolynomial.invert.toRingEquiv).trans
    (torusEquiv k (next r j) true).symm
def openIdeal (j : ℕ) (side : Bool) : Ideal (Open k j side) := Ideal.span {ot k j side}
abbrev OpenHat (j : ℕ) (side : Bool) := AdicCompletion (openIdeal k j side) (Open k j side)
def completeOpen (j : ℕ) (side : Bool) : Open k j side →+* OpenHat k j side := algebraMap _ _
def hatPower (j : ℕ) (side : Bool) (n : ℕ) : Ideal (OpenHat k j side) :=
  (Ideal.span {completeOpen k j side (ot k j side)}) ^ n
def basePower (n : ℕ) : Ideal (Base k) := (Ideal.span {PowerSeries.X}) ^ n

/-- A restriction from the actual completed node to its completed coordinate open. -/
def IsRestriction (j : ℕ) (side : Bool) (R : Chart k j →+* OpenHat k j side) : Prop :=
  R.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
    (completeOpen k j side).comp (openMap k j side) ∧
  ∀ n f, f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n →
    R f ∈ hatPower k j side n

/-- A continuous extension of the specified adjacent map, in both directions. -/
def IsCompletedAdjacent (r j : ℕ)
    (E : OpenHat k j false ≃+* OpenHat k (next r j) true) : Prop :=
  E.toRingHom.comp (completeOpen k j false) =
    (completeOpen k (next r j) true).comp (adjacent k r j).toRingHom ∧
  (∀ n f, f ∈ hatPower k j false n → E f ∈ hatPower k (next r j) true n) ∧
  (∀ n f, f ∈ hatPower k (next r j) true n → E.symm f ∈ hatPower k j false n)

def IsContinuousSection (j : ℕ) (side : Bool) (s : OpenHat k j side →+* Base k) : Prop :=
  ∀ n f, f ∈ hatPower k j side n → s f ∈ basePower k n

def selectedSection (side : Bool) (α : k) (hα : α ≠ 0) : Chart k 0 →+* Base k :=
  Classical.choose (ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels
    k side α hα).1

/-- Actual completed section compatibility, including its providers. This
predicate is only used in existential conclusions of the proposed contract. -/
def CompatibleSections (r j : ℕ) (α : k) (hα : α ≠ 0)
    (RX : Chart k (next r j) →+* OpenHat k (next r j) true)
    (RY : Chart k j →+* OpenHat k j false)
    (E : OpenHat k j false ≃+* OpenHat k (next r j) true)
    (sX : OpenHat k (next r j) true →+* Base k)
    (sY : OpenHat k j false →+* Base k) : Prop :=
  IsRestriction k (next r j) true RX ∧ IsRestriction k j false RY ∧
  IsCompletedAdjacent k r j E ∧
  IsContinuousSection k (next r j) true sX ∧ IsContinuousSection k j false sY ∧
  sX.comp RX = selectedSection k true α hα ∧
  sY.comp RY = selectedSection k false α⁻¹ (inv_ne_zero hα) ∧
  sY = sX.comp E.toRingHom

def horizontal (j : ℕ) (side : Bool) (c : ℕ) : Open k j side :=
  1 - (if side then ox k j side else oy k j side) ^ c
def linearEquation (j : ℕ) (side : Bool) (α : k) : Open k j side :=
  (if side then ox k j side else oy k j side) - openBase k j side (PowerSeries.C α)

def openSpec (j : ℕ) (side : Bool) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (Open k j side))
def adjacentSpec (r j : ℕ) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (adjacent k r j).toRingHom)
def structureMap (j : ℕ) (side : Bool) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (openBase k j side))

end ArithmeticThetaIndexedOverlapsR0058
