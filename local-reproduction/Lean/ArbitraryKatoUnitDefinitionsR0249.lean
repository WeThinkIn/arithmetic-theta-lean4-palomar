import NormalDiscriminantModelR0243
import NormalDiscriminantIndependenceR0243
import RelativeKatoCartierRatioR0170
import PointedCartesianGroupLawR0204

/-! Actual Kato units on the complement of the actual multiplication torsion
ideal. Normal models and their normalized rational functions are accepted
providers; existence and independence on an arbitrary target are new targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryKatoUnitR0249
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryDiscriminantR0243

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

def identityIdeal : (Curve R W).IdealSheafData := (origin R W).ker
def torsionIdeal (c : ℕ) : (Curve R W).IdealSheafData :=
  (identityIdeal R W).comap (G.schemeNsmul c)
def complement (c : ℕ) : (Curve R W).Opens :=
  (torsionIdeal R W G c).support.compl
abbrev UnitSection (c : ℕ) :=
  ((Curve R W).presheaf.obj (Opposite.op (complement R W G c)))ˣ

def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : X.presheaf.obj (Opposite.op U)) : X.presheaf.obj (Opposite.op V) :=
  X.presheaf.map (homOfLE h).op a

variable [Algebra ℚ R]

/-- The value is pulled through M's specific pointed Cartesian map. Existence
of a normalized source representative and of the inclusion is required in the
conclusion, not postulated as target geometric data. -/
def FromModel (M : NormalModel R W) (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∃ hU : Nonempty (complement M.ring M.equation M.law c),
  ∃ g : (Curve M.ring M.equation).functionField,
    Normalized M.ring M.equation M.law c g ∧
    ∃ a : (Curve M.ring M.equation).presheaf.obj
        (Opposite.op (complement M.ring M.equation M.law c)),
      IsUnit a ∧
      @Scheme.germToFunctionField (Curve M.ring M.equation) _
        (complement M.ring M.equation M.law c) hU a = g ∧
      ∃ e : complement R W G c ≤
          M.comparison.map ⁻¹ᵁ complement M.ring M.equation M.law c,
        (v : _) = M.comparison.map.appLE _ _ e a

/-- Normal-source normalization is tested against every actual model. The
accepted normal_discriminant_model supplies models for every elliptic target. -/
def IsKatoUnit (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∀ M : NormalModel R W, FromModel R W G M c v

/-- Actual local Cartier equation; both ideals must also be effective Cartier.
Restrictions are to the intersection with the complement, including empty
opens. This statement does not use a function field on a nonintegral base. -/
def HasCartierDivisor (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (identityIdeal R W) ∧
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (torsionIdeal R W G c) ∧
  ∀ (U : (Curve R W).affineOpens)
    (a b : (Curve R W).presheaf.obj (Opposite.op U.1)),
    IsRegular a → IsRegular b →
    (identityIdeal R W).ideal U = Ideal.span ({a} : Set _) →
    (torsionIdeal R W G c).ideal U = Ideal.span ({b} : Set _) →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      restrict (complement R W G c) (U.1 ⊓ complement R W G c) inf_le_right (v : _) *
        restrict U.1 (U.1 ⊓ complement R W G c) inf_le_left b =
      restrict U.1 (U.1 ⊓ complement R W G c) inf_le_left
        ((ε : _) * a ^ (c ^ 2))

end ArithmeticThetaArbitraryKatoUnitR0249
