module

public import SchemeKatoFullTateExpansionR0252
public import SchemeDiscriminantNaturalityR0244

@[expose] public section

/-! Local initial coefficients of the same canonical unit, in actual identity
ideals and their conormal tensor powers. These are predicates, not providers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKatoInitialR0253
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaTensorPower

/-- An actual identity chart, without a function field or a domain assumption. -/
def AffineIdentityChart (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (c : ℕ) (U : (Curve R W).affineOpens)
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)) : Prop :=
  IsRegular a ∧
  (ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal R W).ideal U =
    Ideal.span ({a} : Set _) ∧
  (ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal R W G c).ideal U =
    (ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal R W).ideal U

/-- Five times the actual unit has coefficient epsilon at order 24; that
coefficient gives d through the actual origin and relative differential. -/
def AffineInitial (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W)
    (v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection R W G 5)
    (d : ArithmeticThetaArbitraryDiscriminantR0243.Sections (HodgePower R W 24)) : Prop :=
  ∀ (U : (Curve R W).affineOpens)
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)),
    AffineIdentityChart R W G 5 U a →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      5 * ArithmeticThetaArbitraryKatoUnitR0249.restrict
          (ArithmeticThetaArbitraryKatoUnitR0249.complement R W G 5)
          (U.1 ⊓ ArithmeticThetaArbitraryKatoUnitR0249.complement R W G 5)
          inf_le_right (v : _) =
        ArithmeticThetaArbitraryKatoUnitR0249.restrict U.1
          (U.1 ⊓ ArithmeticThetaArbitraryKatoUnitR0249.complement R W G 5)
          inf_le_left ((ε : _) * a^24) ∧
      res (HodgePower R W 24) le_top d =
        (origin R W).app U.1 (ε : _) • localPower R W 24 U.1 a

/-- Inclusion into the structure sheaf retains the actual ideal section. -/
def equation {S : Scheme.{u}} (E : Family S) (U : E.curve.Opens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U)) :
    E.curve.presheaf.obj (Opposite.op U) :=
  E.zero.ker.moduleι.app U x

def IdentityChart {S : Scheme.{u}} (E : Family S) (c : ℕ)
    (U : E.curve.affineOpens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U.1)) : Prop :=
  IsRegular (equation E U.1 x) ∧
  (ArithmeticThetaSchemeKatoUnitR0250.identityIdeal E).ideal U =
    Ideal.span ({equation E U.1 x} : Set _) ∧
  (ArithmeticThetaSchemeKatoUnitR0250.torsionIdeal E c).ideal U =
    (ArithmeticThetaSchemeKatoUnitR0250.identityIdeal E).ideal U

/-- The conormal class is e* of the actual ideal section, with no chosen frame. -/
def conormalPower {S : Scheme.{u}} (E : Family S) (U : E.curve.Opens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U)) :=
  tensorPowerSection S (Cotangent E) 24 (E.zero ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection E.zero x)

/-- Every identity point has arbitrarily small affine charts on which the
whole c-torsion ideal equals the identity ideal. No Kato function is supplied. -/
def IdentityChartCover {S : Scheme.{u}} (E : Family S) (c : ℕ) : Prop :=
  ∀ (s : S) (V : E.curve.Opens), E.zero s ∈ V →
    ∃ (U : E.curve.affineOpens)
      (x : E.zero.ker.module.presheaf.obj (Opposite.op U.1)),
      E.zero s ∈ U.1 ∧ U.1 ≤ V ∧ IdentityChart E c U x

/-- Local equations on the given curve, not only after field-valued tests.
The tensor is the actual I/I² class; epsilon is a unit on the entire U. -/
def SchemeInitial {S : Scheme.{u}} (E : Family S)
    (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E 5)
    (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) : Prop :=
  ∀ (U : E.curve.affineOpens)
    (x : E.zero.ker.module.presheaf.obj (Opposite.op U.1)),
    IdentityChart E 5 U x →
    ∃ ε : (E.curve.presheaf.obj (Opposite.op U.1))ˣ,
      5 * ArithmeticThetaArbitraryKatoUnitR0249.restrict
          (ArithmeticThetaSchemeKatoUnitR0250.complement E 5)
          (U.1 ⊓ ArithmeticThetaSchemeKatoUnitR0250.complement E 5)
          inf_le_right (v : _) =
        ArithmeticThetaArbitraryKatoUnitR0249.restrict U.1
          (U.1 ⊓ ArithmeticThetaSchemeKatoUnitR0250.complement E 5)
          inf_le_left ((ε : _) * (equation E U.1 x)^24) ∧
      res (ArithmeticThetaSchemeDiscriminantR0244.Power E) le_top d =
        E.zero.app U.1 (ε : _) • conormalPower E U.1 x

end ArithmeticThetaKatoInitialR0253
