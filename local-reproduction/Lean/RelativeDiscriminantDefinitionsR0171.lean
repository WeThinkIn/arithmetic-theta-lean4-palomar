import RelativeTorsionValueNaturalityR0170
import PullbackTensorSections

/-! Intrinsic initial sections on the actual relative Weierstrass family.
All section, differential and scalar maps are the geometric structure maps.
This file introduces definitions only; existence and naturality are obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeDiscriminantR0171
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaTensorPower

abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj (structureMap R W).kaehler

abbrev HodgePower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :=
  tensorPower (Base R) (Hodge R W) n

def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s

/-- A section generates the actual sheaf on every subopen, including empty opens. -/
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun a : X.presheaf.obj (Opposite.op V) => a • res F h s)

def localDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (a : (Curve R W).presheaf.obj (Opposite.op U)) :
    Γ(Hodge R W, (origin R W) ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection (origin R W)
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U a)

def localPower (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (n : ℕ) (U : (Curve R W).Opens)
    (a : (Curve R W).presheaf.obj (Opposite.op U)) :
    Γ(HodgePower R W n, (origin R W) ⁻¹ᵁ U) :=
  tensorPowerSection (Base R) (Hodge R W) n ((origin R W) ⁻¹ᵁ U)
    (localDifferential R W U a)

variable (R : Type u) [CommRing R] [IsDomain R]
variable (W : WeierstrassCurve R) (G : Law R W)

/-- On this affine open the actual c-torsion Cartier divisor equals the identity.
The property contains no claim about a Kato function or its initial coefficient. -/
def IdentityChart (c : ℕ) (U : (Curve R W).affineOpens)
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)) : Prop :=
  IsRegular a ∧ (identityIdeal R W).ideal U = Ideal.span ({a} : Set _) ∧
    (torsionIdeal R W G c).ideal U = (identityIdeal R W).ideal U

variable [IsIntegral (Curve R W)]

/-- Intrinsic local characterization of c times the order-(c^2-1) initial term.
The coefficient is the actual unit quotient in the function field, evaluated
through the origin's sheaf map; the differential is the actual relative da. -/
def RepresentsInitial (c : ℕ) (g : (Curve R W).functionField)
    (d : Γ(HodgePower R W (c^2-1), ⊤)) : Prop :=
  ∀ (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)),
    IdentityChart R W G c U a →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      (c : (Curve R W).functionField) * g =
        (Curve R W).germToFunctionField U.1 ((ε : _) * a^(c^2-1)) ∧
      res (HodgePower R W (c^2-1)) le_top d =
        (origin R W).app U.1 (ε : _) • localPower R W (c^2-1) U.1 a

variable (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)

def baseMap (ι : R →+* S) : Base S ⟶ Base R := Spec.map (CommRingCat.ofHom ι)

/-- The comparison is characterized on actual local differentials, all opens,
and all scalar pullbacks. This prohibits selecting an unrelated line isomorphism. -/
def IsPowerBaseChange (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W) (n : ℕ)
    (e : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅
      HodgePower S Ws n) : Prop :=
  ∀ (U : (Curve R W).Opens) (a : (Curve R W).presheaf.obj (Opposite.op U))
    (V : (Base S).Opens)
    (h₁ : V ≤ (baseMap R S ι) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U))
    (h₂ : V ≤ (origin S Ws) ⁻¹ᵁ (b ⁻¹ᵁ U)),
    res (HodgePower S Ws n) h₁
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection (baseMap R S ι)
        (localPower R W n U a))) =
    res (HodgePower S Ws n) h₂ (localPower S Ws n (b ⁻¹ᵁ U) (b.app U a))

def InitialBaseChange (ι : R →+* S) (n : ℕ)
    (e : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅
      HodgePower S Ws n)
    (d : Γ(HodgePower R W n, ⊤)) (ds : Γ(HodgePower S Ws n, ⊤)) : Prop :=
  e.hom.app _ (Scheme.Modules.pullbackLocalSection (baseMap R S ι) d) =
    res (HodgePower S Ws n) le_top ds

end ArithmeticThetaRelativeDiscriminantR0171
