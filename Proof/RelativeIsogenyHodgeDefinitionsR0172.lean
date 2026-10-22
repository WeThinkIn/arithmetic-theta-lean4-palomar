module

public import RelativeInitialSectionNaturalityR0171
public import RelativeHodgePowerBaseChangeR0171

@[expose] public section

/-! Actual pullback of the relative Hodge line along a pointed morphism.
The differential map is the accepted universal relative derivation map.
No differential identity or invertibility is included in the geometric data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeIsogenyHodgeR0172
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaPullback

structure PointedMap (R : Type u) [CommRing R]
    (W V : WeierstrassCurve R) where
  map : Curve R W ⟶ Curve R V
  over_eq : map ≫ structureMap R V = structureMap R W
  origin_eq : origin R W ≫ map = origin R V

def PointedMap.identity (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    PointedMap R W W where
  map := 𝟙 _
  over_eq := Category.id_comp _
  origin_eq := Category.comp_id _

def PointedMap.comp {R : Type u} [CommRing R] {W V Z : WeierstrassCurve R}
    (f : PointedMap R W V) (g : PointedMap R V Z) : PointedMap R W Z where
  map := f.map ≫ g.map
  over_eq := by rw [Category.assoc, g.over_eq, f.over_eq]
  origin_eq := by rw [← Category.assoc, f.origin_eq, g.origin_eq]

def curveDifferential {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    (f : PointedMap R W V) :
    (Scheme.Modules.pullback f.map).obj (structureMap R V).kaehler ⟶
      (structureMap R W).kaehler :=
  differentialMap (structureMap R V) (structureMap R W) f.map
    (by simpa using f.over_eq)

def hodgeMap {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    (f : PointedMap R W V) : Hodge R V ⟶ Hodge R W :=
  (pullbackEqIso f.origin_eq.symm (structureMap R V).kaehler).hom ≫
    ((Scheme.Modules.pullbackComp (origin R W) f.map).app
      (structureMap R V).kaehler).inv ≫
    (Scheme.Modules.pullback (origin R W)).map (curveDifferential f)

def tensorMap {X : Scheme.{u}} {H K : X.Modules} (f : H ⟶ K) :
    (n : ℕ) → tensorPower X H n ⟶ tensorPower X K n
  | 0 => 𝟙 _
  | n+1 => sheafTensorMap X (tensorMap f n) f

def powerMap {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    (f : PointedMap R W V) (n : ℕ) : HodgePower R V n ⟶ HodgePower R W n :=
  tensorMap (hodgeMap f) n

/-- Equality of the two actual maps on Hodge powers, in a commuting base-change
diagram. The comparisons are supplied by the accepted Cartesian theorem. -/
def PowerNatural {R S : Type u} [CommRing R] [CommRing S]
    (W V : WeierstrassCurve R) (Ws Vs : WeierstrassCurve S)
    (ι : R →+* S) (f : PointedMap R W V) (fs : PointedMap S Ws Vs) (n : ℕ)
    (eW : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅
      HodgePower S Ws n)
    (eV : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R V n) ≅
      HodgePower S Vs n) : Prop :=
  (Scheme.Modules.pullback (baseMap R S ι)).map (powerMap f n) ≫ eW.hom =
    eV.hom ≫ powerMap fs n

end ArithmeticThetaRelativeIsogenyHodgeR0172
