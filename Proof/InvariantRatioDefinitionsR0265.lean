module

public import GlobalLiteralTateMarkingR0263
public import SchemeGeometricThetaNaturalityR0262

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaInvariantRatiosR0265
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184

/-- Scalar multiplication on the actual identity fibre, through the Spec global ring. -/
def scalarEnd {F : Type u} [Field F] (M : (Base F).Modules)
    (a : F) : End M :=
  P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) M

/-- Equalities of actual sheaf morphisms, so all frames and all opens are covered.
The zeroth component is an isomorphism; it is not just a nonzero chosen value. -/
def ComponentRatios {F : Type u} [Field F] (E : Family (Base F))
    (m : ℕ) (hm : 0 < m) (A B : End (V E m)) (r : Fin m → F) : Prop :=
  IsIso (component E m A B ⟨0,hm⟩) ∧
  ∀ i : Fin m, component E m A B i =
    component E m A B ⟨0,hm⟩ ≫
      scalarEnd ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)) (r i)

def unaryRatio (k : Type) [Field k] (m : ℕ) (hm : 0 < m) (i : Fin m) : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m i) /
    algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ⟨0,hm⟩)

namespace Arithmetic
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
variable (k : Type) [Field k] [CharZero k] (m : ℕ)
  (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
  (Vd : DiskTest k (2*m) D X)

abbrev point := Vd.disk (closedPoint k)
abbrev componentScheme := Component k (2*m) D X (point k m D X Vd)
abbrev coefficientField := (componentScheme k m D X Vd).functionField

/-- The accepted arithmetic generic family, with the same curve, structure map
and group law. This merely packages already proved geometry, not new geometry. -/
def family : Family (Base (coefficientField k m D X Vd)) where
  curve := ArithmeticFamily.curve k (2*m) D X (point k m D X Vd)
  p := ArithmeticFamily.structureMap k (2*m) D X (point k m D X Vd)
  law := {
    mul := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).mul
    one := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).one
    inv := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).inv
    mul_assoc := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).mul_assoc
    one_mul := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).one_mul
    mul_one := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).mul_one
    inv_mul_cancel := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).inv_mul_cancel
    mul_natural := (ArithmeticFamily.groupLaw k (2*m) D X (point k m D X Vd)).mul_natural
    mul_comm := ArithmeticFamily.groupLaw_commutative k (2*m) D X (point k m D X Vd) }
  proper := inferInstance
  dimension := inferInstance
  connected := inferInstance

abbrev tateFamily := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level

/-- All maps are on the chosen arithmetic component and the SAME disk test.
This data is constructed in the final obligation; it is never a premise there. -/
structure Test where
  disk : Disk k ⟶ componentScheme k m D X Vd
  disk_eq : disk ≫ inclusion k (2*m) D X (point k m D X Vd) = Vd.disk
  dominant : IsDominant (genericInclusion k ≫ disk)
  scalar : coefficientField k m D X Vd →+* LaurentSeries k
  generic_eq : Spec.map (CommRingCat.ofHom scalar) ≫
    (componentScheme k m D X Vd).fromSpecStalk (genericPoint (componentScheme k m D X Vd)) =
      genericInclusion k ≫ disk
  base_eq : Spec.map (CommRingCat.ofHom scalar) ≫
    GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X (point k m D X Vd) = Vd.base
  level : ArithmeticThetaSchemeLevelR0204.FullLevel (family k m D X Vd) (2*m)
  x_eq : level.x.val = ArithmeticFamily.label k (2*m) D X (point k m D X Vd) D.atlas.marking.x
  y_eq : level.y.val = ArithmeticFamily.label k (2*m) D X (point k m D X Vd) D.atlas.marking.y
  cartesian : IsPullback
    (ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd scalar base_eq)
    (tateFamily k m D X Vd).p (family k m D X Vd).p (Spec.map (CommRingCat.ofHom scalar))
  pointed : (tateFamily k m D X Vd).zero ≫
    ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd scalar base_eq =
      Spec.map (CommRingCat.ofHom scalar) ≫ (family k m D X Vd).zero
  multiplicative : ArithmeticThetaSchemeLevelR0204.Multiplicative (family k m D X Vd)
    (tateFamily k m D X Vd) (Spec.map (CommRingCat.ofHom scalar))
    (ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd scalar base_eq)
  x_tate : Vd.level.marking.x.val ≫
    ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd scalar base_eq =
      Spec.map (CommRingCat.ofHom scalar) ≫ level.x.val
  y_tate : Vd.level.marking.y.val ≫
    ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd scalar base_eq =
      Spec.map (CommRingCat.ofHom scalar) ≫ level.y.val

variable (T : Test k m D X Vd)
abbrev baseMap := Spec.map (CommRingCat.ofHom T.scalar)
abbrev curveMap := ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd T.scalar T.base_eq

/-- The arithmetic functions ARE the scalars of the scheme invariant-component
maps. The very same Cartesian comparison transports those component maps to
literal Tate evaluation. The signs live on the original arithmetic base. -/
def Realization (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m)) : Prop :=
  let E := family k m D X Vd
  let F := tateFamily k m D X Vd
  ∃ (Q : ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd.level ζ)
    (a : Lift F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)))
    (b : Lift F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)))
    (I : Lift E m (inverse E))
    (α₀ : Lift E m (translation E T.level.x))
    (β₀ : Lift E m (translation E T.level.y)) (signs : Bool × Bool),
    ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd.level Q he hζ a ∧
    ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd.level Q he b ∧
    NormalizedInversion E m I ∧
    MidpointNormalized E m T.level.x I α₀ ∧ MidpointNormalized E m T.level.y I β₀ ∧
    Symmetric E m T.level.x I α₀ ∧ Symmetric E m T.level.y I β₀ ∧
    let α := scaled E m (signUnit _ signs.1) α₀
    let β := scaled E m (signUnit _ signs.2) β₀
    LiftCorresponds E F (baseMap k m D X Vd T) (curveMap k m D X Vd T) T.cartesian T.pointed
      m (translation E T.level.x) (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) α a ∧
    LiftCorresponds E F (baseMap k m D X Vd T) (curveMap k m D X Vd T) T.cartesian T.pointed
      m (translation E T.level.y) (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) β b ∧
    ∃ (A B : End (V E m)) (A' B' : End (V F m)) (r : Fin m → coefficientField k m D X Vd),
      IsAction E m (translation E T.level.x) α A ∧ IsAction E m (translation E T.level.y) β B ∧
      IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' ∧
      IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' ∧
      InvariantComponents E F (baseMap k m D X Vd T) (curveMap k m D X Vd T)
        T.cartesian T.pointed m A B A' B' ∧
      ComponentRatios E m hm A B r ∧
      ComponentRatios F m hm A' B' (unaryRatio k m hm) ∧
      (∀ i, T.scalar (r i) = unaryRatio k m hm i) ∧
      (∀ i, ArithmeticThetaSharpCoverR0194.RationalExpansion k
        (componentScheme k m D X Vd) (genericInclusion k ≫ T.disk) (r i) (unaryRatio k m hm i))

end Arithmetic
end ArithmeticThetaInvariantRatiosR0265
