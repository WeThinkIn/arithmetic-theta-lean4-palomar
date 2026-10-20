module

public import ArithmeticInvariantRatioRealizationR0265

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaInvariantRatiosR0265

/-- A genuine nonempty Zariski representative of a specified generic map.
Both triangles use the original function field and its canonical generic point. -/
structure GenericChart (Z S : Scheme.{u}) [IsIntegral Z]
    (g : Spec (CommRingCat.of Z.functionField) ⟶ S) where
  domain : Z.Opens
  nonempty : Nonempty domain
  map : domain.toScheme ⟶ S
  generic : Spec (CommRingCat.of Z.functionField) ⟶ domain.toScheme
  generic_eq : generic ≫ domain.ι = Z.fromSpecStalk (genericPoint Z)
  map_eq : generic ≫ map = g

variable {Z S : Scheme.{u}} [IsIntegral Z]
  (g : Spec (CommRingCat.of Z.functionField) ⟶ S)
  (M N : S.Modules) (d : M ⟶ N) {n : ℕ} (v : Fin n → (M ⟶ N))

/-- Ratios of the same morphisms at the canonical generic point. -/
def GenericRatios (r : Fin n → Z.functionField) : Prop :=
  IsIso ((Scheme.Modules.pullback g).map d) ∧
  ∀ i, (Scheme.Modules.pullback g).map (v i) =
    (Scheme.Modules.pullback g).map d ≫ scalarEnd ((Scheme.Modules.pullback g).obj N) (r i)

/-- Regular local representatives, with equality of sheaf morphisms on all
opens and their actual images in the original function field. -/
def RegularRatios (C : GenericChart Z S g) (r : Fin n → Z.functionField) : Prop :=
  IsIso ((Scheme.Modules.pullback C.map).map d) ∧
  ∃ a : Fin n → Γ(C.domain.toScheme, ⊤), ∀ i,
    (Scheme.Modules.pullback C.map).map (v i) =
      (Scheme.Modules.pullback C.map).map d ≫
        P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom
          (a i) ((Scheme.Modules.pullback C.map).obj N) ∧
    (Scheme.ΓSpecIso (CommRingCat.of Z.functionField)).hom (C.generic.appTop (a i)) = r i

/-- Localizing inside an existing geometric chart preserves its map to S. -/
def Refines (C C' : GenericChart Z S g) : Prop :=
  ∃ j : C'.domain.toScheme ⟶ C.domain.toScheme,
    IsOpenImmersion j ∧ j ≫ C.domain.ι = C'.domain.ι ∧
      j ≫ C.map = C'.map ∧ C'.generic ≫ j = C.generic

namespace Arithmetic
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
variable (k : Type) [Field k] [CharZero k] (m : ℕ)
  (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
  (Vd : DiskTest k (2*m) D X)

/-- The universal full-level family on its actual arithmetic base, before
passing to any function field or Tate completion. -/
abbrev globalBase := Base D.atlas.quotient.ring
abbrev globalFamily := ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily (2*m) D.atlas
abbrev globalLevel := ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.universalLevel D.atlas
abbrev compactComponent := ArithmeticThetaInvariantRatiosR0265.Arithmetic.componentScheme k m D X Vd
abbrev genericBase := ArithmeticFamily.base k (2*m) D X (Vd.disk (closedPoint k))
abbrev tateBase := Vd.base ≫ D.quotient.inclusion

/-- The chart lies over the selected compact component's actual interior. -/
def IsInteriorChart (C : GenericChart (compactComponent k m D X Vd) (globalBase k m D) (genericBase k m D X Vd)) : Prop :=
  ∃ j : C.domain.toScheme ⟶ OpenBase k (2*m) D,
    j ≫ X.inclusion = C.domain.ι ≫ inclusion k (2*m) D X (Vd.disk (closedPoint k)) ∧
    j ≫ D.quotient.inclusion = C.map

/-- Globally defined, sign-aligned theta lifts and components, with genuine
regular representatives of their rational quotients on the same component.
The final theorem constructs every field in this predicate. -/
def GlobalRealization (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m)) : Prop :=
  let E := globalFamily k m D
  let T := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let P := (globalLevel k m D).x
  let Q := (globalLevel k m D).y
  ∃ (model : ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd.level ζ)
    (a : Lift T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)))
    (b : Lift T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)))
    (I : Lift E m (inverse E)) (α₀ : Lift E m (translation E P))
    (β₀ : Lift E m (translation E Q)) (signs : Bool × Bool),
    ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd.level model he hζ a ∧
    ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd.level model he b ∧
    NormalizedInversion E m I ∧ MidpointNormalized E m P I α₀ ∧
    MidpointNormalized E m Q I β₀ ∧ Symmetric E m P I α₀ ∧ Symmetric E m Q I β₀ ∧
    let α := scaled E m (signUnit (globalBase k m D) signs.1) α₀
    let β := scaled E m (signUnit (globalBase k m D) signs.2) β₀
    ∃ (hc : IsPullback Vd.map T.p E.p (tateBase k m D X Vd))
      (hz : T.zero ≫ Vd.map = tateBase k m D X Vd ≫ E.zero),
      LiftCorresponds E T (tateBase k m D X Vd) Vd.map hc hz m
        (translation E P) (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) α a ∧
      LiftCorresponds E T (tateBase k m D X Vd) Vd.map hc hz m
        (translation E Q) (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) β b ∧
      ∃ (A B : End (V E m)) (A' B' : End (V T m)) (c : Γ(globalBase k m D, ⊤)ˣ),
        IsAction E m (translation E P) α A ∧ IsAction E m (translation E Q) β B ∧
        IsAction T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' ∧
        IsAction T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' ∧
        Relations m A B c ∧ PrimitiveUnit (S := globalBase k m D) m c ∧
        Scheme.Modules.IsInvertible (fixed A) ∧ Orbit m A B c ∧
        Scheme.Modules.IsInvertible (commonValueLine E m A) ∧
        InvariantComponents E T (tateBase k m D X Vd) Vd.map hc hz m A B A' B' ∧
        ComponentRatios T m hm A' B' (unaryRatio k m hm) ∧
        ∃ (C : GenericChart (compactComponent k m D X Vd) (globalBase k m D) (genericBase k m D X Vd))
          (r : Fin m → (compactComponent k m D X Vd).functionField)
          (test : ArithmeticThetaInvariantRatiosR0265.Arithmetic.Test k m D X Vd),
          IsInteriorChart k m D X Vd C ∧
          GenericRatios (genericBase k m D X Vd) (fixed A)
            ((Scheme.Modules.pullback E.zero).obj (thetaLine E m))
            (component E m A B ⟨0,hm⟩) (fun i => component E m A B i) r ∧
          RegularRatios (genericBase k m D X Vd) (fixed A)
            ((Scheme.Modules.pullback E.zero).obj (thetaLine E m))
            (component E m A B ⟨0,hm⟩) (fun i => component E m A B i) C r ∧
          (∀ i, test.scalar (r i) = unaryRatio k m hm i) ∧
          (∀ i, ArithmeticThetaSharpCoverR0194.RationalExpansion k (compactComponent k m D X Vd)
            (genericInclusion k ≫ test.disk) (r i) (unaryRatio k m hm i))

end Arithmetic
end ArithmeticThetaGlobalProjectiveRatiosR0266
