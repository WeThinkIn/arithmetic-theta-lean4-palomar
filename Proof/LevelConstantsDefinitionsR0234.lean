module

public import SchemeHodgeUniversalR0205
public import MetaplecticFiberEquivalenceR0206
public import SmoothProjectiveLevelCompletionR0179
public import CompactifiedLevelForgettingR0179
public import FullLevelBaseChangeR0175

@[expose] public section

/-! Coefficient-field comparisons of the existing full-level moduli schemes.
All comparison maps and their properties are construction targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaLevelConstantsR0234
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205

abbrev constants {k l : Type} [Field k] [Field l] (ι : k →+* l) :
    Base l ⟶ Base k := Spec.map (CommRingCat.ofHom ι)

abbrev Classifies {k : Type} [Field k] [CharZero k] {L : ℕ}
    (D : LevelData k L) {S : Scheme.{0}} (σ : S ⟶ Base k)
    (F : Family S) (M : FullLevel F L)
    (b : S ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve) :=
  ArithmeticThetaSchemeLevelR0204.Classifies k L D.atlas D.two D.cover D.quotient σ F M b f

/-- Forget only the coefficient-field map. Both ordered markings, the actual
elliptic family, Cartesian family comparison and group operation remain fixed. -/
def RespectsClassifiers {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D) : Prop :=
  f ≫ openStructure k L D = openStructure l L E ≫ constants ι ∧
  ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L)
    (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve),
    Classifies E σ F M b g →
    ∃ a : F.curve ⟶ D.atlas.descent.family.curve,
      Classifies D (σ ≫ constants ι) F M (b ≫ f) a

abbrev weight {k : Type} [Field k] [CharZero k] {L : ℕ} (D : LevelData k L) :=
  ModularHodge k L D.atlas D.two D.cover D.quotient

/-- Normalize the entire Hodge isomorphism on every common classified family by
its inclusion-compatible conormal derivative. No scalar or sign is left free. -/
def HodgeCompatible {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) : Prop :=
  ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L)
    (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve)
    (a : F.curve ⟶ D.atlas.descent.family.curve),
    Classifies E σ F M b g → Classifies D (σ ≫ constants ι) F M (b ≫ f) a →
    ∀ (el : (Scheme.Modules.pullback b).obj (weight E) ≅ Cotangent F)
      (ek : (Scheme.Modules.pullback (b ≫ f)).obj (weight D) ≅ Cotangent F),
    ClassifierHodge l L E.atlas E.two E.cover E.quotient F b g el →
    ClassifierHodge k L D.atlas D.two D.cover D.quotient F (b ≫ f) a ek →
    (Scheme.Modules.pullback b).map e.hom ≫ el.hom =
      ((Scheme.Modules.pullbackComp b f).app (weight D)).hom ≫ ek.hom

/-- Extension of the same open comparison to the two specified compactifications. -/
def Extends {k l : Type} [Field k] [Field l] {L : ℕ}
    (ι : k →+* l) (D : LevelData k L) (E : LevelData l L)
    (X : Compactification k L D) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) : Prop :=
  F ≫ X.projection = Y.projection ≫ constants ι ∧ Y.inclusion ≫ F = f ≫ X.inclusion

/-- The module is explicitly induced by the specified field homomorphism. -/
def FiniteConstants {k l : Type} [Field k] [Field l] (ι : k →+* l) : Prop :=
  letI : Algebra k l := ι.toAlgebra
  letI : Module k l := @Algebra.toModule k l _ _ ι.toAlgebra
  FiniteDimensional k l

def constantDegree {k l : Type} [Field k] [Field l] (ι : k →+* l) : ℕ :=
  letI : Algebra k l := ι.toAlgebra
  letI : Module k l := @Algebra.toModule k l _ _ ι.toAlgebra
  Module.finrank k l

end ArithmeticThetaLevelConstantsR0234
