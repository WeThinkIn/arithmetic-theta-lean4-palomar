import ActualKatoFunctionExistenceR0151
import ActualKatoFieldBaseChangeR0151

/-! General characteristic-zero Weierstrass curves. All orders, multiplication
maps and norms are attached to the same actual projective curve. This module
contains definitions only; it asserts no existence or moduli descent. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable (F : Type u) [Field F]

abbrev Curve (W : WeierstrassCurve F) : Scheme.{u} :=
  WeierstrassProjModel.projModelCR W.toProjective

def structureMap (W : WeierstrassCurve F) : Curve F W ⟶ Spec (CommRingCat.of F) :=
  WeierstrassProjModel.projModelStrCR W.toProjective

def origin (W : WeierstrassCurve F) : Spec (CommRingCat.of F) ⟶ Curve F W :=
  (WeierstrassProjModel.kwZeroSect F W).val

abbrev Law (W : WeierstrassCurve F) :=
  WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)

def IsOriginLaw (W : WeierstrassCurve F) (G : Law F W) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)),
    (G.one t).val = t ≫ origin F W) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F))
    (x y : SchemeHomOver t (structureMap F W)), G.mul t x y = G.mul t y x)

def originPoint (W : WeierstrassCurve F) : Curve F W :=
  origin F W (IsLocalRing.closedPoint F)

def katoOrder (W : WeierstrassCurve F) (G : Law F W) (c : ℕ)
    (x : Curve F W) : ℤ := by
  classical
  exact (if x = originPoint F W then (c : ℤ)^2 else 0) -
    (if G.schemeNsmul c x = originPoint F W then 1 else 0)

def HasKatoDivisor (W : WeierstrassCurve F) (G : Law F W) (c : ℕ)
    [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)]
    (g : (Curve F W).functionField) : Prop :=
  g ≠ 0 ∧ ∀ x : Curve F W, Scheme.ord g x = katoOrder F W G c x

def IsKatoFunction (W : WeierstrassCurve F) (G : Law F W) (c : ℕ)
    [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)]
    (g : (Curve F W).functionField) : Prop :=
  HasKatoDivisor F W G c g ∧
    ∀ d : ℕ, 0 < d → Nat.Coprime c d →
      ∀ φ : (Curve F W).functionField →+* (Curve F W).functionField,
        ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ →
          ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g

/-- The finite-dimensional action is explicitly the specified field map,
including when source and target have the same carrier. -/
def HasFieldDegree {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (n : ℕ) : Prop :=
  letI : Algebra K L := φ.toAlgebra
  letI : Module K L := @Algebra.toModule K L _ _ φ.toAlgebra
  FiniteDimensional K L ∧ Module.finrank K L = n

/-- A Cartesian elliptic-curve comparison with the actual origin and all
multiplication maps. No rational-function equality is assumed. -/
def IsBaseChange (K : Type u) [Field K] (W : WeierstrassCurve F)
    (Wb : WeierstrassCurve K) (G : Law F W) (Gb : Law K Wb)
    (ι : F →+* K) (b : Curve K Wb ⟶ Curve F W) : Prop :=
  IsPullback b (structureMap K Wb) (structureMap F W)
    (Spec.map (CommRingCat.ofHom ι)) ∧
  (origin K Wb ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ origin F W) ∧
  (∀ n : ℕ, Gb.schemeNsmul n ≫ b = b ≫ G.schemeNsmul n)

end ArithmeticThetaGeneralEllipticKatoR0168
