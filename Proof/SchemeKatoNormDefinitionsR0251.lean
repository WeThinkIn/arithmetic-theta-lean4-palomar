module

public import SchemeKatoUnitNaturalityR0250
public import SchemeKatoCartierDivisorR0250
public import SchemeMultiplicationDegreeR0250
public import GeometricNormBaseChangeR0150

@[expose] public section

/-! Local determinants specify the norm without assuming global freeness.
The finite etale hypotheses in the obligations supply free affine covers.
No section, norm operator or norm identity is assumed to exist here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry

abbrev Sections (X : Scheme.{u}) (U : X.Opens) :=
  X.presheaf.obj (Opposite.op U)

abbrev restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : Sections X U) : Sections X V :=
  ArithmeticThetaArbitraryKatoUnitR0249.restrict U V h a

/-- Every free affine restriction is tested with the algebra induced by f.app.
The accepted affineNorm definition elaborates its scalar action from that map.
This avoids the totalized norm on a nonfree global section algebra. -/
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U),
    ArithmeticThetaGeometricNormR0150.AffineFree f V.1 →
    ArithmeticThetaGeometricNormR0150.affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) =
      restrict U V.1 e b

abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U

/-- Actual multiplicative maps on the section rings, with their determinant
normalization and restriction compatibility on all opens. -/
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)

/-- The original section restricts to the inverse image of its domain and its
local determinant is the same original section. The inclusion is constructed. -/
def LocallyNormFixed {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens)
    (v : Sections X U) : Prop :=
  ∃ e : f ⁻¹ᵁ U ≤ U, IsNormSection f U (restrict U (f ⁻¹ᵁ U) e v) v

/-- Construct the actual norm family and the restriction used in its fixed-point
equation. This includes the norm operator, not only a conditional equation. -/
def NormInvariant {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens)
    (v : Sections X U) : Prop :=
  ∃ N : NormFamily f, IsNormFamily f N ∧
    ∃ e : f ⁻¹ᵁ U ≤ U, N U (restrict U (f ⁻¹ᵁ U) e v) = v

end ArithmeticThetaSchemeKatoNormR0251
