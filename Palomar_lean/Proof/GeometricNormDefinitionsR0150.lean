module

public import MultiplicationFiniteEtaleDegreeR0148
public import PrincipalDegreeZero
public import HodgeFourTorsionDefinitionsR0147
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

/-! Geometric field norms. The scalar structures are induced by specified
scheme morphisms, and the divisor coefficients use actual scheme points. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaGeometricNormR0150
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The square at the actual generic points specifies the contravariant map. -/
def IsFieldMap (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) : Prop :=
  X.fromSpecStalk (genericPoint X) ≫ f =
    Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)

/-- Determinant norm with precisely the algebra structure induced by φ. -/
def fieldNorm (φ : Y.functionField →+* X.functionField)
    (g : X.functionField) : Y.functionField :=
  letI := φ.toAlgebra
  Algebra.norm Y.functionField g

def FiniteFieldMap (φ : Y.functionField →+* X.functionField) : Prop :=
  letI := φ.toAlgebra
  FiniteDimensional Y.functionField X.functionField

def fieldDegree (φ : Y.functionField →+* X.functionField) : ℕ :=
  letI := φ.toAlgebra
  Module.finrank Y.functionField X.functionField

/-- The structural scalar in the actual function field. -/
def baseScalar (F : Type u) [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    (a : F) : X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact X.germToFunctionField ⊤ (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a))

/-- Norm of a section for the algebra induced by f on an affine open. -/
def affineNorm (f : X ⟶ Y) (U : Y.Opens)
    (a : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U))) :
    Y.presheaf.obj (Opposite.op U) :=
  letI := (f.app U).hom.toAlgebra
  Algebra.norm (Y.presheaf.obj (Opposite.op U)) a

def AffineFree (f : X ⟶ Y) (U : Y.Opens) : Prop :=
  letI := (f.app U).hom.toAlgebra
  Module.Free (Y.presheaf.obj (Opposite.op U))
    (X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))

def NormOnOpen (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField)
    (U : Y.Opens) : Prop :=
  ∀ [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (a : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U))),
    Y.germToFunctionField U (affineNorm f U a) =
      fieldNorm φ (X.germToFunctionField (f ⁻¹ᵁ U) a)

/-- Pushforward order includes the residue degree at each actual fiber point. -/
def pushOrder (f : X ⟶ Y) [IsLocallyNoetherian X]
    (g : X.functionField) (y : Y) : ℤ :=
  ∑ᶠ x : {x : X // f x = y}, (f.residueDegree x.val : ℤ) * Scheme.ord g x.val

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def identityPoint (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) : genericScheme k M :=
  genericPoint k M s hs (IsLocalRing.closedPoint (LaurentSeries k))

/-- The coefficient of c²[0] - [E[c]], with E[c] the actual multiplication fiber.
The proof batch must establish the norm formula, rather than assuming it here. -/
def katoOrder (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ)
    (x : genericScheme k M) : ℤ := by
  classical
  exact (if x = identityPoint k M s hs then (c : ℤ)^2 else 0) -
    (if multiplication k M G c x = identityPoint k M s hs then 1 else 0)

end ArithmeticThetaGeometricNormR0150
