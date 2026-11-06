module

public import AlgebraicTateCoordinatesR0143
public import CoordinateExactPolesR0143
public import CoordinateMarkedEvaluationR0143
public import CoordinateGeometricInversionR0143
public import IdentityPositiveSectionsRankR0138
public import TateGeneralSplitCubic
public import AlgebraicTateCoordinatesDefinitionsR0143
public import TateSeriesDefinitions

@[expose] public section

/-! Exact coordinate bases, cubic equations and the generic affine coordinate
identification. All geometric maps belong to the accepted proper model. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaPolygonCartierR0133

variable (k : Type u) [Field k] [CharZero k]

/-- The actual three marked coordinate values for Q=t^r and even r. -/
def rootSeries (r : ℕ) (j : Fin 3) : PowerSeries k :=
  if j.val = 0 then ArithmeticThetaTateSeries.tateX r 0 (-1)
  else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val = 1 then 1 else -1)

def rootAt (r n : ℕ) (j : Fin 3) : A k n :=
  base k n (trunc (PowerSeries k) PowerSeries.X n (rootSeries k r j))

def basisNumerator (odd : Bool) (r n : ℕ) (j : Fin (degree odd))
    (i : Fin r) : A k n :=
  if j.val = 0 then equation k r n i ^ degree odd
  else if j.val = 1 then
    (if odd then equation k r n i else 1) * numerator k false r n i
  else numerator k true r n i

/-- A basis assertion includes compatibility of every displayed basis vector
and existence and uniqueness of coefficients for EVERY compatible numerator. -/
def CoordinateBasis (odd : Bool) {r n : ℕ} {hr : 0 < r}
    (E : B k n false ≃+* B k n true) : Prop :=
  (∀ j : Fin (degree odd),
    Compatible k r n hr E (degree odd) (basisNumerator k odd r n j)) ∧
  ∀ v : Sections k r n hr E (degree odd), ∃! c : Fin (degree odd) → R k n,
    ∀ i, v.val i = ∑ j, base k n (c j) * basisNumerator k odd r n j i

/-- The logarithmic derivation is relative to the SPECIFIED truncated base map. -/
def LogarithmicDerivative (n : ℕ) : Prop :=
  ∃! D : Derivation ℤ (A k n) (A k n),
    (∀ c : R k n, D (base k n c) = 0) ∧
    D (coordX k n) = coordX k n ∧ D (coordY k n) = -coordY k n ∧
    ∀ (r : ℕ) (hr : 3 ≤ r) (i : Fin r),
      equation k r n i * D (numerator k false r n i) -
        2 * numerator k false r n i * D (equation k r n i) =
          2 * numerator k true r n i

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def modelScalar (M : Model k T) (U : M.X.Opens) (g : PowerSeries k) :
    M.X.presheaf.obj (Opposite.op U) :=
  M.X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (M.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g))

/-- Cross-multiplied equality of actual rational coordinates on every open,
using the actual inclusions of the second and third identity ideal powers. -/
def ModelCubic (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3) : Prop :=
  ∀ (U : M.X.Opens) (a : Γ(powerModule k M s 2, U))
    (b : Γ(powerModule k M s 3, U)),
    let ja : M.X.presheaf.obj (Opposite.op U) :=
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^2)).app U a
    let jb : M.X.presheaf.obj (Opposite.op U) :=
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^3)).app U b
    (show M.X.presheaf.obj (Opposite.op U) from Y.app U b)^2 * ja^3 =
      (∏ j : Fin 3, ((show M.X.presheaf.obj (Opposite.op U) from X.app U a) -
        modelScalar k M U (rootSeries k r j) * ja)) * jb^2

def cubicPolynomial (r : ℕ) : MvPolynomial (Fin 2) (LaurentSeries k) :=
  MvPolynomial.X 1 ^ 2 - ∏ j : Fin 3,
    (MvPolynomial.X 0 - MvPolynomial.C (algebraMap (PowerSeries k) (LaurentSeries k)
      (rootSeries k r j)))

abbrev CubicRing (r : ℕ) :=
  MvPolynomial (Fin 2) (LaurentSeries k) ⧸ Ideal.span {cubicPolynomial k r}

def cubicCoordinate (r : ℕ) (odd : Bool) : CubicRing k r :=
  Ideal.Quotient.mk _ (MvPolynomial.X (if odd then 1 else 0))

def cubicScheme (r : ℕ) : Scheme.{u} := Spec (CommRingCat.of (CubicRing k r))

def cubicStructure (r : ℕ) : cubicScheme k r ⟶ Spec (CommRingCat.of (LaurentSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (CubicRing k r)))

def complement (M : Model k T) (s : baseScheme k ⟶ M.X) :
    (genericScheme k M).Opens :=
  (s.ker.comap (genericInclusion k M)).support.compl

def complementScheme (M : Model k T) (s : baseScheme k ⟶ M.X) : Scheme.{u} :=
  (complement k M s).toScheme

def complementInclusion (M : Model k T) (s : baseScheme k ⟶ M.X) :
    complementScheme k M s ⟶ M.X :=
  (complement k M s).ι ≫ genericInclusion k M

def complementStructure (M : Model k T) (s : baseScheme k ⟶ M.X) :
    complementScheme k M s ⟶ Spec (CommRingCat.of (LaurentSeries k)) :=
  (complement k M s).ι ≫ genericStructure k M

/-- An isomorphism is constrained by its structural map and its two actual
coordinate pullbacks. No independently chosen scalar action or evaluation map. -/
def IsCoordinateIso (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : complementScheme k M s ≅ cubicScheme k r) : Prop :=
  e.hom ≫ cubicStructure k r = complementStructure k M s ∧
  ∀ odd : Bool,
    let f := complementInclusion k M s
    let φ : Dual k M s (degree odd) := match odd with | true => Y | false => X
    let L := (Scheme.Modules.pullback f).obj (powerModule k M s (degree odd))
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^degree odd)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    IsIso j ∧ ∀ (U : (complementScheme k M s).Opens) (v : Γ(L, U)),
      q.app U v =
        (complementScheme k M s).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
            (cubicCoordinate k r odd))) *
        (show (complementScheme k M s).presheaf.obj (Opposite.op U) from j.app U v)

end ArithmeticThetaCubicModelR0144
