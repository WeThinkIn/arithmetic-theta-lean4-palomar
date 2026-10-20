module

public import ArithmeticMillerPairingR0116
public import FullMarkingCharacterR0115

@[expose] public section

/-! Ordinary definitions for the geometric four-torsion pairing.
The local data fields are precisely the already accepted translation and
infinity-expansion predicates. No pairing law or divisor formula is a field.
The scalar pairing is defined by an actual moved-divisor evaluation, with an
explicit totalization when no rational admissible shift exists. All obligations
that use the pairing require an actual full-four basis and prove shift existence.
-/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118

abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e
abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.FF k e

structure LocalData (k : Type u) [Field k] (e : Fin 3 → k) where
  translations : ArithmeticThetaReciprocityR0116.Translations k e
  branch : PowerSeries k
  embedding : FF k e →ₐ[k] LaurentSeries k
  translations_spec : ArithmeticThetaReciprocityR0116.IsTranslationSystem k e translations
  branch_spec : ArithmeticThetaMillerR0114.branchEquation k e branch
  embedding_spec : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e branch embedding

def order (k : Type u) [Field k] (e : Fin 3 → k) (D : LocalData k e)
    (f : FF k e) (P : (Curve k e).Point) : ℤ :=
  ArithmeticThetaReciprocityR0116.pointOrder k e D.translations D.embedding f P

def value (k : Type u) [Field k] (e : Fin 3 → k) (D : LocalData k e)
    (f : FF k e) (P : (Curve k e).Point) : k :=
  ArithmeticThetaReciprocityR0116.localValue k e D.translations D.embedding f P

/-- Normalized Miller function for every point killed by four: 1 at zero,
the square of the vertical line at a nonzero two-torsion point, and the
tangent squared divided by the vertical line through 2P otherwise. -/
def fourFunction (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) :
    (Curve k e).Point → FF k e
  | .zero => 1
  | P@(.some x y _) =>
      if y = 0 then
        (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x)^2
      else
        (algebraMap (ArithmeticThetaMillerR0114.Coord k e) (FF k e)
          (ArithmeticThetaMillerR0114.tangentClass k e x y))^2 /
        (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e)
          (ArithmeticThetaMarkingR0115.pointX k e (2 • P)))

/-- The actual chord/tangent quotient, including identity and vertical cases. -/
def additionFunction (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) :
    (Curve k e).Point → (Curve k e).Point → FF k e
  | .zero, _ => 1
  | _, .zero => 1
  | P@(.some x y _), Q@(.some a b _) =>
      if x = a ∧ y = -b then
        ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x
      else
        (ArithmeticThetaMillerR0114.yFunction k e - algebraMap k (FF k e) y -
          algebraMap k (FF k e) ((Curve k e).slope x a y b) *
            (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x)) /
        (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e)
          (ArithmeticThetaMarkingR0115.pointX k e (P + Q)))

def movedValue (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (D : LocalData k e) (P Q Z : (Curve k e).Point) : k :=
  value k e D (fourFunction k e P) (Q + Z) /
    value k e D (fourFunction k e P) Z *
  (value k e D (fourFunction k e Q) (-Z) /
    value k e D (fourFunction k e Q) (P - Z))

/-- Choose an actual rational shift. Existence and independence of this choice
are targets, not definition fields. The zero branch must be excluded in every
source-facing application by the full-four basis provider. -/
def pairing (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k)
    (D : LocalData k e) (P Q : (Curve k e).Point) : k := by
  classical
  exact if h : ∃ Z : (Curve k e).Point, ArithmeticThetaReciprocityR0116.GoodShift k e P Q Z
    then movedValue k e D P Q (Classical.choose h)
    else 0

end ArithmeticThetaGeometricPairingR0118
