module

public import GeometricInversionLiftR0141
public import NormalizedIdentityFrameR0140
public import GenericDualLocalizationR0140
public import TateSeriesSymmetry

@[expose] public section

/-! Literal Tate coordinate numerators on the actual finite polygon charts.
The finite geometric sums invert only positive-parameter-order terms. The
horizontal factors at the first and last charts are cancelled explicitly.
No future coordinate section or compatibility proof is selected here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraicCoordinatesR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaGenericEvaluationR0140

variable (k : Type u) [Field k] [CharZero k]

def degree (odd : Bool) : ℕ := if odd then 3 else 2

def tau (n : ℕ) : A k n := base k n (parameter k n)

def geometric (n : ℕ) (v : A k n) : A k n :=
  ∑ a ∈ Finset.range (n+1), v^a

def term (odd : Bool) (n : ℕ) (v : A k n) : A k n :=
  v * (if odd then 1+v else 1) * geometric k n v ^ degree odd

/-- The literal numerator of X (false) or Y = (z/2)dX/dz (true), modulo
 t^(n+1), relative to the genuine equation of the marked divisor. -/
def numerator (odd : Bool) (r n : ℕ) (i : Fin r) : A k n :=
  let h := equation k r n i ^ degree odd
  let first := if i.val = 0 then
      coordX k n * (if odd then 1+coordX k n else 1)
    else h * term k odd n (tau k n ^ i.val * coordX k n)
  let positive := h * ∑ a ∈ Finset.range (n+1),
    term k odd n (tau k n ^ (r*(a+1)+i.val) * coordX k n)
  let negative := ∑ a ∈ Finset.range (n+1),
    if a = 0 ∧ i.val+1 = r then
      coordY k n * (if odd then 1+coordY k n else 1)
    else h * term k odd n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)
  if odd then
    base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) *
      (first + positive - negative)
  else
    first + positive + negative - 2 * h * ∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1)))

/-- All actual overlaps and every actual thickness reduction. -/
def CompatibleSystem (odd : Bool) {r : ℕ} {hr : 0 < r}
    (T : Tower k r hr) : Prop :=
  (∀ n, Compatible k r n hr (T.overlap n) (degree odd) (numerator k odd r n)) ∧
  ∀ (n N : ℕ) (h : n ≤ N) (i : Fin r),
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (numerator k odd r N i) = numerator k odd r n i

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def RealizesCoordinate (odd : Bool) (M : Model k T)
    (s : baseScheme k ⟶ M.X) (φ : Dual k M s (degree odd)) : Prop :=
  ∀ n (i : Fin r),
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj (powerModule k M s (degree odd))
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ degree odd)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (equation k r n i ^ degree odd) ∧
      q.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k odd r n i)

def pulled (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (p : baseScheme k ⟶ M.X) (φ : Dual k M s d) :=
  (Scheme.Modules.pullback p).map φ ≫ unitPullback p

def pulledIdeal (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (p : baseScheme k ⟶ M.X) :=
  pulled k M s d p (GlobalCartierIdealLineR0133.idealInclusion (s.ker^d))

def baseScalar (U : (baseScheme k).Opens) (g : PowerSeries k) :
    (baseScheme k).presheaf.obj (Opposite.op U) :=
  (baseScheme k).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g)

/-- Equality of actual sheaf maps along the specified section. The ideal
inclusion is also required to become invertible, so this is regular evaluation. -/
def HasValue (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (p : baseScheme k ⟶ M.X) (φ : Dual k M s d) (g : PowerSeries k) : Prop :=
  IsIso (pulledIdeal k M s d p) ∧
  ∀ (U : (baseScheme k).Opens)
    (x : Γ((Scheme.Modules.pullback p).obj (powerModule k M s d), U)),
    (pulled k M s d p φ).app U x =
      baseScalar k U g * (show (baseScheme k).presheaf.obj (Opposite.op U) from
        (pulledIdeal k M s d p).app U x)

def inversionAction (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal iv)
    (d : ℕ) (φ : Dual k M s d) : Dual k M s d :=
  (ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141.modelLift
    k h3 M hM s hs rot scal iv ha d).hom ≫
      (Scheme.Modules.pullback iv.hom).map φ ≫ unitPullback iv.hom

end ArithmeticThetaAlgebraicCoordinatesR0143
