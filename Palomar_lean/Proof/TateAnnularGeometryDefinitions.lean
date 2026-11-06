module

public import TateNodeCompletion
public import TateNodeRestrictedPresentation
public import TateNodeTorusCharts
public import TateNodeGenericFiber

@[expose] public section

/-! Concrete completions of coordinate opens, adjacent-chart substitution, and
finite approximants for source annular products and theta Laurent sums.
There is no proper model, line bundle, section, or theorem asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularGeometry
open ArithmeticThetaNodeCharts
variable (k : Type u) [Field k]

abbrev CX := AdicCompletion ((nodeIdeal k).map (toXChart k)) (XChart k)
abbrev CY := AdicCompletion ((nodeIdeal k).map (toYChart k)) (YChart k)
abbrev CT := AdicCompletion (Ideal.span {LaurentPolynomial.C (parameter k)}) (Torus k)
def completeX : XChart k →+* CX k := algebraMap _ _
def completeY : YChart k →+* CY k := algebraMap _ _
def completeT : Torus k →+* CT k := algebraMap _ _
def restrictX : CompletedNode k →+* CX k := completionMap (S := XChart k) (nodeIdeal k)
def restrictY : CompletedNode k →+* CY k := completionMap (S := YChart k) (nodeIdeal k)
def polynomialX : PolynomialChart k →+* CX k :=
  (completeX k).comp ((toXChart k).comp (quotientMap k))
def polynomialY : PolynomialChart k →+* CY k :=
  (completeY k).comp ((toYChart k).comp (quotientMap k))
def tx : CX k := completeX k (toXChart k (t k))
def xx : CX k := completeX k (toXChart k (x k))
def xxInv : CX k := completeX k (IsLocalization.Away.invSelf (x k))
/-- In the source convention z=t^j*x_j, y_j=x_(j+1)^(-1). -/
def adjacentPolynomial : PolynomialChart k →+* CX k :=
  MvPolynomial.eval₂Hom ((polynomialX k).comp MvPolynomial.C)
    (fun i => if i = (0 : Fin 2) then tx k * xx k else xxInv k)
def Adjacent (e : CY k ≃+* CX k) : Prop :=
  e.toRingHom.comp (polynomialY k) = adjacentPolynomial k

def ct : CompletedNode k := toCompleted k (t k)
def cx : CompletedNode k := toCompleted k (x k)
def cy : CompletedNode k := toCompleted k (y k)
/-- Actual adic limit, expressed at all powers of the actual structural ideal. -/
def AdicLimit (f : ℕ → CompletedNode k) (a : CompletedNode k) : Prop :=
  ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → a - f N ∈ (completedIdeal k) ^ n

def gammaPartial (r j N : ℕ) : CompletedNode k :=
  (∏ l ∈ Finset.range N, (1 - ct k ^ (r*l+j) * cx k)) *
  (∏ l ∈ Finset.range N, (1 - ct k ^ (r*(l+1)-j-1) * cy k))
def gammaTailPartial (r j N : ℕ) : CompletedNode k :=
  (∏ l ∈ Finset.range N, if r*l+j = 0 then 1 else (1 - ct k ^ (r*l+j) * cx k)) *
  (∏ l ∈ Finset.range N, if r*(l+1)-j-1 = 0 then 1
    else (1 - ct k ^ (r*(l+1)-j-1) * cy k))
def gammaHorizontal (r j : ℕ) : CompletedNode k :=
  (if j = 0 then 1-cx k else 1) * (if j+1 = r then 1-cy k else 1)

/-- A uniform vertical denominator for the j-th annulus. -/
def thetaShift (j : ℕ) : ℕ := (j+1)^2
/-- q=t^(2*m*d), z=t^j*x; use x^a for a>=0 and y^(-a) for a<0. -/
def thetaExponent (d j : ℕ) (a : ℤ) : ℤ :=
  (thetaShift j : ℤ) + (d : ℤ)*a^2 + (if 0 ≤ a then (j : ℤ)*a else ((j : ℤ)+1)*a)
def thetaTerm (d j : ℕ) (a : ℤ) : CompletedNode k :=
  ct k ^ (thetaExponent d j a).toNat *
    (if 0 ≤ a then cx k ^ a.toNat else cy k ^ (-a).toNat)
def thetaPartial (m d j : ℕ) (nu : ℤ) (N : ℕ) : CompletedNode k :=
  ∑ a ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    if a % (m : ℤ) = nu % (m : ℤ) then thetaTerm k d j a else 0

def ThetaLimit (m d j : ℕ) (nu : ℤ) (s : CompletedNode k) : Prop :=
  AdicLimit k (thetaPartial k m d j nu) s

end ArithmeticThetaAnnularGeometry
