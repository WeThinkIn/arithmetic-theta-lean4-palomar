module
public import Mathlib
public import TateBasicFourthIdentity
public import TateGeneralAddition

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarFormal261Tate

namespace Tate

variable {k : Type u} [Field k]

/-- a*t^n in the actual power series ring. -/
def monomial (a : k) (n : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ n

/-- v/(1-v)^2, using the formal power-series inverse. -/
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2

/-- z*d/dz of xTerm(z); evaluated at the annular monomial. -/
def yTerm (v : PowerSeries k) : PowerSeries k := v * (1+v) * ((1-v)⁻¹)^3

/-- r=0 plus the two tails for 1≤r≤N, including the normalization correction. -/
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  xTerm (monomial a i) +
  (∑ j ∈ Finset.range N,
    (xTerm (monomial a (d*(j+1)+i)) +
     xTerm (monomial a⁻¹ (d*(j+1)-i)))) -
  2 * ∑ j ∈ Finset.range N,
    PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1 - monomial 1 (d*(j+1)))⁻¹

/-- One half the logarithmic z-derivative; the negative tail has a minus sign. -/
def partialY (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  PowerSeries.C (2 : k)⁻¹ *
    (yTerm (monomial a i) + ∑ j ∈ Finset.range N,
      (yTerm (monomial a (d*(j+1)+i)) -
       yTerm (monomial a⁻¹ (d*(j+1)-i))))

/-- Stable coefficient candidates; stabilization is a new theorem obligation. -/
def tateX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
def tateY (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialY d i a (n+1))

/-- Q=t^d, z=a*t^i avoiding the identity representative. -/
def Admissible (d i : ℕ) (a : k) : Prop :=
  0 < d ∧ i < d ∧ a ≠ 0 ∧ (i = 0 → a ≠ 1)

/-- The actual series ∑_{r∈ℤ} t^(r²), with the zero index counted once. -/
def theta (k : Type u) [Field k] : PowerSeries k :=
  PowerSeries.mk fun n => (if n = 0 then 1 else 0) +
    2 * ((Finset.filter (fun j : ℕ => j^2 = n) (Finset.Icc 1 n)).card : k)

/-- Exact equality of all coefficients below N; O(t^N) has no analytic meaning here. -/
def AgreeBelow (N : ℕ) (f g : PowerSeries k) : Prop :=
  ∀ n : ℕ, n < N → PowerSeries.coeff n f = PowerSeries.coeff n g

/-- The specified q=s², Q=s⁴ marking, so s is the source's q^(1/2). -/
def e₁ (k : Type u) [Field k] : PowerSeries k := tateX 4 0 (-1)
def e₂ (k : Type u) [Field k] : PowerSeries k := tateX 4 2 1
def e₃ (k : Type u) [Field k] : PowerSeries k := tateX 4 2 (-1)
def xR (k : Type u) [Field k] : PowerSeries k := tateX 4 1 1
def yR (k : Type u) [Field k] : PowerSeries k := tateY 4 1 1

/-- Genuine power-series inclusion into its Laurent-series fraction field. -/
def toLaurent (k : Type u) [Field k] : PowerSeries k →+* LaurentSeries k :=
  HahnSeries.ofPowerSeries ℤ k

/-- Literal source rational expression; division takes place in k((s)). -/
def markedRoot (k : Type u) [Field k] : LaurentSeries k :=
  let j := toLaurent k
  ((j (xR k) - j (e₁ k))^2 -
    (j (e₁ k) - j (e₂ k)) * (j (e₁ k) - j (e₃ k))) / (2*j (yR k))


end Tate

namespace Gamma
noncomputable def partialGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) (N : ℕ) : PowerSeries R :=
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (d * r + i))) *
  (∏ r ∈ Finset.range N, (1 - PowerSeries.C b * PowerSeries.X ^ (d * (r + 1) - i)))

noncomputable def fullGamma {R : Type*} [CommRing R] (d i : ℕ) (a b : R) : PowerSeries R :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (partialGamma d i a b (n + 1)))


end Gamma

namespace UnaryProduct
noncomputable def etaPartial (D N : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range N, (1-PowerSeries.X^(D*(j+1)))
noncomputable def etaProduct (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (etaPartial D d))

end UnaryProduct

namespace Identities
variable {k : Type u} [Field k]

def gammaLaurent (d : ℕ) (i : ℤ) (a : k) : LaurentSeries k :=
  let h := i / (d : ℤ)
  let r := i % (d : ℤ)
  HahnSeries.single (-r*h - (d : ℤ)*(h*(h-1)/2)) ((-a)^(-h)) *
    ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k
      (ArithmeticThetaPalomarFormal261Tate.Gamma.fullGamma d r.toNat a a⁻¹)


end Identities


/-- Exact independent target: accepted-018. -/
theorem basic_fourth :
  ∀ {k : Type u} [Field k] [CharZero k], ArithmeticThetaPalomarFormal261Tate.Tate.theta k ^ 4 = 4 * (ArithmeticThetaPalomarFormal261Tate.Tate.tateX 2 1 (1:k) - ArithmeticThetaPalomarFormal261Tate.Tate.tateX 2 0 (-1:k)) := by
  exact ArithmeticThetaTateSeries.basic_fourth

/-- Exact independent target: accepted-089. -/
theorem general_annular_addition :
  ∀ {k : Type u} [Field k] [CharZero k], ∀ (d i j : ℕ) (a b : k), ArithmeticThetaPalomarFormal261Tate.Tate.Admissible d i a → ArithmeticThetaPalomarFormal261Tate.Tate.Admissible d j b → (ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (ArithmeticThetaPalomarFormal261Tate.Tate.tateX d i (a : k)) - ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (ArithmeticThetaPalomarFormal261Tate.Tate.tateX d j (b : k))) * (ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d (i:ℤ) a)^2 * (ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d (j:ℤ) b)^2 = -HahnSeries.single (j:ℤ) b * (ArithmeticThetaPalomarFormal261Tate.Tate.toLaurent k (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaPalomarFormal261Tate.UnaryProduct.etaProduct d)))^4 * ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d ((i:ℤ)-(j:ℤ)) (a/b) * ArithmeticThetaPalomarFormal261Tate.Identities.gammaLaurent d ((i:ℤ)+(j:ℤ)) (a*b) := by
  exact ArithmeticThetaTateIdentities.general_annular_addition

end ArithmeticThetaPalomarFormal261Tate
#print axioms ArithmeticThetaPalomarFormal261Tate.basic_fourth
#print axioms ArithmeticThetaPalomarFormal261Tate.general_annular_addition
