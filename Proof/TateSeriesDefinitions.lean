module

public import Mathlib

@[expose] public section

/-! Literal coefficientwise Tate annular sums from manuscript lines 659–687.
The formal variable is t; Q=t^d and z=a*t^i, 0≤i<d. Negative-index terms
are rewritten by v/(1-v)^2 = v⁻¹/(1-v⁻¹)^2. No identity is assumed.
Only the stated admissible range is used in proof obligations. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaTateSeries

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

end ArithmeticThetaTateSeries
