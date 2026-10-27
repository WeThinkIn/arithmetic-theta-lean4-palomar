import TateSeriesDefinitions
import FormalNormDefinitions
import UnaryThetaProduct

/-! Ordinary definitions for the next, unproved formal Tate identities.
For Q=t^d and z=a*t^i, write i=h*d+r with 0≤r<d. The Laurent extension
is the finite monomial correction in gamma_Q(Q^h*z)=
(-z)^(-h)*Q^(-h*(h-1)/2)*gamma_Q(z). All identities using this extension
are separate obligations. No geometric algebraization is encoded here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaTateIdentities
variable {k : Type u} [Field k]

def gammaLaurent (d : ℕ) (i : ℤ) (a : k) : LaurentSeries k :=
  let h := i / (d : ℤ)
  let r := i % (d : ℤ)
  HahnSeries.single (-r*h - (d : ℤ)*(h*(h-1)/2)) ((-a)^(-h)) *
    ArithmeticThetaTateSeries.toLaurent k
      (ArithmeticThetaFormalNorm.fullGamma d r.toNat a a⁻¹)

end ArithmeticThetaTateIdentities
