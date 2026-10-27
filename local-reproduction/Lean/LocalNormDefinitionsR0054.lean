import PoweredGammaLocalDivisorR0053
import GeometricTorsionChartSectionsR0053
import ScaledGammaUnitProductR0050

/-! Literal local factors of the manuscript's f_c on the completed r-gon charts.
No period quotient, Kato function, or global divisor is postulated here. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

open ArithmeticThetaAnnularTorsionPrereqR0053

variable (k : Type u) [Field k] [CharZero k]

abbrev Chart := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev GenericChart := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k

def gammaHorizontal (r j : ℕ) : Chart k :=
  ArithmeticThetaScaledAnnularR0050.gammaHorizontal k 1 r j

def gammaUnit (r j : ℕ) (hr : 0 < r) (hj : j < r) : Chart k :=
  Classical.choose (ArithmeticThetaScaledAnnularR0050.gamma_unit_product
    k 1 r j (by omega) (by omega))

def gammaLocal (r j : ℕ) (hr : 0 < r) (hj : j < r) : GenericChart k :=
  toGeneric k (gammaHorizontal k r j * gammaUnit k r j hr hj)

def poweredLocal (r c j : ℕ) (ζ : k)
    (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < r) : GenericChart k :=
  Classical.choose (powered_gamma_local_divisor k r c j ζ hr hc hdiv hcop hζ hj)

def localZ (j : ℕ) : GenericChart k :=
  toGeneric k (chartCoordinate k j)

def localNumerator (c j : ℕ) (ζ : k)
    (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2 * c) : GenericChart k :=
  let r := 2 * c
  tpower k (((r * (c ^ 2 - 1)) / 12 : ℕ) : ℤ) *
    (gammaLocal k r j (by omega) hj) ^ (c ^ 2)

def localDenominator (c j : ℕ) (ζ : k)
    (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2 * c) : GenericChart k :=
  let r := 2 * c
  (-localZ k j) ^ (c * (c - 1) / 2) *
    poweredLocal k r c j ζ (by omega) hc (by simp [r]) hcop hζ hj

end ArithmeticThetaLocalNormR0054
