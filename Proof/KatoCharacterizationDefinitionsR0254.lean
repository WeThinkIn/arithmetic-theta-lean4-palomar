module

public import SchemeKatoNormR0251
public import SchemeKatoUnitUniquenessR0250

@[expose] public section

/-! The restriction of an actual global curve unit to its torsion complement.
No normalization, divisor equation, norm equation or theorem is assumed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaKatoCharacterizationR0254
open AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeKatoUnitR0250

abbrev GlobalUnits {S : Scheme.{u}} (E : Family S) :=
  (E.curve.presheaf.obj (Opposite.op ⊤))ˣ

def restrictGlobal {S : Scheme.{u}} (E : Family S) (c : ℕ)
    (a : GlobalUnits E) : E.curve.presheaf.obj (Opposite.op (complement E c)) :=
  ArithmeticThetaArbitraryKatoUnitR0249.restrict ⊤ (complement E c) le_top (a : _)

end ArithmeticThetaKatoCharacterizationR0254
