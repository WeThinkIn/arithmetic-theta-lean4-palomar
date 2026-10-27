import TateXNumeratorSystemR0143
import TateYNumeratorSystemR0143

/-! Algebraization of both literal Tate coordinate systems on every marked proper model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaAlgebraicCoordinatesR0143
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138

/-- The complete prescribed numerators determine a unique actual sheaf map
from the second or third power of the marked identity ideal to the structure sheaf. -/
theorem algebraic_tate_coordinates :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
      (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s),
      ∀ odd : Bool, ∃! φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s
        (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd),
        ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ := by
  intro k _ _ r hr h3 T M hM s hs odd
  have hc : CompatibleSystem k odd T := by
    cases odd with
    | false => exact tate_x_numerator_system k r hr h3 T
    | true => exact tate_y_numerator_system k r hr h3 T
  let v : FormalNumerators k (T := T) (degree odd) :=
    ⟨fun n => ⟨numerator k odd r n, hc.1 n⟩, hc.2⟩
  exact algebraize_formal k h3 M hM s hs (degree odd) v

end ArithmeticThetaAlgebraicCoordinatesR0143

#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates
