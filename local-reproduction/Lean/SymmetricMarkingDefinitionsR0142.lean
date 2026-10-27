import GeometricScalarLiftR0141
import GeometricShiftLiftR0141
import GeometricInversionLiftR0141
import GeometricThetaRelationsR0141
import GeometricBasisProjectiveValuesR0141
import AlgebraizedGeometricConnectednessR0135

/-! Comparison predicates for genuine sheaf lifts on the accepted generic model.
The constant field map is fixed; no comparison scalar is assumed to exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSymmetricMarkingR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def constant (c : k) : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C c)

/-- Equality on every local section of the actual sheaf, not only on H⁰. -/
def LiftScaled (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M) (c : LaurentSeries k)
    (e e' : Lift k M s d f) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)),
    e'.hom.app U x = scalarAt k M U c • e.hom.app U x

/-- Inversion conjugates the induced actual pullback action to its inverse. -/
def Symmetric (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f fS : genericScheme k M ⟶ genericScheme k M)
    (eS : Lift k M s d fS) (e : Lift k M s d f) : Prop :=
  ∀ φ : GenericDual k M s d,
    act k M s d fS eS (act k M s d f e
      (act k M s d fS eS (act k M s d f e φ))) = φ

/-- Residue translation, with the same positive level used by the theta basis. -/
def shiftIndex (m : ℕ) (hm : 0 < m) (j ν : Fin m) : Fin m :=
  ⟨(ν.val + j.val) % m, Nat.mod_lt _ hm⟩

/-- The finite sign and residue correction acts on the actual sheaf sections. -/
def rephase (M : Model k T) (s : baseScheme k ⟶ M.X) (m : ℕ) (hm : 0 < m)
    (δ : k) (j : Fin m) (β : Fin m → GenericDual k M s m) :
    Fin m → GenericDual k M s m := fun ν =>
  ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140.scale
    (scalarAt k M ⊤ (constant k (δ ^ ν.val))) (β (shiftIndex m hm j ν))

end ArithmeticThetaSymmetricMarkingR0142
