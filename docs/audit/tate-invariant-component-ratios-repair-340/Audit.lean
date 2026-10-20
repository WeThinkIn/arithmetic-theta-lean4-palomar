module
import all TateInvariantComponentRatiosR0265
public import Lean
open Lean Elab Command in
elab "#audit340" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Nat := 0
  let some idx := env.getModuleIdx? `TateInvariantComponentRatiosR0265
    | throwError "Module not imported"
  for name in env.header.moduleData[idx]!.constNames do
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail then continue
    let axioms ← collectAxioms name
    checked := checked + 1
    logInfo m!"AXIOM340 {name}: {axioms}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      bad := bad + 1
      logError m!"UNAPPROVED340 {name}: {axioms}"
  logInfo m!"TOTAL340 checked={checked} bad={bad}"
  if checked == 0 then throwError "No module declarations inspected"
  if bad != 0 then throwError "Unexpected axiom closures"
#audit340

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ArithmeticThetaInvariantRatiosR0265
namespace TateInvariantComponentRatios
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaTateSchemeMarkingR0263
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (Vd : TateLevel k (2*m)) {ζ : kˣ}
  (Q : LocalTheta.MarkedModel k m hm Vd ζ) (he : Even m)

open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141 (act)
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141 (sc sc_one)
open ArithmeticThetaGeometricLiftsR0141.GeometricIntertwinerRigidityR0141

example (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (v : GenericDual k Q.model Q.origin m)
    (hv : act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ) v = v) :
    ∃ c : LaurentSeries k, v = sc k Q.model Q.origin m c
      (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ⟨0,hm⟩) := model_fixed k Vd Q he hζ v hv

end TateInvariantComponentRatios
example :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (Vd : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd ζ), ∀ (a : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd))) (b : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd))), ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd Q he hζ a → ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd Q he b → ∀ (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m)), ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd)) a A → ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd)) b B → ArithmeticThetaInvariantRatiosR0265.ComponentRatios (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m hm A B (ArithmeticThetaInvariantRatiosR0265.unaryRatio k m hm) := tate_invariant_component_ratios
end ArithmeticThetaInvariantRatiosR0265
