module
import all RelativePrimitiveThetaCommutatorR0256
public import Lean
open Lean Elab Command in
elab "#audit329" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Nat := 0
  let some idx := env.getModuleIdx? `RelativePrimitiveThetaCommutatorR0256
    | throwError "Module not imported"
  for name in env.header.moduleData[idx]!.constNames do
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail then continue
    let axioms ← collectAxioms name
    checked := checked + 1
    logInfo m!"AXIOM329 {name}: {axioms}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      bad := bad + 1
      logError m!"UNAPPROVED329 {name}: {axioms}"
  logInfo m!"TOTAL329 checked={checked} bad={bad}"
  if checked == 0 then throwError "No module declarations inspected"
  if bad != 0 then throwError "Unexpected axiom closures"
#audit329

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeThetaRelationsR0256
open RelativePrimitiveThetaCommutator
set_option autoImplicit false
universe u
example {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (𝟙 X ≫ f)).obj M) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app M = eqToHom q :=
  pullback_left_unit f M q

example :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R), ∀ m : ℕ, 0 < m → Even m → ∀ M : ArithmeticThetaLegendreAtlasR0176.FamilyLevel R E (2*m), ∀ (α : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E M.x)) (β : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E M.y)), ∃! c : Rˣ, ArithmeticThetaRelativeThetaRelationsR0256.Commutator E m M.x M.y α β c ∧ ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c := relative_primitive_theta_commutator
