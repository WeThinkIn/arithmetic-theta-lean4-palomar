module
import all SchemeThetaIdentityEvaluationR0261
public import Lean
open Lean Elab Command in
elab "#audit335" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Nat := 0
  let some idx := env.getModuleIdx? `SchemeThetaIdentityEvaluationR0261
    | throwError "Module not imported"
  for name in env.header.moduleData[idx]!.constNames do
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail then continue
    let axioms ← collectAxioms name
    checked := checked + 1
    logInfo m!"AXIOM335 {name}: {axioms}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      bad := bad + 1
      logError m!"UNAPPROVED335 {name}: {axioms}"
  logInfo m!"TOTAL335 checked={checked} bad={bad}"
  if checked == 0 then throwError "No module declarations inspected"
  if bad != 0 then throwError "Unexpected axiom closures"
#audit335

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open ArithmeticThetaSchemeSchrodingerR0261 SchemeThetaIdentityEvaluation
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeThetaMarkingR0259
open Scheme.Modules
attribute [local instance] SchemeLocal.FramedChart.commRing
set_option autoImplicit false
noncomputable section
universe u
example (X : Scheme.{u}) (m : ℕ) : (𝟙_ X.Modules).tensorPow m ≅ 𝟙_ X.Modules := unitPowerIso X m
example {S : Scheme.{u}} (E : Family S) (C : SchemeLocal.FramedChart E) (m : ℕ) :
    (ArithmeticThetaSchemeHodgeR0205.Cotangent (chartFamily E C)).tensorPow m ≅
      𝟙_ (Base C.ring).Modules := chartHodgePowerFrame E C m
example (X : Scheme.{u}) : unitPowerIso X 0 = Iso.refl _ := rfl
example (X : Scheme.{u}) (m : ℕ) :
    unitPowerIso X (m+1) = ((unitPowerIso X m) ⊗ᵢ Iso.refl _) ≪≫ ρ_ _ := rfl

example :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ∀ E : ArithmeticThetaLocalWeierstrassR0203.Family S, ∀ (m : ℕ), 2 ≤ m →
        CategoryTheory.Epi (ArithmeticThetaSchemeSchrodingerR0261.evaluation E m) := scheme_theta_identity_evaluation
