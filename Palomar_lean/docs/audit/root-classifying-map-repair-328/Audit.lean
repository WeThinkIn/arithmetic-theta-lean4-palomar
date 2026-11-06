module
import all RootClassifyingMapR0199
public import Lean
open Lean Elab Command in
elab "#audit328" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Nat := 0
  let some idx := env.getModuleIdx? `RootClassifyingMapR0199
    | throwError "Module not imported"
  for name in env.header.moduleData[idx]!.constNames do
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail then continue
    let axioms ← collectAxioms name
    checked := checked + 1
    logInfo m!"AXIOM328 {name}: {axioms}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      bad := bad + 1
      logError m!"UNAPPROVED328 {name}: {axioms}"
  logInfo m!"TOTAL328 checked={checked} bad={bad}"
  if checked == 0 then throwError "No module declarations inspected"
  if bad != 0 then throwError "Unexpected axiom closures"
#audit328

open CategoryTheory AlgebraicGeometry ArithmeticThetaStackLevelR0199
open ArithmeticThetaRootStackR0198 ArithmeticThetaSquareLinesR0192
open Bicategory
attribute [local instance] CategoryTheory.uliftCategory
set_option autoImplicit false
noncomputable section
universe u
example {B : Scheme.{0}} (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0,1})
    (Y : Over B) (x : F.obj (.mk (.op Y))) (S : Over B) :
    Points S Y ⥤ F.obj (.mk (.op S)) := RootClassifyingMapR0199.component F Y x S
example {B : Scheme.{0}} (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0,1})
    (Y : Over B) (x : F.obj (.mk (.op Y))) {S T : Over B} (a : S ⟶ T) :
    precompose Y a ⋙ RootClassifyingMapR0199.component F Y x S ≅
      RootClassifyingMapR0199.component F Y x T ⋙ (F.map a.op.toLoc).toFunctor :=
  RootClassifyingMapR0199.comparison F Y x a
example {B : Scheme.{0}} (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0,1})
    (Y : Over B) (x : F.obj (.mk (.op Y))) :
    Pseudofunctor.StrongTrans (representable Y) F := RootClassifyingMapR0199.classify F Y x
example (B : Scheme.{0}) (W : B.Modules) (P : Presentation B W)
    (Y : Over B) (H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)) :
    Nonempty (ClassifiedMap P Y H) := root_classifying_map B W P Y H
example {B : Scheme.{0}} {S Y : Over B} (x y : Points S Y) :
    (x ⟶ y) = Discrete.Hom x.down.as y.down.as := rfl
