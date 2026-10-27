import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaEvenMarkingTorsorR0216
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaMultiplierKeyR0217
run_cmd Lean.activateScoped `ArithmeticThetaPhaseFreeKeyR0219
run_cmd Lean.activateScoped `ArithmeticThetaSchemeHodgeR0205
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `F
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `P
run_cmd Lean.activateScoped `P.point
run_cmd Lean.activateScoped `Q
run_cmd Lean.activateScoped `Q.point
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `SheafOfModules
run_cmd Lean.activateScoped `T
run_cmd Lean.activateScoped `j
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaPhaseFreeKeyR0219.phase_free_key_naturality)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∀ (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 c → ∀ (v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K), ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaMultiplierKeyR0217.productLine F K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ArithmeticThetaPhaseFreeKeyR0219.Descends F Q K n γ → ArithmeticThetaMultiplierKeyR0217.AlphaNatural E F b L K c v β γ ∧ (∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine F Q)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P eS → ArithmeticThetaMultiplierKeyR0217.IsRigidification F Q eT → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)) (κT : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q) (ArithmeticThetaMultiplierKeyR0217.productLine F K)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L eS β κ → ArithmeticThetaMultiplierKeyR0217.IsKey F Q K eT γ κT → (∃! j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j) ∧ (∀ j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j → CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map κ.hom) (ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v).hom = CategoryTheory.CategoryStruct.comp j.hom κT.hom))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaPhaseFreeKeyR0219.phase_free_key_naturality
