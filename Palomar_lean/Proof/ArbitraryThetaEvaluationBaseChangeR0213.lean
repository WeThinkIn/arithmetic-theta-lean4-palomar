module

public import ArbitraryThetaGeneratorEvaluationR0213
public import ArbitraryThetaLineBaseChangeR0213
public import ThetaEvaluationBaseChangeR0212

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaUniversalEvaluationR0213
open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaThetaEvaluationR0212

/-- The canonical pushforward comparison over arbitrary rational algebras is
invertible and intertwines the actual origin evaluations. -/
theorem arbitrary_theta_evaluation_base_change :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∀ (S : Type u) [CommRing S] [Algebra ℚ S] (V : WeierstrassCurve S) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law S V), ArithmeticThetaRelativeKatoR0169.IsOriginLaw S V H → ∀ (N : ArithmeticThetaFullLevelCoverR0175.FullLevel S V H 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (f : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S V) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι f), ArithmeticThetaRelativeFourCharacterR0211.MarkingCompatible R W G M S V H N ι f → ∀ (q : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (f)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) (ArithmeticThetaThetaEvaluationR0212.thetaLine S V H N)), ArithmeticThetaThetaEvaluationR0212.PreservesThetaSection R W G M S V H N f q → ∀ (eR : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf))) (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin S V)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine S V H N)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base S).ringCatSheaf))), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M eR → ArithmeticThetaThetaEvaluationR0212.IsRigidification S V H N eS → CategoryTheory.IsIso (ArithmeticThetaThetaEvaluationR0212.pushforwardComparison R W G M S V H N ι f hb.1.w q) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaThetaEvaluationR0212.pushforwardComparison R W G M S V H N ι f hb.1.w q) (ArithmeticThetaThetaEvaluationR0212.evaluation S V H N eS) = CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).map (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M eR)) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).hom) := by
  intro R _ _ W _ G hG M S _ _ V _ H hH N ι f hb hm q hq eR eS heR heS
  exact @EvaluationBaseChange.iso_and_naturality
    (Base R).Modules (Base S).Modules _ _ (pullback (baseMap R S ι))
    (𝟙_ (Base R).Modules) (pushforwardLine R W G M)
    (𝟙_ (Base S).Modules) (pushforwardLine S V H N)
    (generator R W G M) (generator S V H N)
    (arbitrary_theta_generator_evaluation R W G hG M).1 (arbitrary_theta_generator_evaluation S V H hH N).1
    (pullbackUnitIso (baseMap R S ι)) (evaluation R W G M eR)
    (evaluation S V H N eS) (pushforwardComparison R W G M S V H N ι f hb.1.w q)
    (IdentityEvaluation.generator_evaluation R W G M eR heR)
    (IdentityEvaluation.generator_evaluation S V H N eS heS)
    (EvaluationBaseChange.comparison_generator R W G M S V H N ι f hb.1.w q hq)

#print axioms arbitrary_theta_evaluation_base_change
end ArithmeticThetaUniversalEvaluationR0213
