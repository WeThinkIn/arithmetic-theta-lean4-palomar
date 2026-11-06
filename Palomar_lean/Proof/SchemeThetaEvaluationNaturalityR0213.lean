module

public import SchemeThetaEvaluationR0213
public import ThetaLineBaseChangeR0212

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaUniversalEvaluationR0213
open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaLocalWeierstrassR0203

namespace SchemeThetaEvaluationNaturality

/-- Cartier cancellation makes the actual section-preserving comparison unique. -/
lemma unique_line_comparison {S T : Scheme.{u}} (E : Family S)
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (F : Family T)
    (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve)
    (hb : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f) :
    ∃! q : (pullback f).obj (thetaLine E M) ≅ thetaLine F N,
      PreservesThetaSection E M F N f q := by
  obtain ⟨q, hq⟩ := SchemeThetaEvaluation.line_comparison E M F N b f hb
  have hL := (SchemeThetaEvaluation.thetaIdeal_invertible E M).isInvertible_invModule
  have hK := (SchemeThetaEvaluation.thetaIdeal_invertible F N).isInvertible_invModule
  let s := pullbackSection f (thetaMap E M)
  have hz : zeroSchemeIdeal s = thetaIdeal F N := by
    rw [← hL.comap_zeroSchemeIdeal, SchemeThetaEvaluation.thetaMap_eq,
      (SchemeThetaEvaluation.thetaIdeal_invertible E M).zeroSchemeIdeal_invModuleSection,
      SchemeThetaEvaluation.thetaIdeal_comap E M F N b f hb]
  have hZ : (zeroSchemeIdeal s).IsInvertible := hz ▸ SchemeThetaEvaluation.thetaIdeal_invertible F N
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  exact ArithmeticThetaThetaEvaluationR0212.ThetaLineBaseChange.section_cancel
    (hL.pullback f) hK s hZ q'.hom q.hom (hq'.trans hq.symm)

/-- The specified canonical pushforward comparison carries the actual generator. -/
lemma comparison_generator {S T : Scheme.{u}} (E : Family S)
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (F : Family T)
    (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (h : f ≫ E.p = F.p ≫ b)
    (q : (pullback f).obj (thetaLine E M) ≅ thetaLine F N)
    (hq : PreservesThetaSection E M F N f q) :
    (pullback b).map (generator E M) ≫ pushforwardComparison E M F N b f h q =
      (pullbackUnitIso b).hom ≫ generator F N := by
  exact ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.base_change_generator
    h (thetaMap E M) (thetaMap F N) q.hom hq

end SchemeThetaEvaluationNaturality

/-- Arbitrary marked Cartesian maps preserve the actual theta ideal and its
canonical section uniquely, and intertwine the adjunction-defined evaluations. -/
theorem scheme_theta_evaluation_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (hb : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f), (ArithmeticThetaUniversalEvaluationR0213.thetaIdeal E M).comap f = ArithmeticThetaUniversalEvaluationR0213.thetaIdeal F N ∧ (∃! q : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M)) (ArithmeticThetaUniversalEvaluationR0213.thetaLine F N), ArithmeticThetaUniversalEvaluationR0213.PreservesThetaSection E M F N f q) ∧ (∀ (q : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M)) (ArithmeticThetaUniversalEvaluationR0213.thetaLine F N)), ArithmeticThetaUniversalEvaluationR0213.PreservesThetaSection E M F N f q → ∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaLocalWeierstrassR0203.Family.zero E)).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaLocalWeierstrassR0203.Family.zero F)).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine F N)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaUniversalEvaluationR0213.IsRigidification E M eS → ArithmeticThetaUniversalEvaluationR0213.IsRigidification F N eT → CategoryTheory.IsIso (ArithmeticThetaUniversalEvaluationR0213.pushforwardComparison E M F N b f hb.1.w q) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaUniversalEvaluationR0213.pushforwardComparison E M F N b f hb.1.w q) (ArithmeticThetaUniversalEvaluationR0213.evaluation F N eT) = CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map (ArithmeticThetaUniversalEvaluationR0213.evaluation E M eS)) (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso b).hom) := by
  intro k _ _ S σ E M T τ F N b f hbase hb
  refine ⟨SchemeThetaEvaluation.thetaIdeal_comap E M F N b f hb,
    SchemeThetaEvaluationNaturality.unique_line_comparison E M F N b f hb, ?_⟩
  intro q hq eS eT heS heT
  exact @ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.iso_and_naturality
    S.Modules T.Modules _ _ (pullback b)
    (𝟙_ S.Modules) (pushforwardLine E M) (𝟙_ T.Modules) (pushforwardLine F N)
    (generator E M) (generator F N)
    (SchemeThetaEvaluation.generator_isIso E M k σ)
    (SchemeThetaEvaluation.generator_isIso F N k τ)
    (pullbackUnitIso b) (evaluation E M eS) (evaluation F N eT)
    (pushforwardComparison E M F N b f hb.1.w q)
    (SchemeThetaEvaluation.generator_evaluation E M eS heS)
    (SchemeThetaEvaluation.generator_evaluation F N eT heT)
    (SchemeThetaEvaluationNaturality.comparison_generator E M F N b f hb.1.w q hq)

#print axioms scheme_theta_evaluation_naturality
end ArithmeticThetaUniversalEvaluationR0213
