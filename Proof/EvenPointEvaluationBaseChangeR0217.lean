module

public import EvenPointThetaEvaluationR0217
public import ThetaEvaluationBaseChangeR0212
public import ThetaLineBaseChangeR0212

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaRelativeDiscriminantR0171
open Scheme.Modules

namespace EvenPointEvaluationBaseChange

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

lemma unique_line_comparison {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (h : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val) :
    ∃! q : (pullback f).obj (thetaLine E P) ≅ thetaLine F Q,
      PreservesThetaSection E P F Q f q := by
  obtain ⟨q, hq⟩ := EvenPointThetaEvaluation.line_comparison E P F Q b f h hQ
  have hL := (EvenPointThetaEvaluation.thetaIdeal_invertible E P).isInvertible_invModule
  have hK := (EvenPointThetaEvaluation.thetaIdeal_invertible F Q).isInvertible_invModule
  let s := pullbackSection f (thetaMap E P)
  have hz : zeroSchemeIdeal s = thetaIdeal F Q := by
    rw [← hL.comap_zeroSchemeIdeal, EvenPointThetaEvaluation.thetaMap_eq,
      (EvenPointThetaEvaluation.thetaIdeal_invertible E P).zeroSchemeIdeal_invModuleSection,
      EvenPointThetaEvaluation.thetaIdeal_comap E P F Q b f h hQ]
  have hZ : (zeroSchemeIdeal s).IsInvertible := hz ▸ EvenPointThetaEvaluation.thetaIdeal_invertible F Q
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  exact ArithmeticThetaThetaEvaluationR0212.ThetaLineBaseChange.section_cancel
    (hL.pullback f) hK s hZ q'.hom q.hom (hq'.trans hq.symm)

lemma comparison_generator {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (h : f ≫ E.p = F.p ≫ b)
    (q : (pullback f).obj (thetaLine E P) ≅ thetaLine F Q)
    (hq : PreservesThetaSection E P F Q f q) :
    (pullback b).map (generator E P) ≫ pushforwardComparison E P F Q b f h q =
      (pullbackUnitIso b).hom ≫ generator F Q := by
  exact ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.base_change_generator
    h (thetaMap E P) (thetaMap F Q) q.hom hq

end EvenPointEvaluationBaseChange

theorem even_point_evaluation_base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : Family S) (P : EvenPoint E),
      ∀ (T : Scheme.{u}) (F : Family T) (Q : EvenPoint F)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve)
      (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f),
      Q.point.val ≫ f = b ≫ P.point.val →
      (thetaIdeal E P).comap f = thetaIdeal F Q ∧
      (∃! q : Iso ((pullback f).obj (thetaLine E P)) (thetaLine F Q),
        PreservesThetaSection E P F Q f q) ∧
      (∀ q : Iso ((pullback f).obj (thetaLine E P)) (thetaLine F Q),
        PreservesThetaSection E P F Q f q →
        ∀ (eS : Iso ((pullback E.zero).obj (thetaLine E P))
          (SheafOfModules.unit S.ringCatSheaf))
          (eT : Iso ((pullback F.zero).obj (thetaLine F Q))
            (SheafOfModules.unit T.ringCatSheaf)),
          IsRigidification E P eS → IsRigidification F Q eT →
          IsIso (pushforwardComparison E P F Q b f hb.1.w q) ∧
          pushforwardComparison E P F Q b f hb.1.w q ≫ evaluation F Q eT =
            (pullback b).map (evaluation E P eS) ≫
              (pullbackUnitIso b).hom) := by
  intro k _ _ S σ E P T F Q b f hb hQ
  have hI := EvenPointThetaEvaluation.thetaIdeal_comap E P F Q b f hb hQ
  refine ⟨hI, EvenPointEvaluationBaseChange.unique_line_comparison E P F Q b f hb hQ, ?_⟩
  intro q hq eS eT heS heT
  have hE := even_point_theta_evaluation k S σ E P
  have hF := even_point_theta_evaluation k T (b ≫ σ) F Q
  letI : IsIso (generator E P) := hE.2.2.2.2.1
  letI : IsIso (generator F Q) := hF.2.2.2.2.1
  exact @ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.iso_and_naturality
    S.Modules T.Modules _ _ (pullback b)
    (𝟙_ S.Modules) (pushforwardLine E P)
    (𝟙_ T.Modules) (pushforwardLine F Q)
    (generator E P) (generator F Q)
    (by infer_instance) (by infer_instance)
    (pullbackUnitIso b) (evaluation E P eS) (evaluation F Q eT)
    (pushforwardComparison E P F Q b f hb.1.w q)
    (EvenPointThetaEvaluation.generator_evaluation E P eS heS)
    (EvenPointThetaEvaluation.generator_evaluation F Q eT heT)
    (EvenPointEvaluationBaseChange.comparison_generator E P F Q b f hb.1.w q hq)

#print axioms even_point_evaluation_base_change
end ArithmeticThetaMultiplierKeyR0217
