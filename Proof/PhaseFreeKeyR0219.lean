module

public import PhaseFreeAlphaDescentR0219
public import EvenPointThetaEvaluationR0217

@[expose] public section

/-! The phase-free key isomorphism is determined by the actual evaluation square
and the descended alpha tensor, both of which are global frames. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaMultiplierKeyR0217

/-- The unique algebraic key map with its prescribed identity-evaluation normalization,
without a chosen global phase. -/
theorem phase_free_key :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∃! κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ := by
  intro k _ _ S σ E P L m hm β hβ e he
  have heval := ((even_point_theta_evaluation k S σ E P).2.2.2.2.2 e he).2.2
  have hsquare : ArithmeticThetaRelativeDiscriminantR0171.IsFrame
      (inverseSquare E P) ⊤ (evaluationSquare E P e) :=
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorPower_frame
      (AlgebraicGeometry.Scheme.Modules.dual (pushforwardLine E P))
      (evaluationSection E P e) heval 2
  have hframe := (phase_free_alpha_descent k S σ E P L m hm).2 β hβ
  exact InverseCharacterMultiplier.existsUnique_frame_iso
    (inverseSquare E P) (productLine E L) (evaluationSquare E P e) β hsquare hframe

#print axioms phase_free_key
end ArithmeticThetaPhaseFreeKeyR0219
