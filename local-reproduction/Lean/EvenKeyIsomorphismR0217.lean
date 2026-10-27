import EvenPointThetaEvaluationR0217
import AlphaTensorDescentR0217

/-! The fixed-pairing key map is the unique isomorphism between the actual
inverse-square evaluation frame and the descended intrinsic alpha frame. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMultiplierKeyR0217

/-- The algebraic key isomorphism with the prescribed evaluation normalization. -/
theorem even_key_isomorphism :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ∀ (L : S.Modules) (m : ((AlgebraicGeometry.Scheme.Modules.pullback D.projection).obj (L)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.Multiplier E D z L m → ∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∀ β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤), ArithmeticThetaMultiplierKeyR0217.DescendsAlpha E D L m β → ∃! κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ := by
  intro k _ _ S σ E P z hz D hD L m hm e he β hβ
  have heval := ((even_point_theta_evaluation k S σ E P).2.2.2.2.2 e he).2.2
  have hsquare : ArithmeticThetaRelativeDiscriminantR0171.IsFrame
      (inverseSquare E P) ⊤ (evaluationSquare E P e) :=
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorPower_frame
      (AlgebraicGeometry.Scheme.Modules.dual (pushforwardLine E P))
      (evaluationSection E P e) heval 2
  have hframe := (alpha_tensor_descent k S σ E P z hz D hD L m hm).2 β hβ
  exact InverseCharacterMultiplier.existsUnique_frame_iso
    (inverseSquare E P) (productLine E L) (evaluationSquare E P e) β hsquare hframe

#print axioms even_key_isomorphism
end ArithmeticThetaMultiplierKeyR0217
