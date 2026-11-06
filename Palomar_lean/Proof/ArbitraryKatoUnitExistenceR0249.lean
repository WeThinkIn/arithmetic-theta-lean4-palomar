module

public import NormalModelUnitSpecializationR0249
public import NormalModelUnitIndependenceR0249
public import NormalDiscriminantModelR0243

@[expose] public section

/-! Canonical full Kato units over arbitrary rational-algebra elliptic bases. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaArbitraryKatoUnitR0249
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaArbitraryDiscriminantR0243

/-- A normal model exists for every elliptic target. Its specialized unit
agrees with every other normal model, and this condition determines it uniquely. -/
theorem arbitrary_kato_unit_existence :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
      [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∃! v : UnitSection R W G c, IsKatoUnit R W G c v := by
  intro R _ _ W _ G hG c hc hc6
  obtain ⟨M⟩ := normal_discriminant_model R W
  obtain ⟨v, hv, hv_unique⟩ := normal_model_unit_specialization R W G hG c hc hc6 M
  refine ⟨v, ?_, ?_⟩
  · intro N
    obtain ⟨w, hw, _⟩ := normal_model_unit_specialization R W G hG c hc hc6 N
    have h : v = w := normal_model_unit_independence R W G hG c hc hc6 M N v w hv hw
    exact h.symm ▸ hw
  · intro w hw
    exact hv_unique w (hw M)

end ArithmeticThetaArbitraryKatoUnitR0249

#print axioms ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_existence
