module

public import SchemeFourCharacterDefinitionsR0215
public import AffineConormalHodgeNaturalityR0205
public import CartesianIdentityIdealR0205

@[expose] public section

/-! Marked affine coverage and the canonical identity-ideal comparison on every test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205

namespace MarkedAffineTestComparison

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- Retain the test curve, structural map and group law, with geometry pulled
back along its given Cartesian square. -/
def family (P : AffineTest E M) : Family (Base P.ring) where
  curve := ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation
  p := ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation
  law :=
    { mul := P.law.mul, one := P.law.one, inv := P.law.inv
      mul_assoc := P.law.mul_assoc, one_mul := P.law.one_mul
      mul_one := P.law.mul_one, inv_mul_cancel := P.law.inv_mul_cancel
      mul_comm := P.originLaw.2, mul_natural := P.law.mul_natural }
  proper := MorphismProperty.of_isPullback P.cartesian E.proper
  dimension := by
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.of_isPullback P.cartesian E.dimension
  connected := MorphismProperty.of_isPullback P.cartesian E.connected

lemma family_zero (P : AffineTest E M) : (family E M P).zero =
    ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation := by
  change (P.law.one (𝟙 (Base P.ring))).val = _
  simpa only [Category.id_comp] using P.originLaw.1 (𝟙 (Base P.ring))

/-- The accepted unique ideal comparison, transported along the actual origin equality. -/
lemma ideal_comparison (P : AffineTest E M) :
    ∃! i : (Scheme.Modules.pullback P.comparison).obj E.zero.ker.module ≅
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module,
      AffineIdealCompatible E M P i := by
  have hz : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  have h := cartesian_identity_ideal S (Base P.ring) E (family E M P)
    P.base P.comparison P.cartesian hz
  unfold IdealCompatible at h
  rw [family_zero E M P] at h
  exact h

/-- Invertibility concerns the specified derivative, not a chosen frame. -/
lemma hodge_isIso (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj E.zero.ker.module ≅
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module) :
    IsIso (affineHodgeMap E M P i) := by
  have h := AffineConormalHodgeNaturality.differential_isIso (family E M P)
  haveI : IsIso
      (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap
        (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation)
        (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)) := by
    change IsIso (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap
      (family E M P).p (family E M P).zero) at h
    rw [family_zero E M P] at h
    exact h
  unfold affineHodgeMap
  infer_instance

/-- Lift both marked sections on each accepted local Weierstrass chart. -/
lemma coverage (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) (s : S) :
    ∃ P : AffineTest E M, IsOpenImmersion P.base ∧ s ∈ Set.range P.base := by
  obtain ⟨P, hs⟩ := scheme_local_weierstrass k S σ E s
  letI := P.commRing
  letI := P.algebra
  letI : Algebra ℚ P.ring := Algebra.compHom P.ring (algebraMap ℚ k)
  have hz : (SchemeLocalClassifier.family P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [SchemeLocalClassifier.family_zero]
    exact P.zero_eq
  obtain ⟨N, hN, _⟩ := cartesian_full_marking S (Base P.ring) E
    (SchemeLocalClassifier.family P) P.base P.comparison P.cartesian hz P.mul_eq 4 M
  exact ⟨{ ring := P.ring, equation := P.equation, elliptic := P.elliptic
           law := P.law, originLaw := P.originLaw, base := P.base
           comparison := P.comparison, cartesian := P.cartesian
           zero_eq := P.zero_eq, mul_eq := P.mul_eq
           level := SchemeLocalClassifier.affineLevel P N
           x_eq := hN.1, y_eq := hN.2 }, P.openImmersion, hs⟩

end MarkedAffineTestComparison

/-- Cover every base point and compare the identity cotangent on every affine test. -/
theorem marked_affine_test_comparison :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∀ s : S, ∃ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, AlgebraicGeometry.IsOpenImmersion P.base ∧ s ∈ Set.range P.base) ∧ (∀ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, ∃! i : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback P.comparison).obj (ArithmeticThetaLocalWeierstrassR0203.Family.zero E).ker.module) ((ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker.module), ArithmeticThetaSchemeFourCharacterR0215.AffineIdealCompatible E M P i ∧ CategoryTheory.IsIso (ArithmeticThetaSchemeFourCharacterR0215.affineHodgeMap E M P i)) := by
  intro k _ _ S σ E M
  constructor
  · exact MarkedAffineTestComparison.coverage E M k σ
  · intro P
    obtain ⟨i, hi, hu⟩ := MarkedAffineTestComparison.ideal_comparison E M P
    exact ⟨i, ⟨hi, MarkedAffineTestComparison.hodge_isIso E M P i⟩,
      fun j hj => hu j hj.1⟩

#print axioms marked_affine_test_comparison
end ArithmeticThetaSchemeFourCharacterR0215
