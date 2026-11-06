module

public import CartesianFullMarkingR0204
public import ArbitraryAffineClassificationR0202
public import SchemeLocalWeierstrassR0203

@[expose] public section

/-! Local classification of general marked elliptic families in the fixed quotient. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

namespace SchemeLocalClassifier
variable {k : Type u} [Field k] {S : Scheme.{u}} {σ : S ⟶ Base k}
  {E : Family S} (P : LocalPresentation k S σ E)

/-- The presented curve retains its given law and its actual Cartesian geometry. -/
def family : Family (Base P.ring) where
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

lemma family_zero : (family P).zero =
    ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation := by
  change (P.law.one (𝟙 (Base P.ring))).val = _
  simpa only [Category.id_comp] using P.originLaw.1 (𝟙 (Base P.ring))

/-- The two recursive multiplication interfaces agree on every test scheme. -/
lemma multiple_eq {T : Scheme.{u}} (t : T ⟶ Base P.ring)
    (n : ℕ) (x : SchemeHomOver t (family P).p) :
    multiple (family P) t n x = P.law.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.law.mul t (multiple (family P) t n x) x =
      P.law.mul t (P.law.nsmul t n x) x
    rw [ih]

/-- Convert a transported full marking without changing either actual section. -/
def affineLevel {L : ℕ} (N : FullLevel (family P) L) :
    ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law L
      (𝟙 (Base P.ring)) where
  x := N.x
  y := N.y
  killed_x := by rw [← multiple_eq]; exact N.killed_x
  killed_y := by rw [← multiple_eq]; exact N.killed_y
  avoids := by
    intro i j hij
    have h := N.avoids i j hij
    rw [multiple_eq, multiple_eq, family_zero] at h
    exact h

end SchemeLocalClassifier

/-- Every base point has an affine classifier in the same compatible quotient. -/
theorem scheme_local_classifier :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
      (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A),
      ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B →
      ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
        (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
        (S : AlgebraicGeometry.Scheme.{u})
        (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
        (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
        (M : ArithmeticThetaSchemeLevelR0204.FullLevel E L) (s : S),
        ∃ D : ArithmeticThetaSchemeLevelR0204.LocalClassifier k L A B C Q σ E M,
          s ∈ Set.range D.presentation.base := by
  intro k _ _ L hL heven A B hB C Q S σ E M s
  obtain ⟨P, hs⟩ := scheme_local_weierstrass k S σ E s
  have hz : (SchemeLocalClassifier.family P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [SchemeLocalClassifier.family_zero]
    exact P.zero_eq
  obtain ⟨N, hx, _⟩ := cartesian_full_marking S (Base P.ring) E
    (SchemeLocalClassifier.family P) P.base P.comparison P.cartesian hz P.mul_eq L M
  let level := SchemeLocalClassifier.affineLevel P N
  letI : Algebra ℚ P.ring := Algebra.compHom P.ring (algebraMap ℚ k)
  letI : P.equation.IsElliptic := P.elliptic
  obtain ⟨D⟩ := ArithmeticThetaArbitraryAffineR0202.arbitrary_compatible_local_coverage
    k L hL heven A B hB C Q P.ring P.equation P.law P.originLaw level
  obtain ⟨b, f, h⟩ := ArithmeticThetaArbitraryAffineR0202.AffineClassification.descend_local
    hL heven hB P.originLaw D
  exact ⟨{ presentation := P, level := level, x_eq := hx.1, y_eq := hx.2
           base := b, comparison := f, classifies := h }, hs⟩

end ArithmeticThetaSchemeLevelR0204

#print axioms ArithmeticThetaSchemeLevelR0204.scheme_local_classifier
