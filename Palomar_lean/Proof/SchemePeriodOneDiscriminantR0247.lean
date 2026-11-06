module

public import RationalTateDiscriminantR0247
public import SchemeDiscriminantNaturalityR0244

@[expose] public section

/-! The arbitrary rational-ring period-one Tate consumer for the intrinsic
scheme discriminant.  The scheme existence, frame, and base-change laws are
inherited from r0244; this file supplies their coefficientwise Tate test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaRationalTateR0247

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaSchemeDiscriminantR0244

theorem scheme_period_one_discriminant :
    ∀ (X : AlgebraicGeometry.Scheme)
      (σ : Quiver.Hom X (ArithmeticThetaRelativeDiscriminantR0171.Base ℚ))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family X),
      ∃! d : ArithmeticThetaSchemeDiscriminantR0244.Sections E,
        ArithmeticThetaSchemeDiscriminantR0244.IsD2 ℚ σ E d ∧
          ArithmeticThetaRelativeDiscriminantR0171.IsFrame
            (ArithmeticThetaSchemeDiscriminantR0244.Power E) ⊤ d ∧
          ArithmeticThetaRationalTateR0247.HasTateExpansions σ E d ∧
          ∀ (Y : AlgebraicGeometry.Scheme)
            (τ : Quiver.Hom Y (ArithmeticThetaRelativeDiscriminantR0171.Base ℚ))
            (F : ArithmeticThetaLocalWeierstrassR0203.Family Y)
            (b : Quiver.Hom Y X),
            CategoryTheory.CategoryStruct.comp b σ = τ →
            ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b)
              (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F),
              ArithmeticThetaSchemeDiscriminantR0244.IsD2 ℚ τ F e →
              ArithmeticThetaSchemeDiscriminantR0244.pull C d = e := by
  intro X σ E
  obtain ⟨d, hd⟩ :=
    ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_existence ℚ X σ E
  have hframe :=
    ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_frame_uniqueness
      ℚ X σ E d hd
  refine ⟨d, ⟨hd, hframe.1, ?_, ?_⟩, ?_⟩
  · intro A _ _ V
    let := V.elliptic
    have h := hd (LaurentSeries A) (equation A) V.law V.originLaw
      V.base V.base_eq V.comparison
    let B : Algebra ℚ (LaurentSeries A) :=
      ((algebraMap ℚ (LaurentSeries A)).comp (algebraMap ℚ ℚ)).toAlgebra
    have h' : ∀ Q : Algebra ℚ (LaurentSeries A),
        @ArithmeticThetaArbitraryDiscriminantR0243.IsD2
          (LaurentSeries A) _ Q (equation A) (value A V d) := by
      intro Q
      have hB : B = Q := Subsingleton.elim _ _
      subst Q
      exact h
    obtain ⟨δ, hδ, e, he, _⟩ := rational_tate_discriminant A
    obtain ⟨M⟩ := ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model
      (LaurentSeries A) (equation A)
    have hv : value A V d = e := (h' _ M).trans (he.1 M).symm
    rw [hv]
    exact he.2.2 V.differential V.normalized
  · intro Y τ F b hb C e he
    exact ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality
      ℚ X σ E Y τ F b hb C d e hd he
  · intro e he
    exact hframe.2 e he.1

#print axioms scheme_period_one_discriminant

end ArithmeticThetaRationalTateR0247
