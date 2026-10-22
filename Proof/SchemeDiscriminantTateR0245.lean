module

public import UnmarkedTateDiscriminantR0245
public import SchemeDiscriminantNaturalityR0244

@[expose] public section

/-! The intrinsic scheme discriminant and its full expansion through every
actual pointed Cartesian unmarked Tate test. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaSchemeTateDiscriminantR0245
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaTateCuspsR0181

namespace SchemeDiscriminantTate

/-- Universal affine normalization applies to the precise coefficient map of
an actual Tate test. The rational algebra structures agree by uniqueness. -/
theorem test_normalized (k : Type) [Field k] [CharZero k]
    {S : Scheme} (σ : S ⟶ Base k) (E : Family S)
    (d : Sections E) (hd : IsD2 k σ E d)
    (l : Type) [Field l] [CharZero l] (ι : k →+* l) (L : ℕ)
    (V : TateTest k L l ι σ E) :
    NormalizedDiscriminant l L (value k L V d) := by
  letI := V.elliptic
  letI : CharZero (LaurentSeries l) := LaurentSeries.XAdic.charZero l
  let A : Algebra k (LaurentSeries l) :=
    ((algebraMap l (LaurentSeries l)).comp ι).toAlgebra
  letI := A
  have h := hd (LaurentSeries l) (TateCurve l L) V.law V.originLaw
    V.base V.base_eq V.comparison
  let B : Algebra ℚ (LaurentSeries l) :=
    ((algebraMap k (LaurentSeries l)).comp (algebraMap ℚ k)).toAlgebra
  change @ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (LaurentSeries l) _ B
    (TateCurve l L) (value k L V d) at h
  have h' : ∀ Q : Algebra ℚ (LaurentSeries l),
      @ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (LaurentSeries l) _ Q
        (TateCurve l L) (value k L V d) := by
    intro Q
    have hB : B = Q := Subsingleton.elim _ _
    subst Q
    exact h
  exact h' _

end SchemeDiscriminantTate

/-- The same unique canonical section is a frame, has every full unmarked
Tate expansion, and obeys every pointed Cartesian base-change equation. -/
theorem scheme_discriminant_tate :
    ∀ (k : Type) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∃! d : ArithmeticThetaSchemeDiscriminantR0244.Sections E, ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaSchemeDiscriminantR0244.Power E) ⊤ d ∧ ArithmeticThetaSchemeTateDiscriminantR0245.HasTateExpansions k σ E d ∧ ∀ (T : AlgebraicGeometry.Scheme) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b) (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F), ArithmeticThetaSchemeDiscriminantR0244.IsD2 k τ F e → ArithmeticThetaSchemeDiscriminantR0244.pull C d = e := by
  intro k _ _ S σ E
  obtain ⟨d, hd⟩ := scheme_discriminant_existence k S σ E
  have hframe := scheme_discriminant_frame_uniqueness k S σ E d hd
  refine ⟨d, ⟨hd, hframe.1, ?_, ?_⟩, ?_⟩
  · intro l _ _ ι L hL heven V
    exact unmarked_tate_discriminant l L hL heven V.differential V.normalized
      (value k L V d) (SchemeDiscriminantTate.test_normalized k σ E d hd l ι L V)
  · intro T τ F b hb C e he
    exact scheme_discriminant_naturality k S σ E T τ F b hb C d e hd he
  · intro e he
    exact hframe.2 e he.1

#print axioms scheme_discriminant_tate
end ArithmeticThetaSchemeTateDiscriminantR0245
