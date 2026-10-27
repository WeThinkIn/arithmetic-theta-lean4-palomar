import ExtendedMetaplecticDefinitionsR0241

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaActualLevelR0208 ArithmeticThetaMetaplecticComparisonR0206

namespace CoefficientModuliCartesianProof
variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
  {L : ℕ} (ι : k →+* l) (hL : 3 ≤ L) (heven : Even L)
  (P : Provider k L) (Q : Provider l L)

lemma coefficient_condition :
    coefficientMap ι P Q ≫ (base P).hom =
      (base Q).hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι :=
  (P.universal.1.1 (base Q).left
    ((base Q).hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    (model Q (𝟙 (base Q))).family (model Q (𝟙 (base Q))).marking).choose_spec.1.choose_spec.1.1

include hL heven in
/-- A target-field classifier classifies the same marked family over the source
field after composition with the prescribed coefficient comparison. -/
lemma reclassify (S : Scheme.{0}) (τ : S ⟶ Base l)
    (E : Family S) (M : FullLevel E L) (c : S ⟶ (base Q).left)
    (g : E.curve ⟶ Q.atlas.descent.family.curve)
    (hg : Classifies l L Q.atlas Q.two Q.cover Q.quotient τ E M c g) :
    ∃ f : E.curve ⟶ P.atlas.descent.family.curve,
      Classifies k L P.atlas P.two P.cover P.quotient
        (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) E M
        (c ≫ coefficientMap ι P Q) f := by
  let U := model Q (𝟙 (base Q))
  obtain ⟨a, ha, _⟩ := marked_cartesian_reconstruction l L hL heven
    Q.atlas Q.two Q.cover Q.quotient (base Q).left S (base Q).hom τ
    U.family E U.marking M c (𝟙 _) c U.curve g hg.1 U.classifies hg (by simp)
  let H := P.universal.1.1 (base Q).left
    ((base Q).hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) U.family U.marking
  obtain ⟨b, hb, _⟩ := P.universal.1.1 S
    (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) E M
  obtain ⟨f, hf, _⟩ := hb
  have eqb := (P.universal.1.2.2 (base Q).left S
    ((base Q).hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    U.family E U.marking M c a (by
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) hg.1) ha.1
    H.choose b H.choose_spec.1.choose f H.choose_spec.1.choose_spec.1 hf).1
  change b = c ≫ coefficientMap ι P Q at eqb
  exact ⟨f, eqb ▸ hf⟩

include hL heven in
lemma unique_lift (S : Scheme.{0}) (b : S ⟶ (base P).left) (τ : S ⟶ Base l)
    (hb : b ≫ (base P).hom = τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) :
    ∃! c : S ⟶ (base Q).left,
      c ≫ coefficientMap ι P Q = b ∧ c ≫ (base Q).hom = τ := by
  obtain ⟨E, M, f, hf⟩ := P.universal.1.2.1 S
    (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) b hb
  obtain ⟨c, hc, _⟩ := Q.universal.1.1 S τ E M
  obtain ⟨g, hg, _⟩ := hc
  obtain ⟨f', hf'⟩ := reclassify ι hL heven P Q S τ E M c g hg
  have cb : c ≫ coefficientMap ι P Q = b := by
    exact (scheme_classifying_uniqueness k L hL heven P.atlas P.two
      P.canonicalTwo P.cover P.quotient S
      (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι) E M
      (c ≫ coefficientMap ι P Q) b f' f hf' hf).1
  refine ⟨c, ⟨cb, hg.1⟩, ?_⟩
  intro d hd
  obtain ⟨F, N, q, hq⟩ := Q.universal.1.2.1 S τ d hd.2
  obtain ⟨r, hr⟩ := reclassify ι hL heven P Q S τ F N d q hq
  rw [hd.1] at hr
  obtain ⟨a, ha, _⟩ := marked_cartesian_reconstruction k L hL heven
    P.atlas P.two P.cover P.quotient S S
    (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    (τ ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
    E F M N (𝟙 S) b b f r (by simp) hf hr (by simp)
  have H := (Q.universal.1.2.2 S S τ τ E F M N (𝟙 S) a
    (by simp) ha.1 c d g q hg hq).1
  simpa only [Category.id_comp] using H

end CoefficientModuliCartesianProof

/-- The actual full-level universal classifier commutes with every coefficient
embedding as a Cartesian square on arbitrary scheme-valued tests. -/
theorem coefficient_moduli_cartesian :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
      ∀ (P : Provider k L) (Q : Provider l L),
      IsPullback (coefficientMap ι P Q) (base Q).hom (base P).hom
        (ArithmeticThetaScalarExtensionR0240.fieldMap ι) := by
  intro k l _ _ _ _ ι L hL heven P Q
  have w := CoefficientModuliCartesianProof.coefficient_condition ι P Q
  refine ⟨⟨w⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
  intro s
  have H := CoefficientModuliCartesianProof.unique_lift ι hL heven P Q
    s.pt s.fst s.snd s.condition
  exact ⟨H.choose, H.choose_spec.1.1, H.choose_spec.1.2,
    fun h₁ h₂ => H.choose_spec.2 _ ⟨h₁, h₂⟩⟩

#print axioms coefficient_moduli_cartesian
end ArithmeticThetaExtendedMetaplecticR0241
