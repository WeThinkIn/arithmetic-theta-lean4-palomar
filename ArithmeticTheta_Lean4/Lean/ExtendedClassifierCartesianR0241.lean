import CoefficientModuliCartesianR0241

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaActualLevelR0208 ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaMetaplecticStackR0207 ArithmeticThetaSquareLinesR0192
open ActualFamilyFPQCDescentProof

/-- The new-field classifier of the actual pulled family is the Cartesian
pullback of its original classifier. The family, marking and root are the
specified geometric pullback throughout. -/
theorem extended_classifier_cartesian :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
      ∀ (P : ArithmeticThetaActualLevelR0208.Provider k L)
        (Q : ArithmeticThetaActualLevelR0208.Provider l L),
      ∀ (Y : Over (Base k)) (p : Y ⟶ base P)
        (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
        (Z : Over (Base l)) (a : Z.left ⟶ Y.left),
      IsPullback a Z.hom Y.hom (ArithmeticThetaScalarExtensionR0240.fieldMap ι) →
      IsPullback a (classifiedMap Q Z (extendedObject P Y p H Z a)).left p.left
        (coefficientMap ι P Q) := by
  intro k l _ _ _ _ ι L hL heven P Q Y p H Z a ha
  let Zk : Over (Base k) :=
    Over.mk (Z.hom ≫ ArithmeticThetaScalarExtensionR0240.fieldMap ι)
  let ak : Zk ⟶ Y := Over.homMk a ha.w
  let X := extendedObject P Y p H Z a
  let c := classifiedMap Q Z X
  have hpull := congrArg Subtype.val
    (classifier_pull P.universal ak (object P p H))
  change (classifier P.universal (S := Zk) X).val =
    a ≫ (classifier P.universal (S := Y) (object P p H)).val at hpull
  rw [ActualCategoricalRootFiberProof.object_classifier] at hpull
  obtain ⟨f, hf⟩ := CoefficientModuliCartesianProof.reclassify ι hL heven P Q
    Z.left Z.hom X.family X.marking c.left
    (classifierCurve Q.universal (S := Z) X) (classifier_spec Q.universal X)
  have hc : c.left ≫ coefficientMap ι P Q = a ≫ p.left := by
    have hu := (scheme_classifying_uniqueness k L hL heven P.atlas P.two
      P.canonicalTwo P.cover P.quotient Z.left Zk.hom X.family X.marking
      (c.left ≫ coefficientMap ι P Q) (classifier P.universal (S := Zk) X).val
      f (classifierCurve P.universal (S := Zk) X) hf
      (classifier_spec P.universal (S := Zk) X)).1
    exact hu.trans hpull
  have outer : IsPullback a (c.left ≫ (base Q).hom)
      (p.left ≫ (base P).hom) (ArithmeticThetaScalarExtensionR0240.fieldMap ι) := by
    simpa only [Over.w c, Over.w p] using ha
  exact outer.of_bot hc.symm (coefficient_moduli_cartesian k l ι L hL heven P Q)

#print axioms extended_classifier_cartesian
end ArithmeticThetaExtendedMetaplecticR0241
