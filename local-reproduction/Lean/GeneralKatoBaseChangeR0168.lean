import GeneralEllipticBaseChangeR0168
import GeneralKatoExistenceR0168

/-! Naturality for the actual projective Weierstrass curve under arbitrary
characteristic-zero coefficient extensions and Cartesian pointed comparisons. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoExistenceR0151

/-- The unique geometric function-field map preserves the full normalized
Kato predicate, including every positive coprime multiplication norm. -/
theorem general_kato_base_change :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (G : ArithmeticThetaGeneralEllipticKatoR0168.Law F W) (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] (K : Type u) [Field K] [CharZero K] (Wb : WeierstrassCurve K) [Wb.IsElliptic] (Gb : ArithmeticThetaGeneralEllipticKatoR0168.Law K Wb) (hGb : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw K Wb Gb) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve K Wb)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve K Wb)] (ι : F →+* K) (b : Quiver.Hom (ArithmeticThetaGeneralEllipticKatoR0168.Curve K Wb) (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)) (hb : ArithmeticThetaGeneralEllipticKatoR0168.IsBaseChange F K W Wb G Gb ι b), ∃! α : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField →+* (ArithmeticThetaGeneralEllipticKatoR0168.Curve K Wb).functionField, ArithmeticThetaGeometricNormR0150.IsFieldMap b α ∧ ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∀ (g : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField), ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F W G c g → ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction K Wb Gb c (α g) := by
  intro F _ _ W _ G hG _ _ K _ _ Wb _ Gb hGb _ _ ι b hb
  letI : Surjective b :=
    MorphismProperty.of_isPullback (P := @Surjective) hb.1.flip inferInstance
  obtain ⟨α, hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap b
  refine ⟨α, ⟨hα, ?_⟩, ?_⟩
  · intro c hc hc6 g hg
    letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
      WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
    letI : SmoothOfRelativeDimension 1 (structureMap K Wb) :=
      WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Wb.toProjective
    have he : ∀ x : Curve K Wb,
        b x = originPoint F W ↔ x = originPoint K Wb := by
      intro x
      exact DivisorFieldBaseChange.section_point_iff b (Spec.map (CommRingCat.ofHom ι))
        (origin F W) (origin K Wb)
        (DivisorFieldBaseChange.section_pullback (structureMap F W) (structureMap K Wb)
          b (Spec.map (CommRingCat.ofHom ι)) hb.1 (origin F W) (origin K Wb)
          (WeierstrassProjModel.kwZeroSect F W).property
          (WeierstrassProjModel.kwZeroSect K Wb).property hb.2.1) x
    refine ⟨⟨DivisorFieldBaseChange.map_ne_zero α hg.1.1, ?_⟩, ?_⟩
    · intro x
      rw [DivisorFieldBaseChange.basechange_order F K (structureMap F W)
        (structureMap K Wb) ι b hb.1 α hα g hg.1.1 x, hg.1.2]
      have hm : G.schemeNsmul c (b x) = b (Gb.schemeNsmul c x) :=
        (congrArg (fun t : Curve K Wb ⟶ Curve F W => t x) (hb.2.2 c)).symm
      classical
      simp only [katoOrder, hm, he]
    · intro d hd hcd φb hφb
      obtain ⟨hfinite, hetale, hsurj, _, φ, hφ, _⟩ :=
        general_multiplication_degree F W G hG d hd
      letI := hfinite
      letI := hetale
      letI := hsurj
      have hcart : IsPullback b (Gb.schemeNsmul d) (G.schemeNsmul d) b :=
        ActualKatoFieldBaseChange.endomorphism_cartesian
          (structureMap F W) (structureMap K Wb) b (Spec.map (CommRingCat.ofHom ι))
          hb.1 (G.schemeNsmul d) (Gb.schemeNsmul d)
          (G.schemeNsmul_over d) (Gb.schemeNsmul_over d) (hb.2.2 d)
      have hnorm := geometric_norm_base_change
        (Curve F W) (Curve F W) (Curve K Wb) (Curve K Wb)
        (G.schemeNsmul d) (Gb.schemeNsmul d) b b hcart
        φ φb α α hφ hφb hα hα g
      rw [hg.2 d hd hcd φ hφ] at hnorm
      exact hnorm.symm
  · intro β hβ
    exact ActualMultiplicationFieldNorm.fieldMap_unique b α β hα hβ.1

#print axioms general_kato_base_change
end ArithmeticThetaGeneralEllipticKatoR0168
