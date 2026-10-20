module

public import SchemeKatoExpansionDefinitionsR0252
public import NormalModelUnitIndependenceR0249

@[expose] public section

/-! The actual canonical unit has the normalized field germ. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoExpansionR0252
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryKatoUnitR0249
open ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitIndependence
open ArithmeticThetaArbitraryDiscriminantR0243

/-- Identify the germ of the specified unit, retaining its curve and origin law. -/
theorem canonical_kato_field_agreement
    (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)]
    (G : Law F W) (hG : IsOriginLaw F W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (v : UnitSection F W G c) (hv : IsKatoUnit F W G c v) :
    FieldAgreement F W G c v := by
  letI : IsIntegral (GenericCurve F W) := (relative_curve_geometry F W).2.2.2.1
  letI : IsLocallyNoetherian (GenericCurve F W) :=
    (relative_curve_geometry F W).2.2.2.2.1
  letI := complement_nonempty F W G hG c hc
  obtain ⟨g, hg⟩ := normalized_exists F W G hG c hc hc6
  obtain ⟨M⟩ := normal_discriminant_model F W
  obtain ⟨hU, gM, hgM, a, _, ha, e, hv⟩ := hv M
  letI := hU
  have hb : IsBaseChange M.ring M.equation M.law F W G
      M.scalar.toRingHom M.comparison.map :=
    ⟨M.comparison.cartesian, M.comparison.pointed,
      NormalDiscriminantIndependence.comparison_nsmul
        M.comparison M.law M.originLaw G hG⟩
  have he := (relative_kato_arbitrary_base_change
    M.ring M.equation M.law M.originLaw F W G hG
    M.scalar.toRingHom M.comparison.map hb c hc hc6 gM hgM g hg
    _ _ e a (complement_avoids M.ring M.equation M.law c) ha).2
  refine ⟨inferInstance, ?_⟩
  rw [hv, he]
  exact RelativeKatoFiberSpecialization.relative_isKato_over_field
    F W G hG c (by omega) g hg.1

end ArithmeticThetaSchemeKatoExpansionR0252

#print axioms ArithmeticThetaSchemeKatoExpansionR0252.canonical_kato_field_agreement
