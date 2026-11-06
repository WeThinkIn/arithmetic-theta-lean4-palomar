import NormalDiscriminantModelR0243
import NormalDiscriminantIndependenceR0243

/-! Canonical weight-24 frames over every rational coefficient ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryDiscriminantR0243
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- Model existence makes the universal normalization nonvacuous; independence
makes the resulting actual Hodge section canonical. -/
theorem arbitrary_weierstrass_discriminant :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R]
      (W : WeierstrassCurve R) [W.IsElliptic],
      ∃! d : Sections (HodgePower R W 24),
        IsD2 W d ∧ IsFrame (HodgePower R W 24) ⊤ d := by
  intro R _ _ W _
  obtain ⟨M⟩ := normal_discriminant_model R W
  refine ⟨value M, ⟨?_, NormalDiscriminantIndependence.value_frame M⟩, ?_⟩
  · intro N
    exact normal_discriminant_independence R W M N
  · intro d hd
    exact hd.1 M

namespace ArbitraryWeierstrassDiscriminant

section Normal
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)

/-- The identity presentation uses the literal identity of the curve. -/
def identityModel : NormalModel R W where
  ring := R
  equation := W
  law := G
  originLaw := hG
  scalar := AlgHom.id ℚ R
  comparison := {
    map := 𝟙 (Curve R W)
    cartesian := by
      change IsPullback (𝟙 _) (structureMap R W) (structureMap R W)
        (Spec.map (𝟙 (CommRingCat.of R)))
      rw [Spec.map_id]
      exact IsPullback.id_horiz _
    pointed := by
      change origin R W ≫ 𝟙 _ = Spec.map (𝟙 (CommRingCat.of R)) ≫ origin R W
      simp }

theorem identityModel_value :
    value (identityModel R W G hG) = localD R W G hG :=
  NormalDiscriminantIndependence.value_eq_localD R W G hG (identityModel R W G hG)

/-- The universal normalization specializes to the accepted normalized
five-Kato initial section on a normal base. -/
theorem eq_localD (d : Sections (HodgePower R W 24)) (hd : IsD2 W d) :
    d = localD R W G hG :=
  (hd (identityModel R W G hG)).trans (identityModel_value R W G hG)

include hG in
theorem represents_initial (d : Sections (HodgePower R W 24)) (hd : IsD2 W d)
    (g : (Curve R W).functionField) (hg : Normalized R W G 5 g) :
    RepresentsInitial R W G 5 g d := by
  rw [eq_localD R W G hG d hd]
  exact localD_represents R W G hG g hg

end Normal
end ArbitraryWeierstrassDiscriminant

#print axioms arbitrary_weierstrass_discriminant
#print axioms ArbitraryWeierstrassDiscriminant.identityModel_value
#print axioms ArbitraryWeierstrassDiscriminant.eq_localD
#print axioms ArbitraryWeierstrassDiscriminant.represents_initial
end ArithmeticThetaArbitraryDiscriminantR0243
