module

public import ArbitraryWeierstrassDiscriminantR0243

@[expose] public section

/-! Naturality of the normalized weight-24 section for every specified pointed
Cartesian comparison over arbitrary rational algebras. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryDiscriminantR0243
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171

namespace ArbitraryDiscriminantNaturality

/-- Retain the normal source and compose its actual pointed Cartesian map. -/
def composeModel {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {W : WeierstrassCurve R}
    {V : WeierstrassCurve S} (M : NormalModel R W) (ι : R →ₐ[ℚ] S)
    (C : Comparison R S W V ι.toRingHom) : NormalModel S V where
  ring := M.ring
  equation := M.equation
  law := M.law
  originLaw := M.originLaw
  scalar := ι.comp M.scalar
  comparison := NormalDiscriminantIndependence.comparisonCompose M.comparison C

/-- The canonical differential and tensor comparison, including restriction
of global sections, agrees with composition along these same scheme maps. -/
theorem value_composeModel {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} (M : NormalModel R W) (ι : R →ₐ[ℚ] S)
    (C : Comparison R S W V ι.toRingHom) :
    value (composeModel M ι C) = pull C (value M) := by
  apply NormalDiscriminantIndependence.pull_refinement M.comparison C
    (NormalDiscriminantIndependence.comparisonCompose M.comparison C) rfl
  exact Spec.map_comp (CommRingCat.ofHom M.scalar.toRingHom)
    (CommRingCat.ofHom ι.toRingHom)

end ArbitraryDiscriminantNaturality

/-- Universal normal-source normalization is natural for every rational
algebra map and every specified pointed Cartesian comparison. -/
theorem arbitrary_discriminant_naturality :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R]
      (W : WeierstrassCurve R) [W.IsElliptic],
      ∀ (S : Type u) [CommRing S] [Algebra ℚ S]
        (V : WeierstrassCurve S) [V.IsElliptic] (ι : R →ₐ[ℚ] S)
        (C : Comparison R S W V ι.toRingHom)
        (d : Sections (HodgePower R W 24)) (e : Sections (HodgePower S V 24)),
        IsD2 W d → IsD2 V e → pull C d = e := by
  intro R _ _ W _ S _ _ V _ ι C d e hd he
  obtain ⟨M⟩ := normal_discriminant_model R W
  rw [hd M, he (ArbitraryDiscriminantNaturality.composeModel M ι C)]
  exact (ArbitraryDiscriminantNaturality.value_composeModel M ι C).symm

#print axioms ArbitraryDiscriminantNaturality.composeModel
#print axioms ArbitraryDiscriminantNaturality.value_composeModel
#print axioms arbitrary_discriminant_naturality
end ArithmeticThetaArbitraryDiscriminantR0243
