import FramedSchemeQuotientR0174
import RelativeWeierstrassPresentationR0174

/-! Transport the constructed framed quotient through its pointed Weierstrass
presentation. The accepted split-kernel and pointed group-homomorphism theorems
are imported unchanged, and are not redeclared here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeIsogenyHodgeR0172
open ArithmeticThetaCyclicPresentationR0174

/-- The relative cyclic quotient is a pointed elliptic Weierstrass curve over
the original base, with degree exactly `n` and the prescribed ideal-sheaf kernel. -/
theorem relative_cyclic_quotient_existence
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (n : ℕ) (hn : 0 < n)
    (P : CyclicSection R W G n) :
    ∃ (V : WeierstrassCurve R) (hV : V.IsElliptic)
      (f : PointedMap R W V), IsQuotient R W G P f := by
  obtain ⟨Q⟩ := framed_scheme_quotient R W G hG n hn P
  obtain ⟨V, hV, e, he, ho⟩ := relative_weierstrass_presentation R
    Q.target Q.structureMap Q.law Q.geometry Q.dimension Q.hodge
  let : V.IsElliptic := hV
  let f : PointedMap R W V := {
    map := Q.map ≫ e.hom
    over_eq := by rw [Category.assoc, he, Q.over_eq]
    origin_eq := by rw [← Category.assoc, Q.origin_eq, ho] }
  let : IsFinite Q.map := Q.finite
  let : Etale Q.map := Q.etale
  let : Surjective Q.map := Q.surjective
  refine ⟨V, hV, f, ?_⟩
  change IsFinite (Q.map ≫ e.hom) ∧ Etale (Q.map ≫ e.hom) ∧
    Surjective (Q.map ≫ e.hom) ∧ (∀ y, (Q.map ≫ e.hom).finrank y = n) ∧
    (origin R V).ker.comap (Q.map ≫ e.hom) = kernelIdeal R W G P
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro y
    have hs : IsPullback (𝟙 _) (Q.map ≫ e.hom) Q.map e.inv :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hs]
    exact Q.degree (e.inv y)
  · let : IsProper Q.structureMap := Q.geometry.proper
    have : IsClosedImmersion ((Q.law.one (𝟙 _)).val ≫ Q.structureMap) := by
      rw [(Q.law.one (𝟙 _)).property]
      infer_instance
    have : IsClosedImmersion (Q.law.one (𝟙 _)).val :=
      IsClosedImmersion.of_comp _ Q.structureMap
    have : IsClosedImmersion (origin R V) := by rw [← ho]; infer_instance
    have hs : IsPullback (Q.law.one (𝟙 _)).val (𝟙 _) e.hom (origin R V) :=
      IsPullback.of_vert_isIso ⟨by simpa using ho⟩
    have hk : (origin R V).ker.comap e.hom = (Q.law.one (𝟙 _)).val.ker := by
      rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
        ← Scheme.Hom.ker_comp_of_isIso hs.isoPullback.hom, hs.isoPullback_hom_fst]
    rw [Scheme.IdealSheafData.comap_comp, hk]
    exact Q.kernel

end ArithmeticThetaRelativeCyclicQuotientR0173
