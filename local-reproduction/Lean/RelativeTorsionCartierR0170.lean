import RelativeKatoNaturalityDefinitionsR0170
import RelativeCurveGeometryR0169
import RelativeMultiplicationDegreeR0169
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral

set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

namespace RelativeTorsionCartier

private lemma effective_of_invertible {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : I.IsInvertible) : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I := by
  intro x
  obtain ⟨U, f, hx, g, hg, hIg⟩ := hI x
  exact ⟨X.affineBasicOpen f, hx, g, isRegular_iff_mem_nonZeroDivisors.mpr hg, hIg⟩

private lemma support_ne_univ {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I.IsInvertible) : (I.support : Set X) ≠ Set.univ := by
  intro h
  have htop : I.support = ⊤ := SetLike.coe_injective h
  have hbot : I = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp htop
  obtain ⟨U, f, hx, g, hg, hIg⟩ := hI (genericPoint X)
  let : Nonempty (X.affineBasicOpen f : X.Opens) := ⟨⟨genericPoint X, hx⟩⟩
  have hg0 : g = 0 := by
    apply Ideal.span_singleton_eq_bot.mp
    rw [← hIg, hbot]
    rfl
  exact (nonZeroDivisors.ne_zero hg) hg0

end RelativeTorsionCartier

/-- The actual origin and every positive multiplication pullback are Cartier
on the whole relative projective Weierstrass curve. -/
theorem relative_torsion_cartier :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G), ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (ArithmeticThetaRelativeKatoNaturalityR0170.identityIdeal R W) ∧ ∀ n : ℕ, 0 < n → ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G n) := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG
  let : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (relative_curve_geometry R W).2.2.2.2.2.1
  let : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have horigin : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  have hI : (identityIdeal R W).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (origin R W) horigin
  refine ⟨RelativeTorsionCartier.effective_of_invertible hI, ?_⟩
  intro n hn
  let : Surjective (G.schemeNsmul n) :=
    (relative_multiplication_degree R W G hG n hn).2.2.1
  apply RelativeTorsionCartier.effective_of_invertible
  apply hI.comap_of_isIntegral (G.schemeNsmul n)
  intro h
  apply RelativeTorsionCartier.support_ne_univ hI
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ := (G.schemeNsmul n).surjective y
  have hx : x ∈ ((identityIdeal R W).comap (G.schemeNsmul n)).support := by
    change x ∈ (((identityIdeal R W).comap (G.schemeNsmul n)).support : Set _)
    rw [h]
    trivial
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact hx

#print axioms relative_torsion_cartier
end ArithmeticThetaRelativeKatoNaturalityR0170
