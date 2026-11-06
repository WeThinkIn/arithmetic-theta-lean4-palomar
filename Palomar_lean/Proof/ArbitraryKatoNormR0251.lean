module

public import FiniteEtaleNormBaseChangeR0251
public import SchemeMultiplicationDegreeR0250
public import ArbitraryKatoCartierDivisorR0249

@[expose] public section

/-! The determinant norm fixes the same arbitrary-base Kato unit obtained by
specialization from a normal model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaArbitraryDiscriminantR0243
open ArithmeticThetaGeometricNormR0150

namespace ArbitraryKatoNorm
open ArithmeticThetaArbitraryKatoUnitR0249 (complement UnitSection IsKatoUnit)

/-- The inverse-image inclusion follows from preservation of torsion, in the
direction needed to restrict the original unit. -/
lemma model_preimage_le {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} (M : NormalModel R W) (c d : ℕ) :
    M.law.schemeNsmul d ⁻¹ᵁ complement M.ring M.equation M.law c ≤
      complement M.ring M.equation M.law c := by
  intro x hx ht
  apply hx
  apply (RelativeKatoFiberSpecialization.torsion_support M.ring M.equation M.law c _).mpr
  exact RelativeKatoFiberSpecialization.multiplication_preserves_torsion
    M.ring M.equation M.law M.originLaw c d x
    ((RelativeKatoFiberSpecialization.torsion_support M.ring M.equation M.law c x).mp ht)

/-- The existing field norm identifies every affine determinant on the normal
source; separation handles an empty test open without a generic point there. -/
lemma model_norm {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} (M : NormalModel R W) (c : ℕ)
    [Nonempty (complement M.ring M.equation M.law c)]
    (g : (Curve M.ring M.equation).functionField)
    (hg : Normalized M.ring M.equation M.law c g)
    (a : Sections (Curve M.ring M.equation) (complement M.ring M.equation M.law c))
    (ha : (Curve M.ring M.equation).germToFunctionField _ a = g)
    (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d) :
    LocallyNormFixed (M.law.schemeNsmul d)
      (complement M.ring M.equation M.law c) a := by
  obtain ⟨hf, he, hs, _, φ, hφ, _⟩ := relative_multiplication_degree
    M.ring M.equation M.law M.originLaw d hd
  letI := hf
  letI := he
  letI := hs
  refine ⟨model_preimage_le M c d, ?_⟩
  intro V eV hfree
  by_cases hV : Nonempty V.1
  · letI := hV
    obtain ⟨y, hy⟩ := hV
    obtain ⟨x, hx⟩ := (M.law.schemeNsmul d).surjective y
    letI : Nonempty (M.law.schemeNsmul d ⁻¹ᵁ V.1) :=
      ⟨⟨x, by change M.law.schemeNsmul d x ∈ V.1; rwa [hx]⟩⟩
    apply (Curve M.ring M.equation).germToFunctionField_injective V.1
    rw [NormSection.restrict_trans]
    rw [(LocalNorm.affine_field_data (M.law.schemeNsmul d) φ hφ V.1 V.2).2.2 hfree]
    simp only [ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor.rational_restrict]
    rw [ha, hg.1.2.2 d hd hcd φ hφ]
  · apply NormSection.sections_eq_local
    intro x hx
    exact (hV ⟨⟨x, hx⟩⟩).elim

/-- Pullback of a fixed norm section uses the actual sheaf maps, and requires
no reducedness or nonemptiness of the target. -/
lemma fixed_base_change {X Y : Scheme.{u}} (f : X ⟶ X) (fb : Y ⟶ Y)
    (j : Y ⟶ X) [IsFinite f] [Etale f] [IsFinite fb] [Etale fb]
    (h : IsPullback j fb f j) (U : X.Opens) (V : Y.Opens)
    (hV : V = j ⁻¹ᵁ U) (a : Sections X U)
    (ha : LocallyNormFixed f U a) :
    LocallyNormFixed fb V (j.appLE U V (le_of_eq hV) a) := by
  obtain ⟨e, he⟩ := ha
  have eb : fb ⁻¹ᵁ V ≤ V := by
    rw [hV, ← Scheme.Hom.comp_preimage, ← h.w, Scheme.Hom.comp_preimage]
    exact j.preimage_mono e
  obtain ⟨ep, hp⟩ := finite_etale_norm_base_change X X Y Y f fb j j h U
    (restrict U (f ⁻¹ᵁ U) e a) a he V (le_of_eq hV)
  refine ⟨eb, ?_⟩
  rw [NormBaseChange.appLE_restrict] at hp
  simpa only [NormBaseChange.restrict_appLE] using hp

end ArbitraryKatoNorm

/-- Every positive multiplication coprime to c fixes the accepted Kato unit
over every rational algebra, including nonreduced rings and the zero ring. -/
theorem arbitrary_kato_norm :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
      [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∀ v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection R W G c,
        ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit R W G c v →
      ∀ d : ℕ, 0 < d → Nat.Coprime c d →
        LocallyNormFixed (G.schemeNsmul d)
          (ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c) (v : _) := by
  intro R _ _ W _ G hG c _hc _hc6 v hv d hd hcd
  obtain ⟨M⟩ := normal_discriminant_model R W
  obtain ⟨hU, g, hg, a, _haunit, ha, e, hva⟩ := hv M
  letI := hU
  obtain ⟨hf, he, _⟩ := relative_multiplication_degree
    M.ring M.equation M.law M.originLaw d hd
  letI := hf
  letI := he
  obtain ⟨hfb, heb, _⟩ :=
    ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.affine_degree R W G hG d hd
  letI := hfb
  letI := heb
  have hp : IsPullback M.comparison.map (G.schemeNsmul d ≫ structureMap R W)
      (M.law.schemeNsmul d ≫ structureMap M.ring M.equation)
      (Spec.map (CommRingCat.ofHom M.scalar.toRingHom)) := by
    simpa only [WeierstrassProjModel.RelativeGroupLaw.schemeNsmul_over] using
      M.comparison.cartesian
  have hb : IsPullback M.comparison.map (G.schemeNsmul d)
      (M.law.schemeNsmul d) M.comparison.map :=
    hp.of_bot (ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitSpecialization.comparison_nsmul
      M.comparison M.law M.originLaw G hG d).symm M.comparison.cartesian
  rw [hva]
  exact ArbitraryKatoNorm.fixed_base_change _ _ _ hb _ _
    (ArithmeticThetaArbitraryKatoUnitR0249.NormalModelUnitSpecialization.complement_eq
      M.comparison M.law M.originLaw G hG c) a
    (ArbitraryKatoNorm.model_norm M c g hg a ha d hd hcd)

#print axioms arbitrary_kato_norm
end ArithmeticThetaSchemeKatoNormR0251
