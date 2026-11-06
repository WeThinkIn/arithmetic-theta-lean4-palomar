import CartesianIdentityIdealR0205
import AffineConormalHodgeNaturalityR0205

/-! The uniquely normalized Hodge comparison for the actual scheme classifier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

/-- The same universal affine Hodge sheaf identifies canonically with the
identity cotangent of every classified family, with its full normalization. -/
theorem classifying_cotangent_hodge :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
      (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
      (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
      (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
      (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L)
      (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve),
      Classifies k L A B C Q σ E M b f →
      ∃! e : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E,
        ClassifierHodge k L A B C Q E b f e := by
  intro k _ _ L hL heven A B C Q S σ E M b f hc
  let U := universalFamily k L A
  have hz : E.zero ≫ f = (b ≫ Q.inclusion) ≫ U.zero := hc.2.2.1
  obtain ⟨i, hi, unique⟩ := cartesian_identity_ideal
    (Base A.quotient.ring) S U E (b ≫ Q.inclusion) f hc.2.1 hz
  let : IsIso (affineDifferential U) :=
    AffineConormalHodgeNaturality.differential_isIso U
  let d := (Scheme.Modules.pullback b).map
    ((Scheme.Modules.pullback Q.inclusion).map (affineDifferential U))
  let e := (asIso d).symm ≪≫
    (Scheme.Modules.pullbackComp b Q.inclusion).app (Cotangent U) ≪≫
    cotangentComparison U E (b ≫ Q.inclusion) f hz i
  have he : ClassifierHodge k L A B C Q E b f e := by
    refine ⟨hz, i, hi, ?_⟩
    change d ≫ e.hom = _
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  obtain ⟨hz', i', hi', hn'⟩ := he'
  have hii : i' = i := unique i' hi'
  subst i'
  obtain ⟨hz₀, i₀, hi₀, hn₀⟩ := he
  have hi₀i : i₀ = i := unique i₀ hi₀
  subst i₀
  apply Iso.ext
  apply (cancel_epi d).mp
  exact hn'.trans hn₀.symm

end ArithmeticThetaSchemeHodgeR0205

#print axioms ArithmeticThetaSchemeHodgeR0205.classifying_cotangent_hodge
