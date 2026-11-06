module

public import ClassifyingCotangentHodgeR0205
public import SchemeCotangentCoherenceR0205
public import SchemeFullLevelUniversalR0204

@[expose] public section

/-! The same compatible quotient classifies general elliptic families together
with their canonical, natural identity-cotangent Hodge comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

namespace SchemeHodgeUniversal

lemma pullback_assoc_hom {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app M) ≫
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M =
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M := by
  have h := congrArg (fun q ↦ q.app M) (Scheme.Modules.pseudofunctor_associativity a b c)
  dsimp at h
  simp only [Category.id_comp] at h
  apply (cancel_epi ((Scheme.Modules.pullback a).map
    ((Scheme.Modules.pullbackComp b c).inv.app M))).mp
  apply (cancel_epi ((Scheme.Modules.pullbackComp a (b ≫ c)).inv.app M)).mp
  simpa only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- Cancel a fixed invertible normalization in a composable pullback diagram. -/
lemma normalized_naturality {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    {M N : Z.Modules} (d : M ⟶ N) [IsIso d]
    {P : X.Modules} {R : W.Modules}
    (eE : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback c).obj N) ⟶ P)
    (eF : (Scheme.Modules.pullback (a ≫ b)).obj ((Scheme.Modules.pullback c).obj N) ⟶ R)
    (eG : (Scheme.Modules.pullback a).obj P ⟶ R)
    (qE : (Scheme.Modules.pullback (b ≫ c)).obj M ⟶ P)
    (qF : (Scheme.Modules.pullback ((a ≫ b) ≫ c)).obj M ⟶ R)
    (hE : (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map d) ≫ eE =
      (Scheme.Modules.pullbackComp b c).hom.app M ≫ qE)
    (hF : (Scheme.Modules.pullback (a ≫ b)).map ((Scheme.Modules.pullback c).map d) ≫ eF =
      (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M ≫ qF)
    (hG : (Scheme.Modules.pullback a).map qE ≫ eG =
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M ≫ qF) :
    (Scheme.Modules.pullback a).map eE ≫ eG =
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫ eF := by
  apply (cancel_epi ((Scheme.Modules.pullback a).map
    ((Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map d)))).mp
  rw [← Category.assoc, ← Functor.map_comp, hE, Functor.map_comp, Category.assoc, hG]
  rw [← Category.assoc, pullback_assoc_hom, Category.assoc, ← hF]
  rw [← Category.assoc]
  exact congrArg (fun q ↦ q ≫ eF)
    ((Scheme.Modules.pullbackComp a b).hom.naturality
      ((Scheme.Modules.pullback c).map d)).symm

variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)

/-- Normalization by the universal conormal derivative transports the actual
cotangent composition law to the Hodge sheaf. -/
theorem classifier_natural : ClassifierHodgeNatural k L A B C Q := by
  intro S T E F a g hg b f eE eF eG hE hF hG
  obtain ⟨hzE, iE, hiE, hnE⟩ := hE
  obtain ⟨hzF, iF, hiF, hnF⟩ := hF
  let U := universalFamily k L A
  let d := affineDifferential U
  let : IsIso d := AffineConormalHodgeNaturality.differential_isIso U
  have hc := scheme_cotangent_coherence.2 (Base A.quotient.ring) S T U E F
    (b ≫ Q.inclusion) a f g hzE hg hzF
    (cotangentComparison U E (b ≫ Q.inclusion) f hzE iE) eG
    (cotangentComparison U F ((a ≫ b) ≫ Q.inclusion) (g ≫ f) hzF iF)
    ⟨iE, hiE, rfl⟩ hG ⟨iF, hiF, rfl⟩
  exact normalized_naturality a b Q.inclusion d eE.hom eF.hom eG.hom
    _ _ hnE hnF hc

end SchemeHodgeUniversal

/-- A single actual compatible quotient works simultaneously for all test
schemes, with its unique canonical Hodge comparison and base-change law. -/
theorem scheme_hodge_universal :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L),
      ∃ (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
        (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B)
        (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
        (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C),
        HodgeUniversal k L A B C Q := by
  intro k _ _ L hL heven A
  obtain ⟨B, hB, C, Q, hQ⟩ := scheme_full_level_universal k L hL heven A
  exact ⟨B, hB, C, Q, hQ,
    classifying_cotangent_hodge k L hL heven A B C Q,
    SchemeHodgeUniversal.classifier_natural k L A B C Q⟩

end ArithmeticThetaSchemeHodgeR0205

#print axioms ArithmeticThetaSchemeHodgeR0205.SchemeHodgeUniversal.classifier_natural
#print axioms ArithmeticThetaSchemeHodgeR0205.scheme_hodge_universal
