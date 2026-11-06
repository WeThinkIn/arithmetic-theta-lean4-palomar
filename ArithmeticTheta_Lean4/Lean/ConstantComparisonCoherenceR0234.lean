import OpenConstantComparisonR0234
import OpenHodgeConstantComparisonR0234

/-! Identity and composition for coefficient comparisons, including the entire
normalized Hodge isomorphism on every classified test family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaLevelConstantsR0234
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205

namespace ConstantComparisonCoherenceProof

lemma constants_id (k : Type) [Field k] : constants (RingHom.id k) = 𝟙 (Base k) := by
  simp [constants]

lemma constants_comp {k l m : Type} [Field k] [Field l] [Field m]
    (ι : k →+* l) (κ : l →+* m) : constants (κ.comp ι) = constants κ ≫ constants ι := by
  simp [constants]

lemma normalized_transport {k : Type} [Field k] [CharZero k] {L : ℕ}
    (hL : 3 ≤ L) (heven : Even L) (D : LevelData k L)
    {S : Scheme.{0}} (σ : S ⟶ Base k) (F : Family S) (M : FullLevel F L)
    (b c : S ⟶ OpenBase k L D) (h : b = c)
    (a : F.curve ⟶ D.atlas.descent.family.curve)
    (hb : Classifies D σ F M b a)
    (eb : (Scheme.Modules.pullback b).obj (weight D) ≅ Cotangent F)
    (ec : (Scheme.Modules.pullback c).obj (weight D) ≅ Cotangent F)
    (heb : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b a eb)
    (hec : ClassifierHodge k L D.atlas D.two D.cover D.quotient F c a ec) :
    (Scheme.Modules.pullbackCongr h).hom.app (weight D) ≫ ec.hom = eb.hom := by
  subst c
  obtain ⟨e, _, hu⟩ := classifying_cotangent_hodge k L hL heven
    D.atlas D.two D.cover D.quotient S σ F M b a hb
  have hh : ec = eb := (hu ec hec).trans (hu eb heb).symm
  subst ec
  simp [Scheme.Modules.pullbackCongr]

end ConstantComparisonCoherenceProof
open ConstantComparisonCoherenceProof

/-- The coefficient identity is the original base identity and the canonical
pullback identity on its Hodge sheaf. -/
theorem identity_constant_comparison :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L →
    ∀ (D : LevelData k L),
    RespectsClassifiers (RingHom.id k) D D (𝟙 (OpenBase k L D)) ∧
    HodgeCompatible (RingHom.id k) D D (𝟙 (OpenBase k L D))
      ((Scheme.Modules.pullbackId (OpenBase k L D)).app (weight D)) := by
  intro k _ _ L hL heven D
  constructor
  · constructor
    · simp [constants_id]
    · intro S σ F M b g hg
      exact ⟨g, by simpa only [constants_id, Category.comp_id] using hg⟩
  · intro S σ F M b g a hg ha el ek hel hek
    have ha' : Classifies D σ F M b a := by
      simpa only [constants_id, Category.comp_id] using ha
    have hga : g = a := (scheme_classifying_uniqueness k L hL heven
      D.atlas D.two D.canonical D.cover D.quotient S σ F M b b g a hg ha').2
    subst g
    have ht := normalized_transport hL heven D (σ ≫ constants (RingHom.id k))
      F M (b ≫ 𝟙 _) b (Category.comp_id b) a ha ek el hek hel
    simp only [Iso.app_hom]
    rw [← ht, ← Category.assoc, OpenHodgeComparisonProof.pullback_right_unit]

/-- Successive coefficient comparisons compose using the canonical pullback
composition constraint, with no residual scalar ambiguity. -/
theorem composite_constant_comparison :
    ∀ (k l m : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      [Field m] [CharZero m] (ι : k →+* l) (κ : l →+* m) (L : ℕ),
    3 ≤ L → Even L →
    ∀ (D : LevelData k L) (E : LevelData l L) (V : LevelData m L)
      (f : OpenBase l L E ⟶ OpenBase k L D)
      (g : OpenBase m L V ⟶ OpenBase l L E),
    RespectsClassifiers ι D E f → RespectsClassifiers κ E V g →
    ∀ (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
      (d : (Scheme.Modules.pullback g).obj (weight E) ≅ weight V),
    HodgeCompatible ι D E f e → HodgeCompatible κ E V g d →
    RespectsClassifiers (κ.comp ι) D V (g ≫ f) ∧
    HodgeCompatible (κ.comp ι) D V (g ≫ f)
      (((Scheme.Modules.pullbackComp g f).app (weight D)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso e ≪≫ d) := by
  intro k l m _ _ _ _ _ _ ι κ L hL heven D E V f g hf hg e d he hd
  constructor
  · constructor
    · rw [Category.assoc, hf.1, ← Category.assoc, hg.1, Category.assoc, constants_comp]
    · intro S σ F M b v hv
      obtain ⟨aE, hE⟩ := hg.2 S σ F M b v hv
      obtain ⟨aD, hD⟩ := hf.2 S (σ ≫ constants κ) F M (b ≫ g) aE hE
      exact ⟨aD, by simpa only [constants_comp, Category.assoc] using hD⟩
  · intro S σ F M b v a hv ha em ek hem hek
    obtain ⟨aE, hE⟩ := hg.2 S σ F M b v hv
    obtain ⟨el, hel, _⟩ := classifying_cotangent_hodge l L hL heven
      E.atlas E.two E.cover E.quotient S (σ ≫ constants κ) F M (b ≫ g) aE hE
    have ha' : Classifies D ((σ ≫ constants κ) ≫ constants ι)
        F M ((b ≫ g) ≫ f) a := by
      simpa only [constants_comp, Category.assoc] using ha
    obtain ⟨ek', hek', _⟩ := classifying_cotangent_hodge k L hL heven
      D.atlas D.two D.cover D.quotient S _ F M ((b ≫ g) ≫ f) a ha'
    have h1 := hd S σ F M b v aE hv hE em el hem hel
    have h2 := he S (σ ≫ constants κ) F M (b ≫ g) aE a hE ha' el ek' hel hek'
    have ht := normalized_transport hL heven D _ F M ((b ≫ g) ≫ f)
      (b ≫ (g ≫ f)) (Category.assoc b g f) a ha' ek' ek hek' hek
    simp only [Iso.app_hom] at h1 h2 ⊢
    have hn := (Scheme.Modules.pullbackComp b g).hom.naturality e.hom
    simp only [Functor.comp_map] at hn
    dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [h1]
    rw [← Category.assoc ((Scheme.Modules.pullback b).map
      ((Scheme.Modules.pullback g).map e.hom)),
      hn]
    simp only [Category.assoc]
    rw [h2, ← ht]
    rw [← Category.assoc ((Scheme.Modules.pullbackComp b g).hom.app
      ((Scheme.Modules.pullback f).obj (weight D))),
      ← SchemeHodgeUniversal.pullback_assoc_hom]
    simp only [← Functor.map_comp, ← Category.assoc]
    simp [Scheme.Modules.pullbackCongr]

end ArithmeticThetaLevelConstantsR0234

#print axioms ArithmeticThetaLevelConstantsR0234.identity_constant_comparison
#print axioms ArithmeticThetaLevelConstantsR0234.composite_constant_comparison
