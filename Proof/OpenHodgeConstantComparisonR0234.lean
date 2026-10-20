module

public import LevelConstantsDefinitionsR0234

@[expose] public section

/-! The coefficient comparison of the actual modular Hodge sheaves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaLevelConstantsR0234
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaMetaplecticComparisonR0206

namespace OpenHodgeComparisonProof

lemma pullback_right_unit {S T : Scheme.{0}} (b : S ⟶ T) (M : T.Modules) :
    (Scheme.Modules.pullbackComp b (𝟙 T)).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.comp_id b)).hom.app M =
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackId T).hom.app M) := by
  have h := congrArg (fun q => q.app M) (Scheme.Modules.pseudofunctor_left_unitality b)
  have hh : (Scheme.Modules.pullbackComp b (𝟙 T)).inv.app M ≫
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackId T).hom.app M) =
        (Scheme.Modules.pullbackCongr (Category.comp_id b)).hom.app M := by
    simpa [Scheme.Modules.pullbackCongr] using h
  rw [← hh]
  simp

lemma natural_general {k : Type} [Field k] [CharZero k] {L : ℕ}
    (D : LevelData k L) {S T : Scheme.{0}} (U : Family S) (V : Family T)
    (b : T ⟶ S) (q : V.curve ⟶ U.curve) (hz : V.zero ≫ q = b ≫ U.zero)
    (c : S ⟶ OpenBase k L D) (d : T ⟶ OpenBase k L D) (hd : b ≫ c = d)
    (r : U.curve ⟶ D.atlas.descent.family.curve)
    (s : V.curve ⟶ D.atlas.descent.family.curve) (hs : q ≫ r = s)
    (eU : (Scheme.Modules.pullback c).obj (weight D) ≅ Cotangent U)
    (eV : (Scheme.Modules.pullback d).obj (weight D) ≅ Cotangent V)
    (eQ : (Scheme.Modules.pullback b).obj (Cotangent U) ≅ Cotangent V)
    (hU : ClassifierHodge k L D.atlas D.two D.cover D.quotient U c r eU)
    (hV : ClassifierHodge k L D.atlas D.two D.cover D.quotient V d s eV)
    (hQ : CotangentCompatible U V b q hz eQ) :
    (Scheme.Modules.pullback b).map eU.hom ≫ eQ.hom =
      (Scheme.Modules.pullbackComp b c).hom.app (weight D) ≫
        (Scheme.Modules.pullbackCongr hd).hom.app (weight D) ≫ eV.hom := by
  subst d; subst s
  simpa [Scheme.Modules.pullbackCongr] using
    SchemeHodgeUniversal.classifier_natural k L D.atlas D.two D.cover D.quotient
      S T U V b q hz c r eU eV eQ hU hV hQ

lemma identity_detects {S : Scheme.{0}} {M N : S.Modules} (f g : M ⟶ N)
    (h : (Scheme.Modules.pullback (𝟙 S)).map f =
      (Scheme.Modules.pullback (𝟙 S)).map g) : f = g := by
  apply (cancel_epi ((Scheme.Modules.pullbackId S).hom.app M)).mp
  have hf := (Scheme.Modules.pullbackId S).hom.naturality f
  have hg := (Scheme.Modules.pullbackId S).hom.naturality g
  simp only [Functor.id_map] at hf hg
  rw [← hf, ← hg, h]

end OpenHodgeComparisonProof

/-- The full sheaf isomorphism is uniquely fixed by the canonical conormal
comparison on every marked test family. -/
theorem open_hodge_constant_comparison :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
    ∀ (D : LevelData k L) (E : LevelData l L)
      (f : OpenBase l L E ⟶ OpenBase k L D),
      RespectsClassifiers ι D E f →
      ∃! e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E,
        HodgeCompatible ι D E f e := by
  intro k l _ _ _ _ ι L hL heven D E f hf
  obtain ⟨U, MU, gU, hU⟩ := SchemeFullLevelUniversal.converse E.atlas
    (OpenBase l L E) (openStructure l L E) (𝟙 _) (Category.id_comp _)
  obtain ⟨aU, haU'⟩ := hf.2 _ _ U MU (𝟙 _) gU hU
  have haU : Classifies D (openStructure l L E ≫ constants ι) U MU f aU := by
    simpa only [Category.id_comp] using haU'
  obtain ⟨elU, helU, _⟩ := classifying_cotangent_hodge l L hL heven
    E.atlas E.two E.cover E.quotient _ _ U MU (𝟙 _) gU hU
  obtain ⟨ekU, hekU, _⟩ := classifying_cotangent_hodge k L hL heven
    D.atlas D.two D.cover D.quotient _ _ U MU f aU haU
  let d : weight E ≅ Cotangent U :=
    ((Scheme.Modules.pullbackId _).app (weight E)).symm ≪≫ elU
  let e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E := ekU ≪≫ d.symm
  have he : HodgeCompatible ι D E f e := by
    intro S σ F M b g a hl hk el ek hel hek
    obtain ⟨q, ⟨hq, hqg⟩, _⟩ := marked_cartesian_reconstruction l L hL heven
      E.atlas E.two E.cover E.quotient (OpenBase l L E) S
      (openStructure l L E) σ U F MU M b (𝟙 _) b gU g
      hl.1 hU hl (Category.comp_id _).symm
    have hqa : q ≫ aU = a := by
      have hc := SchemeFullLevelUniversal.classifies_comp D.atlas
        (show b ≫ (openStructure l L E ≫ constants ι) = σ ≫ constants ι by
          rw [← Category.assoc]
          exact congrArg (fun t => t ≫ constants ι) hl.1) hq haU
      exact (scheme_classifying_uniqueness k L hL heven D.atlas D.two D.canonical
        D.cover D.quotient S (σ ≫ constants ι) F M
        (b ≫ f) (b ≫ f) (q ≫ aU) a hc hk).2
    obtain ⟨i, hi, _⟩ := cartesian_identity_ideal _ _ U F b q hq.1 hq.2.1
    let c := cotangentComparison U F b q hq.2.1 i
    have hc : CotangentCompatible U F b q hq.2.1 c := ⟨i, hi, rfl⟩
    have hnL := OpenHodgeComparisonProof.natural_general E U F b q hq.2.1
      (𝟙 _) b (Category.comp_id _) gU g hqg elU el c helU hel hc
    rw [← Category.assoc, OpenHodgeComparisonProof.pullback_right_unit] at hnL
    have hd : (Scheme.Modules.pullback b).map d.hom ≫ c.hom = el.hom := by
      apply (cancel_epi ((Scheme.Modules.pullback b).map
        ((Scheme.Modules.pullbackId _).hom.app (weight E)))).mp
      dsimp only [d, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
      simp only [← Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, Category.id_comp]
      exact hnL
    have hnK := OpenHodgeComparisonProof.natural_general D U F b q hq.2.1
      f (b ≫ f) rfl aU a hqa ekU ek c hekU hek hc
    simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] at hnK
    change (Scheme.Modules.pullback b).map (ekU.hom ≫ d.inv) ≫ el.hom = _
    rw [Functor.map_comp, Category.assoc, ← hd, ← Category.assoc
      ((Scheme.Modules.pullback b).map d.inv), ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact hnK
  refine ⟨e, he, ?_⟩
  intro e' he'
  have h1 := he' (OpenBase l L E) (openStructure l L E) U MU (𝟙 _) gU aU
    hU haU' elU ekU helU hekU
  have h2 := he (OpenBase l L E) (openStructure l L E) U MU (𝟙 _) gU aU
    hU haU' elU ekU helU hekU
  apply Iso.ext
  apply OpenHodgeComparisonProof.identity_detects
  exact (cancel_mono elU.hom).mp (h1.trans h2.symm)

#print axioms open_hodge_constant_comparison
end ArithmeticThetaLevelConstantsR0234
