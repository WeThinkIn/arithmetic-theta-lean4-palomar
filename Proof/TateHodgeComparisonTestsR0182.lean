module

public import BoundaryHodgeDefinitionsR0182

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181

namespace TateHodgeComparisonTests

lemma comparison_nsmul (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D)
    (f : Curve (LaurentSeries k) (TateCurve k L) ⟶ D.atlas.descent.family.curve)
    (hf : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two
      D.cover D.quotient (LaurentSeries k) (TateCurve k L) E.law E.marking b f) :
    ∀ n, E.law.schemeNsmul n ≫ f = f ≫ D.atlas.descent.family.law.schemeNsmul n := by
  letI := E.elliptic
  let ι : D.atlas.quotient.ring →+* LaurentSeries k := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have hi : Spec.map (CommRingCat.ofHom ι) = b ≫ D.quotient.inclusion :=
    Spec.map_preimage _
  have hp : IsPullback f (structureMap (LaurentSeries k) (TateCurve k L))
      D.atlas.descent.family.projection (Spec.map (CommRingCat.ofHom ι)) := by
    rw [hi]; exact hf.2.1
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι D.atlas.descent.family.projection (structureMap (LaurentSeries k) (TateCurve k L))
    f hp (ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.toWeierstrassLaw D.atlas.descent.family.law)
  have hone : (E.law.one (𝟙 _)).val = (H.one (𝟙 _)).val := by
    apply hp.hom_ext
    · rw [E.originLaw.1, Category.id_comp, hf.2.2.1, ho, Category.id_comp, hi]
      exact congrArg Subtype.val
        (D.atlas.descent.family.law.one_natural (𝟙 _) (b ≫ D.quotient.inclusion)
          (b ≫ D.quotient.inclusion) (Category.comp_id _))
    · exact (E.law.one (𝟙 _)).property.trans (H.one (𝟙 _)).property.symm
  have hlaw : E.law = H :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext E.law H
      (fun t x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
        (TateCurve k L).toProjective E.law H hone t x y)
      (by
        intro T t
        apply Subtype.ext
        have h1 := congrArg Subtype.val (E.law.one_natural (𝟙 _) t t (Category.comp_id t))
        have h2 := congrArg Subtype.val (H.one_natural (𝟙 _) t t (Category.comp_id t))
        exact h1.symm.trans ((congrArg (fun z => t ≫ z) hone).trans h2))
  intro n
  rw [hlaw]
  exact ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    ι (structureMap (LaurentSeries k) (TateCurve k L)) f hp
    (ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.toWeierstrassLaw D.atlas.descent.family.law) H hm ho n

lemma normalized_frame (k : Type) [Field k] [CharZero k] (L : ℕ)
    (hL : 3 ≤ L) (heven : Even L) (E : TateLevel k L) :
    ∃ δ : CurveFrame k L, Normalized k L δ := by
  letI := E.elliptic
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k L)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k L).toProjective
  have hΩ : Scheme.Modules.IsInvertible
      (structureMap (LaurentSeries k) (TateCurve k L)).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap (LaurentSeries k) (TateCurve k L)).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  exact ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.lifted_global_frame
    k L (Iso.refl _) hL heven (structureMap (LaurentSeries k) (TateCurve k L))
    (Category.id_comp _) hΩ

end TateHodgeComparisonTests

theorem tate_hodge_comparison_tests :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (D : LevelData k L),
      (∀ (E : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
        ClassifiesTate k L D E b → ∃ V : Test k L D, V.level = E ∧ V.base = b) ∧
      (∀ [IsAlgClosed k] (X : Compactification k L D) (x : X.space),
        x ∈ boundary k L D X → ∃ V : DiskTest k L D X, V.disk (closedPoint k) = x) := by
  intro k _ _ L hL heven D
  have enrich : ∀ (E : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E b → ∃ V : Test k L D, V.level = E ∧ V.base = b := by
    intro E b hb
    obtain ⟨f, hf⟩ := hb
    obtain ⟨δ, hδ⟩ := TateHodgeComparisonTests.normalized_frame k L hL heven E
    exact ⟨⟨E, b, f, hf, TateHodgeComparisonTests.comparison_nsmul k L D E b f hf,
      δ, hδ⟩, rfl, rfl⟩
  refine ⟨enrich, ?_⟩
  intro _ X x hx
  obtain ⟨E, b, d, hb, hd, hdx⟩ := every_geometric_boundary_tate_disk k L hL heven D X x hx
  obtain ⟨V, _, hVb⟩ := enrich E b hb
  exact ⟨{ toTest := V, disk := d, extends_eq := hVb.symm ▸ hd }, hdx⟩

#print axioms tate_hodge_comparison_tests
end ArithmeticThetaBoundaryHodgeR0182
