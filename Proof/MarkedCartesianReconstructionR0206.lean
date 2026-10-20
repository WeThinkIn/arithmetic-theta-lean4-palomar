module

public import PointedCartesianGroupLawR0204

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

/-- Recover the unique marked Cartesian arrow from compatible classifiers. -/
theorem marked_cartesian_reconstruction :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C), ∀ (S T : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E L) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F L) (a : Quiver.Hom T S) (b : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring)) (c : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring)) (f : Quiver.Hom E.curve A.descent.family.curve) (g : Quiver.Hom F.curve A.descent.family.curve), CategoryTheory.CategoryStruct.comp a σ = τ → ArithmeticThetaSchemeLevelR0204.Classifies k L A B C Q σ E M b f → ArithmeticThetaSchemeLevelR0204.Classifies k L A B C Q τ F N c g → c = CategoryTheory.CategoryStruct.comp a b → ∃! q : Quiver.Hom F.curve E.curve, ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N a q ∧ CategoryTheory.CategoryStruct.comp q f = g := by
  intro k _ _ L hL heven A B C Q S T σ τ E F M N a b c f g ha hE hF hc
  let q := hE.2.1.lift g (F.p ≫ a) (by
    rw [Category.assoc, ← Category.assoc a b, ← hc]
    exact hF.2.1.w)
  have hqf : q ≫ f = g := hE.2.1.lift_fst _ _ _
  have hqp : q ≫ E.p = F.p ≫ a := hE.2.1.lift_snd _ _ _
  have hq : IsPullback q F.p E.p a := by
    have hout : IsPullback (q ≫ f) F.p A.descent.family.projection
        (a ≫ (b ≫ Q.inclusion)) := by
      rw [hqf, ← Category.assoc, ← hc]
      exact hF.2.1
    exact hout.of_right hqp hE.2.1
  have sec (s : T ⟶ F.curve) (t : S ⟶ E.curve)
      (hs : s ≫ F.p = 𝟙 T) (ht : t ≫ E.p = 𝟙 S)
      (he : s ≫ g = a ≫ (t ≫ f)) : s ≫ q = a ≫ t := by
    apply hE.2.1.hom_ext
    · simpa only [Category.assoc, hqf] using he
    · rw [Category.assoc, hqp, ← Category.assoc, hs, Category.id_comp,
        Category.assoc, ht, Category.comp_id]
  have hz : F.zero ≫ q = a ≫ E.zero := by
    apply sec _ _ (F.law.one (𝟙 T)).property (E.law.one (𝟙 S)).property
    change F.zero ≫ g = a ≫ (E.zero ≫ f)
    rw [hF.2.2.1, hE.2.2.1, hc]
    simp only [Category.assoc]
  have hx : N.x.val ≫ q = a ≫ M.x.val := by
    apply sec _ _ N.x.property M.x.property
    rw [hF.2.2.2.1, hE.2.2.2.1, hc]
    simp only [Category.assoc]
  have hy : N.y.val ≫ q = a ≫ M.y.val := by
    apply sec _ _ N.y.property M.y.property
    rw [hF.2.2.2.2.1, hE.2.2.2.2.1, hc]
    simp only [Category.assoc]
  refine ⟨q, ⟨⟨hq, hz, pointed_cartesian_group_law k S T σ E F a q hq hz,
    hx, hy⟩, hqf⟩, ?_⟩
  intro r hr
  apply hE.2.1.hom_ext
  · exact hr.2.trans hqf.symm
  · exact hr.1.1.w.trans hqp.symm

#print axioms marked_cartesian_reconstruction
end ArithmeticThetaMetaplecticComparisonR0206
