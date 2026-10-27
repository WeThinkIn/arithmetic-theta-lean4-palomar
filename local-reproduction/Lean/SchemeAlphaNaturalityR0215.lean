import SchemeAlphaSectionR0215

/-! Signed alpha is natural for the actual marked Cartesian family map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemeAlphaNaturality
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open SchemeAlphaSection

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (M : FullLevel E 4) (N : FullLevel F 4)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hb : MarkedCartesian E F M N b f)

private lemma mul_base_congr {U : Scheme.{u}} {a b : U ⟶ S} (h : a = b)
    (x y : SchemeHomOver a E.p) (x' y' : SchemeHomOver b E.p)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (E.law.mul a x y).val = (E.law.mul b x' y').val := by
  subst b
  have hxx : x = x' := Subtype.ext hx
  have hyy : y = y' := Subtype.ext hy
  rw [hxx, hyy]

/-- Compose an arbitrary test with the given family map. The ring, equation,
origin, law and full marking of the test are retained literally. -/
def composeTest (P : AffineTest F N) : AffineTest E M where
  ring := P.ring
  equation := P.equation
  elliptic := P.elliptic
  law := P.law
  originLaw := P.originLaw
  base := P.base ≫ b
  comparison := P.comparison ≫ f
  cartesian := P.cartesian.paste_horiz hb.1
  zero_eq := by rw [← Category.assoc, P.zero_eq, Category.assoc, hb.2.1, Category.assoc]
  mul_eq := by
    intro U t x y x' y' hx hy
    let xp : SchemeHomOver (t ≫ P.base) F.p :=
      ⟨x.val ≫ P.comparison, by rw [Category.assoc, P.cartesian.w, ← Category.assoc, x.property]⟩
    let yp : SchemeHomOver (t ≫ P.base) F.p :=
      ⟨y.val ≫ P.comparison, by rw [Category.assoc, P.cartesian.w, ← Category.assoc, y.property]⟩
    let xx : SchemeHomOver ((t ≫ P.base) ≫ b) E.p :=
      ⟨x'.val, x'.property.trans (Category.assoc _ _ _).symm⟩
    let yy : SchemeHomOver ((t ≫ P.base) ≫ b) E.p :=
      ⟨y'.val, y'.property.trans (Category.assoc _ _ _).symm⟩
    have hm := hb.2.2.1 U (t ≫ P.base) xp yp xx yy
      (hx.trans (Category.assoc _ _ _).symm) (hy.trans (Category.assoc _ _ _).symm)
    have hp := P.mul_eq U t x y xp yp rfl rfl
    exact (mul_base_congr E (Category.assoc t P.base b).symm x' y' xx yy rfl rfl).trans
      (hm.trans ((congrArg (fun z => z ≫ f) hp).trans (Category.assoc _ _ _)))
  level := P.level
  x_eq := by rw [← Category.assoc, P.x_eq, Category.assoc, hb.2.2.2.1, Category.assoc]
  y_eq := by rw [← Category.assoc, P.y_eq, Category.assoc, hb.2.2.2.2, Category.assoc]

/-- Existence and uniqueness retain the specified identity-ideal inclusion. -/
lemma cotangent_exists_unique :
    ∃! e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F,
      CotangentCompatible E F b f hb.2.1 e := by
  obtain ⟨i, hi, hu⟩ := cartesian_identity_ideal S T E F b f hb.1 hb.2.1
  refine ⟨cotangentComparison E F b f hb.2.1 i, ⟨i, hi, rfl⟩, ?_⟩
  rintro e ⟨j, hj, rfl⟩
  rw [hu j hj]

/-- Coherence with an explicit identity section. This formulation transports
its equality before instantiating the dependent conormal expressions. -/
lemma comparison_comp_explicit {U : Scheme.{u}} (G : Family U)
    (c : U ⟶ T) (g : G.curve ⟶ F.curve) (t : U ⟶ G.curve) (ht : t = G.zero)
    (hg : t ≫ g = c ≫ F.zero)
    (hgf : t ≫ (g ≫ f) = (c ≫ b) ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hb.2.1 e)
    (j : (Scheme.Modules.pullback g).obj F.zero.ker.module ≅ t.ker.module)
    (i : (Scheme.Modules.pullback (g ≫ f)).obj E.zero.ker.module ≅ t.ker.module)
    (hj : j.hom ≫ t.ker.moduleι = (Scheme.Modules.pullback g).map F.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ g).hom)
    (hi : i.hom ≫ t.ker.moduleι = (Scheme.Modules.pullback (g ≫ f)).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ (g ≫ f)).hom) :
    (Scheme.Modules.pullback c).map e.hom ≫
      (squarePullbackIso c F.zero t g hg.symm F.zero.ker.module).hom ≫
      (Scheme.Modules.pullback t).map j.hom =
    ((Scheme.Modules.pullbackComp c b).app (Cotangent E)).hom ≫
      (squarePullbackIso (c ≫ b) E.zero t (g ≫ f) hgf.symm E.zero.ker.module).hom ≫
      (Scheme.Modules.pullback t).map i.hom := by
  subst t
  exact scheme_cotangent_coherence.2 S T U E F G b c f g hb.2.1 hg hgf
    e (cotangentComparison F G c g hg j)
    (cotangentComparison E G (c ≫ b) (g ≫ f) hgf i)
    he ⟨j, hj, rfl⟩ ⟨i, hi, rfl⟩

lemma test_hodge_comp (P : AffineTest F N)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hb.2.1 e) :
    (Scheme.Modules.pullback P.base).map e.hom ≫
      affineHodgeMap F N P (idealIso F N P) =
    ((Scheme.Modules.pullbackComp P.base b).app (Cotangent E)).hom ≫
      affineHodgeMap E M (composeTest E F M N b f hb P)
        (idealIso E M (composeTest E F M N b f hb P)) := by
  have h := comparison_comp_explicit E F M N b f hb
    (MarkedAffineTestComparison.family F N P) P.base P.comparison
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)
    (MarkedAffineTestComparison.family_zero F N P).symm P.zero_eq
    (composeTest E F M N b f hb P).zero_eq e he
    (idealIso F N P) (idealIso E M (composeTest E F M N b f hb P))
    (idealIso_compatible F N P) (idealIso_compatible E M (composeTest E F M N b f hb P))
  exact congrArg (fun q => q ≫
    ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap
      (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation)
      (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)) h

/-- The affine comparison on a composed test is the composite of the specified
cotangent comparison with the original affine comparison. -/
lemma hodgeIso_comp (P : AffineTest F N)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hb.2.1 e) :
    SchemeAlphaSection.hodgeIso E M (composeTest E F M N b f hb P) =
      composeComparison b P.base (P.base ≫ b) rfl (Cotangent E) (Cotangent F)
        (Hodge P.ring P.equation) e (SchemeAlphaSection.hodgeIso F N P) := by
  apply Iso.ext
  change affineHodgeMap E M (composeTest E F M N b f hb P)
      (idealIso E M (composeTest E F M N b f hb P)) =
    𝟙 _ ≫ ((Scheme.Modules.pullbackComp P.base b).app (Cotangent E)).inv ≫
      (Scheme.Modules.pullback P.base).map e.hom ≫ affineHodgeMap F N P (idealIso F N P)
  rw [Category.id_comp]
  apply (cancel_epi ((Scheme.Modules.pullbackComp P.base b).app (Cotangent E)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (test_hodge_comp E F M N b f hb P e he).symm

/-- The comparison equality acts on the actual global section, including on
an empty test, with no restriction on the test base map. -/
lemma affineAlpha_comp (P : AffineTest F N)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hb.2.1 e)
    (a : Γ(Cotangent E, ⊤)) :
    affineAlpha E M (composeTest E F M N b f hb P)
        (idealIso E M (composeTest E F M N b f hb P)) a =
      affineAlpha F N P (idealIso F N P) (pullAlpha E F b e a) := by
  have h := composeComparison_section b P.base (P.base ≫ b) rfl
    (Cotangent E) (Cotangent F) (Hodge P.ring P.equation) e (SchemeAlphaSection.hodgeIso F N P)
    ⊤ a ⊤ (by simp) (by simp)
  rw [← hodgeIso_comp E F M N b f hb P e he] at h
  change (SchemeAlphaSection.hodgeIso E M (composeTest E F M N b f hb P)).hom.app _
      (Scheme.Modules.pullbackLocalSection (P.base ≫ b) a) =
    (SchemeAlphaSection.hodgeIso F N P).hom.app _
      (Scheme.Modules.pullbackLocalSection P.base
        (e.hom.app _ (Scheme.Modules.pullbackLocalSection b a)))
  simpa only [res_refl, composeTest] using h

lemma pull_realizes
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hb.2.1 e)
    (a : Γ(Cotangent E, ⊤)) (ha : RealizesAlpha E M a) :
    RealizesAlpha F N (pullAlpha E F b e a) := by
  apply (realizes_iff F N _).mpr
  intro P
  rw [← affineAlpha_comp E F M N b f hb P e he a]
  exact (realizes_iff E M a).mp ha (composeTest E F M N b f hb P)

end SchemeAlphaNaturality

/-- The inclusion-normalized cotangent comparison transports the intrinsic
signed alpha along every marked Cartesian family map. -/
theorem scheme_alpha_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (hb : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f), (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 e) ∧ (∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 e → ∀ (a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤)) (a' : (ArithmeticThetaSchemeHodgeR0205.Cotangent F).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha F N a' → ArithmeticThetaSchemeFourCharacterR0215.pullAlpha E F b e a = a') := by
  intro k _ _ S σ E M T τ F N b f hbase hb
  refine ⟨SchemeAlphaNaturality.cotangent_exists_unique E F M N b f hb, ?_⟩
  intro e he a a' ha ha'
  exact SchemeAlphaSection.realizes_unique F N k τ
    (SchemeAlphaNaturality.pull_realizes E F M N b f hb e he a ha) ha'

end ArithmeticThetaSchemeFourCharacterR0215

#print axioms ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_naturality
