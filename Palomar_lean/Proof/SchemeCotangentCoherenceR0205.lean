module

public import SchemeHodgeDefinitionsR0205
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

namespace CotangentCoherenceProof

theorem ideal_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (G : Family U)
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module)
    (j : (Scheme.Modules.pullback g).obj F.zero.ker.module ≅ G.zero.ker.module)
    (k : (Scheme.Modules.pullback (g ≫ f)).obj E.zero.ker.module ≅ G.zero.ker.module)
    (hi : IdealCompatible E F f i) (hj : IdealCompatible F G g j)
    (hk : IdealCompatible E G (g ≫ f) k) :
    (Scheme.Modules.pullback g).map i.hom ≫ j.hom =
      (Scheme.Modules.pullbackComp g f).hom.app E.zero.ker.module ≫ k.hom := by
  let : Mono G.zero.ker.moduleι := inferInstanceAs
    (Mono (Limits.kernel.ι G.zero.ker.subschemeι.unitToPushforwardUnit))
  apply (cancel_mono G.zero.ker.moduleι).mp
  dsimp [IdealCompatible] at hi hj hk
  rw [Category.assoc, hj, ← Category.assoc, ← Functor.map_comp, hi,
    Functor.map_comp, Category.assoc, Category.assoc, hk]
  have hu := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom g f
  change (Scheme.Modules.pullbackComp g f).hom.app _ ≫
    (ArithmeticThetaPullback.pullback_unit_iso _ _ (g ≫ f)).hom =
    (Scheme.Modules.pullback g).map (ArithmeticThetaPullback.pullback_unit_iso _ _ f).hom ≫
      (ArithmeticThetaPullback.pullback_unit_iso _ _ g).hom at hu
  rw [← hu, ← Category.assoc]
  exact congrArg (fun q ↦ q ≫ (ArithmeticThetaPullback.pullback_unit_iso _ _ (g ≫ f)).hom)
    ((Scheme.Modules.pullbackComp g f).hom.naturality E.zero.ker.moduleι)

theorem square_eq {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y)
    (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) :
    squarePullbackIso a s t b h M =
      (Scheme.Modules.pullbackComp a s ≪≫ Scheme.Modules.pullbackCongr h ≪≫
        (Scheme.Modules.pullbackComp t b).symm).app M := by
  have he : pullbackEqIso h M = (Scheme.Modules.pullbackCongr h).app M := by
    generalize a ≫ s = f at h ⊢
    generalize t ≫ b = g at h ⊢
    cases h
    rfl
  simp only [squarePullbackIso, he]
  rfl

theorem square_paste {S T U X Y Z : Scheme.{u}}
    (a : U ⟶ T) (b : T ⟶ S) (r : U ⟶ Z) (s : T ⟶ Y) (t : S ⟶ X)
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (hg : r ≫ g = a ≫ s) (hf : s ≫ f = b ≫ t)
    (hgf : r ≫ (g ≫ f) = (a ≫ b) ≫ t) (M : X.Modules) :
    (Scheme.Modules.pullback a).map (squarePullbackIso b t s f hf.symm M).hom ≫
      (squarePullbackIso a s r g hg.symm ((Scheme.Modules.pullback f).obj M)).hom ≫
        (Scheme.Modules.pullback r).map ((Scheme.Modules.pullbackComp g f).hom.app M) =
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback t).obj M) ≫
      (squarePullbackIso (a ≫ b) t r (g ≫ f) hgf.symm M).hom := by
  have h := Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    g f (g ≫ f) rfl r s t a b (a ≫ b) rfl hg hf hgf M
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Category.comp_id] at h
  have hs (A B X Y : Scheme.{u}) (a : A ⟶ B) (s : B ⟶ Y)
      (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) :
      (squarePullbackIso a s t b h M).inv =
        (squarePullbackIso t b a s h.symm M).hom := by
    simp only [squarePullbackIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom]
    have he : (pullbackEqIso h M).inv = (pullbackEqIso h.symm M).hom := by
      generalize a ≫ s = f at h ⊢
      generalize t ≫ b = g at h ⊢
      cases h
      rfl
    simp only [he, Category.assoc]
  have hp : (squarePullbackIso a s r g hg.symm ((Scheme.Modules.pullback f).obj M)).inv ≫
      (Scheme.Modules.pullback a).map (squarePullbackIso b t s f hf.symm M).inv ≫
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback t).obj M) =
    (Scheme.Modules.pullback r).map ((Scheme.Modules.pullbackComp g f).hom.app M) ≫
      (squarePullbackIso (a ≫ b) t r (g ≫ f) hgf.symm M).inv := by
    rw [hs, hs, hs]
    simpa only [square_eq, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Scheme.Modules.pullbackCongr, Category.assoc] using h
  apply (cancel_mono (squarePullbackIso (a ≫ b) t r (g ≫ f) hgf.symm M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hp]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

theorem unit_id (X : Scheme.{u}) :
    (ArithmeticThetaPullback.pullback_unit_iso X X (𝟙 X)).hom =
      (Scheme.Modules.pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have hi : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
      ((Scheme.Modules.pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf)) =
      (Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf) := by
    rw [← Scheme.Modules.conjugateEquiv_pullbackId_hom]
    rfl
  refine Eq.trans ?_ hi.symm
  change (SheafOfModules.pullbackPushforwardAdjunction (𝟙 X : X ⟶ X).toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit _) = _
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  rfl

theorem ideal_id {S : Scheme.{u}} (E : Family S)
    (i : (Scheme.Modules.pullback (𝟙 E.curve)).obj E.zero.ker.module ≅ E.zero.ker.module)
    (hi : IdealCompatible E E (𝟙 E.curve) i) :
    i.hom = (Scheme.Modules.pullbackId E.curve).hom.app E.zero.ker.module := by
  let : Mono E.zero.ker.moduleι := inferInstanceAs
    (Mono (Limits.kernel.ι E.zero.ker.subschemeι.unitToPushforwardUnit))
  apply (cancel_mono E.zero.ker.moduleι).mp
  rw [hi, unit_id]
  exact (Scheme.Modules.pullbackId E.curve).hom.naturality E.zero.ker.moduleι

theorem square_id {S X : Scheme.{u}} (t : S ⟶ X)
    (h : 𝟙 S ≫ t = t ≫ 𝟙 X) (M : X.Modules) :
    (squarePullbackIso (𝟙 S) t t (𝟙 X) h M).hom ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackId X).hom.app M) =
    (Scheme.Modules.pullbackId S).hom.app ((Scheme.Modules.pullback t).obj M) := by
  have hl := congrArg (fun q ↦ q.app M) (Scheme.Modules.pseudofunctor_left_unitality t)
  have hr := congrArg (fun q ↦ q.app M) (Scheme.Modules.pseudofunctor_right_unitality t)
  simp only [NatTrans.comp_app] at hl hr
  dsimp at hl hr
  simp only [Category.comp_id] at hl hr
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [hl]
  apply (cancel_epi ((Scheme.Modules.pullbackComp (𝟙 S) t).app M).inv).mp
  simp only [Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [hr]
  simp [pullbackEqIso]

theorem square_naturality {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y)
    (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b)
    {M N : Y.Modules} (q : M ⟶ N) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback s).map q) ≫
      (squarePullbackIso a s t b h N).hom =
    (squarePullbackIso a s t b h M).hom ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback b).map q) := by
  simpa only [square_eq, Iso.app_hom, Functor.comp_map] using
    (Scheme.Modules.pullbackComp a s ≪≫ Scheme.Modules.pullbackCongr h ≪≫
      (Scheme.Modules.pullbackComp t b).symm).hom.naturality q

end CotangentCoherenceProof

/-- Inclusion-normalized cotangent comparisons obey the identity and composition
constraints of the sheaf pullback pseudofunctor, on arbitrary test schemes. -/
theorem scheme_cotangent_coherence : CotangentCoherence.{u} := by
  constructor
  · intro S E hz e he
    obtain ⟨i, hi, rfl⟩ := he
    simp only [cotangentComparison, Iso.trans_hom, Functor.mapIso_hom]
    rw [CotangentCoherenceProof.ideal_id E i hi]
    exact CotangentCoherenceProof.square_id E.zero hz.symm E.zero.ker.module
  · intro S T U E F G b a f g hf hg hgf ef eg egf hef heg hegf
    obtain ⟨i, hi, rfl⟩ := hef
    obtain ⟨j, hj, rfl⟩ := heg
    obtain ⟨k, hk, rfl⟩ := hegf
    simp only [cotangentComparison, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    rw [← Category.assoc ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback F.zero).map i.hom)),
      CotangentCoherenceProof.square_naturality a F.zero G.zero g hg.symm i.hom]
    simp only [Category.assoc]
    rw [← Functor.map_comp, CotangentCoherenceProof.ideal_comp E F G f g i j k hi hj hk,
      Functor.map_comp]
    simpa only [Category.assoc, Iso.app_hom] using
      congrArg (fun q ↦ q ≫ (Scheme.Modules.pullback G.zero).map k.hom)
        (CotangentCoherenceProof.square_paste a b G.zero F.zero E.zero g f hg hf hgf
          E.zero.ker.module)

#print axioms scheme_cotangent_coherence

end ArithmeticThetaSchemeHodgeR0205
