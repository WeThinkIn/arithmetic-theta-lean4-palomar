module

public import InverseCharacterMultiplierR0217
public import EvenCoverBaseChangeR0216

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite TopologicalSpace
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier.Transport
open ArithmeticThetaFourTorsion
open ArithmeticThetaPullback

namespace MultiplierBaseChange

lemma cover_change_action
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤))
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D)
    (T : Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
    (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val)
    (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover F)
    (B : CoverChange E D F b f C)
    (A : EvenGroup)
    (qC : C.space ≅ C.space) (hqC : Acts F C A.val qC)
    (qD : D.space ≅ D.space) (hqD : Acts E D A.val qD) :
    qC.hom ≫ B.map = B.map ≫ qD.hom := by
  apply parameter_ext E k σ P z D hD
  · calc
      (qC.hom ≫ B.map) ≫ D.projection = qC.hom ≫ (B.map ≫ D.projection) := by simp [Category.assoc]
      _ = qC.hom ≫ (C.projection ≫ b) := by rw [B.commutes]
      _ = (qC.hom ≫ C.projection) ≫ b := by simp [Category.assoc]
      _ = C.projection ≫ b := by rw [hqC.1]
      _ = B.map ≫ D.projection := B.commutes.symm
      _ = (B.map ≫ qD.hom) ≫ D.projection := by rw [Category.assoc, hqD.1]
  · calc
      (qC.hom ≫ B.map) ≫ D.marking.x.val ≫ D.comparison =
          qC.hom ≫ (B.map ≫ D.marking.x.val) ≫ D.comparison := by simp [Category.assoc]
      _ = qC.hom ≫ (C.marking.x.val ≫ B.familyMap) ≫ D.comparison := by
        rw [B.marked.2.2.2.1]
      _ = (qC.hom ≫ C.marking.x.val ≫ C.comparison) ≫ f := by
        exact congrArg (fun g => qC.hom ≫ C.marking.x.val ≫ g) B.triangle
      _ = (ArithmeticThetaEvenMarkingTorsorR0216.changedX C.family C.marking A.val ≫ C.comparison) ≫ f := by
        rw [hqC.2.1]
      _ = (B.map ≫ ArithmeticThetaEvenMarkingTorsorR0216.changedX D.family D.marking A.val ≫ D.comparison) := by
        simp only [Category.assoc]
        rw [← B.triangle]
        simp only [← Category.assoc]
        rw [EvenCoverRightAction.changed_comp D.family C.family D.marking C.marking
          B.map B.familyMap B.marked A |>.1]
      _ = (B.map ≫ qD.hom) ≫ D.marking.x.val ≫ D.comparison := by
        rw [Category.assoc, hqD.2.1]
  · calc
      (qC.hom ≫ B.map) ≫ D.marking.y.val ≫ D.comparison =
          qC.hom ≫ (B.map ≫ D.marking.y.val) ≫ D.comparison := by simp [Category.assoc]
      _ = qC.hom ≫ (C.marking.y.val ≫ B.familyMap) ≫ D.comparison := by
        rw [B.marked.2.2.2.2]
      _ = (qC.hom ≫ C.marking.y.val ≫ C.comparison) ≫ f := by
        exact congrArg (fun g => qC.hom ≫ C.marking.y.val ≫ g) B.triangle
      _ = (ArithmeticThetaEvenMarkingTorsorR0216.changedY C.family C.marking A.val ≫ C.comparison) ≫ f := by
        rw [hqC.2.2]
      _ = (B.map ≫ ArithmeticThetaEvenMarkingTorsorR0216.changedY D.family D.marking A.val ≫ D.comparison) := by
        simp only [Category.assoc]
        rw [← B.triangle]
        simp only [← Category.assoc]
        rw [EvenCoverRightAction.changed_comp D.family C.family D.marking C.marking
          B.map B.familyMap B.marked A |>.2]
      _ = (B.map ≫ qD.hom) ≫ D.marking.y.val ≫ D.comparison := by
        rw [Category.assoc, hqD.2.2]

theorem cover_change_exists
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤)) (hz : z ^ 2 = -1)
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D)
    (T : Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
    (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val)
    (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover F)
    (hC : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven F Q (b.appTop z) C) :
    Nonempty (CoverChange E D F b f C) := by
  obtain ⟨q, hq, hqdata⟩ :=
    even_cover_base_change k S σ E P z hz D hD T F b f hb Q hQ C hC
  let hcurve := Classical.choose hq.2
  have hcurve_spec := Classical.choose_spec hq.2
  exact ⟨⟨q.val, q.property, hcurve, hcurve_spec.1, hcurve_spec.2⟩⟩

open P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 1000000
lemma action_square_coherence
    (S : Scheme.{u}) (T : Scheme.{u})
    (b : T ⟶ S)
    (Dspace : Scheme.{u}) (Cspace : Scheme.{u})
    (πD : Dspace ⟶ S) (πC : Cspace ⟶ T)
    (Bmap : Cspace ⟶ Dspace) (hB : Bmap ≫ πD = πC ≫ b)
    (qC : Cspace ≅ Cspace) (qD : Dspace ≅ Dspace)
    (hqC : qC.hom ≫ πC = πC)
    (hqD : qD.hom ≫ πD = πD)
    (hact : qC.hom ≫ Bmap = Bmap ≫ qD.hom)
    (L : S.Modules) :
    let L' := (Scheme.Modules.pullback b).obj L
    let MC := (Scheme.Modules.pullback πC).obj L'
    let MD := (Scheme.Modules.pullback πD).obj L
    let MB := (Scheme.Modules.pullback Bmap).obj MD
    let Siso := (Scheme.Modules.pullbackComp πC b).app L ≪≫
      (Scheme.Modules.pullbackCongr hB.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp Bmap πD).app L).symm
    let eC := (Scheme.Modules.pullbackComp qC.hom πC).app L' ≪≫
      (Scheme.Modules.pullbackCongr hqC).app L'
    let eD := (Scheme.Modules.pullbackComp qD.hom πD).app L ≪≫
      (Scheme.Modules.pullbackCongr hqD).app L
    let Sq := (Scheme.Modules.pullback qC.hom).map Siso.hom ≫
      (Scheme.Modules.pullbackComp qC.hom Bmap).hom.app MD ≫
      (Scheme.Modules.pullbackCongr hact).hom.app MD ≫
      (Scheme.Modules.pullbackComp Bmap qD.hom).inv.app MD
    Sq ≫ (Scheme.Modules.pullback Bmap).map eD.hom =
      eC.hom ≫ Siso.hom := by
  dsimp
  let p := πC ≫ b
  have hp : qC.hom ≫ p = p := by simp only [p, ← Category.assoc, hqC]
  have hj : (Bmap ≫ qD.hom) ≫ πD = p := by rw [Category.assoc, hqD, hB]
  let tC := τ πC b p rfl
  let tD := τ Bmap πD p hB
  let tQ := τ qC.hom p p hp
  let tA := τ qC.hom Bmap (Bmap ≫ qD.hom) hact
  let tB := τ Bmap qD.hom (Bmap ≫ qD.hom) rfl
  let tJ := τ (Bmap ≫ qD.hom) πD p hj
  let tEC := τ qC.hom πC πC hqC
  let tED := τ qD.hom πD πD hqD
  have H1 := τ_paste_app qC.hom πC b πC p p hqC rfl rfl L
  have H2 := τ_paste_app qC.hom Bmap πD (Bmap ≫ qD.hom) p p hact hB hj L
  have H3 := τ_paste_app Bmap qD.hom πD (Bmap ≫ qD.hom) πD p rfl hqD hj L
  change tEC.hom.app _ ≫ tC.hom.app L =
    (Scheme.Modules.pullback qC.hom).map (tC.hom.app L) ≫ tQ.hom.app L at H1
  change tA.hom.app _ ≫ tJ.hom.app L =
    (Scheme.Modules.pullback qC.hom).map (tD.hom.app L) ≫ tQ.hom.app L at H2
  change tB.hom.app _ ≫ tJ.hom.app L =
    (Scheme.Modules.pullback Bmap).map (tED.hom.app L) ≫ tD.hom.app L at H3
  have hs : ((Scheme.Modules.pullbackComp πC b).app L ≪≫
      (Scheme.Modules.pullbackCongr hB.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp Bmap πD).app L).symm).hom =
      tC.hom.app L ≫ tD.inv.app L := by
    simp only [tC, tD, τ_hom_app, τ_inv_app, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Scheme.Modules.pullbackCongr, eqToIso.hom,
      eqToIso.inv, eqToHom_app, eqToHom_refl, Category.comp_id, Category.assoc]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom] at hs
  rw [hs]
  change ((Scheme.Modules.pullback qC.hom).map (tC.hom.app L ≫ tD.inv.app L) ≫
    tA.hom.app _ ≫ tB.inv.app _) ≫ (Scheme.Modules.pullback Bmap).map (tED.hom.app L) =
      tEC.hom.app _ ≫ (tC.hom.app L ≫ tD.inv.app L)
  apply (cancel_mono (tD.hom.app L)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← H3, Iso.inv_hom_id_app_assoc, H2]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (Scheme.Modules.pullback qC.hom).map_comp_assoc (tD.inv.app L) (tD.hom.app L), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact H1.symm

lemma iso_hom_inv_section {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(N, ⊤)) : e.hom.app ⊤ (e.inv.app ⊤ s) = s := by
  change (e.inv ≫ e.hom).app ⊤ s = s
  rw [e.inv_hom_id]
  rfl

lemma iso_inv_hom_section {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(M, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
  change (e.hom ≫ e.inv).app ⊤ s = s
  rw [e.hom_inv_id]
  rfl

lemma square_section {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ W)
    (c : X ⟶ Z) (d : Z ⟶ W) (h : a ≫ b = c ≫ d)
    (M : W.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp a b).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp c d).app M).symm).hom.app ⊤
      (pullbackGlobalSection a _ (pullbackGlobalSection b M m)) =
      pullbackGlobalSection c _ (pullbackGlobalSection d M m) := by
  change ((Scheme.Modules.pullbackComp c d).app M).inv.app ⊤
    (((Scheme.Modules.pullbackCongr h).app M).hom.app ⊤
      (((Scheme.Modules.pullbackComp a b).app M).hom.app ⊤
        (pullbackGlobalSection a _ (pullbackGlobalSection b M m)))) = _
  rw [comp_global, congr_global, ← comp_global c d M m, iso_inv_hom_section]


lemma global_app {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (g : M ⟶ N) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map g).app ⊤ (pullbackGlobalSection f M m) =
      pullbackGlobalSection f N (g.app ⊤ m) :=
  (Scheme.Modules.pullbackLocalSection_app f g m).symm

lemma transport_over_section
    {S T D C : Scheme.{u}} (b : T ⟶ S) (πD : D ⟶ S) (πC : C ⟶ T)
    (B : C ⟶ D) (hB : B ≫ πD = πC ≫ b)
    (qC : C ≅ C) (qD : D ≅ D)
    (hqC : qC.hom ≫ πC = πC) (hqD : qD.hom ≫ πD = πD)
    (hact : qC.hom ≫ B = B ≫ qD.hom) (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback πD).obj L, ⊤)) :
    let s := (Scheme.Modules.pullbackComp πC b).app L ≪≫
      (Scheme.Modules.pullbackCongr hB.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp B πD).app L).symm
    let eC := (Scheme.Modules.pullbackComp qC.hom πC).app ((Scheme.Modules.pullback b).obj L) ≪≫
      (Scheme.Modules.pullbackCongr hqC).app ((Scheme.Modules.pullback b).obj L)
    let eD := (Scheme.Modules.pullbackComp qD.hom πD).app L ≪≫
      (Scheme.Modules.pullbackCongr hqD).app L
    eC.hom.app ⊤ (pullbackGlobalSection qC.hom _
      (s.inv.app ⊤ (pullbackGlobalSection B _ m))) =
    s.inv.app ⊤ (pullbackGlobalSection B _
      (eD.hom.app ⊤ (pullbackGlobalSection qD.hom _ m))) := by
  intro s eC eD
  let t := (Scheme.Modules.pullbackComp qC.hom B).app ((Scheme.Modules.pullback πD).obj L) ≪≫
    (Scheme.Modules.pullbackCongr hact).app ((Scheme.Modules.pullback πD).obj L) ≪≫
    ((Scheme.Modules.pullbackComp B qD.hom).app ((Scheme.Modules.pullback πD).obj L)).symm
  let mc := s.inv.app ⊤ (pullbackGlobalSection B _ m)
  have hc := action_square_coherence S T b D C πD πC B hB qC qD hqC hqD hact L
  change ((Scheme.Modules.pullback qC.hom).map s.hom ≫ t.hom) ≫
    (Scheme.Modules.pullback B).map eD.hom = eC.hom ≫ s.hom at hc
  have H := congrArg (fun φ => φ.app ⊤ (pullbackGlobalSection qC.hom _ mc)) hc
  change ((Scheme.Modules.pullback B).map eD.hom).app ⊤
    (t.hom.app ⊤ (((Scheme.Modules.pullback qC.hom).map s.hom).app ⊤
      (pullbackGlobalSection qC.hom _ mc))) =
    s.hom.app ⊤ (eC.hom.app ⊤ (pullbackGlobalSection qC.hom _ mc)) at H
  have hm : s.hom.app ⊤ mc = pullbackGlobalSection B _ m := iso_hom_inv_section s _
  have hmap : ((Scheme.Modules.pullback qC.hom).map s.hom).app ⊤
      (pullbackGlobalSection qC.hom _ mc) =
      pullbackGlobalSection qC.hom _ (pullbackGlobalSection B _ m) :=
    (global_app qC.hom s.hom mc).trans (congrArg (pullbackGlobalSection qC.hom _) hm)
  have ht : t.hom.app ⊤ (((Scheme.Modules.pullback qC.hom).map s.hom).app ⊤
      (pullbackGlobalSection qC.hom _ mc)) =
      pullbackGlobalSection B _ (pullbackGlobalSection qD.hom _ m) :=
    (congrArg (t.hom.app ⊤) hmap).trans (square_section qC.hom B B qD.hom hact _ m)
  have hfinal : s.hom.app ⊤ (eC.hom.app ⊤ (pullbackGlobalSection qC.hom _ mc)) =
      pullbackGlobalSection B _ (eD.hom.app ⊤ (pullbackGlobalSection qD.hom _ m)) :=
    H.symm.trans ((congrArg (((Scheme.Modules.pullback B).map eD.hom).app ⊤) ht).trans
      (global_app B eD.hom _))
  exact (iso_inv_hom_section s _).symm.trans (congrArg (s.inv.app ⊤) hfinal)

end MultiplierBaseChange
open MultiplierBaseChange

theorem multiplier_base_change
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤)) (hz : z ^ 2 = -1)
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D) :
    ∀ (T : Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
      (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve)
      (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f),
      Q.point.val ≫ f = b ≫ P.point.val →
      ∀ (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover F),
      ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven F Q (b.appTop z) C →
      Nonempty (CoverChange E D F b f C) ∧
      (∀ B : CoverChange E D F b f C,
        ∀ (L : S.Modules) (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤)),
        Multiplier E D z L m →
        ∀ (K : T.Modules) (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤)),
        Multiplier F C (b.appTop z) K n →
        ∃! v : (Scheme.Modules.pullback b).obj L ≅ K,
          MultiplierCompatible E D F b f C B L K m n v) := by
  intro T F Q b f hb hQ C hC
  refine ⟨cover_change_exists k S σ E P z hz D hD T F Q b f hb hQ C hC, ?_⟩
  intro B L m hm K n hn
  classical
  let mc := (coverSquare E D F b f C B L).inv.app ⊤ (pullbackGlobalSection B.map _ m)
  have hmc : Multiplier F C (b.appTop z) ((Scheme.Modules.pullback b).obj L) mc := by
    refine ⟨hm.1.pullback b, ?_, ?_⟩
    · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
        (coverSquare E D F b f C B L).symm _
        (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame B.map _ m hm.2.1)
    · intro A qC hqC
      let qD := action E k σ P z D hD A
      have hqD := action_spec E k σ P z D hD A
      have hact := cover_change_action k S σ E P z D hD T F Q b f hQ C B A qC hqC qD hqD
      have H := transport_over_section b D.projection C.projection B.map B.commutes
        qC qD hqC.1 hqD.1 hact L m
      change overPull F C ((Scheme.Modules.pullback b).obj L) qC.hom hqC.1 mc =
        (coverSquare E D F b f C B L).inv.app ⊤
          (pullbackGlobalSection B.map _ (overPull E D L qD.hom hqD.1 m)) at H
      rw [hm.2.2 A qD hqD] at H
      rw [H]
      let mb : Γ((Scheme.Modules.pullback B.map).obj
          ((Scheme.Modules.pullback D.projection).obj L), ⊤) := pullbackGlobalSection B.map _ m
      have hs : pullbackGlobalSection B.map _
          (D.projection.appTop (z ^ (3 * (characterExponent A.val).val)) • m) =
          B.map.appTop (D.projection.appTop (z ^ (3 * (characterExponent A.val).val))) •
            mb :=
        Scheme.Modules.pullbackLocalSection_smul B.map _ m
      rw [hs, Scheme.Modules.Hom.app_smul]
      have hr : B.map.appTop (D.projection.appTop (z ^ (3 * (characterExponent A.val).val))) =
          C.projection.appTop ((b.appTop z) ^ (3 * (characterExponent A.val).val)) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, B.commutes,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_pow]
      rw [hr]
  have hz' : (b.appTop z)^2 = -1 := by rw [← map_pow, hz, map_neg, map_one]
  exact multiplier_unique F k (b ≫ σ) Q (b.appTop z) C hC hz' mc n hmc hn

#print axioms multiplier_base_change

end ArithmeticThetaMultiplierKeyR0217
