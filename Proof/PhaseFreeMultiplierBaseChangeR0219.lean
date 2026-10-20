module

public import PhaseFreeMultiplierR0219

@[expose] public section

/-! Arbitrary pointed Cartesian base change of the phase-free multiplier.
The frame on a test is transported from its composite test over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219.BaseChangeProof
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPullback
open ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (E : Family S) (P : EvenPoint E)
  (F : Family T) (Q : EvenPoint F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hb : Cartesian E F b f) (hQ : Q.point.val ≫ f = b ≫ P.point.val)

abbrev compositeTest (B : MarkedTest F Q) : MarkedTest E P where
  base := B.base
  family := B.family
  marking := B.marking
  map := B.map ≫ b
  comparison := B.comparison ≫ f
  cartesian := SchemeFourCover.cartesian_comp E F B.family b f hb
    B.map B.comparison B.cartesian
  characteristic := by rw [← Category.assoc, B.characteristic, Category.assoc, hQ, Category.assoc]

abbrev compositeMap {A B : MarkedTest F Q} (H : TestMap F Q A B) :
    TestMap E P (compositeTest E P F Q b f hb hQ A) (compositeTest E P F Q b f hb hQ B) where
  map := H.map
  commutes := by dsimp [compositeTest]; rw [← Category.assoc, H.commutes]
  familyMap := H.familyMap
  marked := H.marked
  triangle := by dsimp [compositeTest]; rw [← Category.assoc, H.triangle]

def pulledFrames (L : S.Modules) (m : Frames E P L) :
    Frames F Q ((Scheme.Modules.pullback b).obj L) := fun B =>
  ((Scheme.Modules.pullbackComp B.map b).app L).inv.app ⊤
    (m (compositeTest E P F Q b f hb hQ B))

lemma pulledFrames_natural (L : S.Modules) (m : Frames E P L)
    (hm : IsMultiplier E P L m) (A B : MarkedTest F Q) (H : TestMap F Q A B) :
    testPull F Q ((Scheme.Modules.pullback b).obj L) H
      (pulledFrames E P F Q b f hb hQ L m B) = pulledFrames E P F Q b f hb hQ L m A := by
  let cA := (Scheme.Modules.pullbackComp A.map b).app L
  let cB := (Scheme.Modules.pullbackComp B.map b).app L
  let G := compositeMap E P F Q b f hb hQ H
  have hc := τ_paste_app H.map B.map b A.map (B.map ≫ b) (A.map ≫ b)
    H.commutes rfl rfl L
  have he : (((Scheme.Modules.pullbackComp H.map B.map).app ((Scheme.Modules.pullback b).obj L)) ≪≫
      (Scheme.Modules.pullbackCongr H.commutes).app ((Scheme.Modules.pullback b).obj L)).hom ≫ cA.hom =
    (Scheme.Modules.pullback H.map).map cB.hom ≫
      (((Scheme.Modules.pullbackComp G.map (compositeTest E P F Q b f hb hQ B).map).app L) ≪≫
        (Scheme.Modules.pullbackCongr G.commutes).app L).hom := by
    simpa only [G, compositeMap, compositeTest, cA, cB, τ, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Scheme.Modules.pullbackCongr,
      eqToIso.hom, eqToHom_refl, eqToHom_app, Category.comp_id] using hc
  apply (ConcreteCategory.bijective_of_isIso (cA.hom.app ⊤)).1
  have hs := congrArg (fun g => g.app ⊤ (pullbackGlobalSection H.map _
    (pulledFrames E P F Q b f hb hQ L m B))) he
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hs
  change cA.hom.app ⊤ (testPull F Q _ H (pulledFrames E P F Q b f hb hQ L m B)) = _ at hs
  have hB : cB.hom.app ⊤ (pulledFrames E P F Q b f hb hQ L m B) =
      m (compositeTest E P F Q b f hb hQ B) := MultiplierBaseChange.iso_hom_inv_section cB _
  have hA : cA.hom.app ⊤ (pulledFrames E P F Q b f hb hQ L m A) =
      m (compositeTest E P F Q b f hb hQ A) := MultiplierBaseChange.iso_hom_inv_section cA _
  have hn := MultiplierBaseChange.global_app H.map cB.hom
    (pulledFrames E P F Q b f hb hQ L m B)
  have hn' := hn.trans (congrArg (pullbackGlobalSection H.map _) hB)
  have ht := congrArg
    (fun t => ((((Scheme.Modules.pullbackComp G.map
      (compositeTest E P F Q b f hb hQ B).map).app L) ≪≫
      (Scheme.Modules.pullbackCongr G.commutes).app L).hom.app ⊤ t)) hn'
  exact hs.trans (ht.trans ((hm.2.2.1 _ _ G).trans hA.symm))

lemma pulledFrames_multiplier (L : S.Modules) (m : Frames E P L)
    (hm : IsMultiplier E P L m) :
    IsMultiplier F Q ((Scheme.Modules.pullback b).obj L) (pulledFrames E P F Q b f hb hQ L m) := by
  refine ⟨hm.1.pullback b, ?_, pulledFrames_natural E P F Q b f hb hQ L m hm, ?_, ?_⟩
  · intro B
    exact frame_iso ((Scheme.Modules.pullbackComp B.map b).app L).symm
      (m (compositeTest E P F Q b f hb hQ B))
      (hm.2.1 (compositeTest E P F Q b f hb hQ B))
  · intro B N hN z hz g hg hchange
    have hN' : ArithmeticThetaUniversalEvaluationR0213.evenPoint B.family N ≫
        (B.comparison ≫ f) = (B.map ≫ b) ≫ P.point.val := by
      rw [← Category.assoc, hN, Category.assoc, hQ, Category.assoc]
    have h := hm.2.2.2.1 (compositeTest E P F Q b f hb hQ B) N hN' z hz g hg hchange
    dsimp only [pulledFrames, compositeTest, remark] at h ⊢
    rw [h, Scheme.Modules.Hom.app_smul]
  · intro B N hN hchange
    have hN' : ArithmeticThetaUniversalEvaluationR0213.evenPoint B.family N ≫
        (B.comparison ≫ f) = (B.map ≫ b) ≫ P.point.val := by
      rw [← Category.assoc, hN, Category.assoc, hQ, Category.assoc]
    have h := hm.2.2.2.2 (compositeTest E P F Q b f hb hQ B) N hN' hchange
    dsimp only [pulledFrames, compositeTest, remark] at h ⊢
    rw [h]

abbrev relativeAsTest {A : MarkedTest E P} {B : MarkedTest F Q}
    (H : RelativeTestMap E P F Q b f A B) :
    TestMap E P (compositeTest E P F Q b f hb hQ B) A :=
  ⟨H.map, H.commutes, H.familyMap, H.marked, H.triangle⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma square_frame (L : S.Modules) (m : Frames E P L) (hm : IsMultiplier E P L m)
    (A : MarkedTest E P) (B : MarkedTest F Q) (H : RelativeTestMap E P F Q b f A B) :
    (testSquare E P F Q b f H L).inv.app ⊤ (pullbackGlobalSection H.map _ (m A)) =
      pulledFrames E P F Q b f hb hQ L m B := by
  have h := hm.2.2.1 (compositeTest E P F Q b f hb hQ B) A
    (relativeAsTest E P F Q b f hb hQ H)
  have h' := congrArg (fun t => ((Scheme.Modules.pullbackComp B.map b).app L).inv.app ⊤ t) h
  simpa only [testSquare, testPull, relativeAsTest, pulledFrames, compositeTest,
    Functor.comp_obj,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Scheme.Modules.pullbackCongr,
    Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app] using h'

def identityRelative (B : MarkedTest F Q) :
    RelativeTestMap E P F Q b f (compositeTest E P F Q b f hb hQ B) B where
  map := 𝟙 B.base
  commutes := by simp
  familyMap := 𝟙 B.family.curve
  marked := by
    let D : Cover F := ⟨B.base, B.map, B.family, B.comparison, B.cartesian, B.marking⟩
    exact (EvenCoverTorsor.coverMap_refl F D).2.1
  triangle := by simp

lemma compatible_iff (L : S.Modules) (m : Frames E P L) (hm : IsMultiplier E P L m)
    (K : T.Modules) (n : Frames F Q K) (v : (Scheme.Modules.pullback b).obj L ≅ K) :
    Compatible E P F Q b f L K m n v ↔
      PreservesFrames F Q (pulledFrames E P F Q b f hb hQ L m) n v := by
  constructor
  · intro hv B
    have h := hv (compositeTest E P F Q b f hb hQ B) B (identityRelative E P F Q b f hb hQ B)
    rw [square_frame E P F Q b f hb hQ L m hm] at h
    exact h
  · intro hv A B H
    rw [square_frame E P F Q b f hb hQ L m hm]
    exact hv B

end ArithmeticThetaPhaseFreeKeyR0219.BaseChangeProof

namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open BaseChangeProof

/-- The unique multiplier comparison on every pointed Cartesian base change,
including nonflat maps, characterized on all relative marked tests. -/
theorem phase_free_multiplier_base_change
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    (E : Family S) (P : EvenPoint E) (L : S.Modules) (m : Frames E P L)
    (hm : IsMultiplier E P L m) (T : Scheme.{u}) (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hb : Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val) (K : T.Modules) (n : Frames F Q K)
    (hn : IsMultiplier F Q K n) :
    ∃! v : (Scheme.Modules.pullback b).obj L ≅ K, Compatible E P F Q b f L K m n v := by
  let mb := pulledFrames E P F Q b f hb hQ L m
  have hmb := pulledFrames_multiplier E P F Q b f hb hQ L m hm
  obtain ⟨v, hv⟩ := MultiplierProof.multiplier_iso_exists F Q k (b ≫ σ) mb n hmb hn
  refine ⟨v, (compatible_iff E P F Q b f hb hQ L m hm K n v).2 hv, ?_⟩
  intro w hw
  exact MultiplierProof.frame_preserving_unique F Q k (b ≫ σ) mb n hmb hn w v
    ((compatible_iff E P F Q b f hb hQ L m hm K n w).1 hw) hv

#print axioms phase_free_multiplier_base_change
end ArithmeticThetaPhaseFreeKeyR0219
