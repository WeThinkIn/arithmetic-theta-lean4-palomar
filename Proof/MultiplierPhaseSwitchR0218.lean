module

public import EvenCoverPhaseSwitchR0218

@[expose] public section

/-! Comparison of the actual inverse-character lines at opposite phases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
namespace MultiplierPhaseSwitch
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaFourTorsion
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier.Transport
open ArithmeticThetaMultiplierKeyR0217.MultiplierBaseChange
open ArithmeticThetaPullback
open P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules

/-- Pull a section along a map over the same base, retaining its triangle. -/
def along {S X Y : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback πY).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback πX).obj L, ⊤) :=
  ((τ f πY πX hf).app L).hom.app ⊤ (pullbackGlobalSection f _ m)

lemma along_comp {S X Y Z : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S)
    (πZ : Z ⟶ S) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f ≫ πY = πX) (hg : g ≫ πZ = πY) (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback πZ).obj L, ⊤)) :
    along πX πY f hf L (along πY πZ g hg L m) =
      along πX πZ (f ≫ g) (by rw [Category.assoc, hg, hf]) L m := by
  have H := τ_paste_app f g πZ (f ≫ g) πY πX rfl hg
    (by rw [Category.assoc, hg, hf]) L
  have H' := congrArg (fun φ => φ.app ⊤
    (pullbackGlobalSection f _ (pullbackGlobalSection g _ m))) H
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at H'
  have ht : ((τ f g (f ≫ g) rfl).hom.app ((Scheme.Modules.pullback πZ).obj L)).app ⊤
      (pullbackGlobalSection f _ (pullbackGlobalSection g _ m)) =
      pullbackGlobalSection (f ≫ g) _ m := by
    simpa only [τ, Iso.trans_hom, NatTrans.comp_app, Scheme.Modules.pullbackCongr,
      eqToIso.hom, eqToHom_refl, Category.comp_id, Iso.app_hom] using comp_global f g _ m
  rw [ht] at H'
  have hn := global_app f ((τ g πZ πY hg).hom.app L) (pullbackGlobalSection g _ m)
  exact (H'.trans (congrArg (((τ f πY πX hf).hom.app L).app ⊤) hn)).symm

lemma along_natural {S X Y : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ πY = πX) {L K : S.Modules} (v : L ⟶ K)
    (m : Γ((Scheme.Modules.pullback πY).obj L, ⊤)) :
    ((Scheme.Modules.pullback πX).map v).app ⊤ (along πX πY f hf L m) =
      along πX πY f hf K (((Scheme.Modules.pullback πY).map v).app ⊤ m) := by
  have H := (τ f πY πX hf).hom.naturality v
  have H' := congrArg (fun φ => φ.app ⊤ (pullbackGlobalSection f _ m)) H
  change ((τ f πY πX hf).hom.app K).app ⊤
    (((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback πY).map v)).app ⊤
      (pullbackGlobalSection f _ m)) = _ at H'
  rw [global_app] at H'
  exact H'.symm

lemma along_smul {S X Y : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (L : S.Modules)
    (r : Γ(S, ⊤)) (m : Γ((Scheme.Modules.pullback πY).obj L, ⊤)) :
    along πX πY f hf L (πY.appTop r • m) = πX.appTop r • along πX πY f hf L m := by
  unfold along
  let mf : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πY).obj L), ⊤) :=
    pullbackGlobalSection f _ m
  have hs : pullbackGlobalSection f _ (πY.appTop r • m) =
      f.appTop (πY.appTop r) • mf :=
    Scheme.Modules.pullbackLocalSection_smul f _ m
  rw [hs, Scheme.Modules.Hom.app_smul]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf]

lemma inverse_character_switch {R : Type*} [CommRing R] (z : R) (hz : z ^ 2 = -1)
    (e : ZMod 4) : (-z) ^ (3 * (-e).val) = z ^ (3 * e.val) := by
  have h4 := phase_four z hz
  fin_cases e
  · change (-z)^0 = z^0
    simp
  · change (-z)^9 = z^3
    grind
  · change (-z)^6 = z^6
    ring
  · change (-z)^3 = z^9
    grind

variable {S : Scheme.{u}} (E : Family S) (D C : Cover E)

lemma switch_multiplier (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1)
    (hC : RepresentsEven E P (-z) C)
    (q : D.space ≅ C.space) (h : Switches E D C q)
    (K : S.Modules) (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (hn : Multiplier E C (-z) K n) :
    Multiplier E D z K (switchPull E D C q h K n) := by
  refine ⟨hn.1, ?_, ?_⟩
  · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      (((Scheme.Modules.pullbackComp q.hom C.projection).app K) ≪≫
        (Scheme.Modules.pullbackCongr h.1).app K) _
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame q.hom _ n hn.2.1)
  · intro A a ha
    let B : EvenGroup := ⟨conjugate A.val, (reversal_character.2.2.1 A.val).mpr A.property⟩
    let b := action E k σ P (-z) C hC B
    have hb := action_spec E k σ P (-z) C hC B
    have he := EvenCoverPhaseSwitch.switch_equivariant E k σ P z D C hC q h A.val A.property a b ha hb
    change along D.projection D.projection a.hom ha.1 K
      (along D.projection C.projection q.hom h.1 K n) = _
    rw [along_comp]
    have H : along D.projection C.projection (a.hom ≫ q.hom) (by rw [Category.assoc, h.1, ha.1]) K n =
        along D.projection C.projection q.hom h.1 K
          (along C.projection C.projection b.hom hb.1 K n) := by
      rw [along_comp]
      congr 1
    rw [H]
    change along D.projection C.projection q.hom h.1 K (overPull E C K b.hom hb.1 n) = _
    rw [hn.2.2 B b hb, along_smul]
    have hc : (-z) ^ (3 * (characterExponent B.val).val) = z ^ (3 * (characterExponent A.val).val) := by
      rw [show characterExponent B.val = -characterExponent A.val from reversal_character.2.2.2.1 A.val A.property]
      exact inverse_character_switch z hz _
    rw [hc]
    rfl


lemma along_identity (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (z : Γ(S, ⊤)) (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (hm : Multiplier E D z L m) :
    along D.projection D.projection (𝟙 D.space) (Category.id_comp _) L m = m := by
  have H := hm.2.2 (⟨1, EvenCoverRightAction.one_even⟩ : EvenGroup)
    (Iso.refl D.space) (EvenCoverRightAction.maps_one E k σ D)
  simpa only [finite_character_laws.2.2.2.1, ZMod.val_zero, mul_zero,
    pow_zero, map_one, one_smul, along, overPull, τ, Iso.refl_hom,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app] using H

lemma switch_roundtrip (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (z : Γ(S, ⊤)) (q : D.space ≅ C.space) (h : Switches E D C q)
    (hrev : Switches E C D q.symm) (K : S.Modules)
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (hn : Multiplier E C (-z) K n) :
    switchPull E C D q.symm hrev K (switchPull E D C q h K n) = n := by
  change along C.projection D.projection q.inv hrev.1 K
    (along D.projection C.projection q.hom h.1 K n) = n
  rw [along_comp]
  simpa only [q.inv_hom_id] using along_identity E C k σ (-z) K n hn

lemma switch_frame_inverse (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (z : Γ(S, ⊤)) (q : D.space ≅ C.space) (h : Switches E D C q)
    (hrev : Switches E C D q.symm) (L K : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (hn : Multiplier E C (-z) K n) (v : L ≅ K)
    (hv : SwitchFrame E D C q h L K m n v) :
    SwitchFrame E C D q.symm hrev K L n m v.symm := by
  have H := congrArg (along C.projection D.projection q.inv hrev.1 K) hv
  have Hn := along_natural C.projection D.projection q.inv hrev.1 v.hom m
  have Hr := switch_roundtrip E D C k σ z q h hrev K n hn
  have H' : ((Scheme.Modules.pullback C.projection).map v.hom).app ⊤
      (switchPull E C D q.symm hrev L m) = n := Hn.trans (H.trans Hr)
  change ((Scheme.Modules.pullback C.projection).map v.inv).app ⊤ n = _
  exact (congrArg (((Scheme.Modules.pullback C.projection).map v.inv).app ⊤) H'.symm).trans
    (iso_inv_hom_section ((Scheme.Modules.pullback C.projection).mapIso v) _)

end MultiplierPhaseSwitch
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier
open MultiplierPhaseSwitch

/-- The unique comparison of the given opposite-phase associated lines,
with reversal coherence on their actual level frames. -/
theorem multiplier_phase_switch :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D C : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P (-z) C → ∀ (q : CategoryTheory.Iso (D.space) (C.space)) (h : ArithmeticThetaPhaseSwitchR0218.Switches E D C q), ∀ (L K : S.Modules) (m : ((AlgebraicGeometry.Scheme.Modules.pullback D.projection).obj (L)).presheaf.obj (Opposite.op ⊤)) (n : ((AlgebraicGeometry.Scheme.Modules.pullback C.projection).obj (K)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.Multiplier E D z L m → ArithmeticThetaMultiplierKeyR0217.Multiplier E C (-z) K n → (∃! v : CategoryTheory.Iso (L) (K), ArithmeticThetaPhaseSwitchR0218.SwitchFrame E D C q h L K m n v) ∧ (∀ v : CategoryTheory.Iso (L) (K), ArithmeticThetaPhaseSwitchR0218.SwitchFrame E D C q h L K m n v → ∀ hrev : ArithmeticThetaPhaseSwitchR0218.Switches E C D q.symm, ArithmeticThetaPhaseSwitchR0218.SwitchFrame E C D q.symm hrev K L n m v.symm) := by
  intro k _ _ S σ E P z hz D C hD hC q h L K m n hm hn
  have hn' := switch_multiplier E D C k σ P z hz hC q h K n hn
  refine ⟨multiplier_unique E k σ P z D hD hz m (switchPull E D C q h K n) hm hn', ?_⟩
  intro v hv hrev
  exact switch_frame_inverse E D C k σ z q h hrev L K m n hn v hv

#print axioms multiplier_phase_switch
end ArithmeticThetaPhaseSwitchR0218
