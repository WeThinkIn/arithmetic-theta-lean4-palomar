module

public import AlphaTensorDescentR0217
public import MultiplierBaseChangeR0217

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaPullback ArithmeticThetaSheafTensor

namespace AlphaTensorBaseChange
open AlphaTensorCoherence

private lemma tensor_square (X Y Z W : Scheme.{u})
    (p : X ⟶ Y) (q : Y ⟶ W) (r : X ⟶ Z) (s : Z ⟶ W)
    (h : p ≫ q = r ≫ s) (H K : W.Modules) :
    let sq := fun M : W.Modules => (Scheme.Modules.pullbackComp p q).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp r s).app M).symm
    (sq (sheafTensor W H K)).hom ≫
      (Scheme.Modules.pullback r).map (pullback_sheafTensor_iso Z W s H K).hom ≫
      (pullback_sheafTensor_iso X Z r ((Scheme.Modules.pullback s).obj H)
        ((Scheme.Modules.pullback s).obj K)).hom =
    (Scheme.Modules.pullback p).map (pullback_sheafTensor_iso Y W q H K).hom ≫
      (pullback_sheafTensor_iso X Y p ((Scheme.Modules.pullback q).obj H)
        ((Scheme.Modules.pullback q).obj K)).hom ≫
      (sheafTensorCongr X (sq H) (sq K)).hom := by
  intro sq
  apply (cancel_mono (sheafTensorCongr X ((Scheme.Modules.pullbackComp r s).app H)
    ((Scheme.Modules.pullbackComp r s).app K)).hom).mp
  simp only [Category.assoc]
  rw [← tensor_comp X Z W r s H K, congr_comp]
  have he (M : W.Modules) : sq M ≪≫ (Scheme.Modules.pullbackComp r s).app M =
      (Scheme.Modules.pullbackComp p q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M := by
    simp [sq, Iso.trans_assoc]
  rw [he H, he K, ← congr_comp]
  simp only [sq, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensor_congr X W (p ≫ q) (r ≫ s) h H K]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp p q).app (sheafTensor W H K)).hom,
    tensor_comp X Y W p q H K]
  simp only [Category.assoc]

private lemma compatible_congr {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b b' : T ⟶ S) (f f' : F.curve ⟶ E.curve) (hb : b' = b) (hf : f' = f)
    (hz : F.zero ≫ f = b ≫ E.zero) (hz' : F.zero ≫ f' = b' ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (he : CotangentCompatible E F b f hz e) :
    CotangentCompatible E F b' f' hz'
      ((Scheme.Modules.pullbackCongr hb).app (Cotangent E) ≪≫ e) := by
  subst b'; subst f'
  change CotangentCompatible E F b f hz e at he
  change CotangentCompatible E F b f hz ((Iso.refl _) ≪≫ e)
  simpa using he

private lemma cotangent_square {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (D : Cover E) (C : Cover F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hb : Cartesian E F b f) (B : CoverChange E D F b f C)
    (c : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (hc : CotangentCompatible E F b f hb.2.1 c)
    (d : (Scheme.Modules.pullback D.projection).obj (Cotangent E) ≅ Cotangent D.family)
    (hd : CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 d)
    (e : (Scheme.Modules.pullback C.projection).obj (Cotangent F) ≅ Cotangent C.family)
    (he : CotangentCompatible F C.family C.projection C.comparison C.cartesian.2.1 e)
    (a : (Scheme.Modules.pullback B.map).obj (Cotangent D.family) ≅ Cotangent C.family)
    (ha : CotangentCompatible D.family C.family B.map B.familyMap B.marked.2.1 a) :
    (Scheme.Modules.pullback C.projection).map c.hom ≫ e.hom =
      (coverSquare E D F b f C B (Cotangent E)).hom ≫
        (Scheme.Modules.pullback B.map).map d.hom ≫ a.hom := by
  have hz : C.family.zero ≫ (C.comparison ≫ f) = (C.projection ≫ b) ≫ E.zero := by
    rw [← Category.assoc, C.cartesian.2.1, Category.assoc, hb.2.1, Category.assoc]
  obtain ⟨i, hi, _⟩ := cartesian_identity_ideal S C.space E C.family
    (C.projection ≫ b) (C.comparison ≫ f) (C.cartesian.1.paste_horiz hb.1) hz
  let t := cotangentComparison E C.family (C.projection ≫ b) (C.comparison ≫ f) hz i
  have ht : CotangentCompatible E C.family (C.projection ≫ b) (C.comparison ≫ f) hz t :=
    ⟨i, hi, rfl⟩
  have hz' : C.family.zero ≫ (B.familyMap ≫ D.comparison) =
      (B.map ≫ D.projection) ≫ E.zero := by rw [B.triangle, B.commutes]; exact hz
  let t' := (Scheme.Modules.pullbackCongr B.commutes).app (Cotangent E) ≪≫ t
  have ht' : CotangentCompatible E C.family (B.map ≫ D.projection)
      (B.familyMap ≫ D.comparison) hz' t' :=
    compatible_congr E C.family _ _ _ _ B.commutes B.triangle hz hz' t ht
  have h1 := scheme_cotangent_coherence.2 S T C.space E F C.family b C.projection
    f C.comparison hb.2.1 C.cartesian.2.1 hz c e t hc he ht
  have h2 := scheme_cotangent_coherence.2 S D.space C.space E D.family C.family
    D.projection B.map D.comparison B.familyMap D.cartesian.2.1 B.marked.2.1 hz'
    d a t' hd ha ht'
  rw [h1, h2]
  simp only [coverSquare, t', Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  have hh : (Scheme.Modules.pullbackCongr B.commutes.symm).app (Cotangent E) ≪≫
      (Scheme.Modules.pullbackCongr B.commutes).app (Cotangent E) = Iso.refl _ := by
    apply Iso.ext
    simp [Scheme.Modules.pullbackCongr]
  have hh' := congrArg Iso.hom hh
  simp only [Iso.trans_hom, Iso.refl_hom] at hh'
  rw [← Category.assoc ((Scheme.Modules.pullbackCongr B.commutes.symm).app (Cotangent E)).hom,
    hh', Category.id_comp]


private lemma comparison_square {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (D : Cover E) (C : Cover F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hb : Cartesian E F b f) (B : CoverChange E D F b f C)
    (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (hc : CotangentCompatible E F b f hb.2.1 c)
    (v : (Scheme.Modules.pullback b).obj L ≅ K)
    (d : (Scheme.Modules.pullback D.projection).obj (Cotangent E) ≅ Cotangent D.family)
    (hd : CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 d)
    (e : (Scheme.Modules.pullback C.projection).obj (Cotangent F) ≅ Cotangent C.family)
    (he : CotangentCompatible F C.family C.projection C.comparison C.cartesian.2.1 e)
    (a : (Scheme.Modules.pullback B.map).obj (Cotangent D.family) ≅ Cotangent C.family)
    (ha : CotangentCompatible D.family C.family B.map B.familyMap B.marked.2.1 a) :
    let ρD := pullback_sheafTensor_iso D.space S D.projection (Cotangent E) L ≪≫
      sheafTensorCongr D.space d (Iso.refl _)
    let ρC := pullback_sheafTensor_iso C.space T C.projection (Cotangent F) K ≪≫
      sheafTensorCongr C.space e (Iso.refl _)
    let w := (coverSquare E D F b f C B L).symm ≪≫ (Scheme.Modules.pullback C.projection).mapIso v
    (Scheme.Modules.pullback C.projection).map (productComparison E F b L K c v).hom ≫ ρC.hom =
      (coverSquare E D F b f C B (productLine E L)).hom ≫
        (Scheme.Modules.pullback B.map).map ρD.hom ≫
        (pullback_sheafTensor_iso C.space D.space B.map (Cotangent D.family)
          ((Scheme.Modules.pullback D.projection).obj L)).hom ≫
        (sheafTensorCongr C.space a w).hom := by
  intro ρD ρC w
  have hcot : (Scheme.Modules.pullback C.projection).mapIso c ≪≫ e =
      coverSquare E D F b f C B (Cotangent E) ≪≫
        (Scheme.Modules.pullback B.map).mapIso d ≪≫ a := by
    apply Iso.ext
    exact cotangent_square E F D C b f hb B c hc d hd e he a ha
  have hline : coverSquare E D F b f C B L ≪≫ w =
      (Scheme.Modules.pullback C.projection).mapIso v := by simp [w]
  simp only [ρD, ρC, productComparison, Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback C.projection).map
      (sheafTensorCongr T c v).hom), tensor_naturality]
  rw [← Category.assoc ((Scheme.Modules.pullback B.map).map
      (sheafTensorCongr D.space d (Iso.refl _)).hom), tensor_naturality]
  simp only [Category.assoc]
  rw [congr_comp, congr_comp]
  simp only [Iso.trans_refl, Functor.mapIso_refl, Iso.refl_trans]
  have hs := tensor_square C.space T D.space S C.projection b B.map D.projection
    B.commutes.symm (Cotangent E) L
  change (coverSquare E D F b f C B (productLine E L)).hom ≫ _ = _ at hs
  have hs' := congrArg (fun g => g ≫ (sheafTensorCongr C.space
    ((Scheme.Modules.pullback B.map).mapIso d ≪≫ a) w).hom) hs
  simp only [Category.assoc] at hs'
  rw [hs']
  rw [congr_comp]
  erw [← hcot, hline]

private lemma section_square {S T D C : Scheme.{u}}
    (b : T ⟶ S) (p : D ⟶ S) (q : C ⟶ T) (r : C ⟶ D)
    (h : q ≫ b = r ≫ p) (M : S.Modules) (N : T.Modules)
    (HD LD : D.Modules) (HC LC : C.Modules)
    (v : (Scheme.Modules.pullback b).obj M ≅ N)
    (d : (Scheme.Modules.pullback p).obj M ≅ sheafTensor D HD LD)
    (e : (Scheme.Modules.pullback q).obj N ≅ sheafTensor C HC LC)
    (a : (Scheme.Modules.pullback r).obj HD ≅ HC)
    (w : (Scheme.Modules.pullback r).obj LD ≅ LC)
    (hmaps : (Scheme.Modules.pullback q).map v.hom ≫ e.hom =
      ((Scheme.Modules.pullbackComp q b).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M ≪≫
        ((Scheme.Modules.pullbackComp r p).app M).symm).hom ≫
      (Scheme.Modules.pullback r).map d.hom ≫
      (pullback_sheafTensor_iso C D r HD LD).hom ≫
      (sheafTensorCongr C a w).hom)
    (β : Γ(M, ⊤)) (γ : Γ(N, ⊤)) (aD : Γ(HD, ⊤)) (m : Γ(LD, ⊤))
    (aC : Γ(HC, ⊤)) (n : Γ(LC, ⊤))
    (hβ : d.hom.app ⊤ (pullbackGlobalSection p M β) = tensorSection D HD LD ⊤ aD m)
    (hγ : e.hom.app ⊤ (pullbackGlobalSection q N γ) = tensorSection C HC LC ⊤ aC n)
    (ha : a.hom.app ⊤ (pullbackGlobalSection r HD aD) = aC)
    (hw : w.hom.app ⊤ (pullbackGlobalSection r LD m) = n) :
    pullbackGlobalSection q N (v.hom.app ⊤ (pullbackGlobalSection b M β)) =
      pullbackGlobalSection q N γ := by
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1
  have hs := congrArg (fun g => g.app ⊤
    (pullbackGlobalSection q _ (pullbackGlobalSection b M β))) hmaps
  change e.hom.app ⊤ (((Scheme.Modules.pullback q).map v.hom).app ⊤
      (pullbackGlobalSection q _ (pullbackGlobalSection b M β))) =
    (sheafTensorCongr C a w).hom.app ⊤ ((pullback_sheafTensor_iso C D r HD LD).hom.app ⊤
      (((Scheme.Modules.pullback r).map d.hom).app ⊤
        (((Scheme.Modules.pullbackComp q b).app M ≪≫
          (Scheme.Modules.pullbackCongr h).app M ≪≫
          ((Scheme.Modules.pullbackComp r p).app M).symm).hom.app ⊤
          (pullbackGlobalSection q _ (pullbackGlobalSection b M β))))) at hs
  let x := pullbackGlobalSection q _ (pullbackGlobalSection b M β)
  let sq := (Scheme.Modules.pullbackComp q b).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp r p).app M).symm
  have hsq : sq.hom.app ⊤ x = pullbackGlobalSection r _ (pullbackGlobalSection p M β) :=
    MultiplierBaseChange.square_section q b r p h M β
  have hd : ((Scheme.Modules.pullback r).map d.hom).app ⊤ (sq.hom.app ⊤ x) =
      pullbackGlobalSection r (sheafTensor D HD LD) (tensorSection D HD LD ⊤ aD m) :=
    (congrArg (((Scheme.Modules.pullback r).map d.hom).app ⊤) hsq).trans
      ((MultiplierBaseChange.global_app r d.hom _).trans
        (congrArg (pullbackGlobalSection r (sheafTensor D HD LD)) hβ))
  have ht : (pullback_sheafTensor_iso C D r HD LD).hom.app ⊤
      (((Scheme.Modules.pullback r).map d.hom).app ⊤ (sq.hom.app ⊤ x)) =
      tensorSection C ((Scheme.Modules.pullback r).obj HD) ((Scheme.Modules.pullback r).obj LD)
        ⊤ (pullbackGlobalSection r HD aD) (pullbackGlobalSection r LD m) :=
    (congrArg ((pullback_sheafTensor_iso C D r HD LD).hom.app ⊤) hd).trans
      (pullback_sheafTensor_section C D r HD LD aD m)
  have ht' : (sheafTensorCongr C a w).hom.app ⊤
      ((pullback_sheafTensor_iso C D r HD LD).hom.app ⊤
        (((Scheme.Modules.pullback r).map d.hom).app ⊤ (sq.hom.app ⊤ x))) =
      tensorSection C HC LC ⊤ aC n :=
    (congrArg ((sheafTensorCongr C a w).hom.app ⊤) ht).trans
      ((sheafTensorCongr_section C a w ⊤ _ _).trans
        (congrArg₂ (tensorSection C HC LC ⊤) ha hw))
  have hv := MultiplierBaseChange.global_app q v.hom (pullbackGlobalSection b M β)
  exact (congrArg (e.hom.app ⊤) hv).symm.trans (hs.trans (ht'.trans hγ.symm))

end AlphaTensorBaseChange
open AlphaTensorBaseChange

theorem alpha_tensor_base_change
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : Family S) (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z ^ 2 = -1)
    (D : Cover E) (hD : RepresentsEven E P z D)
    (L : S.Modules) (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (hm : Multiplier E D z L m)
    (T : Scheme.{u}) (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hb : Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val)
    (C : Cover F) (hC : RepresentsEven F Q (b.appTop z) C)
    (K : T.Modules) (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (hn : Multiplier F C (b.appTop z) K n)
    (B : CoverChange E D F b f C)
    (c : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (hc : CotangentCompatible E F b f hb.2.1 c)
    (v : (Scheme.Modules.pullback b).obj L ≅ K)
    (hv : MultiplierCompatible E D F b f C B L K m n v)
    (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤))
    (hβ : DescendsAlpha E D L m β) (hγ : DescendsAlpha F C K n γ) :
    AlphaNatural E F b L K c v β γ := by
  obtain ⟨d, hd⟩ := hβ.1
  obtain ⟨e, he⟩ := hγ.1
  obtain ⟨aD, haD⟩ := hβ.2.1
  obtain ⟨aC, haC⟩ := hγ.2.1
  obtain ⟨a, ha, _⟩ := SchemeAlphaNaturality.cotangent_exists_unique
    D.family C.family D.marking C.marking B.map B.familyMap B.marked
  have halpha : a.hom.app ⊤ (pullbackGlobalSection B.map (Cotangent D.family) aD) = aC := by
    exact (scheme_alpha_naturality k D.space (D.projection ≫ σ) D.family D.marking
      C.space (B.map ≫ (D.projection ≫ σ)) C.family C.marking B.map B.familyMap rfl
      B.marked).2 a ha aD aC haD haC
  let ρD := pullback_sheafTensor_iso D.space S D.projection (Cotangent E) L ≪≫
    sheafTensorCongr D.space d (Iso.refl _)
  let ρC := pullback_sheafTensor_iso C.space T C.projection (Cotangent F) K ≪≫
    sheafTensorCongr C.space e (Iso.refl _)
  let w := (coverSquare E D F b f C B L).symm ≪≫
    (Scheme.Modules.pullback C.projection).mapIso v
  have hw : w.hom.app ⊤ (pullbackGlobalSection B.map _ m) = n := hv
  have hmaps := comparison_square E F D C b f hb B L K c hc v d hd e he a ha
  change (Scheme.Modules.pullback C.projection).map (productComparison E F b L K c v).hom ≫
    ρC.hom = (coverSquare E D F b f C B (productLine E L)).hom ≫
      (Scheme.Modules.pullback B.map).map ρD.hom ≫
      (pullback_sheafTensor_iso C.space D.space B.map (Cotangent D.family)
        ((Scheme.Modules.pullback D.projection).obj L)).hom ≫
      (sheafTensorCongr C.space a w).hom at hmaps
  have hsection := section_square b D.projection C.projection B.map B.commutes.symm
    (productLine E L) (productLine F K) (Cotangent D.family)
    ((Scheme.Modules.pullback D.projection).obj L) (Cotangent C.family)
    ((Scheme.Modules.pullback C.projection).obj K)
    (productComparison E F b L K c v) ρD ρC a w hmaps
    β γ aD m aC n (hβ.2.2 d hd aD haD) (hγ.2.2 e he aC haC) halpha hw
  have hz' : (b.appTop z)^2 = -1 := by rw [← map_pow, hz, map_neg, map_one]
  have hframe := (alpha_tensor_descent k T (b ≫ σ) F Q (b.appTop z) hz' C hC K n hn).2 γ hγ
  obtain ⟨triv, _⟩ := InverseCharacterMultiplier.exists_frame_iso _ γ hframe
  have hM : Scheme.Modules.IsInvertible (productLine F K) := by
    constructor
    intro x
    refine ⟨⊤, trivial, ⟨?_⟩⟩
    exact (Scheme.Modules.pullback (⊤ : T.Opens).ι).mapIso triv.symm ≪≫
      Scheme.Modules.pullbackUnitIso _
  obtain ⟨hf, het, hs, _⟩ := EvenCoverTorsor.geometry F k (b ≫ σ) Q (b.appTop z) hz' C hC
  letI := hf
  letI := het
  letI := hs
  change (productComparison E F b L K c v).hom.app ⊤
    (pullbackGlobalSection b (productLine E L) β) = γ
  apply AlphaDescentFaithfulness.pullback_section_injective C.projection hM
  exact hsection

#print axioms alpha_tensor_base_change
end ArithmeticThetaMultiplierKeyR0217
