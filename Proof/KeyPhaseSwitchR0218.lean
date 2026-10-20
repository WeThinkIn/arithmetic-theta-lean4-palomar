module

public import MultiplierPhaseSwitchR0218

@[expose] public section

/-! Compatibility of the descended signed alpha and the actual key map with reversal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
namespace KeyPhaseSwitch
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaPullback ArithmeticThetaSheafTensor
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier
open ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier.Transport
open ArithmeticThetaMultiplierKeyR0217.MultiplierBaseChange
open ArithmeticThetaMultiplierKeyR0217.AlphaTensorCoherence
open MultiplierPhaseSwitch

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

variable {S : Scheme.{u}} (E : Family S) (D C : Cover E)

lemma switch_marked (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤))
    (hD : RepresentsEven E P z D) (hC : RepresentsEven E P (-z) C)
    (q : D.space ≅ C.space) (h : Switches E D C q) :
    ∃ (N : FullLevel D.family 4) (f : D.family.curve ⟶ C.family.curve),
      Changes D.family D.marking N reversal ∧
      MarkedCartesian C.family D.family C.marking N q.hom f ∧
      f ≫ C.comparison = D.comparison := by
  obtain ⟨N, hN, _⟩ := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).1
  have hrev := (scheme_pairing_reversal k D.space
    (D.projection ≫ σ) D.family D.marking).2 N hN
  have hm : Matches E P (-z) D.family N D.projection D.comparison := by
    constructor
    · rw [hrev.2.1]; exact hD.1.1
    · simpa only [map_neg] using hrev.2.2.1 (D.projection.appTop z) hD.1.2
  obtain ⟨r, ⟨f, hf, ht⟩, _⟩ := hC.2 D.space D.family N
    D.projection D.comparison D.cartesian hm
  have hr : EvenCoverPhaseSwitch.Maps E D C reversal r.val := by
    refine ⟨r.property, ?_, ?_⟩
    · rw [← Category.assoc, ← hf.2.2.2.1, Category.assoc, ht,
        EvenCoverRightAction.changed_x _ _ _ _ hN]
    · rw [← Category.assoc, ← hf.2.2.2.2, Category.assoc, ht,
        EvenCoverRightAction.changed_y _ _ _ _ hN]
  have he := EvenCoverPhaseSwitch.maps_unique E k σ P (-z) D C hC reversal q.hom r.val h hr
  exact ⟨N, f, hN, by simpa only [he] using hf, ht⟩

lemma cotangent_switch (q : D.space ≅ C.space) (h : Switches E D C q)
    (N : FullLevel D.family 4) (f : D.family.curve ⟶ C.family.curve)
    (hf : MarkedCartesian C.family D.family C.marking N q.hom f)
    (ht : f ≫ C.comparison = D.comparison)
    (d : (Scheme.Modules.pullback D.projection).obj (Cotangent E) ≅ Cotangent D.family)
    (hd : CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 d)
    (e : (Scheme.Modules.pullback C.projection).obj (Cotangent E) ≅ Cotangent C.family)
    (he : CotangentCompatible E C.family C.projection C.comparison C.cartesian.2.1 e)
    (a : (Scheme.Modules.pullback q.hom).obj (Cotangent C.family) ≅ Cotangent D.family)
    (ha : CotangentCompatible C.family D.family q.hom f hf.2.1 a) :
    (Scheme.Modules.pullback q.hom).map e.hom ≫ a.hom =
      (((Scheme.Modules.pullbackComp q.hom C.projection).app (Cotangent E)) ≪≫
        (Scheme.Modules.pullbackCongr h.1).app (Cotangent E) ≪≫ d).hom := by
  have hz : D.family.zero ≫ (f ≫ C.comparison) =
      (q.hom ≫ C.projection) ≫ E.zero := by rw [ht, h.1]; exact D.cartesian.2.1
  have hd' := compatible_congr E D.family D.projection (q.hom ≫ C.projection)
    D.comparison (f ≫ C.comparison) h.1 ht D.cartesian.2.1 hz d hd
  exact scheme_cotangent_coherence.2 S C.space D.space E C.family D.family
    C.projection q.hom C.comparison f C.cartesian.2.1 hf.2.1 hz e a
    ((Scheme.Modules.pullbackCongr h.1).app (Cotangent E) ≪≫ d) he ha hd'

/-- Tensor coherence for two different covers over one base. -/
lemma tensor_triangle {X Y B : Scheme.{u}} (p : X ⟶ B) (r : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ r = p) (H K : B.Modules)
    (HD : X.Modules) (HC : Y.Modules)
    (d : (Scheme.Modules.pullback p).obj H ≅ HD)
    (e : (Scheme.Modules.pullback r).obj H ≅ HC)
    (a : (Scheme.Modules.pullback f).obj HC ≅ HD)
    (ha : (Scheme.Modules.pullback f).map e.hom ≫ a.hom =
      ((Scheme.Modules.pullbackComp f r).app H ≪≫
        (Scheme.Modules.pullbackCongr h).app H ≪≫ d).hom) :
    ((Scheme.Modules.pullbackComp f r).app (sheafTensor B H K) ≪≫
      (Scheme.Modules.pullbackCongr h).app (sheafTensor B H K)).hom ≫
      (pullback_sheafTensor_iso X B p H K ≪≫ sheafTensorCongr X d (Iso.refl _)).hom =
    (Scheme.Modules.pullback f).map
      (pullback_sheafTensor_iso Y B r H K ≪≫ sheafTensorCongr Y e (Iso.refl _)).hom ≫
      (pullback_sheafTensor_iso X Y f HC ((Scheme.Modules.pullback r).obj K) ≪≫
        sheafTensorCongr X a ((Scheme.Modules.pullbackComp f r).app K ≪≫
          (Scheme.Modules.pullbackCongr h).app K)).hom := by
  have he : (Scheme.Modules.pullback f).mapIso e ≪≫ a =
      (Scheme.Modules.pullbackComp f r).app H ≪≫ (Scheme.Modules.pullbackCongr h).app H ≪≫ d :=
    Iso.ext ha
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullbackCongr h).app (sheafTensor B H K)).hom,
    tensor_congr X B (f ≫ r) p h H K]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp f r).app (sheafTensor B H K)).hom,
    tensor_comp X Y B f r H K]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (sheafTensorCongr Y e (Iso.refl _)).hom),
    tensor_naturality X Y f e (Iso.refl _)]
  simp only [Category.assoc]
  rw [← Category.assoc (sheafTensorCongr X ((Scheme.Modules.pullbackComp f r).app H)
      ((Scheme.Modules.pullbackComp f r).app K)).hom,
    congr_comp, congr_comp, congr_comp, he]
  simp only [Iso.trans_assoc, Iso.trans_refl, Functor.mapIso_refl, Iso.refl_trans]


lemma triangle_global {X Y B : Scheme.{u}} (p : X ⟶ B) (r : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ r = p) (M : B.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f r).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M).hom.app ⊤
        (pullbackGlobalSection f _ (pullbackGlobalSection r M s)) =
      pullbackGlobalSection p M s := by
  exact (congrArg (((Scheme.Modules.pullbackCongr h).app M).hom.app ⊤)
    (comp_global f r M s)).trans (congr_global h M s)

lemma triangle_section {X Y B : Scheme.{u}} (p : X ⟶ B) (r : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ r = p) (H K : B.Modules)
    (HD : X.Modules) (HC : Y.Modules)
    (d : (Scheme.Modules.pullback p).obj H ≅ HD)
    (e : (Scheme.Modules.pullback r).obj H ≅ HC)
    (a : (Scheme.Modules.pullback f).obj HC ≅ HD)
    (ha : (Scheme.Modules.pullback f).map e.hom ≫ a.hom =
      ((Scheme.Modules.pullbackComp f r).app H ≪≫
        (Scheme.Modules.pullbackCongr h).app H ≪≫ d).hom)
    (γ : Γ(sheafTensor B H K, ⊤)) (aC : Γ(HC, ⊤))
    (n : Γ((Scheme.Modules.pullback r).obj K, ⊤))
    (hγ : (pullback_sheafTensor_iso Y B r H K ≪≫
      sheafTensorCongr Y e (Iso.refl _)).hom.app ⊤
        (pullbackGlobalSection r _ γ) = tensorSection Y HC _ ⊤ aC n) :
    (pullback_sheafTensor_iso X B p H K ≪≫
      sheafTensorCongr X d (Iso.refl _)).hom.app ⊤ (pullbackGlobalSection p _ γ) =
      tensorSection X HD _ ⊤ (a.hom.app ⊤ (pullbackGlobalSection f HC aC))
        (((Scheme.Modules.pullbackComp f r).app K ≪≫
          (Scheme.Modules.pullbackCongr h).app K).hom.app ⊤ (pullbackGlobalSection f _ n)) := by
  have hm := tensor_triangle p r f h H K HD HC d e a ha
  have hs := congrArg (fun g => g.app ⊤
    (pullbackGlobalSection f _ (pullbackGlobalSection r (sheafTensor B H K) γ))) hm
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hs
  let ρD := pullback_sheafTensor_iso X B p H K ≪≫ sheafTensorCongr X d (Iso.refl _)
  let ρC := pullback_sheafTensor_iso Y B r H K ≪≫ sheafTensorCongr Y e (Iso.refl _)
  let w := (Scheme.Modules.pullbackComp f r).app K ≪≫ (Scheme.Modules.pullbackCongr h).app K
  have h1 := (global_app f ρC.hom (pullbackGlobalSection r (sheafTensor B H K) γ)).trans
    (congrArg (pullbackGlobalSection f (sheafTensor Y HC ((Scheme.Modules.pullback r).obj K))) hγ)
  have h2 := (congrArg ((pullback_sheafTensor_iso X Y f HC
    ((Scheme.Modules.pullback r).obj K)).hom.app ⊤) h1).trans
    (pullback_sheafTensor_section X Y f HC ((Scheme.Modules.pullback r).obj K) aC n)
  have h3 := (congrArg ((sheafTensorCongr X a w).hom.app ⊤) h2).trans
    (sheafTensorCongr_section X a w ⊤ _ _)
  exact (congrArg (ρD.hom.app ⊤) (triangle_global p r f h (sheafTensor B H K) γ)).symm.trans
    (hs.trans h3)

lemma tensor_map_section {X B : Scheme.{u}} (p : X ⟶ B) (H L K : B.Modules)
    (HD : X.Modules) (d : (Scheme.Modules.pullback p).obj H ≅ HD) (v : L ≅ K)
    (β : Γ(sheafTensor B H L, ⊤)) (aD : Γ(HD, ⊤))
    (m : Γ((Scheme.Modules.pullback p).obj L, ⊤))
    (hβ : (pullback_sheafTensor_iso X B p H L ≪≫
      sheafTensorCongr X d (Iso.refl _)).hom.app ⊤ (pullbackGlobalSection p _ β) =
      tensorSection X HD _ ⊤ aD m) :
    (pullback_sheafTensor_iso X B p H K ≪≫
      sheafTensorCongr X d (Iso.refl _)).hom.app ⊤
      (pullbackGlobalSection p _ ((sheafTensorCongr B (Iso.refl H) v).hom.app ⊤ β)) =
    tensorSection X HD _ ⊤ aD (((Scheme.Modules.pullback p).map v.hom).app ⊤ m) := by
  let ρ := fun J : B.Modules => pullback_sheafTensor_iso X B p H J ≪≫
    sheafTensorCongr X d (Iso.refl _)
  let t := sheafTensorCongr B (Iso.refl H) v
  have hn : (Scheme.Modules.pullback p).map t.hom ≫ (ρ K).hom =
      (ρ L).hom ≫ (sheafTensorCongr X (Iso.refl HD)
        ((Scheme.Modules.pullback p).mapIso v)).hom := by
    dsimp only [t, ρ]
    simp only [Iso.trans_hom, Category.assoc]
    rw [← Category.assoc, tensor_naturality]
    simp only [Category.assoc]
    rw [congr_comp, congr_comp]
    simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]
  have hs := congrArg (fun g => g.app ⊤ (pullbackGlobalSection p _ β)) hn
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hs
  rw [global_app, hβ, sheafTensorCongr_section] at hs
  exact hs

lemma alpha_switch (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1)
    (hD : RepresentsEven E P z D) (hC : RepresentsEven E P (-z) C)
    (q : D.space ≅ C.space) (h : Switches E D C q)
    (L K : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback C.projection).obj K, ⊤))
    (hn : Multiplier E C (-z) K n)
    (v : L ≅ K) (hv : SwitchFrame E D C q h L K m n v)
    (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine E K, ⊤))
    (hβ : DescendsAlpha E D L m β) (hγ : DescendsAlpha E C K n γ) :
    (sheafTensorCongr S (Iso.refl (Cotangent E)) v).hom.app ⊤ β = γ := by
  obtain ⟨d, hd⟩ := hβ.1
  obtain ⟨e, he⟩ := hγ.1
  obtain ⟨aD, haD⟩ := hβ.2.1
  obtain ⟨aC, haC⟩ := hγ.2.1
  obtain ⟨N, f, hN, hf, ht⟩ := switch_marked E D C k σ P z hD hC q h
  obtain ⟨a, ha, _⟩ := SchemeAlphaNaturality.cotangent_exists_unique
    C.family D.family C.marking N q.hom f hf
  have haN : RealizesAlpha D.family N aD :=
    ((scheme_pairing_reversal k D.space (D.projection ≫ σ) D.family D.marking).2 N hN).2.2.2 aD |>.mp haD
  have halpha : a.hom.app ⊤ (pullbackGlobalSection q.hom (Cotangent C.family) aC) = aD :=
    (scheme_alpha_naturality k C.space (C.projection ≫ σ) C.family C.marking
      D.space (q.hom ≫ (C.projection ≫ σ)) D.family N q.hom f rfl hf).2 a ha aC aD haC haN
  have hc := cotangent_switch E D C q h N f hf ht d hd e he a ha
  have Hγ := triangle_section D.projection C.projection q.hom h.1
    (Cotangent E) K (Cotangent D.family) (Cotangent C.family) d e a hc γ aC n
    (hγ.2.2 e he aC haC)
  rw [halpha] at Hγ
  have Hβ := tensor_map_section D.projection (Cotangent E) L K (Cotangent D.family)
    d v β aD m (hβ.2.2 d hd aD haD)
  rw [show ((Scheme.Modules.pullback D.projection).map v.hom).app ⊤ m =
    switchPull E D C q h K n from hv] at Hβ
  have hsections := (ConcreteCategory.bijective_of_isIso
    ((pullback_sheafTensor_iso D.space S D.projection (Cotangent E) K ≪≫
      sheafTensorCongr D.space d (Iso.refl _)).hom.app ⊤)).1 (Hβ.trans Hγ.symm)
  have hzminus : (-z)^2 = -1 := by simpa only [neg_sq] using hz
  have hframe := (alpha_tensor_descent k S σ E P (-z) hzminus C hC K n hn).2 γ hγ
  obtain ⟨triv, _⟩ := exists_frame_iso _ γ hframe
  have hK : Scheme.Modules.IsInvertible (productLine E K) := by
    constructor
    intro x
    refine ⟨⊤, trivial, ⟨?_⟩⟩
    exact (Scheme.Modules.pullback (⊤ : S.Opens).ι).mapIso triv.symm ≪≫ Scheme.Modules.pullbackUnitIso _
  obtain ⟨hfin, het, hsurj, _⟩ := EvenCoverTorsor.geometry E k σ P z hz D hD
  letI := hfin
  letI := het
  letI := hsurj
  exact AlphaDescentFaithfulness.pullback_section_injective D.projection hK hsections

end KeyPhaseSwitch
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171

/-- Opposite-pairing compatibility of the complete descended section and actual key morphism. -/
theorem key_phase_switch :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 → ∀ (D C : ArithmeticThetaEvenMarkingTorsorR0216.Cover E), ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D → ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P (-z) C → ∀ (q : CategoryTheory.Iso (D.space) (C.space)) (h : ArithmeticThetaPhaseSwitchR0218.Switches E D C q), ∀ (L K : S.Modules) (m : ((AlgebraicGeometry.Scheme.Modules.pullback D.projection).obj (L)).presheaf.obj (Opposite.op ⊤)) (n : ((AlgebraicGeometry.Scheme.Modules.pullback C.projection).obj (K)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.Multiplier E D z L m → ArithmeticThetaMultiplierKeyR0217.Multiplier E C (-z) K n → ∀ (v : CategoryTheory.Iso (L) (K)), ArithmeticThetaPhaseSwitchR0218.SwitchFrame E D C q h L K m n v → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaMultiplierKeyR0217.productLine E K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaMultiplierKeyR0217.DescendsAlpha E D L m β → ArithmeticThetaMultiplierKeyR0217.DescendsAlpha E C K n γ → (ArithmeticThetaPullback.sheafTensorCongr S (CategoryTheory.Iso.refl (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) v).hom.app ⊤ β = γ ∧ (∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)) (κminus : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E K)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ → ArithmeticThetaMultiplierKeyR0217.IsKey E P K e γ κminus → CategoryTheory.CategoryStruct.comp (κ.hom) ((ArithmeticThetaPullback.sheafTensorCongr S (CategoryTheory.Iso.refl (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) v).hom) = κminus.hom) := by
  intro k _ _ S σ E P z hz D C hD hC q h L K m n hm hn v hv β γ hβ hγ
  have H := KeyPhaseSwitch.alpha_switch E D C k σ P z hz hD hC q h L K m n hn v hv β γ hβ hγ
  refine ⟨H, ?_⟩
  intro e he κ κminus hκ hκminus
  have hs : IsFrame (inverseSquare E P) ⊤ (evaluationSquare E P e) :=
    HodgeBaseChange.tensorPower_frame (Scheme.Modules.dual (pushforwardLine E P))
      (evaluationSection E P e) (((even_point_theta_evaluation k S σ E P).2.2.2.2.2 e he).2.2) 2
  apply InverseCharacterMultiplier.hom_ext_of_frame _ hs
  change (sheafTensorCongr S (Iso.refl (Cotangent E)) v).hom.app ⊤
    (κ.hom.app ⊤ (evaluationSquare E P e)) = κminus.hom.app ⊤ (evaluationSquare E P e)
  rw [show κ.hom.app ⊤ (evaluationSquare E P e) = β from hκ]
  exact H.trans hκminus.symm

#print axioms key_phase_switch
end ArithmeticThetaPhaseSwitchR0218
