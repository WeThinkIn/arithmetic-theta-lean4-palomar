module

public import InverseCharacterMultiplierR0217
public import AlphaTensorCoherenceR0217
public import AlphaDescentFaithfulnessR0217
public import SchemeAlphaSectionR0215
public import SchemeAlphaNaturalityR0215
public import SchemeAlphaCharacterR0215

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open Opposite TopologicalSpace
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaSheafTensor ArithmeticThetaPullback

private lemma tensor_section_frame_of_frames
    {X : Scheme.{u}} {H K : X.Modules}
    (a : Γ(H, ⊤)) (ha : IsFrame H ⊤ a)
    (m : Γ(K, ⊤)) (hm : IsFrame K ⊤ m) :
    IsFrame (sheafTensor X H K) ⊤ (tensorSection X H K ⊤ a m) := by
  intro V hV
  let e := ArithmeticThetaSheafTensor.tensorFrame X H K ⊤
    (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame H a ha)
    (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame K m hm)
  have he := ArithmeticThetaSheafTensor.tensorSection_frame X H K ⊤
    (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame H a ha)
    (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame K m hm)
    V hV 1 1
  have hs' : (e.equiv V hV 1) =
      (sheafTensor X H K).presheaf.map (homOfLE hV).op
        (tensorSection X H K ⊤ a m) := by
    rw [tensorSection_restrict]
    have hfa : (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame H a ha).equiv V hV 1 =
        H.presheaf.map (homOfLE hV).op a := by
      simp [ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame,
        LinearEquiv.ofBijective, LinearMap.toSpanSingleton_apply]
      rfl
    have hfm : (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame K m hm).equiv V hV 1 =
        K.presheaf.map (homOfLE hV).op m := by
      simp [ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame,
        LinearEquiv.ofBijective, LinearMap.toSpanSingleton_apply]
      rfl
    rw [← hfa, ← hfm]
    simpa [e] using he.symm
  unfold ArithmeticThetaRelativeDiscriminantR0171.res
  rw [← hs']
  change Function.Bijective (fun x : Γ(X, V) => x • e.equiv V hV 1)
  convert (e.equiv V hV).bijective using 1
  ext x
  simpa using ((e.equiv V hV).map_smul x (1 : Γ(X, V))).symm

private lemma acts_markedCartesian
    (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}}
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤))
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D)
    (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup)
    (q : D.space ≅ D.space)
    (hq : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q) :
    ∃ N : ArithmeticThetaSchemeLevelR0204.FullLevel D.family 4,
      Changes D.family D.marking N A.val ∧
      ∃ f : D.family.curve ⟶ D.family.curve,
        ArithmeticThetaSchemeLevelR0204.MarkedCartesian D.family D.family
          D.marking N q.hom f ∧ f ≫ D.comparison = D.comparison := by
  obtain ⟨N, hN, _⟩ :=
    (ArithmeticThetaSchemeFourCharacterR0215.scheme_four_marking_action k D.space
      (D.projection ≫ σ) D.family D.marking).1 A.val A.property.1
  have hm := ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction.matches_change
    E k σ P z D.family D.marking N D.projection D.comparison A hN hD.1
  obtain ⟨q', ⟨f, hf, hfc⟩, _⟩ := hD.2 D.space D.family N
    D.projection D.comparison D.cartesian hm
  have hq' : ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction.Maps
      E D A.val q'.val := by
    refine ⟨q'.property, ?_, ?_⟩
    · rw [← Category.assoc, ← hf.2.2.2.1, Category.assoc, hfc,
        ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction.changed_x _ _ _ _ hN]
    · rw [← Category.assoc, ← hf.2.2.2.2, Category.assoc, hfc,
        ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction.changed_y _ _ _ _ hN]
  have hqeq := ArithmeticThetaEvenMarkingTorsorR0216.EvenCoverRightAction.maps_unique
    E k σ P z D hD A.val q.hom q'.val hq hq'
  refine ⟨N, hN, f, ?_, hfc⟩
  simpa [hqeq] using hf

private lemma cotangent_invertible
    {S : Scheme.{u}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S) :
    Scheme.Modules.IsInvertible (Cotangent E) := by
  exact Scheme.Modules.IsInvertible.pullback E.zero
    (ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E).isInvertible_module

private lemma restrict_iso_further
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.Opens) (hW : j.opensRange ≤ W) {M N : X.Modules}
    (e : (Scheme.Modules.pullback W.ι).obj M ≅
      (Scheme.Modules.pullback W.ι).obj N) :
    Nonempty ((Scheme.Modules.pullback j).obj M ≅
      (Scheme.Modules.pullback j).obj N) := by
  have hr : Set.range j.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hW
  let j' := IsOpenImmersion.lift W.ι j hr
  have hj : j' ≫ W.ι = j := IsOpenImmersion.lift_fac W.ι j hr
  exact ⟨((Scheme.Modules.pullbackCongr hj).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp j' W.ι).app M).symm ≪≫
    (Scheme.Modules.pullback j').mapIso e ≪≫
    (Scheme.Modules.pullbackComp j' W.ι).app N ≪≫
    (Scheme.Modules.pullbackCongr hj).app N⟩

private lemma sheafTensor_invertible
    {X : Scheme.{u}} {H K : X.Modules}
    (hH : Scheme.Modules.IsInvertible H) (hK : Scheme.Modules.IsInvertible K) :
    Scheme.Modules.IsInvertible (sheafTensor X H K) := by
  constructor
  intro x
  obtain ⟨U, hxU, ⟨eH⟩⟩ := hH.exists_trivialization x
  obtain ⟨V, hxV, ⟨eK⟩⟩ := hK.exists_trivialization x
  let W := U ⊓ V
  obtain ⟨eHW⟩ := restrict_iso_further W.ι U
    (by simpa only [Scheme.Opens.opensRange_ι] using (inf_le_left : W ≤ U))
    (eH ≪≫ (Scheme.Modules.pullbackUnitIso U.ι).symm)
  obtain ⟨eKW⟩ := restrict_iso_further W.ι V
    (by simpa only [Scheme.Opens.opensRange_ι] using (inf_le_right : W ≤ V))
    (eK ≪≫ (Scheme.Modules.pullbackUnitIso V.ι).symm)
  refine ⟨W, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact pullback_sheafTensor_iso W.toScheme X W.ι H K ≪≫
    sheafTensorCongr W.toScheme
      (eHW ≪≫ Scheme.Modules.pullbackUnitIso W.ι)
      (eKW ≪≫ Scheme.Modules.pullbackUnitIso W.ι) ≪≫
    tensorLeftUnitIso W.toScheme _

private lemma frameIso_action_of_invariant
    {S : Scheme.{u}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤))
    (hm : IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ m)
    (hn : IsFrame ((Scheme.Modules.pullback D.projection).obj K) ⊤ n)
    (hm_action : ∀ (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup)
      (q : D.space ≅ D.space) (h : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q),
      overPull E D L q.hom h.1 m = m)
    (hn_action : ∀ (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup)
      (q : D.space ≅ D.space) (h : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q),
      overPull E D K q.hom h.1 n = n)
    (η : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj K)
    (hη : η.hom.app ⊤ m = n)
    (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup) (q : D.space ≅ D.space)
    (hq : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q) :
    pullHom
      (F := InverseCharacterMultiplier.Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom q.hom
        D.projection D.projection hq.1 hq.1 = η.hom := by
  apply InverseCharacterMultiplier.hom_ext_of_frame (overPull E D L q.hom hq.1 m)
    (InverseCharacterMultiplier.overPull_frame E D m hm q.hom hq.1)
  have H := InverseCharacterMultiplier.Transport.pullHom_overPull
    D.projection q.hom hq.1 η.hom m
  rw [hη] at H
  calc
    _ = overPull E D K q.hom hq.1 n := H
    _ = n := hn_action A q hq
    _ = η.hom.app ⊤ m := hη.symm
    _ = η.hom.app ⊤ (overPull E D L q.hom hq.1 m) :=
      congrArg (η.hom.app ⊤) (hm_action A q hq).symm

private lemma cotangentCompatible_congr
    {S T : Scheme.{u}}
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
    (b b' : T ⟶ S) (f f' : F.curve ⟶ E.curve)
    (hb : b' = b) (hf : f' = f)
    (hz : F.zero ≫ f = b ≫ E.zero)
    (hz' : F.zero ≫ f' = b' ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F) :
    CotangentCompatible E F b f hz e →
      CotangentCompatible E F b' f' hz'
        (((Scheme.Modules.pullbackCongr hb).app (Cotangent E)) ≪≫ e) := by
  subst b'
  subst f'
  have hh : hz' = hz := Subsingleton.elim _ _
  cases hh
  change CotangentCompatible E F b f hz e →
    CotangentCompatible E F b f hz ((Iso.refl _) ≪≫ e)
  simpa using fun he => he

set_option maxHeartbeats 2000000 in
private lemma frameIso_pair_eq_of_invariant
    (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤))
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D)
    {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤))
    (hm : IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ m)
    (hn : IsFrame ((Scheme.Modules.pullback D.projection).obj K) ⊤ n)
    (hm_action : ∀ (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup)
      (q : D.space ≅ D.space) (h : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q),
      overPull E D L q.hom h.1 m = m)
    (hn_action : ∀ (A : ArithmeticThetaEvenMarkingTorsorR0216.EvenGroup)
      (q : D.space ≅ D.space) (h : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q),
      overPull E D K q.hom h.1 n = n)
    (η : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj K)
    (hη : η.hom.app ⊤ m = n) :
    pullHom (F := InverseCharacterMultiplier.Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom (InverseCharacterMultiplier.first E D)
        (InverseCharacterMultiplier.first E D ≫ D.projection)
          (InverseCharacterMultiplier.first E D ≫ D.projection) rfl rfl =
    pullHom (F := InverseCharacterMultiplier.Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom (InverseCharacterMultiplier.second E D)
        (InverseCharacterMultiplier.first E D ≫ D.projection)
          (InverseCharacterMultiplier.first E D ≫ D.projection)
          pullback.condition.symm pullback.condition.symm := by
  let p := InverseCharacterMultiplier.first E D ≫ D.projection
  let v := ((Scheme.Modules.pullbackComp (InverseCharacterMultiplier.first E D)
    D.projection).app L).hom.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (InverseCharacterMultiplier.first E D) _ m)
  have hv : IsFrame ((Scheme.Modules.pullback p).obj L) ⊤ v :=
    ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      ((Scheme.Modules.pullbackComp (InverseCharacterMultiplier.first E D) D.projection).app L) _
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame
        (InverseCharacterMultiplier.first E D) _ m hm)
  apply InverseCharacterMultiplier.hom_ext_local_pullback v hv
  intro x
  obtain ⟨U, hx, _, he⟩ := InverseCharacterMultiplier.locallyRelated_action E k σ P z D hD
    (InverseCharacterMultiplier.first E D) (InverseCharacterMultiplier.second E D) pullback.condition _
    (InverseCharacterMultiplier.transition_spec E k σ P z D hD
      (InverseCharacterMultiplier.first E D) (InverseCharacterMultiplier.second E D)
      pullback.condition)
    (InverseCharacterMultiplier.action E k σ P z D hD)
    (InverseCharacterMultiplier.action_spec E k σ P z D hD) x
  let A := InverseCharacterMultiplier.transition E k σ P z D hD
    (InverseCharacterMultiplier.first E D) (InverseCharacterMultiplier.second E D)
      pullback.condition x
  let q := InverseCharacterMultiplier.action E k σ P z D hD A
  have hq : ArithmeticThetaEvenMarkingTorsorR0216.Acts E D A.val q :=
    InverseCharacterMultiplier.action_spec E k σ P z D hD A
  have he' : U.ι ≫ InverseCharacterMultiplier.second E D =
      (U.ι ≫ InverseCharacterMultiplier.first E D) ≫ q.hom := by
    simpa only [Category.assoc] using he
  refine ⟨U, hx, ?_⟩
  apply InverseCharacterMultiplier.Transport.pullHom_map_eq p _ _ U.ι (U.ι ≫ p) rfl
  have H := InverseCharacterMultiplier.Transport.pullHom_action_eq D.projection η.hom q.hom hq.1
    (frameIso_action_of_invariant E D m n hm hn hm_action hn_action η hη A q hq)
    (U.ι ≫ InverseCharacterMultiplier.first E D) (U.ι ≫ p) (Category.assoc _ _ _)
  rw [pullHom_pullHom (F := InverseCharacterMultiplier.Transport.FF) η.hom
    (InverseCharacterMultiplier.first E D) p p U.ι
    (U.ι ≫ p) (U.ι ≫ p) rfl rfl rfl rfl,
    pullHom_pullHom (F := InverseCharacterMultiplier.Transport.FF) η.hom
      (InverseCharacterMultiplier.second E D) p p U.ι
      (U.ι ≫ p) (U.ι ≫ p) pullback.condition.symm pullback.condition.symm rfl rfl]
  apply H.symm.trans
  exact P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2.Gen.pullHom_congr
    InverseCharacterMultiplier.Transport.FF η.hom
      ((U.ι ≫ InverseCharacterMultiplier.first E D) ≫ q.hom)
      (U.ι ≫ InverseCharacterMultiplier.second E D) he'.symm
      (U.ι ≫ p) (U.ι ≫ p) _ _ _ _

set_option maxHeartbeats 2000000 in
theorem alpha_tensor_descent
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤)) (hz : z ^ 2 = -1)
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D)
    (L : S.Modules)
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (hm : Multiplier E D z L m) :
    (∃! β : Γ(productLine E L, ⊤), DescendsAlpha E D L m β) ∧
      (∀ β : Γ(productLine E L, ⊤), DescendsAlpha E D L m β →
        IsFrame (productLine E L) ⊤ β) := by
  obtain ⟨i0, hi0, hi0_unique⟩ :=
    ArithmeticThetaSchemeHodgeR0205.cartesian_identity_ideal S D.space E D.family
      D.projection D.comparison D.cartesian.1 D.cartesian.2.1
  let c0 := ArithmeticThetaSchemeHodgeR0205.cotangentComparison E D.family
    D.projection D.comparison D.cartesian.2.1 i0
  have hc0 : CotangentCompatible E D.family D.projection D.comparison D.cartesian.2.1 c0 :=
    ⟨i0, hi0, rfl⟩
  obtain ⟨a, ha, ha_unique⟩ :=
    (ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_section
      k D.space (D.projection ≫ σ) D.family D.marking).1
  have ha_frame :=
    (ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_section
      k D.space (D.projection ≫ σ) D.family D.marking).2 a ha
  let ρ :=
    (pullback_sheafTensor_iso D.space S D.projection (Cotangent E) L) ≪≫
      sheafTensorCongr D.space c0 (Iso.refl _)
  let t : Γ((Scheme.Modules.pullback D.projection).obj (productLine E L), ⊤) :=
    ρ.inv.app ⊤ (tensorSection D.space (Cotangent D.family)
      ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m)
  have ht : IsFrame ((Scheme.Modules.pullback D.projection).obj (productLine E L)) ⊤ t := by
    apply ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso ρ.symm
    exact tensor_section_frame_of_frames a ha_frame m hm.2.1
  have ht_action : ∀ (A : EvenGroup) (q : D.space ≅ D.space)
      (hq : Acts E D A.val q), overPull E D (productLine E L) q.hom hq.1 t = t := by
    intro A q hq
    obtain ⟨N, hN, f, hf, hfc⟩ := acts_markedCartesian k σ E P z D hD A q hq
    have hN_unique : ∀ N' : ArithmeticThetaSchemeLevelR0204.FullLevel D.family 4,
        Changes D.family D.marking N' A.val → N' = N := by
      intro N' hN'
      exact ((ArithmeticThetaSchemeFourCharacterR0215.scheme_four_marking_action k D.space
        (D.projection ≫ σ) D.family D.marking).1 A.val A.property.1).unique hN' hN
    obtain ⟨N', hN', hphase, hcharacter⟩ :=
      ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_character k D.space
        (D.projection ≫ σ) D.family D.marking (D.projection.appTop z) a hD.1.2 ha
          A.val A.property
    have hNN : N' = N := hN_unique N' hN'
    subst N'
    obtain ⟨i1, hi1, _⟩ :=
      ArithmeticThetaSchemeHodgeR0205.cartesian_identity_ideal D.space D.space
        D.family D.family q.hom f hf.1 hf.2.1
    let c1 := ArithmeticThetaSchemeHodgeR0205.cotangentComparison D.family D.family
      q.hom f hf.2.1 i1
    have hc1 : CotangentCompatible D.family D.family q.hom f hf.2.1 c1 :=
      ⟨i1, hi1, rfl⟩
    have ha1 : RealizesAlpha D.family N
        (ArithmeticThetaSchemeFourCharacterR0215.pullAlpha D.family D.family q.hom c1 a) :=
      ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaNaturality.pull_realizes
        D.family D.family D.marking N q.hom f hf c1 hc1 a ha
    have ha_character := hcharacter _ ha1
    have hgf : D.family.zero ≫ (f ≫ D.comparison) =
        (q.hom ≫ D.projection) ≫ E.zero := by
      rw [Category.assoc, hfc, ← Category.assoc, hq.1]
      exact D.cartesian.2.1
    have hc2 : CotangentCompatible E D.family (q.hom ≫ D.projection)
        (f ≫ D.comparison) hgf
        (((Scheme.Modules.pullbackCongr hq.1).app (Cotangent E)) ≪≫ c0) := by
      exact cotangentCompatible_congr E D.family
        D.projection (q.hom ≫ D.projection) D.comparison (f ≫ D.comparison)
        hq.1 hfc D.cartesian.2.1 hgf c0 hc0
    have hcomp : (Scheme.Modules.pullback q.hom).map c0.hom ≫ c1.hom =
        ((Scheme.Modules.pullbackComp q.hom D.projection).app (Cotangent E)).hom ≫
          ((Scheme.Modules.pullbackCongr hq.1).app (Cotangent E)).hom ≫ c0.hom := by
      simpa only [Iso.trans_hom, Category.assoc] using
        ArithmeticThetaSchemeHodgeR0205.scheme_cotangent_coherence.2
        S D.space D.space E D.family D.family D.projection q.hom D.comparison f
        D.cartesian.2.1 hf.2.1 hgf c0 c1
          (((Scheme.Modules.pullbackCongr hq.1).app (Cotangent E)) ≪≫ c0)
          hc0 hc1 hc2
    apply (ConcreteCategory.bijective_of_isIso (ρ.hom.app ⊤)).1
    change ρ.hom.app ⊤
        (overPull E D (productLine E L) q.hom hq.1
          (ρ.inv.app ⊤ (tensorSection D.space (Cotangent D.family)
            ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m))) =
      ρ.hom.app ⊤ (ρ.inv.app ⊤
        (tensorSection D.space (Cotangent D.family)
          ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m))
    dsimp only [overPull]
    rw [show ArithmeticThetaPullback.pullbackGlobalSection q.hom
        ((Scheme.Modules.pullback D.projection).obj (productLine E L))
        (ρ.inv.app ⊤
          (tensorSection D.space (Cotangent D.family)
            ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m)) =
        ((Scheme.Modules.pullback q.hom).map
          ρ.inv).app ⊤
          (ArithmeticThetaPullback.pullbackGlobalSection q.hom
            (sheafTensor D.space (Cotangent D.family)
              ((Scheme.Modules.pullback D.projection).obj L))
            (tensorSection D.space (Cotangent D.family)
              ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m)) from
      Scheme.Modules.pullbackLocalSection_app q.hom
        ρ.inv
        (tensorSection D.space (Cotangent D.family)
          ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m)]
    let eL := (Scheme.Modules.pullbackComp q.hom D.projection).app L ≪≫
      (Scheme.Modules.pullbackCongr hq.1).app L
    let eP := (Scheme.Modules.pullbackComp q.hom D.projection).app (productLine E L) ≪≫
      (Scheme.Modules.pullbackCongr hq.1).app (productLine E L)
    let τ := pullback_sheafTensor_iso D.space D.space q.hom
      (Cotangent D.family) ((Scheme.Modules.pullback D.projection).obj L) ≪≫
        sheafTensorCongr D.space c1 eL
    have hstruct : eP.hom ≫ ρ.hom =
        (Scheme.Modules.pullback q.hom).map ρ.hom ≫ τ.hom := by
      exact AlphaTensorCoherence.tensor_over D.space S D.projection q.hom hq.1
        (Cotangent E) L (Cotangent D.family) c0 c1 hcomp
    have hcancel : (Scheme.Modules.pullback q.hom).map ρ.inv ≫ eP.hom ≫ ρ.hom = τ.hom := by
      rw [hstruct, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    change ((Scheme.Modules.pullback q.hom).map ρ.inv ≫ eP.hom ≫ ρ.hom).app ⊤ _ =
      (ρ.inv ≫ ρ.hom).app ⊤ _
    rw [hcancel, Iso.inv_hom_id]
    change (sheafTensorCongr D.space c1 eL).hom.app ⊤
      ((pullback_sheafTensor_iso D.space D.space q.hom (Cotangent D.family)
        ((Scheme.Modules.pullback D.projection).obj L)).hom.app ⊤
        (pullbackGlobalSection q.hom _ (tensorSection D.space (Cotangent D.family)
          ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m))) =
      tensorSection D.space (Cotangent D.family) ((Scheme.Modules.pullback D.projection).obj L) ⊤ a m
    erw [pullback_sheafTensor_section D.space D.space q.hom (Cotangent D.family)
      ((Scheme.Modules.pullback D.projection).obj L) a m]
    erw [sheafTensorCongr_section D.space c1 eL ⊤
      (pullbackGlobalSection q.hom _ a) (pullbackGlobalSection q.hom _ m)]
    change tensorSection D.space (Cotangent D.family)
      ((Scheme.Modules.pullback D.projection).obj L) ⊤
      (pullAlpha D.family D.family q.hom c1 a) (overPull E D L q.hom hq.1 m) = _
    rw [ha_character, hm.2.2 A q hq]
    have hscalar : D.projection.appTop z ^ (ArithmeticThetaFourTorsion.characterExponent A.val).val *
        D.projection.appTop (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent A.val).val)) = 1 := by
      rw [map_pow, mul_comm]
      apply InverseCharacterMultiplier.inverse_character_mul
      simpa only [map_pow, map_neg, map_one] using congrArg D.projection.appTop hz
    unfold tensorSection
    rw [TensorProduct.smul_tmul_smul, hscalar, one_smul]
  let M := productLine E L
  have hM : Scheme.Modules.IsInvertible M := sheafTensor_invertible (cotangent_invertible E) hm.1
  let v := pullbackGlobalSection D.projection (𝟙_ S.Modules) (1 : Γ(S, ⊤))
  have hv : IsFrame ((Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)) ⊤ v :=
    HodgeBaseChange.pullback_frame D.projection _ _ (InverseCharacterMultiplier.unit_frame S)
  have hv_action : ∀ (A : EvenGroup) (q : D.space ≅ D.space) (h : Acts E D A.val q),
      overPull E D (𝟙_ S.Modules) q.hom h.1 v = v := by
    intro A q hq
    dsimp only [v]
    erw [← InverseCharacterMultiplier.Transport.unit_inv_one D.projection]
    exact InverseCharacterMultiplier.Transport.over_unit D.projection q.hom hq.1
  obtain ⟨η, hη, _⟩ := InverseCharacterMultiplier.existsUnique_frame_iso _ _ v t hv ht
  have hηpair := frameIso_pair_eq_of_invariant k σ E P z D hD v t hv ht hv_action ht_action η hη
  obtain ⟨e, he, _⟩ := InverseCharacterMultiplier.descend_compatible_iso E k σ P z D hD hz
    (𝟙_ S.Modules) M (Scheme.Modules.isInvertible_unit S) hM η
      (InverseCharacterMultiplier.compatible_of_pair_eq E D η hηpair)
  let β : Γ(M, ⊤) := e.hom.app ⊤ (1 : Γ(S, ⊤))
  have hβ : pullbackGlobalSection D.projection M β = t := by
    change Scheme.Modules.pullbackLocalSection D.projection (e.hom.app ⊤ (1 : Γ(S, ⊤))) = t
    rw [Scheme.Modules.pullbackLocalSection_app]
    change ((Scheme.Modules.pullback D.projection).mapIso e).hom.app ⊤ v = t
    rw [he]
    exact hη
  have hβframe : IsFrame M ⊤ β :=
    ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso e _
      (InverseCharacterMultiplier.unit_frame S)
  have hβdesc : DescendsAlpha E D L m β := by
    refine ⟨⟨c0, hc0⟩, ⟨a, ha⟩, ?_⟩
    intro c hc a' ha'
    obtain ⟨i, hi, rfl⟩ := hc
    have hi_eq := hi0_unique i hi
    subst i
    have ha_eq := ha_unique a' ha'
    subst a'
    rw [hβ]
    change (ρ.inv ≫ ρ.hom).app ⊤ _ = _
    rw [Iso.inv_hom_id]
    rfl
  have huniq : ∀ γ : Γ(M, ⊤), DescendsAlpha E D L m γ → γ = β := by
    intro γ hγ
    obtain ⟨hf, het, hs, _⟩ := EvenCoverTorsor.geometry E k σ P z hz D hD
    letI := hf
    letI := het
    letI := hs
    apply AlphaDescentFaithfulness.pullback_section_injective D.projection hM
    apply (ConcreteCategory.bijective_of_isIso (ρ.hom.app ⊤)).1
    exact (hγ.2.2 c0 hc0 a ha).trans (hβdesc.2.2 c0 hc0 a ha).symm
  exact ⟨⟨β, hβdesc, huniq⟩, fun γ hγ => (huniq γ hγ) ▸ hβframe⟩

#print axioms alpha_tensor_descent
end ArithmeticThetaMultiplierKeyR0217
