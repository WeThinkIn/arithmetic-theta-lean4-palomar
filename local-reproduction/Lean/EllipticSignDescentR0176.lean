import Theorems.Thm_AlgebraicGeometry_exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import FullLevelFreeSignR0176
import AffineFreeSignQuotientR0176
import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective

/-! Effective descent of the elliptic family under simultaneous inversion and sign. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176.EllipticSignDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open FullLevelFreeSignR0176 WeierstrassProjModel

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L) (σ : SignAction R W G Z)

/-- The actual diagonal action on the same Cartesian pullback curve. -/
def deck : coverCurve R W Z ⟶ coverCurve R W Z :=
  pullback.lift
    (G.inv (coverToLevel R W Z ≫ Z.projection)
      ⟨coverToCurve R W Z, pullback.condition⟩).val
    (coverToLevel R W Z ≫ σ.map) (by
      rw [(G.inv _ _).property, Category.assoc, σ.over_eq])

@[reassoc (attr := simp)] lemma deck_level :
    deck G Z σ ≫ coverToLevel R W Z = coverToLevel R W Z ≫ σ.map :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)] lemma deck_curve :
    deck G Z σ ≫ coverToCurve R W Z =
      (G.inv (coverToLevel R W Z ≫ Z.projection)
        ⟨coverToCurve R W Z, pullback.condition⟩).val :=
  pullback.lift_fst _ _ _

lemma deck_base : deck G Z σ ≫ (coverToLevel R W Z ≫ Z.projection) =
    coverToLevel R W Z ≫ Z.projection := by
  rw [deck_level_assoc, σ.over_eq]

/-- Squaring the diagonal action inverts the elliptic coordinate twice. -/
lemma deck_square : deck G Z σ ≫ deck G Z σ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, deck_curve]
    have hn := congrArg Subtype.val (inverse_natural G
      (coverToLevel R W Z ≫ Z.projection) (coverToLevel R W Z ≫ Z.projection)
      (deck G Z σ) (deck_base G Z σ)
      ⟨coverToCurve R W Z, pullback.condition⟩)
    dsimp only [WeierstrassProjModel.schemeHomOverComp] at hn
    rw [hn]
    have he : schemeHomOverComp (deck G Z σ) (deck_base G Z σ)
        (⟨coverToCurve R W Z, pullback.condition⟩ :
          SchemeHomOver (coverToLevel R W Z ≫ Z.projection) (structureMap R W)) =
        G.inv (coverToLevel R W Z ≫ Z.projection)
          ⟨coverToCurve R W Z, pullback.condition⟩ := Subtype.ext (deck_curve G Z σ)
    dsimp only [WeierstrassProjModel.schemeHomOverComp] at he
    rw [he, inverse_twice]
    exact (Category.id_comp _).symm
  · simp only [Category.assoc, deck_level, deck_level_assoc, σ.square,
      Category.comp_id, Category.id_comp]

/-- The free action on the level base makes the action on the family free. -/
lemma deck_free : IsEmpty (equalizer (deck G Z σ) (𝟙 _) : Scheme.{u}) := by
  let E := equalizer (deck G Z σ) (𝟙 _)
  let a : E ⟶ Z.space := equalizer.ι (deck G Z σ) (𝟙 _) ≫ coverToLevel R W Z
  have ha : a ≫ σ.map = a := by
    have h := congrArg (fun f => f ≫ coverToLevel R W Z)
      (equalizer.condition (f := deck G Z σ) (g := 𝟙 _))
    simpa only [a, Category.assoc, deck_level, Category.id_comp] using h
  let b : E ⟶ equalizer σ.map (𝟙 _) :=
    equalizer.lift a (ha.trans (Category.comp_id a).symm)
  letI := σ.free
  exact ⟨fun x => isEmptyElim (b x)⟩

@[reassoc (attr := simp)] lemma coverSection_level
    (s : SchemeHomOver Z.projection (structureMap R W)) :
    coverSection R W Z s ≫ coverToLevel R W Z = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)] lemma coverSection_curve
    (s : SchemeHomOver Z.projection (structureMap R W)) :
    coverSection R W Z s ≫ coverToCurve R W Z = s.val :=
  pullback.lift_fst _ _ _

lemma coverSection_deck_curve (s : SchemeHomOver Z.projection (structureMap R W)) :
    coverSection R W Z s ≫ deck G Z σ ≫ coverToCurve R W Z =
      (G.inv Z.projection s).val := by
  rw [deck_curve]
  have hb : coverSection R W Z s ≫ (coverToLevel R W Z ≫ Z.projection) =
      Z.projection := by simp
  have hn := congrArg Subtype.val (inverse_natural G
    (coverToLevel R W Z ≫ Z.projection) Z.projection
    (coverSection R W Z s) hb ⟨coverToCurve R W Z, pullback.condition⟩)
  dsimp only [WeierstrassProjModel.schemeHomOverComp] at hn
  rw [hn]
  congr 2
  exact Subtype.ext (coverSection_curve G Z s)

/-- The origin is equivariant for the same action. -/
lemma origin_equivariant : coverSection R W Z (G.one Z.projection) ≫ deck G Z σ =
    σ.map ≫ coverSection R W Z (G.one Z.projection) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coverSection_deck_curve,
      Category.assoc, coverSection_curve]
    have hn := congrArg Subtype.val (G.one_natural Z.projection Z.projection
      σ.map σ.over_eq)
    dsimp only [WeierstrassProjModel.schemeHomOverComp] at hn
    rw [hn]
    letI := G.pointGroup Z.projection
    exact congrArg Subtype.val (inv_one : (1 : SchemeHomOver Z.projection (structureMap R W))⁻¹ = 1)
  · simp

/-- Both labeled sections are equivariant, without exchanging their labels. -/
lemma marking_equivariant (s : SchemeHomOver Z.projection (structureMap R W))
    (hs : σ.map ≫ s.val = (G.inv Z.projection s).val) :
    coverSection R W Z s ≫ deck G Z σ = σ.map ≫ coverSection R W Z s := by
  apply pullback.hom_ext
  · rw [Category.assoc, coverSection_deck_curve, Category.assoc, coverSection_curve, hs]
  · simp

lemma x_equivariant : coverSection R W Z Z.level.x ≫ deck G Z σ =
    σ.map ≫ coverSection R W Z Z.level.x := marking_equivariant G Z σ _ σ.x_eq

lemma y_equivariant : coverSection R W Z Z.level.y ≫ deck G Z σ =
    σ.map ≫ coverSection R W Z Z.level.y := marking_equivariant G Z σ _ σ.y_eq


section LocalOrbit

/-- A map to a binary coproduct locally factors through one of its summands. -/
lemma locally_in_coprod {X Y T : Scheme.{u}} (a : T ⟶ X ⨿ Y) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧
      ((∃ b : U.toScheme ⟶ X, b ≫ coprod.inl = U.ι ≫ a) ∨
       (∃ b : U.toScheme ⟶ Y, b ≫ coprod.inr = U.ι ≫ a)) := by
  obtain ⟨x | y, h⟩ := (coprodMk X Y).surjective (a t)
  · let U := a ⁻¹ᵁ (coprod.inl : X ⟶ X ⨿ Y).opensRange
    have ht : t ∈ U := ⟨x, by simpa only [coprodMk_inl] using h⟩
    have hr : Set.range (U.ι ≫ a) ⊆ Set.range (coprod.inl : X ⟶ X ⨿ Y) := by
      rintro _ ⟨z, rfl⟩
      exact z.property
    exact ⟨U, ht, Or.inl ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ hr⟩⟩
  · let U := a ⁻¹ᵁ (coprod.inr : Y ⟶ X ⨿ Y).opensRange
    have ht : t ∈ U := ⟨y, by simpa only [coprodMk_inr] using h⟩
    have hr : Set.range (U.ι ≫ a) ⊆ Set.range (coprod.inr : Y ⟶ X ⨿ Y) := by
      rintro _ ⟨z, rfl⟩
      exact z.property
    exact ⟨U, ht, Or.inr ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ hr⟩⟩

/-- The supplied scheme orbit relation controls maps from arbitrary schemes,
including nonreduced schemes, after a Zariski restriction of the test scheme. -/
lemma quotient_locally_orbit {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Base k} {s : X ⟶ X} (Q : SignQuotient k p s)
    {T : Scheme.{u}} (a b : T ⟶ X) (hab : a ≫ Q.q = b ≫ Q.q) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧
      (U.ι ≫ b = U.ι ≫ a ∨ U.ι ≫ b = U.ι ≫ a ≫ s) := by
  let r := pullback.lift a b hab ≫ Q.relation.inv
  obtain ⟨U, ht, ⟨c, hc⟩ | ⟨c, hc⟩⟩ := locally_in_coprod r t
  · have h1 := congrArg (fun f => f ≫ Q.relation.hom ≫ pullback.fst Q.q Q.q) hc
    have h2 := congrArg (fun f => f ≫ Q.relation.hom ≫ pullback.snd Q.q Q.q) hc
    simp only [Category.assoc, Q.left_fst, Q.left_snd, Category.comp_id,
      r, Iso.inv_hom_id_assoc, pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact ⟨U, ht, Or.inl (h2.symm.trans h1)⟩
  · have h1 := congrArg (fun f => f ≫ Q.relation.hom ≫ pullback.fst Q.q Q.q) hc
    have h2 := congrArg (fun f => f ≫ Q.relation.hom ≫ pullback.snd Q.q Q.q) hc
    simp only [Category.assoc, Q.right_fst, Q.right_snd, Category.comp_id,
      r, Iso.inv_hom_id_assoc, pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact ⟨U, ht, Or.inr (by rw [← Category.assoc, ← h1, ← h2])⟩

end LocalOrbit


section SplitBaseChange
variable {k : Type u} [Field k] {X V : Scheme.{u}} {p : X ⟶ Base k}
    {s : X ⟶ X} (Q : SignQuotient k p s) (e : V ⟶ X)

/-- The identity branch of the pullback of the quotient cover. -/
def firstBranch : V ⟶ pullback (e ≫ Q.q) Q.q :=
  pullback.lift (𝟙 V) e (by simp)

/-- The sign branch of the pullback of the quotient cover. -/
def secondBranch : V ⟶ pullback (e ≫ Q.q) Q.q :=
  pullback.lift (𝟙 V) (e ≫ s) (by simp [Q.invariant])

@[reassoc (attr := simp)] lemma firstBranch_fst :
    firstBranch Q e ≫ pullback.fst _ _ = 𝟙 V := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma firstBranch_snd :
    firstBranch Q e ≫ pullback.snd _ _ = e := pullback.lift_snd _ _ _
@[reassoc (attr := simp)] lemma secondBranch_fst :
    secondBranch Q e ≫ pullback.fst _ _ = 𝟙 V := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma secondBranch_snd :
    secondBranch Q e ≫ pullback.snd _ _ = e ≫ s := pullback.lift_snd _ _ _

instance : IsOpenImmersion (firstBranch Q e) := by
  letI := Q.etale
  letI := Q.finite
  exact (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    (pullback.fst (e ≫ Q.q) Q.q) (firstBranch Q e) (firstBranch_fst Q e)).1

instance : IsOpenImmersion (secondBranch Q e) := by
  letI := Q.etale
  letI := Q.finite
  exact (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    (pullback.fst (e ≫ Q.q) Q.q) (secondBranch Q e) (secondBranch_fst Q e)).1

lemma split_branches_disjoint (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u})) :
    Disjoint (Set.range (firstBranch Q e)) (Set.range (secondBranch Q e)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  constructor
  intro t
  let T := pullback (firstBranch Q e) (secondBranch Q e)
  letI : Nonempty T := ⟨t⟩
  let a : T ⟶ V := pullback.fst (firstBranch Q e) (secondBranch Q e)
  let b : T ⟶ V := pullback.snd (firstBranch Q e) (secondBranch Q e)
  have h := pullback.condition (f := firstBranch Q e) (g := secondBranch Q e)
  have hab : a = b := by
    simpa only [Category.assoc, firstBranch_fst, secondBranch_fst, Category.comp_id]
      using congrArg (fun f => f ≫ pullback.fst (e ≫ Q.q) Q.q) h
  have hs : a ≫ e = b ≫ e ≫ s := by
    simpa only [Category.assoc, firstBranch_snd, secondBranch_snd]
      using congrArg (fun f => f ≫ pullback.snd (e ≫ Q.q) Q.q) h
  apply AffineFreeSignQuotient.no_fixed_test_map s hfree (b ≫ e)
  simpa only [Category.assoc] using hs.symm.trans (congrArg (fun f => f ≫ e) hab)

lemma split_branches_cover :
    Codisjoint (Set.range (firstBranch Q e)) (Set.range (secondBranch Q e)) := by
  rw [codisjoint_iff]
  apply Set.eq_univ_of_forall
  intro t
  have hc : (pullback.fst (e ≫ Q.q) Q.q ≫ e) ≫ Q.q =
      pullback.snd (e ≫ Q.q) Q.q ≫ Q.q := by
    rw [Category.assoc]; exact pullback.condition
  obtain ⟨U, ht, he | he⟩ := quotient_locally_orbit Q
    (pullback.fst (e ≫ Q.q) Q.q ≫ e) (pullback.snd (e ≫ Q.q) Q.q) hc t
  · left
    have hh : U.ι ≫ pullback.fst (e ≫ Q.q) Q.q ≫ firstBranch Q e = U.ι := by
      apply pullback.hom_ext
      · simp
      · simpa only [Category.assoc, firstBranch_snd] using he.symm
    exact ⟨pullback.fst (e ≫ Q.q) Q.q t,
      congrArg (fun f => f ⟨t, ht⟩) hh⟩
  · right
    have hh : U.ι ≫ pullback.fst (e ≫ Q.q) Q.q ≫ secondBranch Q e = U.ι := by
      apply pullback.hom_ext
      · simp
      · simpa only [Category.assoc, secondBranch_snd] using he.symm
    exact ⟨pullback.fst (e ≫ Q.q) Q.q t,
      congrArg (fun f => f ⟨t, ht⟩) hh⟩

/-- The orbit relation remains a binary coproduct after every base change. -/
def splitBaseChange (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u})) :
    V ⨿ V ≅ pullback (e ≫ Q.q) Q.q :=
  (coprodIsCoprod V V).coconePointUniqueUpToIso
    (nonempty_isColimit_binaryCofanMk_of_isCompl (firstBranch Q e) (secondBranch Q e)
      (by
        simpa only [isCompl_iff, disjoint_iff, codisjoint_iff,
          ← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_inf,
          TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_bot,
          TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_opensRange,
          Set.sup_eq_union, Set.inf_eq_inter, Set.bot_eq_empty, Set.top_eq_univ] using
          (show IsCompl (Set.range (firstBranch Q e)) (Set.range (secondBranch Q e)) from
            ⟨split_branches_disjoint Q e hfree, split_branches_cover Q e⟩))).some

@[reassoc (attr := simp)] lemma inl_splitBaseChange
    (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u})) :
    coprod.inl ≫ (splitBaseChange Q e hfree).hom = firstBranch Q e := by
  exact (coprodIsCoprod V V).comp_coconePointUniqueUpToIso_hom _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] lemma inr_splitBaseChange
    (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u})) :
    coprod.inr ≫ (splitBaseChange Q e hfree).hom = secondBranch Q e := by
  exact (coprodIsCoprod V V).comp_coconePointUniqueUpToIso_hom _ ⟨WalkingPair.right⟩

end SplitBaseChange


section DescentDatum
variable {k : Type u} [Field k] {X V : Scheme.{u}} {p : X ⟶ Base k}
    {s : X ⟶ X} (Q : SignQuotient k p s) (e : V ⟶ X)
    (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u}))
    (d : V ⟶ V) (hd : d ≫ e = e ≫ s)

include hfree in
lemma split_hom_ext {T : Scheme.{u}} {a b : pullback (e ≫ Q.q) Q.q ⟶ T}
    (h0 : firstBranch Q e ≫ a = firstBranch Q e ≫ b)
    (h1 : secondBranch Q e ≫ a = secondBranch Q e ≫ b) : a = b := by
  apply (cancel_epi (splitBaseChange Q e hfree).hom).mp
  apply coprod.hom_ext <;> simpa only [inl_splitBaseChange_assoc, inr_splitBaseChange_assoc] using (by assumption)

/-- The transition is identity on the diagonal branch and the specified deck
involution on the other branch. -/
def transition : pullback (e ≫ Q.q) Q.q ⟶ V :=
  (splitBaseChange Q e hfree).inv ≫ coprod.desc (𝟙 V) d

@[reassoc (attr := simp)] lemma first_transition :
    firstBranch Q e ≫ transition Q e hfree d = 𝟙 V := by
  unfold transition
  rw [← inl_splitBaseChange Q e hfree, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]

@[reassoc (attr := simp)] lemma second_transition :
    secondBranch Q e ≫ transition Q e hfree d = d := by
  unfold transition
  rw [← inr_splitBaseChange Q e hfree, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]

include hd in
@[reassoc] lemma transition_comp : transition Q e hfree d ≫ e = pullback.snd (e ≫ Q.q) Q.q := by
  apply split_hom_ext Q e hfree <;> simp [hd]

lemma first_actMap :
    firstBranch Q (pullback.snd (e ≫ Q.q) Q.q) ≫
      DescentAction.actMap (transition Q e hfree d) (transition_comp Q e hfree d hd) =
    transition Q e hfree d ≫ firstBranch Q e := by
  apply pullback.hom_ext <;> simp [transition_comp Q e hfree d hd]

lemma second_actMap :
    secondBranch Q (pullback.snd (e ≫ Q.q) Q.q) ≫
      DescentAction.actMap (transition Q e hfree d) (transition_comp Q e hfree d hd) =
    transition Q e hfree d ≫ secondBranch Q e := by
  apply pullback.hom_ext <;> simp [transition_comp_assoc Q e hfree d hd]

lemma first_proj13 :
    firstBranch Q (pullback.snd (e ≫ Q.q) Q.q) ≫ DescentAction.proj₁₃ Q.q e = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

@[reassoc] lemma second_proj13_first :
    firstBranch Q e ≫ secondBranch Q (pullback.snd (e ≫ Q.q) Q.q) ≫
      DescentAction.proj₁₃ Q.q e = secondBranch Q e := by
  apply pullback.hom_ext <;> simp

@[reassoc] lemma second_proj13_second (hs : s ≫ s = 𝟙 X) :
    secondBranch Q e ≫ secondBranch Q (pullback.snd (e ≫ Q.q) Q.q) ≫
      DescentAction.proj₁₃ Q.q e = firstBranch Q e := by
  apply pullback.hom_ext <;> simp [hs]

/-- A genuine descent cocycle, verified on all four branches of the triple
fiber product by the square of the deck involution. -/
def signDescentDatum (hs : s ≫ s = 𝟙 X) (hdd : d ≫ d = 𝟙 V) :
    DescentAction Q.q e where
  act := transition Q e hfree d
  act_comp := transition_comp Q e hfree d hd
  unit_act := first_transition Q e hfree d
  trans := by
    apply split_hom_ext Q (pullback.snd (e ≫ Q.q) Q.q) hfree
    · rw [← Category.assoc, first_actMap Q e hfree d hd, Category.assoc, first_transition]
      rw [Category.comp_id, ← Category.assoc, first_proj13, Category.id_comp]
    · rw [← Category.assoc, second_actMap Q e hfree d hd, Category.assoc, second_transition]
      apply split_hom_ext Q e hfree
      · rw [← Category.assoc, first_transition, Category.id_comp]
        rw [second_proj13_first_assoc, second_transition]
      · rw [← Category.assoc, second_transition, hdd]
        rw [second_proj13_second_assoc Q e hs, first_transition]

end DescentDatum


section Effective
variable {k : Type u} [Field k] {X V : Scheme.{u}} {p : X ⟶ Base k}
    {s : X ⟶ X} (Q : SignQuotient k p s) (e : V ⟶ X)
    (hfree : IsEmpty (equalizer s (𝟙 X) : Scheme.{u}))
    (d : V ⟶ V)

lemma transition_points (r : (pullback (e ≫ Q.q) Q.q : Scheme.{u})) :
    transition Q e hfree d r = pullback.fst (e ≫ Q.q) Q.q r ∨
    transition Q e hfree d r = d (pullback.fst (e ≫ Q.q) Q.q r) := by
  obtain ⟨v | v, hv⟩ := (coprodMk V V).surjective ((splitBaseChange Q e hfree).inv r)
  · have hr := congrArg (fun z => (splitBaseChange Q e hfree).hom z) hv
    simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, inl_splitBaseChange,
      Iso.inv_hom_id] at hr
    change _ = r at hr
    rw [← hr]
    left
    change (firstBranch Q e ≫ transition Q e hfree d) v =
      (firstBranch Q e ≫ pullback.fst (e ≫ Q.q) Q.q) v
    simp
  · have hr := congrArg (fun z => (splitBaseChange Q e hfree).hom z) hv
    simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, inr_splitBaseChange,
      Iso.inv_hom_id] at hr
    change _ = r at hr
    rw [← hr]
    right
    change (secondBranch Q e ≫ transition Q e hfree d) v =
      d ((secondBranch Q e ≫ pullback.fst (e ≫ Q.q) Q.q) v)
    simp

include hfree in
/-- Effective scheme descent is proved from the constructed cocycle and affine
neighborhoods of its finite orbits. No target scheme is an input. -/
theorem effective_scheme (hd : d ≫ e = e ≫ s) (hs : s ≫ s = 𝟙 X)
    (hdd : d ≫ d = 𝟙 V)
    (haff : ∀ F : Finset V, ∃ U : V.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Base Q.ring) (c : V ⟶ Y),
      IsPullback c e f Q.q ∧ d ≫ c = c := by
  classical
  let A := signDescentDatum Q e hfree d hd hs hdd
  letI := Q.finite
  letI := Q.etale
  haveI : IsFinite A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : Flat A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : LocallyOfFinitePresentation A.act := by rw [A.act_eq_invol_fst]; infer_instance
  have horbit : ∀ x : V, ∃ U : V.Opens, IsAffineOpen U ∧
      ∀ r : (pullback (e ≫ Q.q) Q.q : Scheme.{u}), pullback.fst (e ≫ Q.q) Q.q r = x → A.act r ∈ U := by
    intro x
    obtain ⟨U, hU, hF⟩ := haff {x, d x}
    refine ⟨U, hU, fun r hr => ?_⟩
    rcases transition_points Q e hfree d r with h | h
    · change transition Q e hfree d r ∈ U
      rw [h, hr]
      exact hF x (by simp)
    · change transition Q e hfree d r ∈ U
      rw [h, hr]
      exact hF (d x) (by simp)
  obtain ⟨Y, c, w, hf, hfl, hfp, hsurj, hrel, ⟨hcol⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (e ≫ Q.q) Q.q) A.act
      (fun a b h1 h2 => A.hom_ext h1 h2) (fun T => A.equivalence T) horbit
  letI := hf
  letI := hfl
  letI := hsurj
  have hco : pullback.fst (e ≫ Q.q) Q.q ≫ e ≫ Q.q = A.act ≫ e ≫ Q.q := by
    rw [reassoc_of% A.act_comp, pullback.condition]
  obtain ⟨f, hcf⟩ := Cofork.IsColimit.desc' hcol (e ≫ Q.q) hco
  obtain ⟨i, hi, hi', _⟩ :=
    DescentAction.effective_of_isPullback_of_flat_surjective Q.q A c w hrel f hcf
  refine ⟨Y, f, c, IsPullback.of_iso_pullback ⟨hcf⟩ i.symm ?_ ?_, ?_⟩
  · change i.inv ≫ pullback.fst f Q.q = c
    rw [hi', pullback.lift_fst]
  · change i.inv ≫ pullback.snd f Q.q = e
    rw [hi', pullback.lift_snd]
  · have hw := congrArg (fun a => secondBranch Q e ≫ a) w
    change secondBranch Q e ≫ pullback.fst (e ≫ Q.q) Q.q ≫ c =
      secondBranch Q e ≫ transition Q e hfree d ≫ c at hw
    simpa only [secondBranch_fst_assoc, second_transition_assoc, Category.id_comp] using hw.symm

end Effective

/-- Finite base change of the actual projective cubic has affine neighborhoods
of every finite set. This is the projective effectivity input for sign descent. -/
lemma cover_affine_finite [IsFinite Z.projection] (F : Finset (coverCurve R W Z)) :
    ∃ U : (coverCurve R W Z).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨U, hU, hF⟩ := exists_isAffineOpen_forall_mem_of_isImmersion_proj
    (projModelGradingCR W.toProjective) (𝟙 (Curve R W))
    (F.image (coverToCurve R W Z))
  refine ⟨coverToCurve R W Z ⁻¹ᵁ U, hU.preimage (coverToCurve R W Z), ?_⟩
  intro x hx
  exact hF _ (Finset.mem_image_of_mem _ hx)


section Commutativity
open GoodReductionJacobian
variable {S : Type u} [CommRing S] {Y : Scheme.{u}} {f : Y ⟶ Base S}

/-- Reversing multiplication retains the same actual group scheme and origin. -/
def oppositeLaw (H : GoodReductionJacobian.RelativeGroupLaw S f) :
    GoodReductionJacobian.RelativeGroupLaw S f where
  mul t x y := H.mul t y x
  one := H.one
  inv := H.inv
  mul_assoc t x y z := (H.mul_assoc t z y x).symm
  one_mul := H.mul_one
  mul_one := H.one_mul
  inv_mul_cancel := H.mul_inv_cancel
  mul_natural t t' a ha x y := H.mul_natural t t' a ha y x

/-- Pointed uniqueness for proper smooth connected groups implies
commutativity over arbitrary rings, including disconnected rings. -/
lemma commutative_of_bundle (hY : AbelianSchemePropertyBundle S f)
    (H : GoodReductionJacobian.RelativeGroupLaw S f) : H.IsCommutative := by
  have he := GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
    hY H (oppositeLaw H) rfl
  intro T t x y
  exact congrArg (fun J => J.mul t x y) he
end Commutativity

section FamilyConstruction
variable {k : Type u} [Field k] [Algebra k R]
    (Q : SignQuotient k (Z.projection ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map)

lemma invariant_origin {Y : Scheme.{u}} (c : coverCurve R W Z ⟶ Y)
    (hc : deck G Z σ ≫ c = c) :
    σ.map ≫ coverSection R W Z (G.one Z.projection) ≫ c =
      coverSection R W Z (G.one Z.projection) ≫ c := by
  rw [← Category.assoc, ← origin_equivariant, Category.assoc, hc]

/-- The zero section descends through the actual categorical sign quotient. -/
lemma descended_origin {Y : Scheme.{u}} (f : Y ⟶ Base Q.ring)
    (c : coverCurve R W Z ⟶ Y)
    (hcart : IsPullback c (coverToLevel R W Z) f Q.q)
    (hc : deck G Z σ ≫ c = c) :
    ∃ z : NeronModelInfra.SchemeHomOver (𝟙 (Base Q.ring)) f,
      coverSection R W Z (G.one Z.projection) ≫ c = Q.q ≫ z.val := by
  obtain ⟨z, hz, _⟩ := Q.universal Y
    (coverSection R W Z (G.one Z.projection) ≫ c) (invariant_origin G Z σ c hc)
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  have hzf : z ≫ f = 𝟙 _ := by
    apply (cancel_epi Q.q).mp
    rw [← Category.assoc, hz, Category.assoc, hcart.w]
    simp
  exact ⟨⟨z, hzf⟩, hz.symm⟩

end FamilyConstruction


section GroupDescent
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open GoodReductionJacobian

include G in
lemma source_bundle [W.IsElliptic] :
    AbelianSchemePropertyBundle R (structureMap R W) := by
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap R W) := projModelStrCR_isProper W.toProjective
  letI : GeometricallyIntegral (structureMap R W) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (projModel_pullback_iso_baseChange W.toProjective)
  exact ⟨inferInstance, inferInstance, fun x => by
    rw [← (structureMap R W).range_fiberι, ← Set.image_univ]
    exact isConnected_univ.image _ ((structureMap R W).fiberι x).continuous.continuousOn,
    ⟨toGRJ G⟩⟩

variable {k : Type u} [Field k] [Algebra k R]
    (Q : SignQuotient k (Z.projection ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map)

/-- Descend the pointed group structure on the constructed Cartesian family.
The faithfully flat extension and every structural map are derived from Q.q. -/
lemma descended_group_geometry [W.IsElliptic]
    {Y : Scheme.{u}} (f : Y ⟶ Base Q.ring) (c : coverCurve R W Z ⟶ Y)
    (hcart : IsPullback c (coverToLevel R W Z) f Q.q)
    (z : NeronModelInfra.SchemeHomOver (𝟙 (Base Q.ring)) f)
    (hz : coverSection R W Z (G.one Z.projection) ≫ c = Q.q ≫ z.val) :
    ∃ H : GoodReductionJacobian.RelativeGroupLaw Q.ring f,
      H.IsCommutative ∧ IsProper f ∧ SmoothOfRelativeDimension 1 f ∧
      GeometricallyConnected f ∧ (H.one (𝟙 _)).val = z.val := by
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  obtain ⟨A, hA, hAlg, hfin, hff, het, y, hy⟩ :=
    exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
      Q.q Q.q.surjective (𝟙 (Base Q.ring))
  letI := hA
  letI := hAlg
  letI := hff
  let t : Base A ⟶ Base R := y ≫ Z.projection
  let V : Scheme.{u} := pullback (structureMap R W) t
  let v : V ⟶ Base A := pullback.snd (structureMap R W) t
  let u : V ⟶ coverCurve R W Z :=
    pullback.lift (pullback.fst (structureMap R W) t) (v ≫ y)
      (by rw [Category.assoc]; exact pullback.condition)
  have hu1 : u ≫ coverToCurve R W Z = pullback.fst (structureMap R W) t :=
    pullback.lift_fst _ _ _
  have hu2 : u ≫ coverToLevel R W Z = v ≫ y := pullback.lift_snd _ _ _
  have hup : IsPullback u v (coverToLevel R W Z) y := by
    have hb : IsPullback (u ≫ coverToCurve R W Z) v (structureMap R W) (y ≫ Z.projection) := by
      rw [hu1]
      exact IsPullback.of_hasPullback _ _
    exact hb.of_right hu2 (IsPullback.of_hasPullback _ _)
  have hq : y ≫ Q.q = Spec.map (CommRingCat.ofHom (algebraMap Q.ring A)) := by
    simpa only [Category.comp_id] using hy.w.symm
  have hcp : IsPullback (u ≫ c) v f
      (Spec.map (CommRingCat.ofHom (algebraMap Q.ring A))) := by
    rw [← hq]
    exact hup.paste_horiz hcart
  let H' : GoodReductionJacobian.RelativeGroupLaw A v := (toGRJ G).baseChange t
  have hV : AbelianSchemePropertyBundle A v :=
    (source_bundle G).of_isPullback (IsPullback.of_hasPullback (structureMap R W) t)
  have hu0 : (H'.one (𝟙 _)).val ≫ u = y ≫ coverSection R W Z (G.one Z.projection) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, Category.assoc, coverSection_curve]
      dsimp only [H', GoodReductionJacobian.RelativeGroupLaw.baseChange,
        GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase, toGRJ]
      rw [pullback.lift_fst]
      change (G.one ((𝟙 (Base A)) ≫ t)).val = y ≫ (G.one Z.projection).val
      have hn := congrArg Subtype.val (G.one_natural Z.projection (𝟙 (Base A) ≫ t) y (by simp [t]))
      dsimp only [WeierstrassProjModel.schemeHomOverComp] at hn
      exact hn.symm
    · rw [Category.assoc, hu2, ← Category.assoc, (H'.one (𝟙 _)).property]
      simp
  have hzero : (H'.one (𝟙 _)).val ≫ (u ≫ c) =
      Spec.map (CommRingCat.ofHom (algebraMap Q.ring A)) ≫ z.val := by
    rw [← Category.assoc, hu0, Category.assoc, hz, ← Category.assoc, hq]
  obtain ⟨H, hH⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
      A f z v (u ≫ c) hcp hV H' hzero
  have hY : AbelianSchemePropertyBundle Q.ring f :=
    AbelianSchemePropertyBundle.of_isPullback_of_faithfullyFlat A (u ≫ c) hcp hV H
  have hdim : SmoothOfRelativeDimension 1 f := by
    letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
      projModelStrCR_smoothOfRelativeDimension_one W.toProjective
    letI : SmoothOfRelativeDimension 1 (coverToLevel R W Z) := inferInstance
    exact SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective 1 hcart.flip
  have hconn : GeometricallyConnected f := ⟨by
    intro K _ a V' fst snd hpb
    letI : IsIntegral V' := (hY.geometricallyIntegral_of_commRing).1 a fst snd hpb
    infer_instance⟩
  exact ⟨H, commutative_of_bundle hY H, hY.proper, hdim, hconn, hH⟩

end GroupDescent

end ArithmeticThetaLegendreAtlasR0176.EllipticSignDescent

namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 EllipticSignDescent

/-- Effective descent of the elliptic family for the prescribed simultaneous
sign action, with a Cartesian invariant comparison and the correct origin. -/
theorem elliptic_sign_descent :
∀ (k : Type u) [Field k] [CharZero k] (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L) (Z : ArithmeticThetaFullLevelCoverR0175.LevelScheme R W G L) (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) (σ : ArithmeticThetaLegendreAtlasR0176.SignAction R W G Z) (Q : ArithmeticThetaLegendreAtlasR0176.SignQuotient k (CategoryTheory.CategoryStruct.comp (Z.projection) (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k R)))) σ.map), Nonempty (ArithmeticThetaLegendreAtlasR0176.FamilyDescent k R W G Z σ Q) := by
  intro k _ _ R _ _ _ _ _ _ W _ G hG L hL Z hZ σ Q
  obtain ⟨hfinite, _, _, _⟩ := full_level_cover_geometry R W G hG L (by omega) Z hZ
  letI := hfinite
  obtain ⟨Y, f, c, hcart, hcinv⟩ :=
    effective_scheme Q (coverToLevel R W Z) σ.free (deck G Z σ)
      (deck_level G Z σ) σ.square (deck_square G Z σ) (cover_affine_finite G Z)
  obtain ⟨z, hz⟩ := descended_origin G Z σ Q f c hcart hcinv
  obtain ⟨H, hcomm, hproper, hsmooth, hconn, hzero⟩ :=
    descended_group_geometry G Z σ Q f c hcart z hz
  refine ⟨{
    family := ⟨Y, f, H, hcomm, hproper, hsmooth, hconn⟩
    comparison := c
    cartesian := hcart
    origin_eq := ?_
    action := deck G Z σ
    action_level := deck_level G Z σ
    action_curve := deck_curve G Z σ
    invariant := hcinv }⟩
  change coverSection R W Z (G.one Z.projection) ≫ c = Q.q ≫ (H.one (𝟙 _)).val
  rw [hzero]
  exact hz

#print axioms elliptic_sign_descent
end ArithmeticThetaLegendreAtlasR0176
