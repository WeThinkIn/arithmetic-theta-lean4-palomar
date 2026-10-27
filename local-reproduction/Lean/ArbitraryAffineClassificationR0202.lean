import ArbitraryCompatibleLocalCoverageR0202
import ArbitraryClassifyingUniquenessR0202

/-! Effective descent of the arbitrary affine marked-Weierstrass classifier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202
namespace AffineClassification
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaCompatibleLevelR0178.NormalAffineClassifyingConstruction

/-- Affine tests detect equality of scheme maps, including nilpotent directions. -/
lemma affine_ext {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ (S : Type u) [CommRing S] (a : Base S ⟶ X), a ≫ f = a ≫ g) : f = g := by
  apply X.affineCover.hom_ext
  intro j
  let U := X.affineCover.X j
  let v : Base Γ(U, ⊤) ⟶ U := U.isoSpec.inv
  apply (cancel_epi v).mp
  simpa only [Category.assoc] using h Γ(U, ⊤) (v ≫ X.affineCover.f j)

section Local
variable {k : Type u} [Field k] [CharZero k] {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
  {A : LegendreAtlas k L} {B : TwoMarking k L A} (hB : CanonicalTwo k L A B)
  {C : CompatibleCover k L A B} {Q : CompatibleQuotient k L A B C}
  {R : Type u} [CommRing R] [Algebra ℚ R] [Algebra k R]
  {W : WeierstrassCurve R} [W.IsElliptic] {G : Law R W} (hG : IsOriginLaw R W G)
  {M : FullLevel R W G L (𝟙 (Base R))}
  (N : ArithmeticThetaArbitraryAffineR0202.LocalComparison k L A B C Q R W G M)

include hL heven hB hG

/-- Compare two lifts on every affine test scheme. -/
lemma affine_agreement (K : Type u) [CommRing K]
    (a₁ a₂ : Base K ⟶ Base N.comparison.ring)
    (ha : a₁ ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom) =
      a₂ ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom)) :
    a₁ ≫ N.base = a₂ ≫ N.base ∧
    ∀ (z₁ z₂ : Base K ⟶ Curve N.comparison.ring (W.map N.comparison.inclusion.toRingHom)),
      z₁ ≫ structureMap _ _ = a₁ → z₂ ≫ structureMap _ _ = a₂ →
      z₁ ≫ N.comparison.sourceMap = z₂ ≫ N.comparison.sourceMap →
      z₁ ≫ N.comparison.comparison = z₂ ≫ N.comparison.comparison := by
  let i := a₁ ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom)
  let α : R →+* K := (Spec.preimage i).hom
  have hi : baseMap R K α = i := Spec.map_preimage i
  letI : Algebra R K := α.toAlgebra
  letI : Algebra k K := (α.comp (algebraMap k R)).toAlgebra
  letI : Algebra ℚ K := (α.comp (algebraMap ℚ R)).toAlgebra
  let V := W.map α
  letI : V.IsElliptic := inferInstance
  obtain ⟨b, _, hb, hob, _⟩ := NormalFormConstruction.coefficient_comparison W α
  change IsPullback b (structureMap K V) (structureMap R W) (baseMap R K α) at hb
  change origin K V ≫ b = baseMap R K α ≫ origin R W at hob
  obtain ⟨H, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      α (structureMap R W) (structureMap K V) b hb G
  have hH : IsOriginLaw K V H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [hj, hG.1, Category.assoc, hob, baseMap]
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (H.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hBC := ArbitraryLocalCoverage.pointed_base_change G H hG hH α b hb hob
  let M₀ := BaseChange.restrict M (baseMap R K α)
    (by simp : baseMap R K α ≫ 𝟙 _ = 𝟙 _ ≫ baseMap R K α)
  let MK := ArbitraryLocalCoverage.MarkingTransport.up hBC hG hH M₀
  have hx : MK.x.val ≫ b = i ≫ M.x.val := by
    calc
      _ = M₀.x.val := ArbitraryLocalCoverage.MarkingTransport.up_x hBC hG hH M₀
      _ = _ := by change baseMap R K α ≫ M.x.val = _; rw [hi]
  have hy : MK.y.val ≫ b = i ≫ M.y.val := by
    calc
      _ = M₀.y.val := ArbitraryLocalCoverage.MarkingTransport.up_y hBC hG hH M₀
      _ = _ := by change baseMap R K α ≫ M.y.val = _; rw [hi]
  have hi₁ : a₁ ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom) =
      baseMap R K α := hi.symm
  have hi₂ : a₂ ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom) =
      baseMap R K α := ha.symm.trans hi.symm
  have build (a : Base K ⟶ Base N.comparison.ring)
      (hai : a ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom) =
        baseMap R K α) :
      ∃ c : Curve K V ⟶ Curve N.comparison.ring (W.map N.comparison.inclusion.toRingHom),
        c ≫ N.comparison.sourceMap = b ∧
        c ≫ structureMap _ _ = structureMap K V ≫ a ∧
        Classifies k L A B C Q K V H MK (a ≫ N.base) (c ≫ N.comparison.comparison) := by
    let c := N.comparison.sourceCartesian.lift b (structureMap K V ≫ a)
      (by rw [Category.assoc, hai]; exact hb.w)
    have hcb : c ≫ N.comparison.sourceMap = b := N.comparison.sourceCartesian.lift_fst _ _ _
    have hcp : c ≫ structureMap _ _ = structureMap K V ≫ a :=
      N.comparison.sourceCartesian.lift_snd _ _ _
    have hc : IsPullback c (structureMap K V) (structureMap _ _) a := by
      have hout : IsPullback (c ≫ N.comparison.sourceMap) (structureMap K V)
          (structureMap R W) (a ≫ Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom)) := by
        rw [hcb, hai]; exact hb
      exact hout.of_right hcp N.comparison.sourceCartesian
    have sec (s : Base K ⟶ Curve K V)
        (t : Base N.comparison.ring ⟶ Curve N.comparison.ring (W.map N.comparison.inclusion.toRingHom))
        (hs : s ≫ structureMap K V = 𝟙 _)
        (ht : t ≫ structureMap _ _ = 𝟙 _)
        (he : s ≫ b = a ≫ t ≫ N.comparison.sourceMap) : s ≫ c = a ≫ t := by
      apply N.comparison.sourceCartesian.hom_ext
      · rw [Category.assoc, hcb]; exact he
      · rw [Category.assoc, hcp, ← Category.assoc, hs, Category.id_comp,
          Category.assoc, ht, Category.comp_id]
    refine ⟨c, hcb, hcp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, N.over_eq]
      change a ≫ Spec.map (CommRingCat.ofHom (algebraMap k N.comparison.ring)) =
        Spec.map (CommRingCat.ofHom (α.comp (algebraMap k R)))
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      change a ≫ _ = baseMap R K α ≫ _
      rw [← hai, Category.assoc]
      congr 1
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext N.comparison.inclusion.comp_algebraMap.symm)
    · simpa only [Category.assoc, N.factorization] using hc.paste_horiz N.comparison.cartesian
    · rw [← Category.assoc, sec (origin K V) (origin _ _)
          (BaseChange.origin_over _ _) (BaseChange.origin_over _ _) (by
            rw [hob, N.comparison.sourceOrigin, ← Category.assoc, hai]),
        Category.assoc, N.comparison.origin_eq, ← N.factorization]
      simp only [Category.assoc]
    · rw [← Category.assoc, sec MK.x.val N.comparison.x MK.x.property N.comparison.x_over (by
            rw [hx, N.comparison.x_lift, ← Category.assoc, hai, hi]),
        Category.assoc, N.comparison.x_eq, ← N.factorization]
      simp only [Category.assoc]
    · rw [← Category.assoc, sec MK.y.val N.comparison.y MK.y.property N.comparison.y_over (by
            rw [hy, N.comparison.y_lift, ← Category.assoc, hai, hi]),
        Category.assoc, N.comparison.y_eq, ← N.factorization]
      simp only [Category.assoc]
  obtain ⟨c₁, hc₁b, hc₁p, h₁⟩ := build a₁ hi₁
  obtain ⟨c₂, hc₂b, hc₂p, h₂⟩ := build a₂ hi₂
  obtain ⟨hebase, hecurve⟩ := arbitrary_classifying_uniqueness k L hL heven A B hB C Q
    K V H hH MK _ _ _ _ h₁ h₂
  refine ⟨hebase, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hz
  let z := hb.lift (z₁ ≫ N.comparison.sourceMap) (𝟙 _) (by
    rw [Category.assoc, N.comparison.sourceCartesian.w, ← Category.assoc, hz₁,
      hi₁, Category.id_comp])
  have hzb : z ≫ b = z₁ ≫ N.comparison.sourceMap := hb.lift_fst _ _ _
  have hzp : z ≫ structureMap K V = 𝟙 _ := hb.lift_snd _ _ _
  have hc₁ : z ≫ c₁ = z₁ := by
    apply N.comparison.sourceCartesian.hom_ext
    · rw [Category.assoc, hc₁b, hzb]
    · rw [Category.assoc, hc₁p, ← Category.assoc, hzp, Category.id_comp, hz₁]
  have hc₂ : z ≫ c₂ = z₂ := by
    apply N.comparison.sourceCartesian.hom_ext
    · rw [Category.assoc, hc₂b, hzb, hz]
    · rw [Category.assoc, hc₂p, ← Category.assoc, hzp, Category.id_comp, hz₂]
  rw [← hc₁, ← hc₂, Category.assoc, Category.assoc, hecurve]

include N

/-- Effective descent of both maps, their Cartesian square, and all three
specified sections along the constructed finite etale extension. -/
lemma descend_local : ∃ (b : Base R ⟶ Base Q.quotient.ring)
    (f : Curve R W ⟶ A.descent.family.curve), Classifies k L A B C Q R W G M b f := by
  let i := Spec.map (CommRingCat.ofHom N.comparison.inclusion.toRingHom)
  let p := N.comparison.sourceMap
  let ps := structureMap N.comparison.ring (W.map N.comparison.inclusion.toRingHom)
  letI : IsFinite i := N.comparison.finite
  letI : Etale i := N.comparison.etale
  letI : Surjective i := N.comparison.surjective
  letI : IsFinite p := MorphismProperty.of_isPullback N.comparison.sourceCartesian.flip inferInstance
  letI : Etale p := MorphismProperty.of_isPullback N.comparison.sourceCartesian.flip inferInstance
  letI : Surjective p := MorphismProperty.of_isPullback N.comparison.sourceCartesian.flip inferInstance
  have hi_over : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k N.comparison.ring)) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext N.comparison.inclusion.comp_algebraMap)
  have hbkernel : pullback.fst i i ≫ N.base = pullback.snd i i ≫ N.base := by
    apply affine_ext
    intro K _ a
    have ha : (a ≫ pullback.fst i i) ≫ i = (a ≫ pullback.snd i i) ≫ i := by
      simp only [Category.assoc, pullback.condition]
    simpa only [Category.assoc] using (affine_agreement hL heven hB hG N K _ _ ha).1
  obtain ⟨b, hb⟩ := descend_map i N.base hbkernel
  have hb_over : b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    apply (cancel_epi i).mp
    rw [← Category.assoc, hb, N.over_eq, hi_over]
  have hcp : N.comparison.comparison ≫ A.descent.family.projection =
      p ≫ structureMap R W ≫ b ≫ Q.inclusion := by
    rw [N.comparison.cartesian.w, ← N.factorization, ← hb]
    change ps ≫ (i ≫ b) ≫ Q.inclusion = _
    simp only [Category.assoc]
    rw [← N.comparison.sourceCartesian.w_assoc]
  have hfkernel : pullback.fst p p ≫ N.comparison.comparison =
      pullback.snd p p ≫ N.comparison.comparison := by
    apply affine_ext
    intro K _ z
    let z₁ := z ≫ pullback.fst p p
    let z₂ := z ≫ pullback.snd p p
    have hz : z₁ ≫ p = z₂ ≫ p := by
      simp only [z₁, z₂, Category.assoc, pullback.condition]
    have ha : (z₁ ≫ ps) ≫ i = (z₂ ≫ ps) ≫ i := by
      rw [Category.assoc, Category.assoc, ← N.comparison.sourceCartesian.w,
        ← Category.assoc, ← Category.assoc, hz]
      simpa only [Category.assoc] using
        congrArg (fun t => z₂ ≫ t) N.comparison.sourceCartesian.w
    simpa only [z₁, z₂, Category.assoc] using
      (affine_agreement hL heven hB hG N K _ _ ha).2 z₁ z₂ rfl rfl hz
  obtain ⟨f, hf⟩ := descend_map p N.comparison.comparison hfkernel
  have hfp : f ≫ A.descent.family.projection = structureMap R W ≫ b ≫ Q.inclusion := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hf, hcp]
  have hcart : IsPullback f (structureMap R W) A.descent.family.projection (b ≫ Q.inclusion) := by
    apply cartesian_descends i (structureMap R W) ps p N.comparison.sourceCartesian
      A.descent.family.projection (b ≫ Q.inclusion) f (by simpa only [Category.assoc] using hfp)
    simpa only [hf, ← Category.assoc, hb, N.factorization] using N.comparison.cartesian
  refine ⟨b, f, hb_over, hcart, ?_, ?_, ?_⟩
  · apply (cancel_epi i).mp
    rw [← Category.assoc, ← N.comparison.sourceOrigin, Category.assoc, hf,
      N.comparison.origin_eq, ← N.factorization, ← hb]
    simp only [Category.assoc]
  · apply (cancel_epi i).mp
    rw [← Category.assoc, ← N.comparison.x_lift, Category.assoc, hf,
      N.comparison.x_eq, ← N.factorization, ← hb]
    simp only [Category.assoc]
  · apply (cancel_epi i).mp
    rw [← Category.assoc, ← N.comparison.y_lift, Category.assoc, hf,
      N.comparison.y_eq, ← N.factorization, ← hb]
    simp only [Category.assoc]

end Local
end AffineClassification
open CategoryTheory AlgebraicGeometry ArithmeticThetaCompatibleLevelR0178

/-- One fixed compatible quotient classifies all affine marked Weierstrass families. -/
theorem arbitrary_affine_classification :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L), ∃ (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C), ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), ∃! b : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeDiscriminantR0171.Base Q.quotient.ring), ∃! f : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve R W) A.descent.family.curve, ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q R W G M b f := by
  intro k _ _ L hL heven A
  obtain ⟨B, hB⟩ := ArithmeticThetaCompatibleLevelR0178.NormalAffineClassifyingConstruction.canonical_marking k L A
  obtain ⟨C⟩ := compatible_level_subcover k L hL heven A B hB
  obtain ⟨Q⟩ := compatible_sign_quotient k L hL heven A B hB C
  refine ⟨B, hB, C, Q, ?_⟩
  intro R _ _ _ W _ G hG M
  obtain ⟨N⟩ := arbitrary_compatible_local_coverage k L hL heven A B hB C Q R W G hG M
  obtain ⟨b, f, h⟩ := AffineClassification.descend_local hL heven hB hG N
  refine ⟨b, ⟨f, h, ?_⟩, ?_⟩
  · intro f' hf'
    exact (arbitrary_classifying_uniqueness k L hL heven A B hB C Q R W G hG M
      b b f' f hf' h).2
  · intro b' hb'
    obtain ⟨f', hf', _⟩ := hb'
    exact (arbitrary_classifying_uniqueness k L hL heven A B hB C Q R W G hG M
      b' b f' f hf' h).1


#print axioms arbitrary_affine_classification
end ArithmeticThetaArbitraryAffineR0202
