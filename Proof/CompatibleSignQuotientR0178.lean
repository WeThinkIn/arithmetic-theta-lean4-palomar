module

public import CompatibleLevelDefinitionsR0178
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

/-! Restriction of the actual sign quotient to the compatible marking locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaCompatibleLevelR0178
namespace CompatibleSignQuotientR0178
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreAtlasR0176.FullLevelFreeSignR0176
open ArithmeticThetaLegendreAtlasR0176.EllipticSignDescent
open ArithmeticThetaRelativeKatoNaturalityR0170
open WeierstrassProjModel

lemma inverse_two {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (hx : G.nsmul t 2 x = G.one t) :
    G.inv t x = x := by
  letI := G.pointGroup t
  have h : x * x = 1 := by
    rw [← pow_two]
    exact (RelativeKatoFiberSpecialization.nsmul_pow G t 2 x).symm.trans hx
  exact (eq_inv_of_mul_eq_one_left h).symm

lemma sign_reduction {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {X T : Scheme.{u}} (p : X ⟶ Base R) (s : X ⟶ X)
    (hs : s ≫ p = p) (x : SchemeHomOver p (structureMap R W))
    (hx : s ≫ x.val = (G.inv p x).val) (n : ℕ) (a : T ⟶ X)
    (b : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hb : G.nsmul (𝟙 _) 2 b = G.one (𝟙 _))
    (h : a ≫ (G.nsmul p n x).val = (a ≫ p) ≫ b.val) :
    (a ≫ s) ≫ (G.nsmul p n x).val = ((a ≫ s) ≫ p) ≫ b.val := by
  have he : schemeHomOverComp s hs x = G.inv p x := Subtype.ext hx
  have hn : s ≫ (G.nsmul p n x).val = (G.inv p (G.nsmul p n x)).val := by
    have hh := G.nsmul_natural p p s hs n x
    rw [he] at hh
    have hi : G.nsmul p n (G.inv p x) = G.inv p (G.nsmul p n x) := by
      letI := G.pointGroup p
      simp only [RelativeKatoFiberSpecialization.nsmul_pow]
      exact inv_pow x n
    exact (congrArg Subtype.val hh).trans (congrArg Subtype.val hi)
  have hb' : G.inv (a ≫ p)
      (schemeHomOverComp (a ≫ p) (Category.comp_id _) b) =
      schemeHomOverComp (a ≫ p) (Category.comp_id _) b := by
    rw [← inverse_natural, inverse_two G _ b hb]
  have hh : schemeHomOverComp a rfl (G.nsmul p n x) =
      schemeHomOverComp (a ≫ p) (Category.comp_id _) b := Subtype.ext h
  rw [Category.assoc, hn]
  have hi := congrArg Subtype.val (inverse_natural G p (a ≫ p) a rfl (G.nsmul p n x))
  rw [hh, hb'] at hi
  simpa only [Category.assoc, hs, WeierstrassProjModel.schemeHomOverComp] using hi

variable (k : Type u) [Field k] [CharZero k] (L : ℕ) (A : LegendreAtlas k L)
  (B : TwoMarking k L A) (C : CompatibleCover k L A B)

lemma compatible_sign : CompatibleAt k L A B (C.inclusion ≫ A.sign.map) := by
  exact ⟨sign_reduction A.law _ _ A.sign.over_eq _ A.sign.x_eq _ _ _
      B.killed_x C.compatible.1,
    sign_reduction A.law _ _ A.sign.over_eq _ A.sign.y_eq _ _ _
      B.killed_y C.compatible.2⟩

lemma restricted_sign : ∃ s : C.space ⟶ C.space,
    s ≫ C.inclusion = C.inclusion ≫ A.sign.map ∧ s ≫ s = 𝟙 _ ∧
    IsEmpty (equalizer s (𝟙 C.space) : Scheme.{u}) := by
  letI := C.openImmersion
  obtain ⟨s, hs, _⟩ := (C.represents _ _).mp (compatible_sign k L A B C)
  refine ⟨s, hs, ?_, ?_⟩
  · apply (cancel_mono C.inclusion).mp
    rw [Category.assoc, hs, ← Category.assoc, hs, Category.assoc, A.sign.square]
    simp
  · let e := equalizer.ι s (𝟙 C.space)
    have he : (e ≫ C.inclusion) ≫ A.sign.map = (e ≫ C.inclusion) ≫ 𝟙 _ := by
      rw [Category.assoc, ← hs, ← Category.assoc]
      have hh : e ≫ s = e := by simpa [e] using equalizer.condition s (𝟙 C.space)
      rw [hh, Category.comp_id]
    let f := equalizer.lift (e ≫ C.inclusion) he
    letI := A.sign.free
    exact ⟨fun x => isEmptyElim (f x)⟩

/-- Equality of scheme maps can be checked on neighborhoods of every point. -/
lemma hom_ext_locally {X Y : Scheme.{u}} (a b : X ⟶ Y)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ a = U.ι ≫ b) : a = b := by
  choose U hx he using h
  let cover := X.openCoverOfIsOpenCover U (by
    apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  exact cover.hom_ext _ _ he


section Restriction
variable {k : Type u} [Field k] {X V : Scheme.{u}} {p : X ⟶ Base k}
  {σ : X ⟶ X} (Q : SignQuotient k p σ) (i : V ⟶ X)
  [IsOpenImmersion i] [IsClosedImmersion i]
  (s : V ⟶ V) (hs : s ≫ i = i ≫ σ)

include hs in
/-- The image of the invariant clopen subscheme is saturated for the quotient. -/
lemma saturated : Q.q ⁻¹' (Set.range (i ≫ Q.q)) = Set.range i := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := i ≫ Q.q) (g := Q.q) v x hv
    have hcov := (codisjoint_iff.mp (split_branches_cover Q i))
    have hm : z ∈ Set.range (firstBranch Q i) ∪ Set.range (secondBranch Q i) := by
      change z ∈ Set.range (firstBranch Q i) ⊔ Set.range (secondBranch Q i)
      rw [hcov]; trivial
    obtain ⟨w, hw⟩ | ⟨w, hw⟩ := hm
    · refine ⟨w, ?_⟩
      have h := congrArg (fun a => pullback.snd (i ≫ Q.q) Q.q a) hw
      simpa only [← Scheme.Hom.comp_apply, firstBranch_snd, hz] using h
    · refine ⟨s w, ?_⟩
      have h := congrArg (fun a => pullback.snd (i ≫ Q.q) Q.q a) hw
      simpa only [← Scheme.Hom.comp_apply, secondBranch_snd, ← hs, hz] using h
  · rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩

include hs in
lemma restriction_model : ∃ (U : (Base Q.ring).Opens) (r : V ⟶ U.toScheme),
    IsClosedImmersion U.ι ∧ IsPullback i r Q.q U.ι ∧
    s ≫ r = r ∧ Surjective r ∧
    (∀ (T : Scheme.{u}) (a : V ⟶ T), s ≫ a = a →
      ∃! b : U.toScheme ⟶ T, r ≫ b = a) := by
  letI := Q.finite
  letI := Q.etale
  let U : (Base Q.ring).Opens := ⟨Set.range (i ≫ Q.q), by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Q.q.isOpenMap _ i.isOpenEmbedding.isOpen_range⟩
  have hclosed : IsClosed (U : Set (Base Q.ring)) := by
    change IsClosed (Set.range (i ≫ Q.q))
    exact (i ≫ Q.q).isClosedMap.isClosed_range
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  let r : V ⟶ U.toScheme := IsOpenImmersion.lift U.ι (i ≫ Q.q)
    (by rw [Scheme.Opens.range_ι]; exact Set.Subset.rfl)
  have hr : r ≫ U.ι = i ≫ Q.q := IsOpenImmersion.lift_fac _ _ _
  have hp : IsPullback i r Q.q U.ι := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback r i U.ι Q.q hr.symm
    apply TopologicalSpace.Opens.ext
    simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
    exact saturated Q i s hs
  letI : IsFinite r := MorphismProperty.of_isPullback hp Q.finite
  letI : Etale r := MorphismProperty.of_isPullback hp Q.etale
  have hsurj : Surjective r := by
    constructor
    intro y
    obtain ⟨v, hv⟩ := y.property
    refine ⟨v, U.ι.injective ?_⟩
    change (r ≫ U.ι) v = y.val
    rw [hr]
    exact hv
  letI := hsurj
  have hinv : s ≫ r = r := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, hr, ← Category.assoc, hs, Category.assoc, Q.invariant]
  refine ⟨U, r, inferInstance, hp, hinv, hsurj, ?_⟩
  intro T a ha
  have hcoeq : pullback.fst r r ≫ a = pullback.snd r r ≫ a := by
    apply hom_ext_locally
    intro z
    have he : (pullback.fst r r ≫ i) ≫ Q.q = (pullback.snd r r ≫ i) ≫ Q.q := by
      calc
        _ = (pullback.fst r r ≫ r) ≫ U.ι := by simp only [Category.assoc, hr]
        _ = (pullback.snd r r ≫ r) ≫ U.ι := by rw [pullback.condition]
        _ = _ := by simp only [Category.assoc, hr]
    obtain ⟨W, hz, hw | hw⟩ := quotient_locally_orbit Q
      (pullback.fst r r ≫ i) (pullback.snd r r ≫ i) he z
    · have hh : W.ι ≫ pullback.snd r r = W.ι ≫ pullback.fst r r := by
        apply (cancel_mono i).mp
        simpa only [Category.assoc] using hw
      exact ⟨W, hz, by simp only [← Category.assoc, hh]⟩
    · have hh : W.ι ≫ pullback.snd r r = (W.ι ≫ pullback.fst r r) ≫ s := by
        apply (cancel_mono i).mp
        simpa only [Category.assoc, hs] using hw
      exact ⟨W, hz, by simpa only [Category.assoc, ha] using (congrArg (fun b => b ≫ a) hh).symm⟩
  obtain ⟨b, hb⟩ := IsRegularEpi.exists_of_isKernelPair r
    (IsKernelPair.of_hasPullback r) a hcoeq
  exact ⟨b, hb, fun c hc => (cancel_epi r).mp (hc.trans hb.symm)⟩

include hs in
/-- Two genuine categorical quotients are uniquely isomorphic; the image model
therefore identifies the affine sign quotient with an actual clopen subscheme. -/
lemma quotient_inclusion {pv : V ⟶ Base k} (Qc : SignQuotient k pv s) :
    ∃ j : Base Qc.ring ⟶ Base Q.ring,
      IsPullback i Qc.q Q.q j ∧ IsOpenImmersion j ∧ IsClosedImmersion j := by
  obtain ⟨U, r, hclosed, hp, hinv, hsurj, huniv⟩ := restriction_model Q i s hs
  letI := Qc.etale
  letI := Qc.finite
  letI := Qc.surjective
  letI := hsurj
  letI : Etale r := MorphismProperty.of_isPullback hp Q.etale
  letI := hclosed
  obtain ⟨f, hf, _⟩ := Qc.universal U.toScheme r hinv
  obtain ⟨g, hg, _⟩ := huniv (Base Qc.ring) Qc.q Qc.invariant
  let e : Base Qc.ring ≅ U.toScheme :=
    ⟨f, g, (cancel_epi Qc.q).mp (by simp [← Category.assoc, hf, hg]),
      (cancel_epi r).mp (by simp [← Category.assoc, hg, hf])⟩
  letI : IsIso e.hom := e.isIso_hom
  refine ⟨e.hom ≫ U.ι, ?_, inferInstance, inferInstance⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    (by simp) (by simpa [e] using hg) (by simp) (by simp)

end Restriction

end CompatibleSignQuotientR0178

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open CompatibleSignQuotientR0178

/-- The actual compatible locus has its free degree-two affine sign quotient,
Cartesian over an open-and-closed subscheme of the accepted quotient. -/
theorem compatible_sign_quotient :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
      (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A),
      ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B →
      ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B),
      Nonempty (ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) := by
  intro k _ _ L hL heven A B hB C
  letI := C.openImmersion
  letI := C.closedImmersion
  letI := A.quotient.finite
  letI := A.quotient.etale
  letI := A.quotient.smooth
  letI : IsAffine C.space := isAffine_of_isAffineHom (C.inclusion ≫ A.quotient.q)
  obtain ⟨s, hs, hsq, hfree⟩ := restricted_sign k L A B C
  let p := C.inclusion ≫ A.level.projection ≫ legendreBaseMap k
  have hp : (C.inclusion ≫ A.quotient.q) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) = p := by
    rw [Category.assoc, A.quotient.over_eq]
  letI : SmoothOfRelativeDimension 1 p := hp ▸
    smoothOfRelativeDimension_comp 0 1 (C.inclusion ≫ A.quotient.q)
      (Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)))
  have hover : s ≫ p = p := by
    dsimp only [p]
    rw [← Category.assoc, hs, Category.assoc, ← Category.assoc A.sign.map,
      A.sign.over_eq]
  obtain ⟨Qc⟩ := affine_free_sign_quotient k C.space p s hover hsq hfree
  obtain ⟨j, hj, hopen, hclosed⟩ := quotient_inclusion A.quotient C.inclusion s hs Qc
  letI := Qc.finite
  letI := Qc.etale
  letI := Qc.surjective
  refine ⟨{
    sign := s
    sign_eq := hs
    sign_square := hsq
    sign_free := hfree
    quotient := Qc
    inclusion := j
    cartesian := hj
    openImmersion := hopen
    closedImmersion := hclosed
    over_eq := ?_ }⟩
  apply (cancel_epi Qc.q).mp
  rw [← Category.assoc, ← hj.w, Category.assoc, A.quotient.over_eq, Qc.over_eq]

#print axioms compatible_sign_quotient
end ArithmeticThetaCompatibleLevelR0178
