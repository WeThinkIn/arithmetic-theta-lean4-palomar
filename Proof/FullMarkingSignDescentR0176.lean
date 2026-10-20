module

public import EllipticSignDescentR0176

@[expose] public section

/-! Both labeled torsion sections descend to every pointed Cartesian family descent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 EllipticSignDescent
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

lemma mul_congr {R : Type u} [CommRing R] {A T : Scheme.{u}}
    {f : A ⟶ Base R} (H : GoodReductionJacobian.RelativeGroupLaw R f)
    {t t' : T ⟶ Base R} (ht : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (H.mul t x y).val = (H.mul t' x' y').val := by
  subst t'
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  subst x'; subst y'; rfl

section CartesianLaw
variable {R S : Type u} [CommRing R] [CommRing S]
  {A V : Scheme.{u}} {f : A ⟶ Base R} {v : V ⟶ Base S}
  {c : V ⟶ A} {b : Base S ⟶ Base R} (h : IsPullback c v f b)

def down {T : Scheme.{u}} {t : T ⟶ Base S} (x : SchemeHomOver t v) :
    SchemeHomOver (t ≫ b) f :=
  ⟨x.val ≫ c, by rw [Category.assoc, h.w, ← Category.assoc, x.property]⟩

def up {T : Scheme.{u}} {t : T ⟶ Base S} (x : SchemeHomOver (t ≫ b) f) :
    SchemeHomOver t v := ⟨h.lift x.val t x.property, h.lift_snd _ _ _⟩

@[simp] lemma down_up {T : Scheme.{u}} {t : T ⟶ Base S}
    (x : SchemeHomOver (t ≫ b) f) : down h (up h x) = x :=
  Subtype.ext (h.lift_fst _ _ _)

@[simp] lemma up_down {T : Scheme.{u}} {t : T ⟶ Base S}
    (x : SchemeHomOver t v) : up h (down h x) = x := by
  apply Subtype.ext
  apply h.hom_ext
  · exact h.lift_fst _ _ _
  · exact (h.lift_snd _ _ _).trans x.property.symm

lemma down_natural {T U : Scheme.{u}} (t : T ⟶ Base S) (s : U ⟶ Base S)
    (a : U ⟶ T) (ha : a ≫ t = s) (x : SchemeHomOver t v) :
    down h (GoodReductionJacobian.schemeHomOverComp a ha x) =
      GoodReductionJacobian.schemeHomOverComp a (by rw [← Category.assoc, ha]) (down h x) :=
  Subtype.ext (Category.assoc _ _ _)

def cartesianLaw (H : GoodReductionJacobian.RelativeGroupLaw R f) :
    GoodReductionJacobian.RelativeGroupLaw S v where
  mul t x y := up h (H.mul _ (down h x) (down h y))
  one t := up h (H.one _)
  inv t x := up h (H.inv _ (down h x))
  mul_assoc t x y z := by simp only [down_up, H.mul_assoc]
  one_mul t x := by simp only [down_up, H.one_mul, up_down]
  mul_one t x := by simp only [down_up, H.mul_one, up_down]
  inv_mul_cancel t x := by simp only [down_up, H.inv_mul_cancel]
  mul_natural t s a ha x y := by
    apply_fun down h
    · rw [down_natural, down_up, down_up, H.mul_natural, down_natural, down_natural]
    · intro x y hxy
      simpa only [up_down] using congrArg (up h) hxy

@[simp] lemma cartesian_mul (H : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Base S) (x y : SchemeHomOver t v) :
    ((cartesianLaw h H).mul t x y).val ≫ c = (H.mul _ (down h x) (down h y)).val :=
  h.lift_fst _ _ _

@[simp] lemma cartesian_one (H : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Base S) :
    ((cartesianLaw h H).one t).val ≫ c = (H.one (t ≫ b)).val := h.lift_fst _ _ _
end CartesianLaw

section Sections
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {W : WeierstrassCurve R} {G : Law R W} {L : ℕ}
  {Z : LevelScheme R W G L} {σ : SignAction R W G Z}
  {Q : SignQuotient k (Z.projection ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map}
  (D : FamilyDescent k R W G Z σ Q)

lemma action_eq : D.action = deck G Z σ := by
  apply pullback.hom_ext
  · exact D.action_curve.trans (deck_curve G Z σ).symm
  · exact D.action_level.trans (deck_level G Z σ).symm

lemma section_descends (s : SchemeHomOver Z.projection (structureMap R W))
    (hs : σ.map ≫ s.val = (G.inv Z.projection s).val) :
    ∃ z : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection,
      coverSection R W Z s ≫ D.comparison = Q.q ≫ z.val := by
  have hi : σ.map ≫ coverSection R W Z s ≫ D.comparison =
      coverSection R W Z s ≫ D.comparison := by
    rw [← Category.assoc, ← marking_equivariant G Z σ s hs, Category.assoc,
      ← action_eq D, D.invariant]
  obtain ⟨z, hz, _⟩ := Q.universal _ _ hi
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  have hz' : z ≫ D.family.projection = 𝟙 _ := by
    apply (cancel_epi Q.q).mp
    rw [← Category.assoc, hz, Category.assoc, D.cartesian.w]
    simp
  exact ⟨⟨z, hz'⟩, hz.symm⟩
def imagePoint (s : SchemeHomOver Z.projection (structureMap R W)) :
    SchemeHomOver Q.q D.family.projection :=
  ⟨coverSection R W Z s ≫ D.comparison, by
    rw [Category.assoc, D.cartesian.w, coverSection_level_assoc]⟩

lemma image_one : imagePoint D (G.one Z.projection) = D.family.law.one Q.q := by
  apply Subtype.ext
  change coverSection R W Z (G.one Z.projection) ≫ D.comparison = _
  rw [D.origin_eq]
  exact congrArg Subtype.val (D.family.law.one_natural (𝟙 _) Q.q Q.q (Category.comp_id _))

lemma image_mul [W.IsElliptic] [IsAffine Z.space]
    (s t : SchemeHomOver Z.projection (structureMap R W)) :
    imagePoint D (G.mul Z.projection s t) =
      D.family.law.mul Q.q (imagePoint D s) (imagePoint D t) := by
  let A : Type u := Γ(Z.space, ⊤)
  let e : Z.space ≅ Base A := Z.space.isoSpec
  let v := coverToLevel R W Z ≫ e.hom
  let b := e.inv ≫ Z.projection
  let q := e.inv ≫ Q.q
  have h1 : IsPullback (coverToCurve R W Z) v (structureMap R W) b :=
    (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp [v]) (by simp) (by simp [b])
  have h2 : IsPullback D.comparison v D.family.projection q :=
    D.cartesian.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp [v]) (by simp) (by simp [q])
  let H := cartesianLaw h1 (toGRJ G)
  let J := cartesianLaw h2 D.family.law
  have hbundle : GoodReductionJacobian.AbelianSchemePropertyBundle A v :=
    (source_bundle G).of_isPullback h1
  have ho : H.one (𝟙 _) = J.one (𝟙 _) := by
    apply Subtype.ext
    apply h2.hom_ext
    · have hh : (H.one (𝟙 _)).val = e.inv ≫ coverSection R W Z (G.one Z.projection) := by
        apply h1.hom_ext
        · rw [Category.assoc, coverSection_curve]
          change ((cartesianLaw h1 (toGRJ G)).one (𝟙 _)).val ≫ _ = _
          rw [cartesian_one]
          change (G.one (𝟙 _ ≫ b)).val = _
          rw [show (G.one (𝟙 _ ≫ b)).val = (G.one b).val from
            congrArg (fun a => (G.one a).val) (Category.id_comp b)]
          simpa only [WeierstrassProjModel.schemeHomOverComp] using
            (congrArg Subtype.val (G.one_natural Z.projection b e.inv rfl)).symm
        · rw [(H.one (𝟙 _)).property]
          simp [v]
      rw [hh, Category.assoc, D.origin_eq]
      change _ = ((cartesianLaw h2 D.family.law).one (𝟙 _)).val ≫ _
      rw [cartesian_one]
      rw [show (D.family.law.one (𝟙 _ ≫ q)).val = (D.family.law.one q).val from
        congrArg (fun a => (D.family.law.one a).val) (Category.id_comp q)]
      simpa only [q, Category.assoc, GoodReductionJacobian.schemeHomOverComp] using
        congrArg Subtype.val (D.family.law.one_natural (𝟙 _) q q (Category.comp_id _))
    · rw [(H.one (𝟙 _)).property, (J.one (𝟙 _)).property]
  have he := GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
    hbundle H J ho
  let liftS (a : SchemeHomOver Z.projection (structureMap R W)) :
      SchemeHomOver e.hom v :=
    ⟨coverSection R W Z a, by simp [v]⟩
  have hs :
      (H.mul e.hom (liftS s) (liftS t)).val =
        coverSection R W Z (G.mul Z.projection s t) := by
    apply h1.hom_ext
    · change ((cartesianLaw h1 (toGRJ G)).mul _ _ _).val ≫ _ = _
      rw [cartesian_mul, coverSection_curve]
      dsimp only [down, liftS, toGRJ]
      simp only [coverSection_curve]
      have hb : e.hom ≫ b = Z.projection := by simp [b]
      exact mul_congr (toGRJ G) hb _ _ s t rfl rfl
    · rw [(H.mul _ _ _).property]
      simp [v]
  have hm := congrArg (fun K : GoodReductionJacobian.RelativeGroupLaw A v =>
    (K.mul e.hom (liftS s) (liftS t)).val ≫ D.comparison) he
  rw [hs] at hm
  change _ = ((cartesianLaw h2 D.family.law).mul _ _ _).val ≫ _ at hm
  rw [cartesian_mul] at hm
  apply Subtype.ext
  dsimp only [down, liftS] at hm
  have hq : e.hom ≫ q = Q.q := by simp [q]
  exact hm.trans (mul_congr D.family.law hq _ _ (imagePoint D s) (imagePoint D t) rfl rfl)

lemma image_nsmul [W.IsElliptic] [IsAffine Z.space]
    (s : SchemeHomOver Z.projection (structureMap R W)) (n : ℕ) :
    imagePoint D (G.nsmul Z.projection n s) =
      D.family.law.nsmul Q.q n (imagePoint D s) := by
  induction n with
  | zero => exact image_one D
  | succ n ih =>
    rw [G.nsmul_succ, D.family.law.nsmul_succ, image_mul, ih]
lemma section_cartesian (s : SchemeHomOver Z.projection (structureMap R W))
    (z : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection)
    (hz : coverSection R W Z s ≫ D.comparison = Q.q ≫ z.val) :
    IsPullback (coverSection R W Z s) Q.q D.comparison z.val := by
  have hout : IsPullback (coverSection R W Z s ≫ coverToLevel R W Z)
      Q.q Q.q (z.val ≫ D.family.projection) := by
    rw [coverSection_level, z.property]
    exact IsPullback.of_id_fst
  exact hout.of_right hz D.cartesian.flip

lemma preimage_section (s : SchemeHomOver Z.projection (structureMap R W))
    (z : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection)
    (hz : coverSection R W Z s ≫ D.comparison = Q.q ≫ z.val) :
    D.comparison ⁻¹' Set.range z.val = Set.range (coverSection R W Z s) := by
  let h := section_cartesian D s z hz
  rw [← Scheme.Pullback.range_fst]
  rw [← h.isoPullback_hom_fst]
  change Set.range (pullback.fst D.comparison z.val) =
    Set.range ((pullback.fst D.comparison z.val) ∘ h.isoPullback.hom)
  rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

lemma disjoint_descends (s t : SchemeHomOver Z.projection (structureMap R W))
    (x y : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection)
    (hx : coverSection R W Z s ≫ D.comparison = Q.q ≫ x.val)
    (hy : coverSection R W Z t ≫ D.comparison = Q.q ≫ y.val)
    (hdis : Disjoint (Set.range s.val) (Set.range t.val)) :
    Disjoint (Set.range x.val) (Set.range y.val) := by
  letI := Q.surjective
  letI : Surjective D.comparison := MorphismProperty.of_isPullback D.cartesian.flip inferInstance
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  obtain ⟨a, rfl⟩ := D.comparison.surjective z
  have has : a ∈ Set.range (coverSection R W Z s) := by
    rw [← preimage_section D s x hx]; exact hxz
  have hat : a ∈ Set.range (coverSection R W Z t) := by
    rw [← preimage_section D t y hy]; exact hyz
  obtain ⟨b, hb⟩ := has
  obtain ⟨c, hc⟩ := hat
  have hds := Set.disjoint_left.mp hdis
  apply hds (a := coverToCurve R W Z a)
  · refine ⟨b, ?_⟩
    rw [← hb, ← Scheme.Hom.comp_apply, coverSection_curve]
  · refine ⟨c, ?_⟩
    rw [← hc, ← Scheme.Hom.comp_apply, coverSection_curve]

lemma section_nsmul {S : Type u} [CommRing S] {E : Scheme.{u}} {f : E ⟶ Base S}
    (H : GoodReductionJacobian.RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Base S) (z : SchemeHomOver t f) (n : ℕ) :
    (H.nsmul t n z).val = z.val ≫ H.schemeNsmul n := by
  have hh := congrArg Subtype.val (H.nsmul_natural f t z.val z.property n
    GoodReductionJacobian.RelativeGroupLaw.idPoint)
  simpa only [GoodReductionJacobian.schemeHomOverComp,
    GoodReductionJacobian.RelativeGroupLaw.idPoint, Category.comp_id,
    GoodReductionJacobian.RelativeGroupLaw.schemeNsmul] using hh.symm

lemma torsion_descends [W.IsElliptic] [IsAffine Z.space]
    (s : SchemeHomOver Z.projection (structureMap R W))
    (z : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection)
    (hz : coverSection R W Z s ≫ D.comparison = Q.q ≫ z.val)
    (hn : G.nsmul Z.projection L s = G.one Z.projection) :
    z.val ≫ D.family.law.schemeNsmul L = (D.family.law.one (𝟙 _)).val := by
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  apply (cancel_epi Q.q).mp
  have hp : imagePoint D s = GoodReductionJacobian.schemeHomOverComp Q.q
      (Category.comp_id Q.q) z := Subtype.ext hz
  have hh := congrArg Subtype.val (image_nsmul D s L)
  rw [hn, image_one, hp, ← D.family.law.nsmul_natural] at hh
  have ho := congrArg Subtype.val
    (D.family.law.one_natural (𝟙 _) Q.q Q.q (Category.comp_id _))
  dsimp only [GoodReductionJacobian.schemeHomOverComp] at hh ho
  rw [← ho] at hh
  rw [← section_nsmul]
  exact hh.symm

lemma combination_descends [W.IsElliptic] [IsAffine Z.space]
    (x y : SchemeHomOver (𝟙 (Base Q.ring)) D.family.projection)
    (hx : coverSection R W Z Z.level.x ≫ D.comparison = Q.q ≫ x.val)
    (hy : coverSection R W Z Z.level.y ≫ D.comparison = Q.q ≫ y.val)
    (i j : ℕ) :
    coverSection R W Z (G.mul Z.projection (G.nsmul Z.projection i Z.level.x)
      (G.nsmul Z.projection j Z.level.y)) ≫ D.comparison =
    Q.q ≫ (D.family.law.mul (𝟙 _) (D.family.law.nsmul (𝟙 _) i x)
      (D.family.law.nsmul (𝟙 _) j y)).val := by
  have hp : imagePoint D Z.level.x = GoodReductionJacobian.schemeHomOverComp Q.q
      (Category.comp_id Q.q) x := Subtype.ext hx
  have hq : imagePoint D Z.level.y = GoodReductionJacobian.schemeHomOverComp Q.q
      (Category.comp_id Q.q) y := Subtype.ext hy
  have hh := image_mul D (G.nsmul Z.projection i Z.level.x) (G.nsmul Z.projection j Z.level.y)
  rw [image_nsmul, image_nsmul, hp, hq, ← D.family.law.nsmul_natural,
    ← D.family.law.nsmul_natural, ← D.family.law.mul_natural] at hh
  exact congrArg Subtype.val hh

end Sections
end ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent

namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 FullMarkingSignDescent

/-- Both labels descend to the supplied elliptic family, with full torsion marking. -/
theorem full_marking_sign_descent :
∀ (k : Type u) [Field k] [CharZero k] (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L) (Z : ArithmeticThetaFullLevelCoverR0175.LevelScheme R W G L) (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) (σ : ArithmeticThetaLegendreAtlasR0176.SignAction R W G Z) (Q : ArithmeticThetaLegendreAtlasR0176.SignQuotient k (CategoryTheory.CategoryStruct.comp (Z.projection) (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k R)))) σ.map) (D : ArithmeticThetaLegendreAtlasR0176.FamilyDescent k R W G Z σ Q), ∃ M : ArithmeticThetaLegendreAtlasR0176.FamilyLevel Q.ring D.family L, CategoryTheory.CategoryStruct.comp (ArithmeticThetaLegendreAtlasR0176.coverSection R W Z Z.level.x) (D.comparison) = CategoryTheory.CategoryStruct.comp (Q.q) (M.x.val) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaLegendreAtlasR0176.coverSection R W Z Z.level.y) (D.comparison) = CategoryTheory.CategoryStruct.comp (Q.q) (M.y.val) := by
  intro k _ _ R _ _ _ _ _ _ W _ G hG L hL Z hZ σ Q D
  obtain ⟨hf, _, _, _⟩ := full_level_cover_geometry R W G hG L (by omega) Z hZ
  letI := hf
  haveI : IsAffine Z.space := isAffine_of_isAffineHom Z.projection
  obtain ⟨x, hx⟩ := section_descends D Z.level.x σ.x_eq
  obtain ⟨y, hy⟩ := section_descends D Z.level.y σ.y_eq
  refine ⟨{
    x := x
    y := y
    killed_x := torsion_descends D Z.level.x x hx Z.level.killed_x
    killed_y := torsion_descends D Z.level.y y hy Z.level.killed_y
    avoids := ?_ }, hx, hy⟩
  intro i j hij
  apply disjoint_descends D
    (G.mul Z.projection (G.nsmul Z.projection i.val Z.level.x)
      (G.nsmul Z.projection j.val Z.level.y)) (G.one Z.projection)
    _ _ (combination_descends D x y hx hy i.val j.val) D.origin_eq
  apply (Z.level.avoids i j hij).mono_right
  rintro _ ⟨z, rfl⟩
  rw [hG.1]
  exact ⟨Z.projection z, rfl⟩

#print axioms full_marking_sign_descent
end ArithmeticThetaLegendreAtlasR0176
