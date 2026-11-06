module

public import LevelCompactificationDefinitionsR0179
public import Theorems.Thm_AlgebraicGeometry_IsFinite_of_comp_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
public import NormalAffineClassifyingConstructionR0178

@[expose] public section

-- Preserve the original elaborated instance path after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

/-! Supporting constructions for forgetting full even level on the specified
compatible quotient. All helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaLevelCompactificationR0179
namespace LevelForgettingMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaRelativeKatoNaturalityR0170

/-- The accepted descent construction applies to every specified compatible
presentation, rather than only the existentially chosen presentation in its
packaged final theorem. -/
lemma classifies_exists_unique (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : LevelData k L)
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (M : FullLevel R W G L (𝟙 (Base R))) :
    ∃! b : Base R ⟶ OpenBase k L D,
      ∃! a : Curve R W ⟶ D.atlas.descent.family.curve,
        Classifies k L D.atlas D.two D.cover D.quotient R W G M b a := by
  obtain ⟨N⟩ := compatible_local_coverage k L hL heven D.atlas D.two D.canonical
    D.cover D.quotient R W G hG M
  obtain ⟨b, a, h⟩ := NormalAffineClassifyingConstruction.descend_local
    hL heven D.canonical hG N
  refine ⟨b, ⟨a, h, ?_⟩, ?_⟩
  · intro a' ha'
    exact (compatible_classifying_uniqueness k L hL heven D.atlas D.two D.canonical
      D.cover D.quotient R W G hG M b b a' a ha' h).2
  · intro b' hb'
    obtain ⟨a', ha', _⟩ := hb'
    exact (compatible_classifying_uniqueness k L hL heven D.atlas D.two D.canonical
      D.cover D.quotient R W G hG M b' b a' a ha' h).1

/-- The two reduced labels have a unique classification in the specified
target presentation. This reuses the accepted divisor reduction. -/
lemma reduced_classification (k : Type u) [Field k] [CharZero k]
    (L d : ℕ) (hL : 0 < L) (hd : 3 ≤ d) (hdeven : Even d) (hdL : d ∣ L)
    (E : LevelData k d)
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (M : FullLevel R W G L (𝟙 (Base R))) :
    ∃ N : FullLevel R W G d (𝟙 (Base R)),
      N.x = G.nsmul (𝟙 _) (L / d) M.x ∧
      N.y = G.nsmul (𝟙 _) (L / d) M.y ∧
      ∃! b : Base R ⟶ OpenBase k d E,
        ∃! a : Curve R W ⟶ E.atlas.descent.family.curve,
          Classifies k d E.atlas E.two E.cover E.quotient R W G N b a := by
  obtain ⟨N, hx, hy⟩ := full_level_divisor_reduction R W G hG L d hL (by omega) hdL M
  exact ⟨N, hx, hy, classifies_exists_unique k d hd hdeven E R W G hG N⟩

/-- Iteration of the given law on arbitrary scheme-valued points. -/
lemma nsmul_mul {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {T : Scheme.{u}} (t : T ⟶ Base R)
    (m n : ℕ) (x : SchemeHomOver t (structureMap R W)) :
    G.nsmul t n (G.nsmul t m x) = G.nsmul t (m * n) x := by
  letI := G.pointGroup t
  have hp (a : ℕ) (z : SchemeHomOver t (structureMap R W)) :
      G.nsmul t a z = z ^ a := by
    induction a with
    | zero => rfl
    | succ a ih => rw [G.nsmul_succ, ih]; rfl
  rw [hp, hp, hp, pow_mul]

/-- Extension of divisor reduction to the universal marking on an arbitrary
test scheme, including nonreduced and disconnected test schemes. -/
def reduceMarking {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    {G : Law R W} {T : Scheme.{u}} {t : T ⟶ Base R}
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (M : FullLevel R W G L t) : FullLevel R W G d t where
  x := G.nsmul t (L / d) M.x
  y := G.nsmul t (L / d) M.y
  killed_x := by rw [nsmul_mul, Nat.div_mul_cancel hdL, M.killed_x]
  killed_y := by rw [nsmul_mul, Nat.div_mul_cancel hdL, M.killed_y]
  avoids := by
    intro i j hij
    have hq : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
    have hlt (a : Fin d) : L / d * a.val < L := by
      have h := Nat.mul_lt_mul_of_pos_left a.isLt hq
      rwa [Nat.div_mul_cancel hdL] at h
    rw [nsmul_mul, nsmul_mul]
    apply M.avoids ⟨L / d * i.val, hlt i⟩ ⟨L / d * j.val, hlt j⟩
    rcases hij with hi | hj
    · exact Or.inl (Nat.mul_ne_zero (Nat.ne_of_gt hq) hi)
    · exact Or.inr (Nat.mul_ne_zero (Nat.ne_of_gt hq) hj)

/-- Equality of full markings is equality of their two actual sections. -/
lemma marking_ext {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    {G : Law R W} {T : Scheme.{u}} {t : T ⟶ Base R} {L : ℕ}
    {M N : FullLevel R W G L t} (hx : M.x = N.x) (hy : M.y = N.y) : M = N := by
  cases M
  cases N
  cases hx
  cases hy
  rfl

/-- Reducing a universal marking commutes with arbitrary test-scheme pullback. -/
lemma reduceMarking_restrict {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    {G : Law R W} {T U : Scheme.{u}} {t : T ⟶ Base R} {s : U ⟶ Base R}
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (M : FullLevel R W G L t) (q : U ⟶ T) (hq : q ≫ t = s) :
    reduceMarking hL hd hdL (BaseChange.restrict M q hq) =
      BaseChange.restrict (reduceMarking hL hd hdL M) q hq := by
  apply marking_ext
  · exact (G.nsmul_natural t s q hq (L / d) M.x).symm
  · exact (G.nsmul_natural t s q hq (L / d) M.y).symm

open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

/-- The chosen atlas presentations carry the same law on the same Legendre
curve: the origin determines the group law. -/
lemma atlas_law_eq (k : Type u) [Field k] [CharZero k] {L d : ℕ}
    (A : LegendreAtlas k L) (B : LegendreAtlas k d) : A.law = B.law := by
  letI := (legendre_family_geometry k).1
  letI := (legendre_family_geometry k).2.2.2.1
  have he : toGRJ A.law = toGRJ B.law :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
      (BaseChange.geometry (LegendreRing k) (legendre k) A.law) _ _
      (Subtype.ext ((A.originLaw.1 _).trans (B.originLaw.1 _).symm))
  exact congrArg (fun H : GoodReductionJacobian.RelativeGroupLaw (LegendreRing k)
      (structureMap (LegendreRing k) (legendre k)) =>
    (⟨H.mul, H.one, H.inv, H.mul_assoc, H.one_mul, H.mul_one,
      H.inv_mul_cancel, H.mul_natural⟩ : Law (LegendreRing k) (legendre k))) he

/-- Transport along equality of actual group laws retains both scheme maps. -/
def changeLaw {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    {G H : Law R W} (h : G = H) {T : Scheme.{u}} {t : T ⟶ Base R}
    {L : ℕ} (M : FullLevel R W G L t) : FullLevel R W H L t where
  x := M.x
  y := M.y
  killed_x := by rw [← h]; exact M.killed_x
  killed_y := by rw [← h]; exact M.killed_y
  avoids := by rw [← h]; exact M.avoids

/-- The canonical ordered two-marking is independent of the atlas presentation. -/
lemma canonical_labels_eq (k : Type u) [Field k] [CharZero k] {L d : ℕ}
    (D : LevelData k L) (E : LevelData k d) :
    D.two.x.val = E.two.x.val ∧ D.two.y.val = E.two.y.val := by
  exact ⟨TwoTorsionSplitCubicR0177.coordinates_ext D.canonical.1 E.canonical.1,
    TwoTorsionSplitCubicR0177.coordinates_ext D.canonical.2 E.canonical.2⟩

/-- The half multiple after reduction is the original half multiple. This
includes equal levels and arbitrary even composite divisors. -/
lemma reduce_half {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {T : Scheme.{u}} (t : T ⟶ Base R)
    {L d : ℕ} (hdL : d ∣ L) (heven : Even d)
    (x : SchemeHomOver t (structureMap R W)) :
    G.nsmul t (d / 2) (G.nsmul t (L / d) x) = G.nsmul t (L / 2) x := by
  rw [nsmul_mul, ← Nat.mul_div_assoc _ heven.two_dvd, Nat.div_mul_cancel hdL]

/-- Forget the marking on the actual compatible covers, before taking sign
quotients. No morphism or descent datum is supplied as a hypothesis. -/
lemma cover_reduction_exists (k : Type u) [Field k] [CharZero k]
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d) :
    ∃ f : D.cover.space ⟶ E.cover.space,
      f ≫ E.cover.inclusion ≫ E.atlas.level.projection =
        D.cover.inclusion ≫ D.atlas.level.projection ∧
      f ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
        D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val ∧
      f ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
        D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val := by
  let t := D.cover.inclusion ≫ D.atlas.level.projection
  let M := BaseChange.restrict D.atlas.level.level D.cover.inclusion (rfl : _ = t)
  have hlaw := atlas_law_eq k D.atlas E.atlas
  let N := changeLaw hlaw (reduceMarking hL hd hdL M)
  obtain ⟨a, ha, _⟩ := E.atlas.represents D.cover.space t N
  have half (s : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (z : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (hz : a.val ≫ s.val =
        (D.atlas.law.nsmul t (L / d)
          (WeierstrassProjModel.schemeHomOverComp D.cover.inclusion rfl z)).val) :
      a.val ≫ (E.atlas.law.nsmul E.atlas.level.projection (d / 2) s).val =
        D.cover.inclusion ≫ (D.atlas.law.nsmul D.atlas.level.projection (L / 2) z).val := by
    have hs : WeierstrassProjModel.schemeHomOverComp a.val a.property s =
        D.atlas.law.nsmul t (L / d)
          (WeierstrassProjModel.schemeHomOverComp D.cover.inclusion rfl z) := Subtype.ext hz
    have hn := congrArg Subtype.val (E.atlas.law.nsmul_natural
      E.atlas.level.projection t a.val a.property (d / 2) s)
    have hN (n : ℕ) (x : SchemeHomOver t (structureMap (LegendreRing k) (legendre k))) :
        E.atlas.law.nsmul t n x = D.atlas.law.nsmul t n x :=
      congrArg (fun G : Law (LegendreRing k) (legendre k) => G.nsmul t n x) hlaw.symm
    rw [hs, hN, reduce_half _ _ hdL hdeven] at hn
    exact hn.trans (congrArg Subtype.val (D.atlas.law.nsmul_natural
      D.atlas.level.projection t D.cover.inclusion rfl (L / 2) z)).symm
  have hc : CompatibleAt k d E.atlas E.two a.val := by
    constructor
    · rw [half _ _ ha.1, D.cover.compatible.1, (canonical_labels_eq k D E).1,
        a.property]
    · rw [half _ _ ha.2, D.cover.compatible.2, (canonical_labels_eq k D E).2,
        a.property]
  obtain ⟨f, hf, _⟩ := (E.cover.represents D.cover.space a.val).mp hc
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hf]; exact a.property
  · rw [← Category.assoc, hf, ha.1]
    exact (congrArg Subtype.val (D.atlas.law.nsmul_natural
      D.atlas.level.projection t D.cover.inclusion rfl (L / d) D.atlas.level.level.x)).symm
  · rw [← Category.assoc, hf, ha.2]
    exact (congrArg Subtype.val (D.atlas.law.nsmul_natural
      D.atlas.level.projection t D.cover.inclusion rfl (L / d) D.atlas.level.level.y)).symm

/-- Maps into a compatible cover are determined by the base map and the two
universal labels. -/
lemma cover_hom_ext (k : Type u) [Field k] [CharZero k] {d : ℕ}
    (E : LevelData k d) {T : Scheme.{u}} (f g : T ⟶ E.cover.space)
    (hp : f ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      g ≫ E.cover.inclusion ≫ E.atlas.level.projection)
    (hx : f ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val)
    (hy : f ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val) : f = g := by
  letI := E.cover.openImmersion
  apply (cancel_mono E.cover.inclusion).mp
  exact BaseChange.represents_ext E.atlas.represents _ _
    (by simpa only [Category.assoc] using hp) rfl
    (by simpa only [Category.assoc] using hx)
    (by simpa only [Category.assoc] using hy)

lemma sign_nsmul {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G : Law R W) {T : Scheme.{u}} (t : T ⟶ Base R) (s : T ⟶ T)
    (hs : s ≫ t = t) (x : SchemeHomOver t (structureMap R W))
    (hx : s ≫ x.val = (G.inv t x).val) (n : ℕ) :
    s ≫ (G.nsmul t n x).val = (G.inv t (G.nsmul t n x)).val := by
  have he : WeierstrassProjModel.schemeHomOverComp s hs x = G.inv t x := Subtype.ext hx
  have hn := G.nsmul_natural t t s hs n x
  rw [he] at hn
  have hi : G.nsmul t n (G.inv t x) = G.inv t (G.nsmul t n x) := by
    letI := G.pointGroup t
    simp only [RelativeKatoFiberSpecialization.nsmul_pow]
    exact inv_pow x n
  exact (congrArg Subtype.val hn).trans (congrArg Subtype.val hi)

lemma inverse_comp_eq {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (G H : Law R W) (hGH : G = H) {T U V : Scheme.{u}}
    (t : T ⟶ Base R) (s : U ⟶ Base R) (r : V ⟶ Base R)
    (a : V ⟶ T) (b : V ⟶ U) (ha : a ≫ t = r) (hb : b ≫ s = r)
    (x : SchemeHomOver t (structureMap R W))
    (y : SchemeHomOver s (structureMap R W)) (hxy : a ≫ x.val = b ≫ y.val) :
    a ≫ (G.inv t x).val = b ≫ (H.inv s y).val := by
  subst H
  have he : WeierstrassProjModel.schemeHomOverComp a ha x =
      WeierstrassProjModel.schemeHomOverComp b hb y := Subtype.ext hxy
  exact (congrArg Subtype.val (FullLevelFreeSignR0176.inverse_natural G t r a ha x)).trans
    ((congrArg (fun z => (G.inv r z).val) he).trans
      (congrArg Subtype.val (FullLevelFreeSignR0176.inverse_natural G s r b hb y)).symm)

/-- Forgetting the labels is equivariant for the actual simultaneous sign
actions on the compatible covers. -/
lemma cover_reduction_equivariant (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (f : D.cover.space ⟶ E.cover.space)
    (hp : f ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hx : f ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
    (hy : f ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val) :
    D.quotient.sign ≫ f = f ≫ E.quotient.sign := by
  have inv_label
      (x : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (y : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (hDx : D.atlas.sign.map ≫ x.val = (D.atlas.law.inv _ x).val)
      (hEy : E.atlas.sign.map ≫ y.val = (E.atlas.law.inv _ y).val)
      (hxy : f ≫ E.cover.inclusion ≫ y.val = D.cover.inclusion ≫
        (D.atlas.law.nsmul _ (L / d) x).val) :
      (D.quotient.sign ≫ f) ≫ E.cover.inclusion ≫ y.val =
        (f ≫ E.quotient.sign) ≫ E.cover.inclusion ≫ y.val := by
    have hi := inverse_comp_eq E.atlas.law D.atlas.law
      (atlas_law_eq k E.atlas D.atlas) E.atlas.level.projection D.atlas.level.projection
      (D.cover.inclusion ≫ D.atlas.level.projection) (f ≫ E.cover.inclusion)
      D.cover.inclusion (by simpa only [Category.assoc] using hp) rfl
      y (D.atlas.law.nsmul _ (L / d) x) (by simpa only [Category.assoc] using hxy)
    calc
      (D.quotient.sign ≫ f) ≫ E.cover.inclusion ≫ y.val =
          D.quotient.sign ≫ D.cover.inclusion ≫
            (D.atlas.law.nsmul _ (L / d) x).val := by rw [Category.assoc, hxy]
      _ = D.cover.inclusion ≫ (D.atlas.law.inv _ (D.atlas.law.nsmul _ (L / d) x)).val := by
        rw [← Category.assoc, D.quotient.sign_eq, Category.assoc,
          sign_nsmul _ _ _ D.atlas.sign.over_eq _ hDx]
      _ = f ≫ E.cover.inclusion ≫ (E.atlas.law.inv _ y).val := by
        simpa only [Category.assoc] using hi.symm
      _ = (f ≫ E.quotient.sign) ≫ E.cover.inclusion ≫ y.val := by
        rw [Category.assoc, ← Category.assoc E.quotient.sign,
          E.quotient.sign_eq, Category.assoc, hEy]
  apply cover_hom_ext k E
  · simp only [Category.assoc]
    rw [hp, ← Category.assoc, D.quotient.sign_eq, Category.assoc, D.atlas.sign.over_eq,
      ← Category.assoc E.quotient.sign, E.quotient.sign_eq, Category.assoc,
      E.atlas.sign.over_eq, hp]
  · exact inv_label _ _ D.atlas.sign.x_eq E.atlas.sign.x_eq hx
  · exact inv_label _ _ D.atlas.sign.y_eq E.atlas.sign.y_eq hy

/-- Descend the explicitly constructed cover morphism through the specified
categorical sign quotients, preserving its defining square and scalar map. -/
lemma quotient_reduction_exists (k : Type u) [Field k] [CharZero k]
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d) :
    ∃ (g : D.cover.space ⟶ E.cover.space) (f : OpenBase k L D ⟶ OpenBase k d E),
      g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
        D.cover.inclusion ≫ D.atlas.level.projection ∧
      g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
        D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val ∧
      g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
        D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val ∧
      D.quotient.quotient.q ≫ f = g ≫ E.quotient.quotient.q ∧
      f ≫ openStructure k d E = openStructure k L D := by
  obtain ⟨g, hp, hx, hy⟩ := cover_reduction_exists k L d hL hd hdeven hdL D E
  have he := cover_reduction_equivariant k D E g hp hx hy
  obtain ⟨f, hf, _⟩ := D.quotient.quotient.universal (OpenBase k d E)
    (g ≫ E.quotient.quotient.q) (by
      rw [← Category.assoc, he, Category.assoc, E.quotient.quotient.invariant])
  refine ⟨g, f, hp, hx, hy, hf, ?_⟩
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.etale
  letI := D.quotient.quotient.surjective
  apply (cancel_epi D.quotient.quotient.q).mp
  change D.quotient.quotient.q ≫ f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E.quotient.quotient.ring)) =
    D.quotient.quotient.q ≫ Spec.map (CommRingCat.ofHom (algebraMap k D.quotient.quotient.ring))
  rw [← Category.assoc, hf, Category.assoc, E.quotient.quotient.over_eq,
    D.quotient.quotient.over_eq]
  simpa only [Category.assoc] using congrArg (fun a => a ≫ legendreBaseMap k) hp

/-- The cover reduction is finite étale, by cancellation against the specified
finite étale projections to the same punctured Legendre line. -/
lemma cover_reduction_finite_etale (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (g : D.cover.space ⟶ E.cover.space)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection) : IsFinite g ∧ Etale g := by
  let p := E.cover.inclusion ≫ E.atlas.level.projection
  letI : IsFinite p := E.cover.finite
  letI : Etale p := E.cover.etale
  letI : IsFinite (g ≫ p) := by rw [show g ≫ p = _ from hp]; exact D.cover.finite
  letI : Etale (g ≫ p) := by rw [show g ≫ p = _ from hp]; exact D.cover.etale
  exact ⟨IsFinite.of_comp g p, Etale.of_comp g p⟩

/-- Finiteness and flatness of the quotient map descend from the constructed
cover map. The finite-type input follows from the actual smooth scalar map. -/
lemma quotient_reduction_finite_flat (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (g : D.cover.space ⟶ E.cover.space) (f : OpenBase k L D ⟶ OpenBase k d E)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hf : D.quotient.quotient.q ≫ f = g ≫ E.quotient.quotient.q)
    (hk : f ≫ openStructure k d E = openStructure k L D) : IsFinite f ∧ Flat f := by
  obtain ⟨hfin, het⟩ := cover_reduction_finite_etale k D E g hp
  letI := hfin
  letI := het
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.etale
  letI := D.quotient.quotient.surjective
  letI := E.quotient.quotient.finite
  letI := E.quotient.quotient.etale
  letI : IsFinite (D.quotient.quotient.q ≫ f) := by rw [hf]; infer_instance
  letI : Flat (D.quotient.quotient.q ≫ f) := by rw [hf]; infer_instance
  letI : SmoothOfRelativeDimension 1 (openStructure k L D) := D.quotient.quotient.smooth
  letI : LocallyOfFiniteType (f ≫ openStructure k d E) := by rw [hk]; infer_instance
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (openStructure k d E)
  exact ⟨IsFinite.of_comp_of_surjective D.quotient.quotient.q f,
    Flat.of_comp_of_flat_of_surjective D.quotient.quotient.q f⟩

open scoped TensorProduct

/-- Unramifiedness descends along a faithfully flat étale extension of the
source ring, using the actual cotangent base-change isomorphism. -/
lemma ring_unramified_descent {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (he : g.Etale) (hf : g.FaithfullyFlat)
    (hc : (g.comp f).FormallyUnramified) : f.FormallyUnramified := by
  algebraize [f, g, g.comp f]
  constructor
  have : Subsingleton (T ⊗[S] KaehlerDifferential R S) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality S T _

/-- A source affine étale surjection detects formal unramifiedness. -/
lemma unramified_of_etale_cover {X Y Z : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ Z)
    [IsAffineHom q] [Etale q] [Surjective q] [FormallyUnramified (q ≫ f)] :
    FormallyUnramified f := by
  rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
  intro W V e
  let U : X.affineOpens := ⟨q ⁻¹ᵁ (V : Y.Opens), V.2.preimage q⟩
  have eU : (U : X.Opens) ≤ q ⁻¹ᵁ (V : Y.Opens) := le_rfl
  have eWU : (U : X.Opens) ≤ (q ≫ f) ⁻¹ᵁ (W : Z.Opens) := fun x hx => e hx
  let φ := f.appLE W V e
  let ψ := q.appLE V U eU
  have hcomp : φ ≫ ψ = (q ≫ f).appLE W U eWU :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hc : ((q ≫ f).appLE W U eWU).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified (q ≫ f) inferInstance W U eWU
  have he : ψ.hom.Etale := HasRingHomProperty.appLE @Etale q inferInstance V U eU
  have hflat : ψ.hom.Flat := HasRingHomProperty.appLE @Flat q inferInstance V U eU
  have hs : Function.Surjective (PrimeSpectrum.comap ψ.hom) := by
    intro p
    obtain ⟨x, hx⟩ := q.surjective (V.2.fromSpec p)
    have hxU : x ∈ (U : X.Opens) := by
      change q x ∈ (V : Y.Opens)
      rw [hx]
      exact V.2.range_fromSpec.le ⟨p, rfl⟩
    obtain ⟨a, rfl⟩ := U.2.range_fromSpec.ge hxU
    refine ⟨a, V.2.isOpenImmersion_fromSpec.base_open.injective ?_⟩
    change V.2.fromSpec (Spec.map ψ a) = V.2.fromSpec p
    rw [← hx, ← Scheme.Hom.comp_apply,
      IsAffineOpen.SpecMap_appLE_fromSpec q V.2 U.2 eU, Scheme.Hom.comp_apply]
  have hfaith : ψ.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hflat, hs⟩
  rw [← hcomp, CommRingCat.hom_comp] at hc
  exact ring_unramified_descent φ.hom ψ.hom he hfaith hc

/-- The descended reduction is finite étale, with no ramification introduced
by passage through either of the actual free sign quotients. -/
lemma quotient_reduction_finite_etale (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (D : LevelData k L) (E : LevelData k d)
    (g : D.cover.space ⟶ E.cover.space) (f : OpenBase k L D ⟶ OpenBase k d E)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hf : D.quotient.quotient.q ≫ f = g ≫ E.quotient.quotient.q)
    (hk : f ≫ openStructure k d E = openStructure k L D) : IsFinite f ∧ Etale f := by
  obtain ⟨hfin, hflat⟩ := quotient_reduction_finite_flat k D E g f hp hf hk
  letI := hfin
  letI := hflat
  letI := (cover_reduction_finite_etale k D E g hp).2
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.etale
  letI := D.quotient.quotient.surjective
  letI := E.quotient.quotient.etale
  letI : Etale (D.quotient.quotient.q ≫ f) := by rw [hf]; infer_instance
  letI : FormallyUnramified f := unramified_of_etale_cover D.quotient.quotient.q f
  letI : SmoothOfRelativeDimension 1 (openStructure k d E) := E.quotient.quotient.smooth
  letI : IsLocallyNoetherian (OpenBase k d E) :=
    LocallyOfFiniteType.isLocallyNoetherian (openStructure k d E)
  exact ⟨hfin, Etale.of_formallyUnramified_of_flat f⟩

/-- Every geometric point of the actual compatible quotient is represented by
an actual elliptic Weierstrass curve with both full labels. -/
lemma geometric_point_classification (k : Type u) [Field k] [CharZero k]
    {L : ℕ} (D : LevelData k L) (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
    (b : Base K ⟶ OpenBase k L D)
    (hk : b ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic) (G : Law K W)
      (_ : IsOriginLaw K W G) (M : FullLevel K W G L (𝟙 (Base K)))
      (a : Curve K W ⟶ D.atlas.descent.family.curve),
      Classifies k L D.atlas D.two D.cover D.quotient K W G M b a := by
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨c, hc⟩ := CompatibleClassifyingUniqueness.lift_geometric_point D.quotient.quotient.q b
  obtain ⟨α, hα⟩ := Spec.map_surjective ((c ≫ D.cover.inclusion) ≫ D.atlas.level.projection)
  obtain ⟨P⟩ := CompatibleClassifyingUniqueness.presentation_exists k L D.atlas K α.hom
    (c ≫ D.cover.inclusion) hα.symm
  have he : (c ≫ D.cover.inclusion) ≫ D.atlas.quotient.q = b ≫ D.quotient.inclusion := by
    rw [Category.assoc, D.quotient.cartesian.w, ← Category.assoc, hc]
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.hom.toAlgebra
  refine ⟨(legendre k).map α.hom, inferInstance, P.law, P.originLaw,
    P.marking, P.comparison, hk, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using P.cartesian
  · simpa only [he] using P.origin_eq
  · simpa only [he] using P.x_eq
  · simpa only [he] using P.y_eq

/-- The prescribed classifying comparisons determine the quotient morphism
uniquely. Detection uses all geometric points and reducedness from the actual
smooth structural map; no connectedness assumption is used. -/
lemma reduction_unique (k : Type u) [Field k] [CharZero k]
    (L d : ℕ) (hL : 0 < L) (hd : 3 ≤ d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d)
    (f g : OpenBase k L D ⟶ OpenBase k d E)
    (hf : RespectsReduction k L D E f) (hg : RespectsReduction k L D E g) : f = g := by
  have geom (K : Type u) [Field K] [IsAlgClosed K] (b : Base K ⟶ OpenBase k L D) :
      b ≫ f = b ≫ g := by
    obtain ⟨β, rfl⟩ := Spec.map_surjective b
    letI : Algebra k K := (β.hom.comp (algebraMap k D.quotient.quotient.ring)).toAlgebra
    letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    have hk : Spec.map β ≫ openStructure k L D =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [openStructure, ← Spec.map_comp]
      rfl
    obtain ⟨W, hW, G, hG, M, a, ha⟩ := geometric_point_classification k D K (Spec.map β) hk
    letI := hW
    obtain ⟨N, hx, hy, b', ⟨a', hb', _⟩, _⟩ := reduced_classification
      k L d hL hd hdeven hdL E K W G hG M
    exact (hf.2 K W G hG M N hx hy _ b' a a' ha hb').trans
      (hg.2 K W G hG M N hx hy _ b' a a' ha hb').symm
  letI : SmoothOfRelativeDimension 1 (openStructure k L D) := D.quotient.quotient.smooth
  letI : IsReduced (OpenBase k L D) :=
    Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (openStructure k L D)
  apply NormalAffineClassifyingConstruction.reduced_ext (openStructure k d E) f g
    (hf.1.trans hg.1.symm)
  intro K _ b
  let σ := algebraMap K (AlgebraicClosure K)
  apply CompatibleClassifyingUniqueness.affine_ext σ σ.injective
  simpa only [Category.assoc] using geom (AlgebraicClosure K)
    (Spec.map (CommRingCat.ofHom σ) ≫ b)

open CompatibleClassifyingUniqueness

/-- On a geometric presentation, the cover reduction classifies precisely the
two multiplied labels on the same coefficient Weierstrass curve. -/
lemma reduced_presentation_classifies (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d) (g : D.cover.space ⟶ E.cover.space)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hx : g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
    (hy : g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val)
    (K : Type u) [Field K] [Algebra k K] (c : Base K ⟶ D.cover.space)
    (α : LegendreRing k →+* K)
    (ha : (c ≫ D.cover.inclusion) ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α))
    (P : Presentation k L D.atlas K α (c ≫ D.cover.inclusion))
    (hk : (c ≫ g ≫ E.quotient.quotient.q) ≫ openStructure k d E =
      Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ a : Curve K ((legendre k).map α) ⟶ E.atlas.descent.family.curve,
      Classifies k d E.atlas E.two E.cover E.quotient K ((legendre k).map α) P.law
        (reduceMarking hL hd hdL P.marking) (c ≫ g ≫ E.quotient.quotient.q) a := by
  have haE : ((c ≫ g) ≫ E.cover.inclusion) ≫ E.atlas.level.projection =
      Spec.map (CommRingCat.ofHom α) := by
    simpa only [Category.assoc, hp] using ha
  obtain ⟨Q⟩ := presentation_exists k d E.atlas K α ((c ≫ g) ≫ E.cover.inclusion) haE
  have he : (((c ≫ g) ≫ E.cover.inclusion) ≫ E.atlas.quotient.q) =
      (c ≫ g ≫ E.quotient.quotient.q) ≫ E.quotient.inclusion := by
    simp only [Category.assoc, E.quotient.cartesian.w]
  have label
      (x : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (y : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (p q : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)))
      (hpc : p.val ≫ P.coeff = (c ≫ D.cover.inclusion) ≫ x.val)
      (hqc : q.val ≫ Q.coeff = ((c ≫ g) ≫ E.cover.inclusion) ≫ y.val)
      (hxy : g ≫ E.cover.inclusion ≫ y.val = D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) x).val) :
      (P.law.nsmul (𝟙 _) (L / d) p).val = q.val := by
    apply P.coefficient.1.hom_ext
    · rw [nsmul_coeff P ha x p hpc, P.coeff_eq, ← Q.coeff_eq, hqc]
      simpa only [Category.assoc] using (congrArg (fun a => c ≫ a) hxy).symm
    · exact (P.law.nsmul _ _ p).property.trans q.property.symm
  have hpx := label _ _ _ _ P.x_coeff Q.x_coeff hx
  have hpy := label _ _ _ _ P.y_coeff Q.y_coeff hy
  refine ⟨Q.comparison, hk, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using Q.cartesian
  · simpa only [he] using Q.origin_eq
  · change (P.law.nsmul (𝟙 _) (L / d) P.marking.x).val ≫ Q.comparison = _
    rw [hpx]
    simpa only [he] using Q.x_eq
  · change (P.law.nsmul (𝟙 _) (L / d) P.marking.y).val ≫ Q.comparison = _
    rw [hpy]
    simpa only [he] using Q.y_eq

/-- Pull back a classification along a genuine Cartesian Weierstrass
comparison preserving the origin and the specified pair of sections. -/
lemma classifies_pullback (k : Type u) [Field k] [CharZero k] {d : ℕ}
    (E : LevelData k d)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (G : Law R W) (H : Law S V)
    (M : FullLevel R W G d (𝟙 (Base R))) (N : FullLevel S V H d (𝟙 (Base S)))
    (i : Base S ⟶ Base R) (c : Curve S V ⟶ Curve R W)
    (hcart : IsPullback c (structureMap S V) (structureMap R W) i)
    (ho : origin S V ≫ c = i ≫ origin R W)
    (hx : N.x.val ≫ c = i ≫ M.x.val) (hy : N.y.val ≫ c = i ≫ M.y.val)
    (hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k S)))
    (b : Base R ⟶ OpenBase k d E) (a : Curve R W ⟶ E.atlas.descent.family.curve)
    (h : Classifies k d E.atlas E.two E.cover E.quotient R W G M b a) :
    Classifies k d E.atlas E.two E.cover E.quotient S V H N (i ≫ b) (c ≫ a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, h.1, hi]
  · simpa only [Category.assoc] using hcart.paste_horiz h.2.1
  · rw [← Category.assoc, ho, Category.assoc, h.2.2.1]
    simp only [Category.assoc]
  · rw [← Category.assoc, hx, Category.assoc, h.2.2.2.1]
    simp only [Category.assoc]
  · rw [← Category.assoc, hy, Category.assoc, h.2.2.2.2]
    simp only [Category.assoc]

/-- The descended morphism satisfies the full frozen classifying comparison
on every normal integral Noetherian rational test ring and both reduced labels. -/
lemma quotient_reduction_respects (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (hL : 0 < L) (hd : 3 ≤ d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d)
    (g : D.cover.space ⟶ E.cover.space) (f : OpenBase k L D ⟶ OpenBase k d E)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hxg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
    (hyg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val)
    (hf : D.quotient.quotient.q ≫ f = g ≫ E.quotient.quotient.q)
    (hk : f ≫ openStructure k d E = openStructure k L D) :
    RespectsReduction k L D E f := by
  refine ⟨hk, ?_⟩
  intro R _ _ _ _ _ _ W _ G hG M N hx hy b b' a a' hb hb'
  let K := AlgebraicClosure (FractionRing R)
  let σ : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hσ : Function.Injective σ :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  let i := Spec.map (CommRingCat.ofHom σ)
  letI : Algebra k K := (σ.comp (algebraMap k R)).toAlgebra
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    rfl
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨c, hc⟩ := lift_geometric_point D.quotient.quotient.q (i ≫ b)
  obtain ⟨α, hα⟩ := Spec.map_surjective ((c ≫ D.cover.inclusion) ≫ D.atlas.level.projection)
  obtain ⟨P⟩ := presentation_exists k L D.atlas K α.hom (c ≫ D.cover.inclusion) hα.symm
  have hca : (c ≫ D.cover.inclusion) ≫ D.atlas.quotient.q =
      i ≫ (b ≫ D.quotient.inclusion) := by
    rw [Category.assoc, D.quotient.cartesian.w, ← Category.assoc, hc, Category.assoc]
  obtain ⟨v, hv, ho, hvx, hvy⟩ := comparison_to_source P M i (b ≫ D.quotient.inclusion)
    a hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hca
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.hom.toAlgebra
  letI : ((legendre k).map α.hom).IsElliptic := inferInstance
  have hbase := MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    G P.law hG P.originLaw σ v hv ho
  let MK := reduceMarking hL (by omega : 0 < d) hdL P.marking
  have label (x : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α.hom)))
      (y : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
      (hxy : x.val ≫ v = i ≫ y.val) :
      (P.law.nsmul (𝟙 _) (L / d) x).val ≫ v =
        i ≫ (G.nsmul (𝟙 _) (L / d) y).val := by
    open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential in
    rw [← comp_schemeNsmul, Category.assoc, hbase.2.2, ← Category.assoc,
      hxy, Category.assoc, comp_schemeNsmul]
  have hnx : MK.x.val ≫ v = i ≫ N.x.val := by
    rw [hx]
    exact label _ _ hvx
  have hny : MK.y.val ≫ v = i ≫ N.y.val := by
    rw [hy]
    exact label _ _ hvy
  have hcf : c ≫ g ≫ E.quotient.quotient.q = (i ≫ b) ≫ f := by
    exact (congrArg (fun a => c ≫ a) hf.symm).trans
      ((Category.assoc c D.quotient.quotient.q f).symm.trans (congrArg (fun a => a ≫ f) hc))
  have hscalar : (c ≫ g ≫ E.quotient.quotient.q) ≫ openStructure k d E =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hcf, Category.assoc, hk, Category.assoc]
    exact (congrArg (fun a => i ≫ a) hb.1).trans hi
  obtain ⟨aK, haK⟩ := reduced_presentation_classifies k hL (by omega : 0 < d) hdL
    D E g hp hxg hyg K c α.hom hα.symm P hscalar
  have hbK := classifies_pullback k E R K W ((legendre k).map α.hom) G P.law
    N MK i v hv ho hnx hny hi b' a' hb'
  have he := (compatible_classifying_uniqueness k d hd hdeven E.atlas E.two E.canonical
    E.cover E.quotient K ((legendre k).map α.hom) P.law P.originLaw MK
    (c ≫ g ≫ E.quotient.quotient.q) (i ≫ b') aK (v ≫ a') haK hbK).1
  apply affine_ext σ hσ
  simpa only [hcf, Category.assoc] using he

/-- A power of every element of a finite monoid is idempotent. -/
lemma finite_idempotent_power {M : Type u} [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (α := ℕ) (x ^ ·)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (by omega)
  let p := j - i
  have hp : 0 < p := by dsimp [p]; omega
  have hperiod (a : ℕ) (hia : i ≤ a) : x ^ (a + p) = x ^ a := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hia
    have hj : i + p = j := by dsimp [p]; omega
    calc
      x ^ (i + r + p) = x ^ (i + p) * x ^ r := by rw [← pow_add]; congr 1; omega
      _ = x ^ i * x ^ r := by rw [hj, ← he]
      _ = x ^ (i + r) := (pow_add _ _ _).symm
  have hiter (a r : ℕ) (hia : i ≤ a) : x ^ (a + p * r) = x ^ a := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hperiod _ (by omega), ih]
  let n := p * (i + 1)
  have hn : 0 < n := Nat.mul_pos hp (by omega)
  have hin : i ≤ n := by dsimp [n]; nlinarith
  refine ⟨n, hn, ?_⟩
  rw [← pow_add]
  exact hiter n (i + 1) hin

/-- Units lift along every surjection of finite rings. The idempotent-power
correction is valid for noncommutative rings, hence for matrix rings as well. -/
lemma finite_ring_lift_unit {R S : Type u} [Ring R] [Ring S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) (v : Sˣ) :
    ∃ u : Rˣ, f u = v := by
  obtain ⟨a, ha⟩ := hf (v : S)
  obtain ⟨n, hn, he⟩ := finite_idempotent_power a
  let e := a ^ n
  have hee : e * e = e := he
  have hfe : f e = 1 := by
    apply (IsIdempotentElem.iff_eq_one_of_isUnit ?_).mp
    · change f e * f e = f e
      rw [← map_mul, hee]
    · simpa only [e, map_pow, ha] using v.isUnit.pow n
  let b := a * e + (1 - e)
  let c := a ^ (n - 1) * e + (1 - e)
  have hc : Commute e (a ^ (n - 1)) := (Commute.refl a).pow_pow n (n - 1)
  have hc' : Commute e a := (Commute.refl a).pow_left n
  have haexp : a * a ^ (n - 1) = e := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hmul : (a * e) * (a ^ (n - 1) * e) = e := by
    rw [hc.mul_mul_mul_comm, ← mul_assoc, haexp, mul_assoc, hee, hee]
  have hright : (a * e) * (1 - e) = 0 := by
    rw [mul_sub, mul_one, mul_assoc, hee, sub_self]
  have hleft : (1 - e) * (a ^ (n - 1) * e) = 0 := by
    rw [sub_mul, one_mul, ← mul_assoc, hc.eq, mul_assoc, hee, sub_self]
  have hrest : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have hbc : b * c = 1 := by
    dsimp [b, c]
    rw [add_mul, mul_add, mul_add, hmul, hright, hleft, hrest]
    simp
  have hub : IsUnit b := (isUnit_iff_exists_inv).mpr ⟨c, hbc⟩
  refine ⟨hub.unit, ?_⟩
  rw [hub.unit_spec]
  simp only [b, map_add, map_mul, map_sub, map_one, ha, hfe, mul_one, sub_self, add_zero]

namespace Counting
open CoverGeometryR0175

abbrev Residues (n : ℕ) := ZMod n × ZMod n

lemma residue_killed (n : ℕ) (x : Residues n) : n • x = 0 := by
  ext <;> simp [nsmul_eq_mul]

lemma pair_hom_ext (n : ℕ) [NeZero n] {H : Type*} [AddCommGroup H]
    (f g : Residues n →+ H) (hx : f (1, 0) = g (1, 0)) (hy : f (0, 1) = g (0, 1)) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  have he : x = x.1.val • (1, 0) + x.2.val • (0, 1) := by
    ext <;> simp [nsmul_eq_mul]
  rw [he, map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul, hx, hy]

def residueMap {L d : ℕ} (hdL : d ∣ L) : Residues L →+ Residues d :=
  (ZMod.castHom hdL (ZMod d)).toAddMonoidHom.prodMap
    (ZMod.castHom hdL (ZMod d)).toAddMonoidHom

@[simp] lemma residueMap_fst {L d : ℕ} (hdL : d ∣ L) : residueMap hdL (1, 0) = (1, 0) := by
  exact Prod.ext (map_one (ZMod.castHom hdL (ZMod d))) (map_zero (ZMod.castHom hdL (ZMod d)))

@[simp] lemma residueMap_snd {L d : ℕ} (hdL : d ∣ L) : residueMap hdL (0, 1) = (0, 1) := by
  exact Prod.ext (map_zero (ZMod.castHom hdL (ZMod d))) (map_one (ZMod.castHom hdL (ZMod d)))

lemma residueMap_surjective {L d : ℕ} (hdL : d ∣ L) : Function.Surjective (residueMap hdL) := by
  intro x
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective hdL x.1
  obtain ⟨b, hb⟩ := ZMod.castHom_surjective hdL x.2
  exact ⟨(a, b), Prod.ext ha hb⟩

def reduceEnd {L d : ℕ} [NeZero d] (hdL : d ∣ L)
    (f : AddMonoid.End (Residues L)) : AddMonoid.End (Residues d) :=
  pairHom d (residue_killed d) (residueMap hdL (f (1, 0))) (residueMap hdL (f (0, 1)))

lemma reduceEnd_comp {L d : ℕ} [NeZero L] [NeZero d] (hdL : d ∣ L)
    (f : AddMonoid.End (Residues L)) :
    (reduceEnd hdL f).comp (residueMap hdL) = (residueMap hdL).comp f := by
  apply pair_hom_ext L <;> simp [reduceEnd]

def reduceEndHom {L d : ℕ} [NeZero L] [NeZero d] (hdL : d ∣ L) :
    AddMonoid.End (Residues L) →+* AddMonoid.End (Residues d) where
  toFun := reduceEnd hdL
  map_zero' := by apply pair_hom_ext d <;> simp [reduceEnd]
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := residueMap_surjective hdL x
    exact DFunLike.congr_fun (reduceEnd_comp hdL 1) x
  map_add' f g := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := residueMap_surjective hdL x
    have h (F : AddMonoid.End (Residues L)) (x : Residues L) :
        reduceEnd hdL F (residueMap hdL x) = residueMap hdL (F x) :=
      DFunLike.congr_fun (reduceEnd_comp hdL F) x
    change reduceEnd hdL (f + g) (residueMap hdL x) =
      reduceEnd hdL f (residueMap hdL x) + reduceEnd hdL g (residueMap hdL x)
    rw [h, h, h]
    exact map_add (residueMap hdL) (f x) (g x)
  map_mul' f g := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := residueMap_surjective hdL x
    have h (F : AddMonoid.End (Residues L)) (x : Residues L) :
        reduceEnd hdL F (residueMap hdL x) = residueMap hdL (F x) :=
      DFunLike.congr_fun (reduceEnd_comp hdL F) x
    change reduceEnd hdL (f * g) (residueMap hdL x) =
      reduceEnd hdL f (reduceEnd hdL g (residueMap hdL x))
    rw [h, h, h]
    rfl

lemma reduceEndHom_surjective {L d : ℕ} [NeZero L] [NeZero d] (hdL : d ∣ L) :
    Function.Surjective (reduceEndHom hdL) := by
  intro f
  obtain ⟨x, hx⟩ := residueMap_surjective hdL (f (1, 0))
  obtain ⟨y, hy⟩ := residueMap_surjective hdL (f (0, 1))
  refine ⟨pairHom L (residue_killed L) x y, ?_⟩
  change reduceEnd hdL (pairHom L (residue_killed L) x y) = f
  apply pair_hom_ext d
  · exact (pairHom_fst d (residue_killed d) _ _).trans
      ((congrArg (residueMap hdL) (pairHom_fst L (residue_killed L) x y)).trans hx)
  · exact (pairHom_snd d (residue_killed d) _ _).trans
      ((congrArg (residueMap hdL) (pairHom_snd L (residue_killed L) x y)).trans hy)

/-- Every automorphism of the two residue coordinates lifts across an arbitrary
divisor of a positive level; no prime-power or fixed-pairing restriction. -/
lemma lift_residue_automorphism {L d : ℕ} [NeZero L] [NeZero d] (hdL : d ∣ L)
    (e : Residues d ≃+ Residues d) :
    ∃ e' : Residues L ≃+ Residues L,
      ∀ x, residueMap hdL (e' x) = e (residueMap hdL x) := by
  let v : (AddMonoid.End (Residues d))ˣ :=
    { val := e.toAddMonoidHom
      inv := e.symm.toAddMonoidHom
      val_inv := by apply AddMonoidHom.ext; intro x; exact e.apply_symm_apply x
      inv_val := by apply AddMonoidHom.ext; intro x; exact e.symm_apply_apply x }
  letI : Finite (AddMonoid.End (Residues L)) :=
    Finite.of_injective (fun f : AddMonoid.End (Residues L) => (f : Residues L → Residues L))
      DFunLike.coe_injective
  obtain ⟨w, hw⟩ := finite_ring_lift_unit (reduceEndHom hdL) (reduceEndHom_surjective hdL) v
  let e' : Residues L ≃+ Residues L :=
    { toFun := (w : AddMonoid.End (Residues L))
      invFun := (↑w⁻¹ : AddMonoid.End (Residues L))
      map_add' := (w : AddMonoid.End (Residues L)).map_add
      left_inv := fun x => DFunLike.congr_fun w.inv_val x
      right_inv := fun x => DFunLike.congr_fun w.val_inv x }
  refine ⟨e', ?_⟩
  intro x
  have h := DFunLike.congr_fun (reduceEnd_comp hdL (w : AddMonoid.End (Residues L))) x
  change reduceEndHom hdL w (residueMap hdL x) = residueMap hdL (e' x) at h
  rw [hw] at h
  exact h.symm

variable {H : Type u} [AddCommGroup H]

abbrev Torsion (n : ℕ) := Submodule.torsionBy ℤ H (n : ℤ)

lemma torsion_killed (n : ℕ) (x : Torsion (H := H) n) : n • x = 0 := by
  simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (n : ℤ) x

def torsionReduction {L d : ℕ} (hdL : d ∣ L) : Torsion (H := H) L →+ Torsion (H := H) d where
  toFun x := ⟨(L / d) • x.val, by
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul, smul_smul,
      Nat.mul_comm, Nat.div_mul_cancel hdL]
    exact congrArg Subtype.val (torsion_killed L x)⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [smul_add]

def reduceBasis {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (a : BasisPair (H := Torsion (H := H) L) L) :
    BasisPair (H := Torsion (H := H) d) d :=
  ⟨(torsionReduction hdL a.val.1, torsionReduction hdL a.val.2), by
    intro i j hij hz
    have hq : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
    have hlt (i : Fin d) : i.val * (L / d) < L := by
      have h := Nat.mul_lt_mul_of_pos_right i.isLt hq
      rwa [Nat.mul_comm d, Nat.div_mul_cancel hdL] at h
    have hn : i.val * (L / d) ≠ 0 ∨ j.val * (L / d) ≠ 0 :=
      hij.imp (fun h => Nat.mul_ne_zero h (Nat.ne_of_gt hq))
        (fun h => Nat.mul_ne_zero h (Nat.ne_of_gt hq))
    apply a.property ⟨_, hlt i⟩ ⟨_, hlt j⟩ hn
    apply Subtype.ext
    have hh := congrArg Subtype.val hz
    simpa only [torsionReduction, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Submodule.coe_add, Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero,
      smul_smul] using hh⟩

section BasisFibers
variable {L d : ℕ} [NeZero L] [NeZero d]
  [Finite (Torsion (H := H) L)] [Finite (Torsion (H := H) d)]
  (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
  (hcL : Nat.card (Torsion (H := H) L) = L ^ 2)
  (hcd : Nat.card (Torsion (H := H) d) = d ^ 2)

lemma basis_reduction_natural (a : BasisPair (H := Torsion (H := H) L) L)
    (x : Residues L) :
    torsionReduction hdL (basisPairEquiv L (torsion_killed L) hcL a x) =
      basisPairEquiv d (torsion_killed d) hcd (reduceBasis hL hd hdL a) (residueMap hdL x) := by
  have he : (torsionReduction hdL).comp
      (basisPairEquiv L (torsion_killed L) hcL a).toAddMonoidHom =
      (basisPairEquiv d (torsion_killed d) hcd (reduceBasis hL hd hdL a)).toAddMonoidHom.comp
        (residueMap hdL) := by
    apply pair_hom_ext L <;>
      simp [basisPairEquiv, reduceBasis, residueMap_fst, residueMap_snd]
  exact DFunLike.congr_fun he x

lemma reduceBasis_change (s : Residues L ≃+ Residues L) (t : Residues d ≃+ Residues d)
    (hst : ∀ x, residueMap hdL (s x) = t (residueMap hdL x))
    (a : BasisPair (H := Torsion (H := H) L) L) :
    reduceBasis hL hd hdL (SubcoverR0178.basisChange L (torsion_killed L) hcL s a) =
      SubcoverR0178.basisChange d (torsion_killed d) hcd t (reduceBasis hL hd hdL a) := by
  apply (basisPairEquiv d (torsion_killed d) hcd).injective
  apply AddEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := residueMap_surjective hdL x
  rw [← basis_reduction_natural hL hd hdL hcL hcd]
  have change_eval {n : ℕ} [NeZero n] [Finite (Torsion (H := H) n)]
      (hc : Nat.card (Torsion (H := H) n) = n ^ 2)
      (s : Residues n ≃+ Residues n) (a : BasisPair (H := Torsion (H := H) n) n)
      (x : Residues n) :
      basisPairEquiv n (torsion_killed n) hc
        (SubcoverR0178.basisChange n (torsion_killed n) hc s a) x =
          basisPairEquiv n (torsion_killed n) hc a (s x) := by
    simp [SubcoverR0178.basisChange, SubcoverR0178.precompose]
  rw [change_eval, change_eval, basis_reduction_natural hL hd hdL hcL hcd, hst]

def reductionFiberEquiv (a b : BasisPair (H := Torsion (H := H) d) d) :
    {x // reduceBasis hL hd hdL x = a} ≃ {x // reduceBasis hL hd hdL x = b} := by
  let ea := basisPairEquiv d (torsion_killed d) hcd a
  let eb := basisPairEquiv d (torsion_killed d) hcd b
  let t := eb.trans ea.symm
  let s := (lift_residue_automorphism hdL t).choose
  have hs := (lift_residue_automorphism hdL t).choose_spec
  have ht : SubcoverR0178.basisChange d (torsion_killed d) hcd t a = b := by
    apply (basisPairEquiv d (torsion_killed d) hcd).injective
    simp only [SubcoverR0178.basisChange, Equiv.trans_apply, Equiv.apply_symm_apply]
    apply AddEquiv.ext
    intro x
    exact ea.apply_symm_apply (eb x)
  apply (SubcoverR0178.basisChange L (torsion_killed L) hcL s).subtypeEquiv
  intro x
  rw [reduceBasis_change hL hd hdL hcL hcd s t hs, ← ht]
  exact (SubcoverR0178.basisChange d (torsion_killed d) hcd t).injective.eq_iff.symm

include hcL hcd in
/-- Exact cardinality and nonemptiness of every divisor-reduction fiber of
full torsion bases, with the full GL degree. -/
lemma card_reduction_fiber
    (eL : Residues L ≃+ Torsion (H := H) L)
    (b : BasisPair (H := Torsion (H := H) d) d) :
    Nat.card {x // reduceBasis hL hd hdL x = b} = levelDegree L / levelDegree d ∧
      0 < Nat.card {x // reduceBasis hL hd hdL x = b} := by
  let r := reduceBasis (H := H) hL hd hdL
  have hc : Nat.card (BasisPair (H := Torsion (H := H) d) d) = levelDegree d :=
    card_basisPair d (torsion_killed d) hcd (basisPairEquiv d (torsion_killed d) hcd b)
  let e := (Equiv.sigmaFiberEquiv r).symm.trans
    (Equiv.sigmaCongrRight fun a => reductionFiberEquiv hL hd hdL hcL hcd a b) |>.trans
      (Equiv.sigmaEquivProd _ _)
  have count : levelDegree L = levelDegree d * Nat.card {x // r x = b} := by
    rw [← card_basisPair L (torsion_killed L) hcL eL, Nat.card_congr e, Nat.card_prod, hc]
  constructor
  · rw [count, Nat.mul_div_cancel_left _ (CoverGeometryR0175.levelDegree_pos d hd)]
  · have hp := CoverGeometryR0175.levelDegree_pos L hL
    rw [count] at hp
    change 0 < Nat.card {x // r x = b}
    exact Nat.pos_of_mul_pos_left hp

end BasisFibers
end Counting

section CoverFibers
variable (k : Type u) [Field k] [CharZero k] {L d : ℕ}
  (hL : 0 < L) (hd : 0 < d) (hdeven : Even d) (hdL : d ∣ L)
  (D : LevelData k L) (E : LevelData k d)
  (g : D.cover.space ⟶ E.cover.space)
  (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
    D.cover.inclusion ≫ D.atlas.level.projection)
  (hxg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
    D.cover.inclusion ≫
      (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
  (hyg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
    D.cover.inclusion ≫
      (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val)
  {T : Scheme.{u}} (b : T ⟶ E.cover.space)

def targetMarking : FullLevel (LegendreRing k) (legendre k) D.atlas.law d
    ((b ≫ E.cover.inclusion) ≫ E.atlas.level.projection) :=
  changeLaw (atlas_law_eq k E.atlas D.atlas)
    (BaseChange.restrict E.atlas.level.level (b ≫ E.cover.inclusion) rfl)

include hdeven hdL in
lemma compatible_of_reduced_marking
    (M : FullLevel (LegendreRing k) (legendre k) D.atlas.law L
      ((b ≫ E.cover.inclusion) ≫ E.atlas.level.projection))
    (hM : reduceMarking hL hd hdL M = targetMarking k D E b)
    (a : SchemeHomOver ((b ≫ E.cover.inclusion) ≫ E.atlas.level.projection)
      D.atlas.level.projection)
    (hax : a.val ≫ D.atlas.level.level.x.val = M.x.val)
    (hay : a.val ≫ D.atlas.level.level.y.val = M.y.val) :
    CompatibleAt k L D.atlas D.two a.val := by
  let t := (b ≫ E.cover.inclusion) ≫ E.atlas.level.projection
  have label
      (x : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (y : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
      (z : SchemeHomOver t (structureMap (LegendreRing k) (legendre k)))
      (u v : SchemeHomOver (𝟙 (Base (LegendreRing k)))
        (structureMap (LegendreRing k) (legendre k)))
      (hxy : a.val ≫ x.val = z.val)
      (hz : D.atlas.law.nsmul t (L / d) z =
        WeierstrassProjModel.schemeHomOverComp (b ≫ E.cover.inclusion) rfl y)
      (hy : E.cover.inclusion ≫ (E.atlas.law.nsmul E.atlas.level.projection (d / 2) y).val =
        (E.cover.inclusion ≫ E.atlas.level.projection) ≫ v.val)
      (huv : u.val = v.val) :
      a.val ≫ (D.atlas.law.nsmul D.atlas.level.projection (L / 2) x).val =
        (a.val ≫ D.atlas.level.projection) ≫ u.val := by
    have ha : WeierstrassProjModel.schemeHomOverComp a.val a.property x = z := Subtype.ext hxy
    have hn := congrArg Subtype.val (D.atlas.law.nsmul_natural
      D.atlas.level.projection t a.val a.property (L / 2) x)
    rw [ha] at hn
    have hhalf := reduce_half D.atlas.law t hdL hdeven z
    rw [hz] at hhalf
    have hsame (s : SchemeHomOver t (structureMap (LegendreRing k) (legendre k))) :
        D.atlas.law.nsmul t (d / 2) s = E.atlas.law.nsmul t (d / 2) s :=
      congrArg (fun G : Law (LegendreRing k) (legendre k) => G.nsmul t (d / 2) s)
        (atlas_law_eq k D.atlas E.atlas)
    rw [hsame] at hhalf
    have hb := congrArg Subtype.val (E.atlas.law.nsmul_natural E.atlas.level.projection
      t (b ≫ E.cover.inclusion) rfl (d / 2) y)
    calc
      a.val ≫ (D.atlas.law.nsmul _ (L / 2) x).val = (D.atlas.law.nsmul t (L / 2) z).val := hn
      _ = (b ≫ E.cover.inclusion) ≫ (E.atlas.law.nsmul _ (d / 2) y).val :=
        (congrArg Subtype.val hhalf).symm.trans hb.symm
      _ = (a.val ≫ D.atlas.level.projection) ≫ u.val := by
        rw [Category.assoc, hy, ← huv, a.property]
        simp only [Category.assoc]
  exact ⟨label _ _ _ _ _ hax (congrArg FullLevel.x hM) E.cover.compatible.1
      (canonical_labels_eq k D E).1,
    label _ _ _ _ _ hay (congrArg FullLevel.y hM) E.cover.compatible.2
      (canonical_labels_eq k D E).2⟩

include hp hxg hyg in
def coverFiberMarkingEquiv : SchemeHomOver b g ≃
    {M : FullLevel (LegendreRing k) (legendre k) D.atlas.law L
        ((b ≫ E.cover.inclusion) ≫ E.atlas.level.projection) //
      reduceMarking hL hd hdL M = targetMarking k D E b} := by
  let t := (b ≫ E.cover.inclusion) ≫ E.atlas.level.projection
  have hover (a : SchemeHomOver b g) :
      (a.val ≫ D.cover.inclusion) ≫ D.atlas.level.projection = t := by
    rw [Category.assoc, ← hp, ← Category.assoc, a.property]
    rfl
  let mark (a : SchemeHomOver b g) := BaseChange.restrict D.atlas.level.level
    (a.val ≫ D.cover.inclusion) (hover a)
  have red (a : SchemeHomOver b g) :
      reduceMarking hL hd hdL (mark a) = targetMarking k D E b := by
    have label (x : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
        (y : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
        (h : g ≫ E.cover.inclusion ≫ y.val = D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) x).val) :
        D.atlas.law.nsmul t (L / d)
            (WeierstrassProjModel.schemeHomOverComp (a.val ≫ D.cover.inclusion) (hover a) x) =
          WeierstrassProjModel.schemeHomOverComp (b ≫ E.cover.inclusion) rfl y := by
      apply Subtype.ext
      have hn := congrArg Subtype.val (D.atlas.law.nsmul_natural D.atlas.level.projection
        t (a.val ≫ D.cover.inclusion) (hover a) (L / d) x)
      refine hn.symm.trans ?_
      change (a.val ≫ D.cover.inclusion) ≫ _ = (b ≫ E.cover.inclusion) ≫ _
      rw [Category.assoc, ← h, ← Category.assoc, a.property, Category.assoc]
    exact marking_ext (label _ _ hxg) (label _ _ hyg)
  refine Equiv.ofBijective (fun a => ⟨mark a, red a⟩) ⟨?_, ?_⟩
  · intro a a' he
    apply Subtype.ext
    have hm := congrArg Subtype.val he
    apply cover_hom_ext k D
    · exact (Category.assoc _ _ _).symm.trans ((hover a).trans
        ((hover a').symm.trans (Category.assoc _ _ _)))
    · simpa only [mark, BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
        Category.assoc] using congrArg (fun M => M.x.val) hm
    · simpa only [mark, BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
        Category.assoc] using congrArg (fun M => M.y.val) hm
  · intro M
    obtain ⟨a, ha, _⟩ := D.atlas.represents T t M.val
    obtain ⟨c, hc, _⟩ := (D.cover.represents T a.val).mp
      (compatible_of_reduced_marking k hL hd hdeven hdL D E b M.val M.property a ha.1 ha.2)
    have hcproj : c ≫ D.cover.inclusion ≫ D.atlas.level.projection = t := by
      rw [← Category.assoc, hc]; exact a.property
    have label (x : SchemeHomOver D.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
        (y : SchemeHomOver E.atlas.level.projection
        (structureMap (LegendreRing k) (legendre k)))
        (z : SchemeHomOver t (structureMap (LegendreRing k) (legendre k)))
        (h : g ≫ E.cover.inclusion ≫ y.val = D.cover.inclusion ≫
          (D.atlas.law.nsmul D.atlas.level.projection (L / d) x).val)
        (ha : a.val ≫ x.val = z.val)
        (hz : D.atlas.law.nsmul t (L / d) z =
          WeierstrassProjModel.schemeHomOverComp (b ≫ E.cover.inclusion) rfl y) :
        (c ≫ g) ≫ E.cover.inclusion ≫ y.val = b ≫ E.cover.inclusion ≫ y.val := by
      have he : WeierstrassProjModel.schemeHomOverComp a.val a.property x = z := Subtype.ext ha
      have hn := congrArg Subtype.val (D.atlas.law.nsmul_natural D.atlas.level.projection
        t a.val a.property (L / d) x)
      rw [he, hz] at hn
      rw [Category.assoc, h, ← Category.assoc, hc]
      simpa only [WeierstrassProjModel.schemeHomOverComp, Category.assoc] using hn
    have hcg : c ≫ g = b := by
      apply cover_hom_ext k E
      · rw [Category.assoc, hp, hcproj]; rfl
      · exact label _ _ _ hxg ha.1 (congrArg FullLevel.x M.property)
      · exact label _ _ _ hyg ha.2 (congrArg FullLevel.y M.property)
    refine ⟨⟨c, hcg⟩, ?_⟩
    apply Subtype.ext
    apply marking_ext <;> apply Subtype.ext
    · change (c ≫ D.cover.inclusion) ≫ D.atlas.level.level.x.val = M.val.x.val
      rw [hc]; exact ha.1
    · change (c ≫ D.cover.inclusion) ≫ D.atlas.level.level.y.val = M.val.y.val
      rw [hc]; exact ha.2

end CoverFibers

open CoverGeometryR0175

/-- Evaluation on an algebraically closed field identifies actual marking
reduction with reduction of the actual elliptic curve's torsion bases. -/
lemma marking_reduction_fiber_card
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L)
    (t : Base K ⟶ Base R)
    (ht : t = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (N : FullLevel R W G d t) :
    Nat.card {M : FullLevel R W G L t // reduceMarking hL hd hdL M = N} =
        levelDegree L / levelDegree d ∧
      0 < Nat.card {M : FullLevel R W G L t // reduceMarking hL hd hdL M = N} := by
  classical
  subst t
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  have ho : (G.one (𝟙 _)).val = (WeierstrassProjModel.kwZeroSect R W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G ho
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let H := (W.toProjective.baseChange K).toAffine.Point
  have hm (x y : SchemeHomOver t (structureMap R W)) :
      ev K (G.mul t x y) = ev K x + ev K y := hev.1 K x y
  have hz : ev K (G.one t) = 0 := by
    have h := hm (G.one t) (G.one t)
    rw [G.one_mul] at h
    exact (add_left_cancel (a := ev K (G.one t)) ((add_zero _).trans h)).symm
  have card (n : ℕ) (hn : n ≠ 0) :
      Nat.card (Submodule.torsionBy ℤ H (n : ℤ)) = n ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine (Nat.cast_ne_zero.mpr hn) (by norm_num)
  have hcL := card L (Nat.ne_of_gt hL)
  have hcd := card d (Nat.ne_of_gt hd)
  letI : Finite (Submodule.torsionBy ℤ H (L : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcL]; exact pow_ne_zero 2 (Nat.ne_of_gt hL))
  letI : Finite (Submodule.torsionBy ℤ H (d : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcd]; exact pow_ne_zero 2 (Nat.ne_of_gt hd))
  obtain ⟨eL⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (Nat.ne_of_gt hL) (fun n hn => card n (ne_zero_of_dvd_ne_zero (Nat.ne_of_gt hL) hn))
  let eM := fieldMarkEquiv (L := L) (hG := hG) (t := t) (ev := ev K) (hm := hm) (hz := hz)
  let eN := fieldMarkEquiv (L := d) (hG := hG) (t := t) (ev := ev K) (hm := hm) (hz := hz)
  have red (M : FullLevel R W G L t) :
      eN (reduceMarking hL hd hdL M) = Counting.reduceBasis hL hd hdL (eM M) := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact eval_nsmul t (ev K) hm hz M.x (L / d)
    · exact eval_nsmul t (ev K) hm hz M.y (L / d)
  let e : {M : FullLevel R W G L t // reduceMarking hL hd hdL M = N} ≃
      {a // Counting.reduceBasis hL hd hdL a = eN N} :=
    eM.subtypeEquiv (fun M => by rw [← red M]; exact eN.injective.eq_iff.symm)
  have he := Counting.card_reduction_fiber hL hd hdL hcL hcd eL (eN N)
  rw [Nat.card_congr e]
  exact he

/-- Rank equals the number of geometric lifts, with an arbitrary scheme as
target. The reduction to an affine target is the actual pullback along b. -/
lemma finrank_geometric {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (K : Type u) [Field K] [IsAlgClosed K] (b : Base K ⟶ Y) :
    f.finrank (b (IsLocalRing.closedPoint K)) = Nat.card (SchemeHomOver b f) := by
  let p := pullback.snd f b
  let e : SchemeHomOver (𝟙 (Base K)) p ≃ SchemeHomOver b f :=
    { toFun a := ⟨a.val ≫ pullback.fst f b, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, a.property, Category.id_comp]⟩
      invFun a := ⟨pullback.lift a.val (𝟙 _) (by simpa using a.property),
        pullback.lift_snd _ _ _⟩
      left_inv a := by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · exact (pullback.lift_snd _ _ _).trans a.property.symm
      right_inv a := Subtype.ext (pullback.lift_fst _ _ _) }
  have h := finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed p K (RingHom.id K)
  simp only [CommRingCat.ofHom_id, Spec.map_id] at h
  rw [← Scheme.Hom.finrank_pullback_snd f b]
  exact h.trans (Nat.card_congr e)

lemma cover_reduction_degree (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d) (g : D.cover.space ⟶ E.cover.space)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hxg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
    (hyg : g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val) :
    ∀ y, g.finrank y = levelDegree L / levelDegree d ∧ 0 < g.finrank y := by
  obtain ⟨hfin, het⟩ := cover_reduction_finite_etale k D E g hp
  letI := hfin
  letI := het
  intro y
  let K := AlgebraicClosure (E.cover.space.residueField y)
  let b : Base K ⟶ E.cover.space :=
    Spec.map (CommRingCat.ofHom (algebraMap (E.cover.space.residueField y) K)) ≫
      E.cover.space.fromSpecResidueField y
  have hb : b (IsLocalRing.closedPoint K) = y := by
    dsimp only [b]
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply (X := E.cover.space) y _
  let t := (b ≫ E.cover.inclusion) ≫ E.atlas.level.projection
  obtain ⟨α, hα⟩ := Spec.map_surjective t
  letI : Algebra (LegendreRing k) K := α.hom.toAlgebra
  letI : Algebra k K := (α.hom.comp (algebraMap k (LegendreRing k))).toAlgebra
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨hrdom, hrnoeth, _, hrell, _⟩ := legendre_family_geometry k
  letI := hrdom
  letI := hrnoeth
  letI := hrell
  have hm := marking_reduction_fiber_card (LegendreRing k) (legendre k) D.atlas.law
    D.atlas.originLaw K L d hL hd hdL t hα.symm (targetMarking k D E b)
  have he := Nat.card_congr (coverFiberMarkingEquiv k hL hd hdeven hdL D E g hp hxg hyg b)
  rw [← hb, finrank_geometric g K b, he]
  exact hm

/-- The two degree-two quotient maps cancel from the rank comparison.
Positivity of every actual cover fiber also descends surjectivity. -/
lemma quotient_reduction_degree (k : Type u) [Field k] [CharZero k]
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d)
    (g : D.cover.space ⟶ E.cover.space) (f : OpenBase k L D ⟶ OpenBase k d E)
    (hp : g ≫ E.cover.inclusion ≫ E.atlas.level.projection =
      D.cover.inclusion ≫ D.atlas.level.projection)
    (hx : g ≫ E.cover.inclusion ≫ E.atlas.level.level.x.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.x).val)
    (hy : g ≫ E.cover.inclusion ≫ E.atlas.level.level.y.val =
      D.cover.inclusion ≫
        (D.atlas.law.nsmul D.atlas.level.projection (L / d) D.atlas.level.level.y).val)
    (hf : D.quotient.quotient.q ≫ f = g ≫ E.quotient.quotient.q)
    (hk : f ≫ openStructure k d E = openStructure k L D) :
    Surjective f ∧ ∀ y, f.finrank y = levelDegree L / levelDegree d := by
  obtain ⟨hfg, heg⟩ := cover_reduction_finite_etale k D E g hp
  obtain ⟨hff, hef⟩ := quotient_reduction_finite_etale k D E g f hp hf hk
  letI := hfg
  letI := heg
  letI := hff
  letI := hef
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.etale
  letI := E.quotient.quotient.finite
  letI := E.quotient.quotient.etale
  letI := E.quotient.quotient.surjective
  have hg := cover_reduction_degree k hL hd hdeven hdL D E g hp hx hy
  letI : Surjective g := g.one_le_finrank_iff_surjective.mp (fun y => (hg y).2)
  letI : Surjective (D.quotient.quotient.q ≫ f) := by rw [hf]; infer_instance
  refine ⟨Surjective.of_comp D.quotient.quotient.q f, ?_⟩
  intro y
  have h₁ := Scheme.Hom.finrank_comp_of_finrank_eq_const D.quotient.quotient.q f
    2 D.quotient.quotient.degree y
  have h₂ := Scheme.Hom.finrank_comp_of_finrank_eq_const g E.quotient.quotient.q
    (levelDegree L / levelDegree d) (fun z => (hg z).1) y
  rw [hf, h₂, E.quotient.quotient.degree] at h₁
  omega

end LevelForgettingMap

/-- The unique actual map forgetting full even level on the compatible sign
quotients, characterized by both reduced labels on all prescribed test rings. -/
theorem level_forgetting_map
    (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (hL : 3 ≤ L) (_heven : Even L)
    (d : ℕ) (hd : 3 ≤ d) (hdeven : Even d) (hdL : d ∣ L)
    (D : LevelData k L) (E : LevelData k d) :
    ∃! f : Quiver.Hom (OpenBase k L D) (OpenBase k d E), IsReduction k L D E f := by
  have hLpos : 0 < L := by omega
  have hdpos : 0 < d := by omega
  obtain ⟨g, f, hp, hx, hy, hf, hk⟩ :=
    LevelForgettingMap.quotient_reduction_exists k L d hLpos hdpos hdeven hdL D E
  have hr := LevelForgettingMap.quotient_reduction_respects
    k hLpos hd hdeven hdL D E g f hp hx hy hf hk
  obtain ⟨hfin, het⟩ :=
    LevelForgettingMap.quotient_reduction_finite_etale k D E g f hp hf hk
  obtain ⟨hsur, hdeg⟩ := LevelForgettingMap.quotient_reduction_degree
    k hLpos hdpos hdeven hdL D E g f hp hx hy hf hk
  refine ⟨f, ⟨hr, hfin, het, hsur, hdeg⟩, ?_⟩
  intro f' hf'
  exact LevelForgettingMap.reduction_unique k L d hLpos hd hdeven hdL D E f' f hf'.1 hr

#print axioms level_forgetting_map
end ArithmeticThetaLevelCompactificationR0179
