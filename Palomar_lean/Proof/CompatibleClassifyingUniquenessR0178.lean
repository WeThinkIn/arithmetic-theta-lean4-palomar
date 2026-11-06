module

public import OrderedTwoSignRigidityR0178
public import MarkedLegendreAtlasLocalCoverageR0177
public import FullLevelAutomorphismRigidityR0176

@[expose] public section

/-! Uniqueness of compatible marked classifications. Geometric points detect
affine base maps; ordered Legendre coordinates and the actual sign action
identify their quotient images. Full-level rigidity then identifies the family maps. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaCompatibleLevelR0178
namespace CompatibleClassifyingUniqueness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177

/-- Two Cartesian comparisons over the same base map differ by an actual
automorphism of the source. Full level rigidity kills that automorphism. -/
lemma comparison_eq_of_base_eq
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L)
    (M : FullLevel R W G L (𝟙 (Base R)))
    {Y S : Scheme.{u}} (p : Y ⟶ S) (b : Base R ⟶ S)
    (f₁ f₂ : Curve R W ⟶ Y)
    (h₁ : IsPullback f₁ (structureMap R W) p b)
    (h₂ : IsPullback f₂ (structureMap R W) p b)
    (ho : origin R W ≫ f₁ = origin R W ≫ f₂)
    (hx : M.x.val ≫ f₁ = M.x.val ≫ f₂)
    (hy : M.y.val ≫ f₁ = M.y.val ≫ f₂) : f₁ = f₂ := by
  let e : Curve R W ≅ Curve R W := h₁.isoPullback ≪≫ h₂.isoPullback.symm
  have he : e.hom ≫ f₂ = f₁ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]
  have hp : e.hom ≫ structureMap R W = structureMap R W := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd]
  have hs {T : Scheme.{u}} (s : T ⟶ Curve R W) (h : s ≫ f₁ = s ≫ f₂) :
      s ≫ e.hom = s := by
    apply h₂.hom_ext
    · rw [Category.assoc, he, h]
    · rw [Category.assoc, hp]
  have hid := full_level_automorphism_rigidity R W G hG L hL M e hp
    (hs _ ho) (hs _ hx) (hs _ hy)
  rw [← he, hid, Category.id_comp]

/-- Affine morphisms are detected after an injective extension of the source ring. -/
lemma affine_ext {R S K : Type u} [CommRing R] [CommRing S] [CommRing K]
    (σ : R →+* K) (hσ : Function.Injective σ) (a b : Base R ⟶ Base S)
    (h : Spec.map (CommRingCat.ofHom σ) ≫ a = Spec.map (CommRingCat.ofHom σ) ≫ b) :
    a = b := by
  obtain ⟨a', rfl⟩ := Spec.map_surjective a
  obtain ⟨b', rfl⟩ := Spec.map_surjective b
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply hσ
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hh := Spec.map_injective h
  exact CategoryTheory.congr_fun hh x

/-- A finite surjection admits a lift of every geometric point. -/
lemma lift_geometric_point {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q] [Surjective q]
    (b : Base K ⟶ Y) : ∃ a : Base K ⟶ X, a ≫ q = b := by
  let Z := pullback b q
  let p : Z ⟶ Base K := pullback.fst b q
  letI : IsFinite p := inferInstanceAs (IsFinite (pullback.fst b q))
  letI : Surjective p := inferInstanceAs (Surjective (pullback.fst b q))
  letI : Nonempty Z := by
    obtain ⟨z, _⟩ := p.surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  letI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Z).Nonempty) isOpen_univ.isLocallyClosed
  refine ⟨pointOfClosedPoint p z hz ≫ pullback.snd b q, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp, Category.id_comp]

/-- A fixed coefficient map for each actual ring homomorphism. -/
def coefficientMap (k K : Type u) [Field k] [Field K] (α : LegendreRing k →+* K) :
    Curve K ((legendre k).map α) ⟶ Curve (LegendreRing k) (legendre k) :=
  let h := WeierstrassProjModel.exists_isCoefficientHom (legendre k).toProjective α
  AlgebraicGeometry.Proj.map h.choose h.choose_spec.choose

/-- An actual coefficient presentation of a point of the level cover. -/
structure Presentation (k : Type u) [Field k] (L : ℕ) (A : LegendreAtlas k L)
    (K : Type u) [Field K] (α : LegendreRing k →+* K)
    (a : Base K ⟶ A.level.space) where
  law : Law K ((legendre k).map α)
  originLaw : IsOriginLaw K ((legendre k).map α) law
  coeff : Curve K ((legendre k).map α) ⟶ Curve (LegendreRing k) (legendre k)
  coeff_eq : coeff = coefficientMap k K α
  coefficient : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
    (LegendreRing k) (legendre k) A.law K ((legendre k).map α) law α coeff
  marking : FullLevel K ((legendre k).map α) law L (𝟙 (Base K))
  x_coeff : marking.x.val ≫ coeff = a ≫ A.level.level.x.val
  y_coeff : marking.y.val ≫ coeff = a ≫ A.level.level.y.val
  comparison : Curve K ((legendre k).map α) ⟶ A.descent.family.curve
  cartesian : IsPullback comparison (structureMap K ((legendre k).map α))
    A.descent.family.projection (a ≫ A.quotient.q)
  origin_eq : origin K ((legendre k).map α) ≫ comparison =
    (a ≫ A.quotient.q) ≫ (A.descent.family.law.one (𝟙 _)).val
  x_eq : marking.x.val ≫ comparison = (a ≫ A.quotient.q) ≫ A.marking.x.val
  y_eq : marking.y.val ≫ comparison = (a ≫ A.quotient.q) ≫ A.marking.y.val
  coordinates : ∀ (P : Base (LegendreRing k) ⟶ Curve (LegendreRing k) (legendre k))
    (x y : LegendreRing k), HasCoordinates (LegendreRing k) (legendre k) P x y →
    ∃ p : Base K ⟶ Curve K ((legendre k).map α),
      HasCoordinates K ((legendre k).map α) p (α x) (α y) ∧
      p ≫ coeff = Spec.map (CommRingCat.ofHom α) ≫ P

lemma presentation_exists (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (A : LegendreAtlas k L) (K : Type u) [Field K]
    (α : LegendreRing k →+* K) (a : Base K ⟶ A.level.space)
    (ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α)) :
    Nonempty (Presentation k L A K α a) := by
  obtain ⟨hd, hn, hi, he, _, _⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := hi
  letI := he
  let hc := WeierstrassProjModel.exists_isCoefficientHom (legendre k).toProjective α
  let φ := hc.choose
  have hφ := hc.choose_spec.choose
  have hcoef := hc.choose_spec.choose_spec
  let b := AlgebraicGeometry.Proj.map φ hφ
  have hb : IsPullback b (structureMap K ((legendre k).map α))
      (structureMap (LegendreRing k) (legendre k)) (Spec.map (CommRingCat.ofHom α)) :=
    WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
    (legendre k).toProjective α φ hφ hcoef
  have ho : origin K ((legendre k).map α) ≫ b =
      Spec.map (CommRingCat.ofHom α) ≫ origin (LegendreRing k) (legendre k) :=
    OrderedLegendreParameterRigidity.coefficient_origin (legendre k) α φ hφ hcoef
  obtain ⟨H, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      α (structureMap (LegendreRing k) (legendre k))
      (structureMap K ((legendre k).map α)) b hb A.law
  have hH : IsOriginLaw K ((legendre k).map α) H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [hj, A.originLaw.1, Category.assoc, ho]
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (H.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, A.originLaw.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hbase : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      (LegendreRing k) (legendre k) A.law K ((legendre k).map α) H α b :=
    ⟨hb, ho, ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
      α (structureMap K ((legendre k).map α)) b hb A.law H hm hj⟩
  let N := BaseChange.up hbase A.originLaw hH
    (BaseChange.restrict A.level.level a (ha.trans (Category.id_comp _).symm))
  have hx : N.x.val ≫ b = a ≫ A.level.level.x.val := BaseChange.up_x hbase A.originLaw hH _
  have hy : N.y.val ≫ b = a ≫ A.level.level.y.val := BaseChange.up_y hbase A.originLaw hH _
  let d : Curve K ((legendre k).map α) ⟶ coverCurve (LegendreRing k) (legendre k) A.level :=
    pullback.lift b (structureMap K ((legendre k).map α) ≫ a) (by
      rw [Category.assoc, ha]; exact hb.w)
  have hd : IsPullback d (structureMap K ((legendre k).map α))
      (coverToLevel (LegendreRing k) (legendre k) A.level) a := by
    have hout : IsPullback (d ≫ coverToCurve (LegendreRing k) (legendre k) A.level)
        (structureMap K ((legendre k).map α))
        (structureMap (LegendreRing k) (legendre k)) (a ≫ A.level.projection) := by
      simpa only [d, coverToCurve, pullback.lift_fst, ha] using hb
    exact hout.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have hdo : origin K ((legendre k).map α) ≫ d = a ≫
      coverSection (LegendreRing k) (legendre k) A.level (A.law.one A.level.projection) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      rw [ho, A.originLaw.1, ← Category.assoc, ha]
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, BaseChange.origin_over, Category.id_comp]
  have hdx : N.x.val ≫ d = a ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.x := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, d, pullback.lift_fst, coverSection] using hx
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, N.x.property, Category.id_comp]
  have hdy : N.y.val ≫ d = a ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.y := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, d, pullback.lift_fst, coverSection] using hy
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, N.y.property, Category.id_comp]
  refine ⟨⟨H, hH, b, rfl, hbase, N, hx, hy, d ≫ A.descent.comparison,
    hd.paste_horiz A.descent.cartesian, ?_, ?_, ?_, ?_⟩⟩
  · rw [← Category.assoc, hdo, Category.assoc, A.descent.origin_eq, Category.assoc]
  · rw [← Category.assoc, hdx, Category.assoc, A.x_eq, Category.assoc]
  · rw [← Category.assoc, hdy, Category.assoc, A.y_eq, Category.assoc]
  · intro P x y hP
    exact OrderedLegendreParameterRigidity.coefficient_coordinates
      (legendre k) α φ hφ hcoef P x y hP

section PresentationLemmas
variable {k : Type u} [Field k] [CharZero k] {L : ℕ} {A : LegendreAtlas k L}
  {K : Type u} [Field K] {α : LegendreRing k →+* K}
  {a : Base K ⟶ A.level.space}
  (P : Presentation k L A K α a)
  (ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α))

include ha in
lemma nsmul_coeff (s : SchemeHomOver A.level.projection
      (structureMap (LegendreRing k) (legendre k)))
    (t : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)))
    (ht : t.val ≫ P.coeff = a ≫ s.val) (n : ℕ) :
    (P.law.nsmul (𝟙 _) n t).val ≫ P.coeff =
      a ≫ (A.law.nsmul A.level.projection n s).val := by
  letI := (legendre_family_geometry k).1
  have ht' : BaseChange.point P.coefficient (𝟙 _) t =
      WeierstrassProjModel.schemeHomOverComp a
        (ha.trans (Category.id_comp _).symm) s := Subtype.ext ht
  have h := congrArg Subtype.val (BaseChange.point_nsmul P.coefficient (𝟙 _) t n)
  rw [ht'] at h
  have hn := congrArg Subtype.val (A.law.nsmul_natural A.level.projection
    (𝟙 _ ≫ Spec.map (CommRingCat.ofHom α)) a
      (ha.trans (Category.id_comp _).symm) n s)
  exact h.trans hn.symm

include ha in
lemma canonical_points (B : TwoMarking k L A) (hB : CanonicalTwo k L A B)
    (hc : CompatibleAt k L A B a) :
    ∃ p0 p1 : Base K ⟶ Curve K ((legendre k).map α),
      HasCoordinates K ((legendre k).map α) p0 0 0 ∧
      HasCoordinates K ((legendre k).map α) p1 1 0 ∧
      (P.law.nsmul (𝟙 _) (L / 2) P.marking.x).val = p0 ∧
      (P.law.nsmul (𝟙 _) (L / 2) P.marking.y).val = p1 := by
  obtain ⟨p0, hp0, he0⟩ := P.coordinates B.x.val 0 0 hB.1
  obtain ⟨p1, hp1, he1⟩ := P.coordinates B.y.val 1 0 hB.2
  refine ⟨p0, p1, by simpa only [map_zero] using hp0,
    by simpa only [map_zero, map_one] using hp1, ?_, ?_⟩
  · apply P.coefficient.1.hom_ext
    · rw [nsmul_coeff P ha _ _ P.x_coeff, hc.1, ha, he0]
    · exact (P.law.nsmul _ _ _).property.trans hp0.1.symm
  · apply P.coefficient.1.hom_ext
    · rw [nsmul_coeff P ha _ _ P.y_coeff, hc.2, ha, he1]
    · exact (P.law.nsmul _ _ _).property.trans hp1.1.symm

omit [CharZero k] in
/-- The Cartesian square in a classification lifts the same presentation back
to the original family, including its origin and both labels. -/
lemma comparison_to_source
    {R : Type u} [CommRing R] {W : WeierstrassCurve R} {G : Law R W}
    (M : FullLevel R W G L (𝟙 (Base R)))
    (i : Base K ⟶ Base R) (b : Base R ⟶ Base A.quotient.ring)
    (f : Curve R W ⟶ A.descent.family.curve)
    (hf : IsPullback f (structureMap R W) A.descent.family.projection b)
    (ho : origin R W ≫ f = b ≫ (A.descent.family.law.one (𝟙 _)).val)
    (hx : M.x.val ≫ f = b ≫ A.marking.x.val)
    (hy : M.y.val ≫ f = b ≫ A.marking.y.val)
    (hai : a ≫ A.quotient.q = i ≫ b) :
    ∃ g : Curve K ((legendre k).map α) ⟶ Curve R W,
      IsPullback g (structureMap K ((legendre k).map α)) (structureMap R W) i ∧
      origin K ((legendre k).map α) ≫ g = i ≫ origin R W ∧
      P.marking.x.val ≫ g = i ≫ M.x.val ∧
      P.marking.y.val ≫ g = i ≫ M.y.val := by
  let g := hf.lift P.comparison (structureMap K ((legendre k).map α) ≫ i)
    (by rw [P.cartesian.w, hai, Category.assoc])
  have hgf : g ≫ f = P.comparison := hf.lift_fst _ _ _
  have hgp : g ≫ structureMap R W = structureMap K ((legendre k).map α) ≫ i :=
    hf.lift_snd _ _ _
  have hg : IsPullback g (structureMap K ((legendre k).map α)) (structureMap R W) i := by
    have hout : IsPullback (g ≫ f) (structureMap K ((legendre k).map α))
        A.descent.family.projection (i ≫ b) := by
      rw [hgf, ← hai]; exact P.cartesian
    exact hout.of_right hgp hf
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · apply hf.hom_ext
    · simp only [Category.assoc, hgf, P.origin_eq, hai, ho]
    · rw [Category.assoc, hgp, ← Category.assoc, BaseChange.origin_over,
        Category.id_comp, Category.assoc, BaseChange.origin_over, Category.comp_id]
  · apply hf.hom_ext
    · simp only [Category.assoc, hgf, P.x_eq, hai, hx]
    · rw [Category.assoc, hgp, ← Category.assoc, P.marking.x.property,
        Category.id_comp, Category.assoc, M.x.property, Category.comp_id]
  · apply hf.hom_ext
    · simp only [Category.assoc, hgf, P.y_eq, hai, hy]
    · rw [Category.assoc, hgp, ← Category.assoc, P.marking.y.property,
        Category.id_comp, Category.assoc, M.y.property, Category.comp_id]

end PresentationLemmas

lemma pointed_iso_nsmul {K : Type u} [Field K] (W V : WeierstrassCurve K)
    [W.IsElliptic] (G : Law K W) (H : Law K V)
    (hG : IsOriginLaw K W G) (hH : IsOriginLaw K V H)
    (e : Curve K W ≅ Curve K V)
    (hp : e.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K V)
    (x : SchemeHomOver (𝟙 (Base K)) (structureMap K W))
    (y : SchemeHomOver (𝟙 (Base K)) (structureMap K V))
    (hxy : x.val ≫ e.hom = y.val) (n : ℕ) :
    (G.nsmul (𝟙 _) n x).val ≫ e.hom = (H.nsmul (𝟙 _) n y).val := by
  have hb : IsPullback e.hom (structureMap K W) (structureMap K V)
      (baseMap K K (RingHom.id K)) := by
    simp only [baseMap, CommRingCat.ofHom_id, Spec.map_id]
    apply IsPullback.of_horiz_isIso
    constructor
    simpa only [baseMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using hp
  have hbase := MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    H G hH hG (RingHom.id K) e.hom hb
      (by simpa only [baseMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using ho)
  open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential in
  rw [← comp_schemeNsmul, Category.assoc, hbase.2.2, ← Category.assoc, hxy,
    comp_schemeNsmul]

lemma parameter_hom_ext {k K : Type u} [Field k] [CommRing K]
    (α β : LegendreRing k →+* K)
    (hscalar : α.comp (algebraMap k (LegendreRing k)) =
      β.comp (algebraMap k (LegendreRing k)))
    (hpar : α (parameter k) = β (parameter k)) : α = β := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro c
    exact RingHom.congr_fun hscalar c
  · exact hpar

lemma mapped_sign_rigidity (k K : Type u) [Field k] [Field K] [CharZero K]
    (α : LegendreRing k →+* K)
    (G : Law K ((legendre k).map α)) (hG : IsOriginLaw K ((legendre k).map α) G)
    (p0 p1 : Base K ⟶ Curve K ((legendre k).map α))
    (hp0 : HasCoordinates K ((legendre k).map α) p0 0 0)
    (hp1 : HasCoordinates K ((legendre k).map α) p1 1 0)
    (e : Curve K ((legendre k).map α) ≅ Curve K ((legendre k).map α))
    (he : e.hom ≫ structureMap K ((legendre k).map α) = structureMap K ((legendre k).map α))
    (ho : origin K ((legendre k).map α) ≫ e.hom = origin K ((legendre k).map α))
    (h0 : p0 ≫ e.hom = p0) (h1 : p1 ≫ e.hom = p1) :
    e.hom = 𝟙 _ ∨ e.hom = inversion K ((legendre k).map α) G := by
  have hw : (legendre k).map α = legendreAt K (α (parameter k)) := by
    ext <;> simp [legendre, legendreAt]
  have hu : IsUnit (α (parameter k) * (α (parameter k) - 1)) := by
    have h := (IsLocalization.Away.algebraMap_isUnit
      (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) : Polynomial k)).map α
    simpa only [map_mul, map_sub, map_one, parameter] using h
  revert G hG p0 p1 hp0 hp1 e he ho h0 h1
  rw [hw]
  exact ordered_two_sign_rigidity K (α (parameter k)) hu

lemma coordinates_ext {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (p q : Base R ⟶ Curve R W) (x y : R)
    (hp : HasCoordinates R W p x y) (hq : HasCoordinates R W q x y) : p = q := by
  obtain ⟨hp, χ, rfl, χx, χy⟩ := hp
  obtain ⟨hq, ψ, rfl, ψx, ψy⟩ := hq
  have he : χ = ψ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.WMLocal.zChart_ringHom_ext
      W χ ψ (RingHom.ext (fun t =>
        (OrderedLegendreParameterRigidity.evaluation_scalar W χ hp t).trans
          (OrderedLegendreParameterRigidity.evaluation_scalar W ψ hq t).symm))
      (χx.trans ψx.symm) (χy.trans ψy.symm)
  rw [he]

lemma inverse_coeff {k : Type u} [Field k] [CharZero k] {L : ℕ}
    {A : LegendreAtlas k L} {K : Type u} [Field K]
    {α : LegendreRing k →+* K} {a : Base K ⟶ A.level.space}
    (P : Presentation k L A K α a)
    (ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α))
    (s : SchemeHomOver A.level.projection (structureMap (LegendreRing k) (legendre k)))
    (t : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)))
    (ht : t.val ≫ P.coeff = a ≫ s.val) :
    (P.law.inv (𝟙 _) t).val ≫ P.coeff = a ≫ (A.law.inv A.level.projection s).val := by
  letI := (legendre_family_geometry k).1
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.toAlgebra
  letI : ((legendre k).map α).IsElliptic := inferInstance
  letI := P.law.pointGroup (𝟙 (Base K))
  letI := A.law.pointGroup (𝟙 (Base K) ≫ baseMap (LegendreRing k) K α)
  let m : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)) →*
      SchemeHomOver (𝟙 (Base K) ≫ baseMap (LegendreRing k) K α)
        (structureMap (LegendreRing k) (legendre k)) := {
    toFun := BaseChange.point P.coefficient (𝟙 _)
    map_one' := BaseChange.point_one P.coefficient A.originLaw P.originLaw _
    map_mul' := BaseChange.point_mul P.coefficient A.originLaw P.originLaw _ }
  have h := congrArg Subtype.val (map_inv m t)
  have ht' : BaseChange.point P.coefficient (𝟙 _) t =
      WeierstrassProjModel.schemeHomOverComp a
        (ha.trans (Category.id_comp _).symm) s := Subtype.ext ht
  change (P.law.inv (𝟙 _) t).val ≫ P.coeff =
    (A.law.inv _ (BaseChange.point P.coefficient (𝟙 _) t)).val at h
  rw [ht'] at h
  exact h.trans (congrArg Subtype.val
    (FullLevelFreeSignR0176.inverse_natural A.law A.level.projection
      (𝟙 _ ≫ baseMap (LegendreRing k) K α) a
        (ha.trans (Category.id_comp _).symm) s)).symm

lemma presentations_same_quotient {k : Type u} [Field k] [CharZero k]
    (L : ℕ) (A : LegendreAtlas k L) (B : TwoMarking k L A)
    (hB : CanonicalTwo k L A B) (K : Type u) [Field K] [CharZero K]
    (α β : LegendreRing k →+* K) (a c : Base K ⟶ A.level.space)
    (ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α))
    (hc : c ≫ A.level.projection = Spec.map (CommRingCat.ofHom β))
    (hscalar : α.comp (algebraMap k (LegendreRing k)) =
      β.comp (algebraMap k (LegendreRing k)))
    (hca : CompatibleAt k L A B a) (hcc : CompatibleAt k L A B c)
    (P : Presentation k L A K α a) (T : Presentation k L A K β c)
    (e : Curve K ((legendre k).map α) ≅ Curve K ((legendre k).map β))
    (he : e.hom ≫ structureMap K ((legendre k).map β) =
      structureMap K ((legendre k).map α))
    (ho : origin K ((legendre k).map α) ≫ e.hom = origin K ((legendre k).map β))
    (hx : P.marking.x.val ≫ e.hom = T.marking.x.val)
    (hy : P.marking.y.val ≫ e.hom = T.marking.y.val) :
    a ≫ A.quotient.q = c ≫ A.quotient.q := by
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.toAlgebra
  letI : ((legendre k).map α).IsElliptic := inferInstance
  obtain ⟨p0, p1, hp0, hp1, hn0, hn1⟩ := canonical_points P ha B hB hca
  obtain ⟨q0, q1, hq0, hq1, hm0, hm1⟩ := canonical_points T hc B hB hcc
  have h0 : p0 ≫ e.hom = q0 := by
    rw [← hn0, ← hm0]
    exact pointed_iso_nsmul _ _ P.law T.law P.originLaw T.originLaw e he ho _ _ hx _
  have h1 : p1 ≫ e.hom = q1 := by
    rw [← hn1, ← hm1]
    exact pointed_iso_nsmul _ _ P.law T.law P.originLaw T.originLaw e he ho _ _ hy _
  have hpar : α (parameter k) = β (parameter k) :=
    OrderedLegendreParameterRigidity.local_a4 _ _ p0 p1 q0 q1 hp0 hp1 hq0 hq1 e he ho h0 h1
  have hab := parameter_hom_ext α β hscalar hpar
  subst β
  have hq0p : q0 = p0 := coordinates_ext _ _ _ 0 0 hq0 hp0
  have hq1p : q1 = p1 := coordinates_ext _ _ _ 1 0 hq1 hp1
  have hcoeff : P.coeff = T.coeff := P.coeff_eq.trans T.coeff_eq.symm
  rcases mapped_sign_rigidity k K α P.law P.originLaw p0 p1 hp0 hp1 e he ho
      (h0.trans hq0p) (h1.trans hq1p) with hid | hinv
  · have hax : a ≫ A.level.level.x.val = c ≫ A.level.level.x.val := by
      rw [← P.x_coeff, ← T.x_coeff, hcoeff]
      congr 1
      simpa only [hid, Category.comp_id] using hx
    have hay : a ≫ A.level.level.y.val = c ≫ A.level.level.y.val := by
      rw [← P.y_coeff, ← T.y_coeff, hcoeff]
      congr 1
      simpa only [hid, Category.comp_id] using hy
    rw [BaseChange.represents_ext A.represents a c ha hc hax hay]
  · have hs (s : SchemeHomOver A.level.projection
        (structureMap (LegendreRing k) (legendre k)))
        (t : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)))
        (v : SchemeHomOver (𝟙 (Base K)) (structureMap K ((legendre k).map α)))
        (ht : t.val ≫ P.coeff = a ≫ s.val) (hv : t.val ≫ e.hom = v.val) :
        v.val ≫ T.coeff = a ≫ (A.law.inv A.level.projection s).val := by
      rw [← hv, hinv, OrderedTwoSignRigidity.comp_inversion, ← hcoeff]
      exact inverse_coeff P ha s t ht
    have hax : (a ≫ A.sign.map) ≫ A.level.level.x.val = c ≫ A.level.level.x.val := by
      rw [Category.assoc, A.sign.x_eq, ← T.x_coeff]
      exact (hs _ _ _ P.x_coeff hx).symm
    have hay : (a ≫ A.sign.map) ≫ A.level.level.y.val = c ≫ A.level.level.y.val := by
      rw [Category.assoc, A.sign.y_eq, ← T.y_coeff]
      exact (hs _ _ _ P.y_coeff hy).symm
    have heq := BaseChange.represents_ext A.represents (a ≫ A.sign.map) c
      (by rw [Category.assoc, A.sign.over_eq]; exact ha) hc hax hay
    rw [← heq, Category.assoc, A.quotient.invariant]

lemma compatible_comp {k : Type u} [Field k] {L : ℕ} {A : LegendreAtlas k L}
    (B : TwoMarking k L A) (C : CompatibleCover k L A B)
    {T : Scheme.{u}} (a : T ⟶ C.space) : CompatibleAt k L A B (a ≫ C.inclusion) := by
  constructor
  · simpa only [Category.assoc] using congrArg (fun z => a ≫ z) C.compatible.1
  · simpa only [Category.assoc] using congrArg (fun z => a ≫ z) C.compatible.2

lemma base_eq_at_geometric_point (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (A : LegendreAtlas k L) (B : TwoMarking k L A)
    (hB : CanonicalTwo k L A B) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C)
    (R : Type u) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (b₁ b₂ : Base R ⟶ Base Q.quotient.ring)
    (f₁ f₂ : Curve R W ⟶ A.descent.family.curve)
    (h₁ : Classifies k L A B C Q R W G M b₁ f₁)
    (h₂ : Classifies k L A B C Q R W G M b₂ f₂)
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (i : Base K ⟶ Base R) : i ≫ b₁ = i ≫ b₂ := by
  letI := Q.quotient.finite
  letI := Q.quotient.surjective
  obtain ⟨a₁, ha₁⟩ := lift_geometric_point Q.quotient.q (i ≫ b₁)
  obtain ⟨a₂, ha₂⟩ := lift_geometric_point Q.quotient.q (i ≫ b₂)
  let a := a₁ ≫ C.inclusion
  let c := a₂ ≫ C.inclusion
  have hai : a ≫ A.quotient.q = i ≫ (b₁ ≫ Q.inclusion) := by
    dsimp only [a]
    rw [Category.assoc, Q.cartesian.w, ← Category.assoc, ha₁, Category.assoc]
  have hci : c ≫ A.quotient.q = i ≫ (b₂ ≫ Q.inclusion) := by
    dsimp only [c]
    rw [Category.assoc, Q.cartesian.w, ← Category.assoc, ha₂, Category.assoc]
  let α : LegendreRing k →+* K := (Spec.preimage (a ≫ A.level.projection)).hom
  let β : LegendreRing k →+* K := (Spec.preimage (c ≫ A.level.projection)).hom
  have ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α) :=
    (Spec.map_preimage _).symm
  have hc : c ≫ A.level.projection = Spec.map (CommRingCat.ofHom β) :=
    (Spec.map_preimage _).symm
  have hascalar : (a ≫ A.level.projection) ≫ legendreBaseMap k =
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    calc
      _ = (a ≫ A.quotient.q) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) := by
        simp only [Category.assoc, A.quotient.over_eq]
      _ = _ := by
        rw [hai]
        simp only [Category.assoc, Q.over_eq, h₁.1]
  have hcscalar : (c ≫ A.level.projection) ≫ legendreBaseMap k =
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    calc
      _ = (c ≫ A.quotient.q) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) := by
        simp only [Category.assoc, A.quotient.over_eq]
      _ = _ := by
        rw [hci]
        simp only [Category.assoc, Q.over_eq, h₂.1]
  have hscalar : α.comp (algebraMap k (LegendreRing k)) =
      β.comp (algebraMap k (LegendreRing k)) := by
    have h : Spec.map (CommRingCat.ofHom (α.comp (algebraMap k (LegendreRing k)))) =
        Spec.map (CommRingCat.ofHom (β.comp (algebraMap k (LegendreRing k)))) := by
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        ← ha, ← hc]
      exact hascalar.trans hcscalar.symm
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨P⟩ := presentation_exists k L A K α a ha
  obtain ⟨T⟩ := presentation_exists k L A K β c hc
  obtain ⟨g₁, hg₁, ho₁, hx₁, hy₁⟩ := comparison_to_source P M i (b₁ ≫ Q.inclusion) f₁
    h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2 hai
  obtain ⟨g₂, hg₂, ho₂, hx₂, hy₂⟩ := comparison_to_source T M i (b₂ ≫ Q.inclusion) f₂
    h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 h₂.2.2.2.2 hci
  let e : Curve K ((legendre k).map α) ≅ Curve K ((legendre k).map β) :=
    hg₁.isoPullback ≪≫ hg₂.isoPullback.symm
  have heg : e.hom ≫ g₂ = g₁ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]
  have hep : e.hom ≫ structureMap K ((legendre k).map β) =
      structureMap K ((legendre k).map α) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd]
  have heo : origin K ((legendre k).map α) ≫ e.hom = origin K ((legendre k).map β) := by
    apply hg₂.hom_ext
    · rw [Category.assoc, heg, ho₁, ho₂]
    · rw [Category.assoc, hep, BaseChange.origin_over, BaseChange.origin_over]
  have hex : P.marking.x.val ≫ e.hom = T.marking.x.val := by
    apply hg₂.hom_ext
    · rw [Category.assoc, heg, hx₁, hx₂]
    · rw [Category.assoc, hep, P.marking.x.property, T.marking.x.property]
  have hey : P.marking.y.val ≫ e.hom = T.marking.y.val := by
    apply hg₂.hom_ext
    · rw [Category.assoc, heg, hy₁, hy₂]
    · rw [Category.assoc, hep, P.marking.y.property, T.marking.y.property]
  have heq := presentations_same_quotient L A B hB K α β a c ha hc hscalar
    (compatible_comp B C a₁) (compatible_comp B C a₂) P T e hep heo hex hey
  letI := Q.openImmersion
  apply (cancel_mono Q.inclusion).mp
  simpa only [Category.assoc] using hai.symm.trans (heq.trans hci)

end CompatibleClassifyingUniqueness
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open CompatibleClassifyingUniqueness

/-- Both maps of a compatible marked Cartesian classification are unique. -/
theorem compatible_classifying_uniqueness :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A), ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B → ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (b₁ b₂ : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeDiscriminantR0171.Base Q.quotient.ring)) (f₁ f₂ : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve R W) A.descent.family.curve), ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q R W G M b₁ f₁ → ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q R W G M b₂ f₂ → b₁ = b₂ ∧ f₁ = f₂ := by
  intro k _ _ L hL _heven A B hB C Q R _ _ _ _ _ _ W _ G hG M b₁ b₂ f₁ f₂ h₁ h₂
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  let K := AlgebraicClosure (FractionRing R)
  let σ : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hσ : Function.Injective σ :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hb : b₁ = b₂ := affine_ext σ hσ b₁ b₂
    (base_eq_at_geometric_point k L A B hB C Q R W G M b₁ b₂ f₁ f₂ h₁ h₂ K
      (Spec.map (CommRingCat.ofHom σ)))
  subst b₂
  refine ⟨rfl, comparison_eq_of_base_eq R W G hG L hL M
    A.descent.family.projection (b₁ ≫ Q.inclusion) f₁ f₂ h₁.2.1 h₂.2.1 ?_ ?_ ?_⟩
  · exact h₁.2.2.1.trans h₂.2.2.1.symm
  · exact h₁.2.2.2.1.trans h₂.2.2.2.1.symm
  · exact h₁.2.2.2.2.trans h₂.2.2.2.2.symm

#print axioms compatible_classifying_uniqueness
end ArithmeticThetaCompatibleLevelR0178
