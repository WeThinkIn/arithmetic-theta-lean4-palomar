module

public import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
public import ArbitraryFullLevelRigidityR0202
public import ArbitraryOrderedParameterR0202
public import CompatibleClassifyingUniquenessR0178

@[expose] public section

/-! Uniqueness of arbitrary-affine marked classifications. Exact ordered
parameters are compared on a common finite étale cover. The actual sign relation
and unramified local lifting identify the base maps without reducedness.
Full-level rigidity then identifies the family maps. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202.ClassifyingUniqueness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaCompatibleLevelR0178

lemma comparison_eq_of_base_eq
    (R : Type u) [CommRing R] [Algebra ℚ R]
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
  have hid := arbitrary_full_level_rigidity R W G hG L hL M e hp
    (hs _ ho) (hs _ hx) (hs _ hy)
  rw [← he, hid, Category.id_comp]

def coefficientMap (k K : Type u) [Field k] [CommRing K] (α : LegendreRing k →+* K) :
    Curve K ((legendre k).map α) ⟶ Curve (LegendreRing k) (legendre k) :=
  let h := WeierstrassProjModel.exists_isCoefficientHom (legendre k).toProjective α
  AlgebraicGeometry.Proj.map h.choose h.choose_spec.choose

/-- An actual coefficient presentation of a point of the level cover. -/
structure Presentation (k : Type u) [Field k] (L : ℕ) (A : LegendreAtlas k L)
    (K : Type u) [CommRing K] (α : LegendreRing k →+* K)
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
    (L : ℕ) (A : LegendreAtlas k L) (K : Type u) [CommRing K]
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
  obtain ⟨H, hH, hbase, N, hx, hy⟩ := FullLevelRigidity.transport_level
    (legendre k) ((legendre k).map α) A.law A.originLaw α b hb ho L
    (BaseChange.restrict A.level.level a ha)
  change N.x.val ≫ b = a ≫ A.level.level.x.val at hx
  change N.y.val ≫ b = a ≫ A.level.level.y.val at hy
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
  {K : Type u} [CommRing K] {α : LegendreRing k →+* K}
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
  open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential in
  calc
    _ = t.val ≫ P.coeff ≫ A.law.schemeNsmul n := by
      rw [← comp_schemeNsmul, Category.assoc, P.coefficient.2.2]
    _ = a ≫ (A.law.nsmul A.level.projection n s).val := by
      rw [← Category.assoc, ht, Category.assoc, comp_schemeNsmul]

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


/-- Origin laws on the actual smooth Weierstrass model have the same operations
on all scheme-valued points; this retains nilpotent test directions. -/
lemma origin_law_mul_eq {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G H : Law R W)
    (hG : IsOriginLaw R W G) (hH : IsOriginLaw R W H)
    {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t (structureMap R W)) :
    G.mul t x y = H.mul t x y := by
  open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree in
  have he : toGRJ G = toGRJ H :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
      (BaseChange.geometry R W G) _ _ (Subtype.ext ((hG.1 _).trans (hH.1 _).symm))
  exact congrArg (fun J => J.mul t x y) he

lemma pointed_iso_nsmul {R : Type u} [CommRing R]
    (W V : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (H : Law R V)
    (hG : IsOriginLaw R W G) (hH : IsOriginLaw R V H)
    (e : Curve R W ≅ Curve R V)
    (hp : e.hom ≫ structureMap R V = structureMap R W)
    (ho : origin R W ≫ e.hom = origin R V)
    (x : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (y : SchemeHomOver (𝟙 (Base R)) (structureMap R V))
    (hxy : x.val ≫ e.hom = y.val) (n : ℕ) :
    (G.nsmul (𝟙 _) n x).val ≫ e.hom = (H.nsmul (𝟙 _) n y).val := by
  have hb : IsPullback e.hom (structureMap R W) (structureMap R V)
      (baseMap R R (RingHom.id R)) := by
    simp only [baseMap, CommRingCat.ofHom_id, Spec.map_id]
    apply IsPullback.of_horiz_isIso
    constructor
    simpa only [Category.comp_id] using hp
  obtain ⟨J, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      (RingHom.id R) (structureMap R V) (structureMap R W) e.hom hb H
  have hJ : IsOriginLaw R W J := by
    constructor
    · intro T t
      apply (cancel_mono e.hom).mp
      simp only [hj, hH.1, Category.assoc, ho,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
    · intro T t a b
      apply Subtype.ext
      apply (cancel_mono e.hom).mp
      rw [hm, hm, hH.2]
  have hjn : J.nsmul (𝟙 _) n x = G.nsmul (𝟙 _) n x := by
    induction n with
    | zero => exact Subtype.ext ((hJ.1 _).trans (hG.1 _).symm)
    | succ n ih => rw [J.nsmul_succ, G.nsmul_succ,
        origin_law_mul_eq W J G hJ hG, ih]
  have hn := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    (RingHom.id R) (structureMap R W) e.hom hb H J hm hj
  open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential in
  calc
    _ = (J.nsmul (𝟙 _) n x).val ≫ e.hom := by rw [hjn]
    _ = x.val ≫ e.hom ≫ H.schemeNsmul n := by
      rw [← comp_schemeNsmul, Category.assoc, hn]
    _ = _ := by rw [← Category.assoc, hxy, comp_schemeNsmul]

lemma mapped_parameter {k R : Type u} [Field k] [CommRing R] [Algebra ℚ R]
    (α β : LegendreRing k →+* R)
    (p0 p1 : Base R ⟶ Curve R ((legendre k).map α))
    (q0 q1 : Base R ⟶ Curve R ((legendre k).map β))
    (hp0 : HasCoordinates R ((legendre k).map α) p0 0 0)
    (hp1 : HasCoordinates R ((legendre k).map α) p1 1 0)
    (hq0 : HasCoordinates R ((legendre k).map β) q0 0 0)
    (hq1 : HasCoordinates R ((legendre k).map β) q1 1 0)
    (e : Curve R ((legendre k).map α) ≅ Curve R ((legendre k).map β))
    (he : e.hom ≫ structureMap R ((legendre k).map β) = structureMap R ((legendre k).map α))
    (ho : origin R ((legendre k).map α) ≫ e.hom = origin R ((legendre k).map β))
    (h0 : p0 ≫ e.hom = q0) (h1 : p1 ≫ e.hom = q1) :
    α (parameter k) = β (parameter k) := by
  have hw (γ : LegendreRing k →+* R) :
      (legendre k).map γ = legendreAt R (γ (parameter k)) := by
    ext <;> simp [legendre, legendreAt]
  have hu (γ : LegendreRing k →+* R) : IsUnit (γ (parameter k) * (γ (parameter k) - 1)) := by
    have h := (IsLocalization.Away.algebraMap_isUnit
      (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) : Polynomial k)).map γ
    simpa only [map_mul, map_sub, map_one, parameter] using h
  revert p0 p1 q0 q1 hp0 hp1 hq0 hq1 e he ho h0 h1
  rw [hw α, hw β]
  exact arbitrary_ordered_parameter R (α (parameter k)) (β (parameter k)) (hu α) (hu β)

lemma presentations_parameter {k R : Type u} [Field k] [CharZero k]
    [CommRing R] [Algebra ℚ R] (L : ℕ) (A : LegendreAtlas k L)
    (B : TwoMarking k L A) (hB : CanonicalTwo k L A B)
    (α β : LegendreRing k →+* R) (a c : Base R ⟶ A.level.space)
    (ha : a ≫ A.level.projection = Spec.map (CommRingCat.ofHom α))
    (hc : c ≫ A.level.projection = Spec.map (CommRingCat.ofHom β))
    (hscalar : α.comp (algebraMap k (LegendreRing k)) = β.comp (algebraMap k (LegendreRing k)))
    (hca : CompatibleAt k L A B a) (hcc : CompatibleAt k L A B c)
    (P : Presentation k L A R α a) (T : Presentation k L A R β c)
    (e : Curve R ((legendre k).map α) ≅ Curve R ((legendre k).map β))
    (he : e.hom ≫ structureMap R ((legendre k).map β) = structureMap R ((legendre k).map α))
    (ho : origin R ((legendre k).map α) ≫ e.hom = origin R ((legendre k).map β))
    (hx : P.marking.x.val ≫ e.hom = T.marking.x.val)
    (hy : P.marking.y.val ≫ e.hom = T.marking.y.val) : α = β := by
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) R := α.toAlgebra
  letI : ((legendre k).map α).IsElliptic := inferInstance
  obtain ⟨p0, p1, hp0, hp1, hn0, hn1⟩ := canonical_points P ha B hB hca
  obtain ⟨q0, q1, hq0, hq1, hm0, hm1⟩ := canonical_points T hc B hB hcc
  have h0 : p0 ≫ e.hom = q0 := by
    rw [← hn0, ← hm0]
    exact pointed_iso_nsmul _ _ P.law T.law P.originLaw T.originLaw e he ho _ _ hx _
  have h1 : p1 ≫ e.hom = q1 := by
    rw [← hn1, ← hm1]
    exact pointed_iso_nsmul _ _ P.law T.law P.originLaw T.originLaw e he ho _ _ hy _
  exact CompatibleClassifyingUniqueness.parameter_hom_ext α β hscalar
    (mapped_parameter α β p0 p1 q0 q1 hp0 hp1 hq0 hq1 e he ho h0 h1)

/-- A field-valued point of the actual sign relation selects one of its two
open branches. This claim is used only after residue-field specialization. -/
lemma field_sign_orbit {k F : Type u} [Field k] [Field F]
    {X : Scheme.{u}} {p : X ⟶ Base k} {σ : X ⟶ X}
    (Q : SignQuotient k p σ) (a c : Base F ⟶ X)
    (h : a ≫ Q.q = c ≫ Q.q) : a = c ∨ a ≫ σ = c := by
  let d : Base F ⟶ X ⨿ X := pullback.lift a c h ≫ Q.relation.inv
  have hd : d ≫ Q.relation.hom = pullback.lift a c h := by
    simp only [d, Category.assoc, Q.relation.inv_hom_id, Category.comp_id]
  have branch (j : X ⟶ X ⨿ X) [IsOpenImmersion j]
      (z : X) (hz : j z = d (IsLocalRing.closedPoint F)) :
      ∃ b : Base F ⟶ X, b ≫ j = d := by
    have hr : Set.range d ⊆ Set.range j := by
      rintro _ ⟨v, rfl⟩
      exact ⟨z, hz.trans (congrArg d (Subsingleton.elim _ _))⟩
    exact ⟨IsOpenImmersion.lift j d hr, IsOpenImmersion.lift_fac j d hr⟩
  obtain ⟨z | z, hz⟩ := (coprodMk X X).surjective (d (IsLocalRing.closedPoint F))
  · obtain ⟨b, hb⟩ := branch coprod.inl z (by simpa only [coprodMk_inl] using hz)
    have hb' : (b ≫ coprod.inl) ≫ Q.relation.hom = pullback.lift a c h := by rw [hb, hd]
    have hba : b = a := by
      have hh := congrArg (fun f => f ≫ pullback.fst Q.q Q.q) hb'
      simpa only [Category.assoc, Q.left_fst, Category.comp_id, pullback.lift_fst] using hh
    have hbc : b = c := by
      have hh := congrArg (fun f => f ≫ pullback.snd Q.q Q.q) hb'
      simpa only [Category.assoc, Q.left_snd, Category.comp_id, pullback.lift_snd] using hh
    exact Or.inl (hba.symm.trans hbc)
  · obtain ⟨b, hb⟩ := branch coprod.inr z (by simpa only [coprodMk_inr] using hz)
    have hb' : (b ≫ coprod.inr) ≫ Q.relation.hom = pullback.lift a c h := by rw [hb, hd]
    have hba : b = a := by
      have hh := congrArg (fun f => f ≫ pullback.fst Q.q Q.q) hb'
      simpa only [Category.assoc, Q.right_fst, Category.comp_id, pullback.lift_fst] using hh
    have hbc : b ≫ σ = c := by
      have hh := congrArg (fun f => f ≫ pullback.snd Q.q Q.q) hb'
      simpa only [Category.assoc, Q.right_snd, pullback.lift_snd] using hh
    exact Or.inr (by rw [← hba]; exact hbc)
lemma parameter_eq_of_lifts (k : Type u) [Field k] [CharZero k]
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
    (K : Type u) [CommRing K] [Algebra ℚ K]
    (i : Base K ⟶ Base R) (a₁ a₂ : Base K ⟶ C.space)
    (ha₁ : a₁ ≫ Q.quotient.q = i ≫ b₁)
    (ha₂ : a₂ ≫ Q.quotient.q = i ≫ b₂) :
    a₁ ≫ C.inclusion ≫ A.level.projection = a₂ ≫ C.inclusion ≫ A.level.projection := by
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
  have hab := presentations_parameter L A B hB α β a c ha hc hscalar
    (CompatibleClassifyingUniqueness.compatible_comp B C a₁)
    (CompatibleClassifyingUniqueness.compatible_comp B C a₂) P T e hep heo hex hey
  change a ≫ A.level.projection = c ≫ A.level.projection
  rw [ha, hc, hab]

/-- The sign choice is made on a local test ring using the actual torsor
relation on its residue field; unramifiedness retains nilpotent information. -/
lemma local_quotient_eq {k S : Type u} [Field k] [CharZero k]
    [CommRing S] [IsLocalRing S] (L : ℕ) (A : LegendreAtlas k L)
    (B : TwoMarking k L A) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C) (a c : Base S ⟶ C.space)
    (hp : a ≫ C.inclusion ≫ A.level.projection = c ≫ C.inclusion ≫ A.level.projection)
    (hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ a ≫ Q.quotient.q =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ c ≫ Q.quotient.q) :
    a ≫ Q.quotient.q = c ≫ Q.quotient.q := by
  letI := C.etale
  let t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))
  have hr : (t ≫ a) ≫ Q.quotient.q = (t ≫ c) ≫ Q.quotient.q := by
    simpa only [Category.assoc] using hres
  rcases field_sign_orbit Q.quotient (t ≫ a) (t ≫ c) hr with he | he
  · have hac := eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
      (C.inclusion ≫ A.level.projection) S a c hp he
    rw [hac]
  · have hsp : (a ≫ Q.sign) ≫ C.inclusion ≫ A.level.projection =
        c ≫ C.inclusion ≫ A.level.projection := by
      rw [Category.assoc a Q.sign, ← Category.assoc Q.sign, Q.sign_eq, Category.assoc,
        A.sign.over_eq, hp]
    have hac := eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
      (C.inclusion ≫ A.level.projection) S (a ≫ Q.sign) c hsp
      (by simpa only [Category.assoc] using he)
    rw [← hac, Category.assoc, Q.quotient.invariant]

lemma affine_ext_local {R T : Type u} [CommRing R] [CommRing T]
    (a b : Base R ⟶ Base T)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))) ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply Module.eq_of_localization_maximal
    (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap R (Localization.AtPrime P))
  intro P hP
  have hh := h P
  rw [← Spec.map_comp, ← Spec.map_comp] at hh
  exact CategoryTheory.congr_fun (Spec.map_injective hh) x

lemma base_eq_of_local_lifts (k : Type u) [Field k] [CharZero k]
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
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra ℚ S]
    (i : Base S ⟶ Base R) (a₁ a₂ : Base S ⟶ C.space)
    (ha₁ : a₁ ≫ Q.quotient.q = i ≫ b₁)
    (ha₂ : a₂ ≫ Q.quotient.q = i ≫ b₂) : i ≫ b₁ = i ≫ b₂ := by
  have hp := parameter_eq_of_lifts k L A B hB C Q R W G M b₁ b₂ f₁ f₂
    h₁ h₂ S i a₁ a₂ ha₁ ha₂
  let F := IsLocalRing.ResidueField S
  letI : Algebra ℚ F := ((IsLocalRing.residue S).comp (algebraMap ℚ S)).toAlgebra
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  let K := AlgebraicClosure F
  let t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))
  let τ := algebraMap F K
  have hgeom := CompatibleClassifyingUniqueness.base_eq_at_geometric_point
    k L A B hB C Q R W G M b₁ b₂ f₁ f₂ h₁ h₂ K
    (Spec.map (CommRingCat.ofHom τ) ≫ t ≫ i)
  have hres : t ≫ a₁ ≫ Q.quotient.q = t ≫ a₂ ≫ Q.quotient.q := by
    apply CompatibleClassifyingUniqueness.affine_ext τ τ.injective
    simpa only [Category.assoc, ha₁, ha₂] using hgeom
  have he := local_quotient_eq L A B C Q a₁ a₂ hp hres
  exact ha₁.symm.trans (he.trans ha₂)

/-- Pull back both finite étale sign torsors, then compare on localizations of
the common affine cover. The zero ring is included by localization extensionality. -/
lemma base_eq (k : Type u) [Field k] [CharZero k]
    (L : ℕ) (A : LegendreAtlas k L) (B : TwoMarking k L A)
    (hB : CanonicalTwo k L A B) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C)
    (R : Type u) [CommRing R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (b₁ b₂ : Base R ⟶ Base Q.quotient.ring)
    (f₁ f₂ : Curve R W ⟶ A.descent.family.curve)
    (h₁ : Classifies k L A B C Q R W G M b₁ f₁)
    (h₂ : Classifies k L A B C Q R W G M b₂ f₂) : b₁ = b₂ := by
  let q := Q.quotient.q
  letI : IsFinite q := Q.quotient.finite
  letI : Etale q := Q.quotient.etale
  letI : Surjective q := Q.quotient.surjective
  let d := pullback.fst b₁ q ≫ b₂
  let X := pullback d q
  let p : X ⟶ Base R := pullback.fst d q ≫ pullback.fst b₁ q
  let a₁ : X ⟶ C.space := pullback.fst d q ≫ pullback.snd b₁ q
  let a₂ : X ⟶ C.space := pullback.snd d q
  have hp₁ : a₁ ≫ q = p ≫ b₁ := by
    simpa only [a₁, p, Category.assoc] using congrArg (fun f => pullback.fst d q ≫ f)
      (pullback.condition (f := b₁) (g := q)).symm
  have hp₂ : a₂ ≫ q = p ≫ b₂ := by
    exact (pullback.condition (f := d) (g := q)).symm.trans (Category.assoc _ _ _).symm
  letI : Flat p := inferInstanceAs (Flat (pullback.fst d q ≫ pullback.fst b₁ q))
  letI : Surjective p := inferInstanceAs (Surjective (pullback.fst d q ≫ pullback.fst b₁ q))
  letI : Epi p := Flat.epi_of_flat_of_surjective p
  letI : IsAffine X := inferInstanceAs (IsAffine (pullback d q))
  let S := Γ(X, ⊤)
  let v : Base S ⟶ X := X.isoSpec.inv
  apply (cancel_epi p).mp
  apply (cancel_epi v).mp
  apply affine_ext_local
  intro P hP
  let T := Localization.AtPrime P
  let t := Spec.map (CommRingCat.ofHom (algebraMap S T))
  let i : Base T ⟶ Base R := t ≫ v ≫ p
  let ι : R →+* T := (Spec.preimage i).hom
  letI : Algebra ℚ T := (ι.comp (algebraMap ℚ R)).toAlgebra
  have he := base_eq_of_local_lifts k L A B hB C Q R W G M b₁ b₂ f₁ f₂
    h₁ h₂ T i (t ≫ v ≫ a₁) (t ≫ v ≫ a₂)
    (by change (t ≫ v ≫ a₁) ≫ q = i ≫ b₁
        simp only [Category.assoc, hp₁, i])
    (by change (t ≫ v ≫ a₂) ≫ q = i ≫ b₂
        simp only [Category.assoc, hp₂, i])
  simpa only [Category.assoc, i] using he

#print axioms affine_ext_local
#print axioms base_eq_of_local_lifts
#print axioms base_eq

#print axioms parameter_eq_of_lifts
#print axioms local_quotient_eq

#print axioms field_sign_orbit

#print axioms mapped_parameter
#print axioms presentations_parameter

#print axioms origin_law_mul_eq
#print axioms pointed_iso_nsmul

#print axioms comparison_eq_of_base_eq
#print axioms presentation_exists
#print axioms canonical_points
#print axioms comparison_to_source
end ArithmeticThetaArbitraryAffineR0202.ClassifyingUniqueness

namespace ArithmeticThetaArbitraryAffineR0202
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCompatibleLevelR0178

/-- Both actual classifying maps are unique over every commutative rational
k-algebra. The local sign comparison is descended along faithfully flat covers. -/
theorem arbitrary_classifying_uniqueness :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A), ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B → ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) (R : Type u) [CommRing R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (b₁ b₂ : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeDiscriminantR0171.Base Q.quotient.ring)) (f₁ f₂ : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve R W) A.descent.family.curve), ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q R W G M b₁ f₁ → ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q R W G M b₂ f₂ → b₁ = b₂ ∧ f₁ = f₂ := by
  intro k _ _ L hL _heven A B hB C Q R _ _ _ W _ G hG M b₁ b₂ f₁ f₂ h₁ h₂
  have hb := ClassifyingUniqueness.base_eq k L A B hB C Q R W G M b₁ b₂ f₁ f₂ h₁ h₂
  subst b₂
  refine ⟨rfl, ClassifyingUniqueness.comparison_eq_of_base_eq R W G hG L hL M
    A.descent.family.projection (b₁ ≫ Q.inclusion) f₁ f₂ h₁.2.1 h₂.2.1 ?_ ?_ ?_⟩
  · exact h₁.2.2.1.trans h₂.2.2.1.symm
  · exact h₁.2.2.2.1.trans h₂.2.2.2.1.symm
  · exact h₁.2.2.2.2.trans h₂.2.2.2.2.symm

#print axioms arbitrary_classifying_uniqueness
end ArithmeticThetaArbitraryAffineR0202
