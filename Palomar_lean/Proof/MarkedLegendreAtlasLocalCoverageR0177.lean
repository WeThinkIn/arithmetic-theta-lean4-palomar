module

public import FullLevelDivisorReductionR0177
public import LegendreNormalFormR0177
public import LegendreFamilyGeometryR0176
public import FullLevelBaseChangeR0175

@[expose] public section

/-! Local coverage of the accepted marked Legendre family. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
namespace MarkedLegendreAtlasLocalCoverageR0177
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

/-- A pointed Cartesian comparison of elliptic curves respects multiplication.
The group law is determined by its origin, so this applies to the specified laws. -/
lemma pointed_base_change {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] {W : WeierstrassCurve R} {V : WeierstrassCurve S}
    [V.IsElliptic] (G : Law R W) (H : Law S V)
    (hG : IsOriginLaw R W G) (hH : IsOriginLaw S V H)
    (f : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : IsPullback b (structureMap S V) (structureMap R W) (baseMap R S f))
    (ho : origin S V ≫ b = baseMap R S f ≫ origin R W) :
    IsBaseChange R W G S V H f b := by
  obtain ⟨J, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      f (structureMap R W) (structureMap S V) b hb G
  have hJ : ∀ {T : Scheme.{u}} (t : T ⟶ Base S),
      (J.one t).val = t ≫ origin S V := by
    intro T t
    apply hb.hom_ext
    · simp only [hj, hG.1, Category.assoc, ho, baseMap]
    · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
      exact (J.one t).property
  have he : toGRJ H = toGRJ J :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
      (BaseChange.geometry S V H) _ _ (Subtype.ext ((hH.1 _).trans (hJ _).symm))
  refine ⟨hb, ho, ?_⟩
  intro n
  rw [← toGRJ_schemeNsmul, he, toGRJ_schemeNsmul]
  exact ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    f (structureMap S V) b hb G J hm hj n

end MarkedLegendreAtlasLocalCoverageR0177
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176
open MarkedLegendreAtlasLocalCoverageR0177

/-- Every full even level family in the stated normal affine domain is locally
a Cartesian pullback of the same accepted sign-quotient family, with both labels. -/
theorem marked_legendre_atlas_local_coverage :
    ∀ (k : Type u) [Field k] [CharZero k] (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L), Nonempty (ArithmeticThetaLegendreComparisonR0177.AtlasComparison k R W G M A) := by
  intro k _ _ R _ _ _ _ _ _ W _ G hG L hL heven M A
  obtain ⟨M₂, _, _⟩ := full_level_divisor_reduction R W G hG L 2
    (by omega) (by omega) (even_iff_two_dvd.mp heven) M
  obtain ⟨N⟩ := legendre_normal_form k R W G hG M₂
  let S := N.ring
  let f := N.inclusion
  let p := N.parameterMap
  let V := (legendre k).map p.toRingHom
  obtain ⟨hd, hn, hi, he, _, _⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := hi
  letI := he
  letI : Algebra (LegendreRing k) S := p.toRingHom.toAlgebra
  letI : V.IsElliptic := inferInstance
  obtain ⟨bV, _, hbV, hoV, _⟩ :=
    NormalFormConstruction.coefficient_comparison (legendre k) p.toRingHom
  change IsPullback bV (structureMap S V) (structureMap (LegendreRing k) (legendre k))
    (baseMap (LegendreRing k) S p.toRingHom) at hbV
  change origin S V ≫ bV = baseMap (LegendreRing k) S p.toRingHom ≫
    origin (LegendreRing k) (legendre k) at hoV
  obtain ⟨H, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      p.toRingHom (structureMap (LegendreRing k) (legendre k)) (structureMap S V)
      bV hbV A.law
  have hH : IsOriginLaw S V H := by
    constructor
    · intro T t
      apply hbV.hom_ext
      · simp only [hj, A.originLaw.1, Category.assoc, hoV, baseMap]
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (H.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hbV.hom_ext
      · rw [hm, hm, A.originLaw.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hNV := pointed_base_change G H hG hH f.toRingHom N.map N.cartesian N.origin_eq
  have hVB : IsBaseChange (LegendreRing k) (legendre k) A.law S V H p.toRingHom bV :=
    ⟨hbV, hoV, ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
      p.toRingHom (structureMap S V) bV hbV A.law H hm hj⟩
  let M₀ := BaseChange.restrict M (baseMap R S f.toRingHom)
    (by simp : baseMap R S f.toRingHom ≫ 𝟙 (Base R) =
      𝟙 (Base S) ≫ baseMap R S f.toRingHom)
  let B := BaseChange.up hNV hG hH M₀
  let C := BaseChange.down hVB A.originLaw hH B
  obtain ⟨q, hqx, _⟩ := A.represents (Base S)
    (𝟙 (Base S) ≫ baseMap (LegendreRing k) S p.toRingHom) C
  have hq : q.val ≫ A.level.projection = baseMap (LegendreRing k) S p.toRingHom := by
    simpa only [Category.id_comp] using q.property
  let d : Curve S V ⟶ coverCurve (LegendreRing k) (legendre k) A.level :=
    pullback.lift bV (structureMap S V ≫ q.val) (by
      rw [Category.assoc, hq]; exact hbV.w)
  have hd : IsPullback d (structureMap S V)
      (coverToLevel (LegendreRing k) (legendre k) A.level) q.val := by
    have hout : IsPullback (d ≫ coverToCurve (LegendreRing k) (legendre k) A.level)
        (structureMap S V) (structureMap (LegendreRing k) (legendre k))
        (q.val ≫ A.level.projection) := by
      simpa only [d, coverToCurve, pullback.lift_fst, hq] using hbV
    exact hout.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have hdo : origin S V ≫ d = q.val ≫
      coverSection (LegendreRing k) (legendre k) A.level (A.law.one A.level.projection) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      rw [hoV, A.originLaw.1, ← Category.assoc, hq]
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, BaseChange.origin_over, Category.id_comp]
  have hdx : B.x.val ≫ d = q.val ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.x := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      exact hqx.1.symm
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, B.x.property, Category.id_comp]
  have hdy : B.y.val ≫ d = q.val ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      exact hqx.2.symm
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, B.y.property, Category.id_comp]
  obtain ⟨b, _, hb, hob, _⟩ := NormalFormConstruction.coefficient_comparison W f.toRingHom
  let Ws := W.map f.toRingHom
  let c : Curve S Ws ⟶ Curve S V := N.cartesian.lift b (structureMap S Ws) hb.w
  have hcN : c ≫ N.map = b := N.cartesian.lift_fst _ _ _
  have hcf : c ≫ structureMap S V = structureMap S Ws := N.cartesian.lift_snd _ _ _
  have hc : IsPullback c (structureMap S Ws) (structureMap S V) (𝟙 (Base S)) := by
    have hout : IsPullback (c ≫ N.map) (structureMap S Ws) (structureMap R W)
        (𝟙 (Base S) ≫ baseMap R S f.toRingHom) := by
      simpa only [hcN, Category.id_comp, baseMap] using hb
    exact hout.of_right (by simpa only [Category.comp_id] using hcf) N.cartesian
  have hco : origin S Ws ≫ c = origin S V := by
    apply N.cartesian.hom_ext
    · rw [Category.assoc, hcN, hob, N.origin_eq]
    · rw [Category.assoc, hcf, BaseChange.origin_over, BaseChange.origin_over]
  let x := hb.lift (baseMap R S f.toRingHom ≫ M.x.val) (𝟙 (Base S)) (by
    simp only [Category.assoc, M.x.property, Category.comp_id, Category.id_comp, baseMap])
  let y := hb.lift (baseMap R S f.toRingHom ≫ M.y.val) (𝟙 (Base S)) (by
    simp only [Category.assoc, M.y.property, Category.comp_id, Category.id_comp, baseMap])
  have hx : x ≫ structureMap S Ws = 𝟙 _ := hb.lift_snd _ _ _
  have hy : y ≫ structureMap S Ws = 𝟙 _ := hb.lift_snd _ _ _
  have hxb : x ≫ b = baseMap R S f.toRingHom ≫ M.x.val := hb.lift_fst _ _ _
  have hyb : y ≫ b = baseMap R S f.toRingHom ≫ M.y.val := hb.lift_fst _ _ _
  have hxc : x ≫ c = B.x.val := by
    apply N.cartesian.hom_ext
    · rw [Category.assoc, hcN, hxb]
      exact (BaseChange.up_x hNV hG hH M₀).symm
    · rw [Category.assoc, hcf, hx, B.x.property]
  have hyc : y ≫ c = B.y.val := by
    apply N.cartesian.hom_ext
    · rw [Category.assoc, hcN, hyb]
      exact (BaseChange.up_y hNV hG hH M₀).symm
    · rw [Category.assoc, hcf, hy, B.y.property]
  refine ⟨{ ring := S
            inclusion := f
            finite := N.finite
            etale := N.etale
            surjective := N.surjective
            degree := N.degree
            sourceMap := b
            sourceCartesian := hb
            sourceOrigin := hob
            x := x
            y := y
            x_over := hx
            y_over := hy
            x_lift := hxb
            y_lift := hyb
            base := q.val ≫ A.quotient.q
            base_over := ?_
            comparison := c ≫ d ≫ A.descent.comparison
            cartesian := ?_
            origin_eq := ?_
            x_eq := ?_
            y_eq := ?_ }⟩
  · rw [Category.assoc, A.quotient.over_eq, ← Category.assoc, hq]
    change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (LegendreRing k))) = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (AlgHom.comp_algebraMap p)
  · simpa only [Category.id_comp, Category.assoc] using hc.paste_horiz (hd.paste_horiz A.descent.cartesian)
  · rw [← Category.assoc, hco, ← Category.assoc, hdo, Category.assoc,
      A.descent.origin_eq, Category.assoc]
  · rw [← Category.assoc, hxc, ← Category.assoc, hdx, Category.assoc,
      A.x_eq, Category.assoc]
  · rw [← Category.assoc, hyc, ← Category.assoc, hdy, Category.assoc,
      A.y_eq, Category.assoc]

#print axioms marked_legendre_atlas_local_coverage
end ArithmeticThetaLegendreComparisonR0177
