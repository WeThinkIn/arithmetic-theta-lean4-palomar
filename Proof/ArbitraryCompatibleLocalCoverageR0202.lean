module

public import ArbitraryLegendreNormalFormR0202

@[expose] public section

/-! Local coverage in the specified compatibility quotient. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential


namespace ArbitraryLocalCoverage

/-- Reducing both marked sections by the quotient of levels preserves full level,
including divisor one. Avoidance is inherited on the entire base. -/
theorem full_level_divisor_reduction :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), ∃ N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G d (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), N.x = G.nsmul (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (L / d) M.x ∧ N.y = G.nsmul (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (L / d) M.y := by
  intro R _ _ W _ G hG L d hL hd hdL M
  let := FullLevelCyclicLiftsR0175.sectionGroup G hG
  have hqd : L / d * d = L := Nat.div_mul_cancel hdL
  have hq : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
  have hlt (i : Fin d) : L / d * i.val < L := by
    have h := Nat.mul_lt_mul_of_pos_left i.isLt hq
    rwa [hqd] at h
  have hmul (n : ℕ) (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      G.nsmul (𝟙 (Base R)) n (G.nsmul (𝟙 (Base R)) (L / d) z) =
        G.nsmul (𝟙 (Base R)) (L / d * n) z := by
    simp only [RelativeKatoFiberSpecialization.nsmul_pow, pow_mul]
  let N : FullLevel R W G d (𝟙 (Base R)) :=
    { x := G.nsmul (𝟙 (Base R)) (L / d) M.x
      y := G.nsmul (𝟙 (Base R)) (L / d) M.y
      killed_x := by rw [hmul, hqd, M.killed_x]
      killed_y := by rw [hmul, hqd, M.killed_y]
      avoids := by
        intro i j hij
        rw [hmul, hmul]
        apply M.avoids ⟨L / d * i.val, hlt i⟩ ⟨L / d * j.val, hlt j⟩
        rcases hij with hi | hj
        · exact Or.inl (Nat.mul_ne_zero (Nat.ne_of_gt hq) hi)
        · exact Or.inr (Nat.mul_ne_zero (Nat.ne_of_gt hq) hj) }
  exact ⟨N, rfl, rfl⟩

/-- A pointed Cartesian map respects the given elliptic laws over arbitrary rings.
Uniqueness of the law is applied on the actual projective curve over S. -/
lemma pointed_base_change {R S : Type u} [CommRing R]
    [CommRing S] {W : WeierstrassCurve R} {V : WeierstrassCurve S}
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
  have hone : (H.one (𝟙 _)).val = (J.one (𝟙 _)).val :=
    (hH.1 _).trans (hJ _).symm
  have hlaw : H = J :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext H J
      (fun t x y => WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
        V.toProjective H J hone t x y)
      (by intro T t; exact Subtype.ext ((hH.1 t).trans (hJ t).symm))
  refine ⟨hb, ho, ?_⟩
  intro n
  rw [hlaw]
  exact ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    f (structureMap S V) b hb G J hm hj n

namespace MarkingTransport
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {G : Law R W}
  {S : Type u} [CommRing S] {Ws : WeierstrassCurve S} {Gs : Law S Ws}
  {ι : R →+* S} {b : Curve S Ws ⟶ Curve R W}
  (hb : IsBaseChange R W G S Ws Gs ι b)

abbrev point {T : Scheme.{u}} (t : T ⟶ Base S)
    (x : SchemeHomOver t (structureMap S Ws)) :
    SchemeHomOver (t ≫ baseMap R S ι) (structureMap R W) :=
  ⟨x.val ≫ b, by rw [Category.assoc, hb.1.w, ← Category.assoc, x.property]; rfl⟩

def pointEquiv {T : Scheme.{u}} (t : T ⟶ Base S) :
    SchemeHomOver t (structureMap S Ws) ≃
    SchemeHomOver (t ≫ baseMap R S ι) (structureMap R W) where
  toFun := point hb t
  invFun x := ⟨hb.1.lift x.val t x.property, hb.1.lift_snd _ _ _⟩
  left_inv x := Subtype.ext (hb.1.hom_ext (hb.1.lift_fst _ _ _)
    ((hb.1.lift_snd _ _ _).trans x.property.symm))
  right_inv x := Subtype.ext (hb.1.lift_fst _ _ _)

@[simp] lemma point_symm {T : Scheme.{u}} (t : T ⟶ Base S)
    (x : SchemeHomOver (t ≫ baseMap R S ι) (structureMap R W)) :
    point hb t ((pointEquiv hb t).symm x) = x := (pointEquiv hb t).apply_symm_apply x

lemma point_natural {T U : Scheme.{u}} (t : T ⟶ Base S) (s : U ⟶ Base S)
    (q : U ⟶ T) (hq : q ≫ t = s) (x : SchemeHomOver t (structureMap S Ws)) :
    point hb s (WeierstrassProjModel.schemeHomOverComp q hq x) =
      WeierstrassProjModel.schemeHomOverComp q (by rw [← Category.assoc, hq]) (point hb t x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Transport the actual natural group operations through the Cartesian square. -/
def transported : GoodReductionJacobian.RelativeGroupLaw S (structureMap S Ws) where
  mul t x y := (pointEquiv hb t).symm (G.mul _ (point hb t x) (point hb t y))
  one t := (pointEquiv hb t).symm (G.one _)
  inv t x := (pointEquiv hb t).symm (G.inv _ (point hb t x))
  mul_assoc t x y z := by
    apply (pointEquiv hb t).injective
    simp only [Equiv.apply_symm_apply, point_symm, G.mul_assoc]
  one_mul t x := by
    apply (pointEquiv hb t).injective
    simp only [Equiv.apply_symm_apply, point_symm, G.one_mul]
    rfl
  mul_one t x := by
    apply (pointEquiv hb t).injective
    simp only [Equiv.apply_symm_apply, point_symm, G.mul_one]
    rfl
  inv_mul_cancel t x := by
    apply (pointEquiv hb t).injective
    simp only [Equiv.apply_symm_apply, point_symm, G.inv_mul_cancel]
  mul_natural t s q hq x y := by
    apply (pointEquiv hb s).injective
    change point hb s (WeierstrassProjModel.schemeHomOverComp q hq _) = _
    rw [point_natural]
    change WeierstrassProjModel.schemeHomOverComp q _
      ((pointEquiv hb t) ((pointEquiv hb t).symm _)) =
      (pointEquiv hb s) ((pointEquiv hb s).symm _)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, G.mul_natural]
    rw [← point_natural hb t s q hq, ← point_natural hb t s q hq]
    rfl

lemma geometry (S : Type u) [CommRing S] (Ws : WeierstrassCurve S) [Ws.IsElliptic]
    (Gs : Law S Ws) : GoodReductionJacobian.AbelianSchemePropertyBundle S (structureMap S Ws) := by
  letI : SmoothOfRelativeDimension 1 (structureMap S Ws) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Ws.toProjective
  letI : GeometricallyIntegral (structureMap S Ws) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso Ws
      (WeierstrassProjModel.projModel_pullback_iso_baseChange Ws.toProjective)
  letI : GeometricallyConnected (structureMap S Ws) := ⟨by
    intro K _ y Z fst snd h
    letI : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    infer_instance⟩
  exact ⟨inferInstance, WeierstrassProjModel.projModelStrCR_isProper Ws.toProjective,
    fun s => (structureMap S Ws).isConnected_preimage_singleton s, ⟨toGRJ Gs⟩⟩

lemma point_one (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {T : Scheme.{u}} (t : T ⟶ Base S) : point hb t (Gs.one t) = G.one _ := by
  apply Subtype.ext
  change (Gs.one t).val ≫ b = (G.one _).val
  rw [hGs.1, hG.1, Category.assoc, hb.2.1, ← Category.assoc]
  rfl

lemma point_mul [Ws.IsElliptic] (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {T : Scheme.{u}} (t : T ⟶ Base S) (x y : SchemeHomOver t (structureMap S Ws)) :
    point hb t (Gs.mul t x y) = G.mul _ (point hb t x) (point hb t y) := by
  have he : toGRJ Gs = transported hb :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
      (geometry S Ws Gs) _ _ (by
        apply (pointEquiv hb (𝟙 _)).injective
        change point hb (𝟙 _) (Gs.one _) = (pointEquiv hb _) ((pointEquiv hb _).symm _)
        rw [Equiv.apply_symm_apply, point_one hb hG hGs])
  have hm := congrArg (fun H : GoodReductionJacobian.RelativeGroupLaw S (structureMap S Ws) =>
    H.mul t x y) he
  change Gs.mul t x y = (pointEquiv hb t).symm _ at hm
  rw [hm]
  exact (pointEquiv hb t).apply_symm_apply _

lemma point_nsmul {T : Scheme.{u}} (t : T ⟶ Base S)
    (x : SchemeHomOver t (structureMap S Ws)) (n : ℕ) :
    point hb t (Gs.nsmul t n x) = G.nsmul _ n (point hb t x) := by
  apply Subtype.ext
  change (Gs.nsmul t n x).val ≫ b = (G.nsmul _ n (point hb t x)).val
  rw [← comp_schemeNsmul, ← comp_schemeNsmul, Category.assoc, hb.2.2]
  rfl


lemma origin_over (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    origin R W ≫ structureMap R W = 𝟙 _ := (WeierstrassProjModel.kwZeroSect R W).property

include hb in
lemma origin_cartesian : IsPullback (origin S Ws) (baseMap R S ι) b (origin R W) := by
  have hc : origin S Ws ≫ b = baseMap R S ι ≫ origin R W := hb.2.1
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hc
    (fun s => s.fst ≫ structureMap S Ws) (fun s => ?_) (fun s => ?_)
    (fun s m hm _ => ?_))
  · apply hb.1.hom_ext
    · rw [Category.assoc, hc, Category.assoc]
      change s.fst ≫ structureMap S Ws ≫ Spec.map (CommRingCat.ofHom ι) ≫ origin R W = _
      rw [← hb.1.w_assoc, ← Category.assoc s.fst b, s.condition]
      simp only [Category.assoc]
      rw [← Category.assoc (origin R W) (structureMap R W), origin_over, Category.id_comp]
    · rw [Category.assoc, origin_over, Category.comp_id]
  · have H := congrArg (fun a => a ≫ structureMap R W) s.condition
    simpa only [Category.assoc, hb.1.w, origin_over, Category.comp_id, baseMap] using H
  · rw [← hm, Category.assoc, origin_over, Category.comp_id]

include hb in
lemma origin_preimage : b ⁻¹' Set.range (origin R W) = Set.range (origin S Ws) := by
  let h := origin_cartesian hb
  rw [← Scheme.Pullback.range_fst b (origin R W), ← h.isoPullback_hom_fst]
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨h.isoPullback.inv v, ?_⟩
    change (h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst b (origin R W)) v = _
    simp
  · rintro ⟨v, rfl⟩
    exact ⟨h.isoPullback.hom v, rfl⟩

variable [Ws.IsElliptic]

lemma point_combination (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {T : Scheme.{u}} (t : T ⟶ Base S) (x y : SchemeHomOver t (structureMap S Ws))
    (i j : ℕ) :
    point hb t (Gs.mul t (Gs.nsmul t i x) (Gs.nsmul t j y)) =
      G.mul _ (G.nsmul _ i (point hb t x)) (G.nsmul _ j (point hb t y)) := by
  rw [point_mul hb hG hGs, point_nsmul, point_nsmul]

/-- Forget the changed base while retaining the actual two scheme maps. -/
def down (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ} (A : FullLevel S Ws Gs L t) :
    FullLevel R W G L (t ≫ baseMap R S ι) where
  x := point hb t A.x
  y := point hb t A.y
  killed_x := by rw [← point_nsmul, A.killed_x, point_one hb hG hGs]
  killed_y := by rw [← point_nsmul, A.killed_y, point_one hb hG hGs]
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    have hc := congrArg Subtype.val (point_combination hb hG hGs t A.x A.y i.val j.val)
    rw [← hc] at hz
    have H : (Gs.mul t (Gs.nsmul t i.val A.x) (Gs.nsmul t j.val A.y)).val z ∈
        b ⁻¹' Set.range (origin R W) := hz
    rw [origin_preimage hb] at H
    exact Set.disjoint_left.mp (A.avoids i j hij) (Set.mem_range_self z) H

/-- Lift a full marking along the actual Cartesian family comparison. -/
def up (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ} (A : FullLevel R W G L (t ≫ baseMap R S ι)) :
    FullLevel S Ws Gs L t where
  x := (pointEquiv hb t).symm A.x
  y := (pointEquiv hb t).symm A.y
  killed_x := by
    apply (pointEquiv hb t).injective
    change point hb t (Gs.nsmul t L _) = point hb t (Gs.one t)
    rw [point_nsmul, point_symm, A.killed_x, point_one hb hG hGs]
  killed_y := by
    apply (pointEquiv hb t).injective
    change point hb t (Gs.nsmul t L _) = point hb t (Gs.one t)
    rw [point_nsmul, point_symm, A.killed_y, point_one hb hG hGs]
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨s, hs⟩
    have hc := congrArg Subtype.val (point_combination hb hG hGs t
      ((pointEquiv hb t).symm A.x) ((pointEquiv hb t).symm A.y) i.val j.val)
    simp only [point_symm] at hc
    apply Set.disjoint_left.mp (A.avoids i j hij) (Set.mem_range_self z)
    refine ⟨(baseMap R S ι) s, ?_⟩
    have H := congrArg (fun a => b a) hs
    change (origin S Ws ≫ b) s = _ at H
    rw [hb.2.1] at H
    rw [← hc]
    exact H


lemma up_x {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ}
    (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    (A : FullLevel R W G L (t ≫ baseMap R S ι)) :
    (up hb hG hGs A).x.val ≫ b = A.x.val := hb.1.lift_fst _ _ _
lemma up_y {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ}
    (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    (A : FullLevel R W G L (t ≫ baseMap R S ι)) :
    (up hb hG hGs A).y.val ≫ b = A.y.val := hb.1.lift_fst _ _ _


end MarkingTransport
end ArbitraryLocalCoverage

/-- The ordered normal form makes the full marking compatible, so its
classifying map factors through the specified sign quotient. -/
theorem arbitrary_compatible_local_coverage :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A), ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B → ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) (R : Type u) [CommRing R] [Algebra ℚ R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), Nonempty (ArithmeticThetaArbitraryAffineR0202.LocalComparison k L A B C Q R W G M) := by
  intro k _ _ L hL heven A B hB C Q R _ _ _ W _ G hG M
  obtain ⟨M₂, hM₂x, hM₂y⟩ := ArbitraryLocalCoverage.full_level_divisor_reduction R W G hG L 2
    (by omega) (by omega) (even_iff_two_dvd.mp heven) M
  obtain ⟨N⟩ := arbitrary_legendre_normal_form k R W G hG M₂
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
  obtain ⟨bV, _, hbV, hoV, _, _, _, hliftV⟩ :=
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
  have hNV := ArbitraryLocalCoverage.pointed_base_change G H hG hH f.toRingHom N.map N.cartesian N.origin_eq
  have hVB : IsBaseChange (LegendreRing k) (legendre k) A.law S V H p.toRingHom bV :=
    ⟨hbV, hoV, ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
      p.toRingHom (structureMap S V) bV hbV A.law H hm hj⟩
  let M₀ := BaseChange.restrict M (baseMap R S f.toRingHom)
    (by simp : baseMap R S f.toRingHom ≫ 𝟙 (Base R) =
      𝟙 (Base S) ≫ baseMap R S f.toRingHom)
  let BM := ArbitraryLocalCoverage.MarkingTransport.up hNV hG hH M₀
  let CM := ArbitraryLocalCoverage.MarkingTransport.down hVB A.originLaw hH BM
  obtain ⟨q, hqx, _⟩ := A.represents (Base S)
    (𝟙 (Base S) ≫ baseMap (LegendreRing k) S p.toRingHom) CM
  have hq : q.val ≫ A.level.projection = baseMap (LegendreRing k) S p.toRingHom := by
    simpa only [Category.id_comp] using q.property
  have hredx : (H.nsmul (𝟙 (Base S)) (L / 2) BM.x).val = N.point0 := by
    apply N.cartesian.hom_ext
    · rw [← comp_schemeNsmul, Category.assoc, hNV.2.2, ← Category.assoc,
        ArbitraryLocalCoverage.MarkingTransport.up_x hNV hG hH M₀]
      change (baseMap R S f.toRingHom ≫ M.x.val) ≫ G.schemeNsmul (L / 2) = _
      rw [Category.assoc, comp_schemeNsmul, ← hM₂x]
      exact N.point0_eq.symm
    · exact (H.nsmul (𝟙 (Base S)) (L / 2) BM.x).property.trans
        N.point0_coordinates.1.symm
  have hredy : (H.nsmul (𝟙 (Base S)) (L / 2) BM.y).val = N.point1 := by
    apply N.cartesian.hom_ext
    · rw [← comp_schemeNsmul, Category.assoc, hNV.2.2, ← Category.assoc,
        ArbitraryLocalCoverage.MarkingTransport.up_y hNV hG hH M₀]
      change (baseMap R S f.toRingHom ≫ M.y.val) ≫ G.schemeNsmul (L / 2) = _
      rw [Category.assoc, comp_schemeNsmul, ← hM₂y]
      exact N.point1_eq.symm
    · exact (H.nsmul (𝟙 (Base S)) (L / 2) BM.y).property.trans
        N.point1_coordinates.1.symm
  obtain ⟨P₀, hP₀, hP₀b⟩ := hliftV B.x.val 0 0 hB.1
  obtain ⟨P₁, hP₁, hP₁b⟩ := hliftV B.y.val 1 0 hB.2
  have hP₀eq : N.point0 = P₀ :=
    TwoTorsionSplitCubicR0177.coordinates_ext N.point0_coordinates
      (by simpa only [map_zero] using hP₀)
  have hP₁eq : N.point1 = P₁ :=
    TwoTorsionSplitCubicR0177.coordinates_ext N.point1_coordinates
      (by simpa only [map_zero, map_one] using hP₁)
  have hcompat : CompatibleAt k L A B q.val := by
    constructor
    · rw [← comp_schemeNsmul, ← Category.assoc, hqx.1]
      change (BM.x.val ≫ bV) ≫ A.law.schemeNsmul (L / 2) = _
      rw [Category.assoc, ← hVB.2.2, ← Category.assoc, comp_schemeNsmul,
        hredx, hP₀eq, hP₀b, hq]
      rfl
    · rw [← comp_schemeNsmul, ← Category.assoc, hqx.2]
      change (BM.y.val ≫ bV) ≫ A.law.schemeNsmul (L / 2) = _
      rw [Category.assoc, ← hVB.2.2, ← Category.assoc, comp_schemeNsmul,
        hredy, hP₁eq, hP₁b, hq]
      rfl
  obtain ⟨qc, hqc, _⟩ := (C.represents (Base S) q.val).mp hcompat
  have hfactor : (qc ≫ Q.quotient.q) ≫ Q.inclusion = q.val ≫ A.quotient.q := by
    rw [Category.assoc, ← Q.cartesian.w, ← Category.assoc, hqc]
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
  have hdx : BM.x.val ≫ d = q.val ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.x := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      exact hqx.1.symm
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, BM.x.property, Category.id_comp]
  have hdy : BM.y.val ≫ d = q.val ≫
      coverSection (LegendreRing k) (legendre k) A.level A.level.level.y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.lift_fst, coverSection]
      exact hqx.2.symm
    · simp only [Category.assoc, d, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, BM.y.property, Category.id_comp]
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
  have hxc : x ≫ c = BM.x.val := by
    apply N.cartesian.hom_ext
    · rw [Category.assoc, hcN, hxb]
      exact (ArbitraryLocalCoverage.MarkingTransport.up_x hNV hG hH M₀).symm
    · rw [Category.assoc, hcf, hx, BM.x.property]
  have hyc : y ≫ c = BM.y.val := by
    apply N.cartesian.hom_ext
    · rw [Category.assoc, hcN, hyb]
      exact (ArbitraryLocalCoverage.MarkingTransport.up_y hNV hG hH M₀).symm
    · rw [Category.assoc, hcf, hy, BM.y.property]
  let comparison : ArithmeticThetaArbitraryAffineR0202.AtlasComparison k R W G M A := by
    refine { ring := S
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
             y_eq := ?_ }
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
  refine ⟨{ comparison := comparison
            base := qc ≫ Q.quotient.q
            factorization := hfactor
            over_eq := ?_ }⟩
  rw [← Q.over_eq, ← Category.assoc, hfactor]
  exact comparison.base_over

#print axioms arbitrary_compatible_local_coverage
end ArithmeticThetaArbitraryAffineR0202
