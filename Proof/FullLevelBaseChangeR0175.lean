module

public import FullLevelRepresentabilityR0175
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
namespace BaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

variable {R : Type u} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {G : Law R W}
  {S : Type u} [CommRing S] [IsDomain S] {Ws : WeierstrassCurve S} {Gs : Law S Ws}
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

/-- Full markings pull back along arbitrary morphisms of test schemes. -/
def restrict {R : Type u} [CommRing R] {W : WeierstrassCurve R} {G : Law R W}
    {T U : Scheme.{u}} {t : T ⟶ Base R} {s : U ⟶ Base R} {L : ℕ}
    (A : FullLevel R W G L t) (q : U ⟶ T) (hq : q ≫ t = s) : FullLevel R W G L s where
  x := WeierstrassProjModel.schemeHomOverComp q hq A.x
  y := WeierstrassProjModel.schemeHomOverComp q hq A.y
  killed_x := G.isTorsionPoint_schemeHomOverComp _ _ _ hq L A.killed_x
  killed_y := G.isTorsionPoint_schemeHomOverComp _ _ _ hq L A.killed_y
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    have hc := Representability.combination_natural R W G t s q hq A.x A.y i.val j.val
    rw [← hc] at hz
    exact Set.disjoint_left.mp (A.avoids i j hij) (Set.mem_range_self (q z)) hz


lemma represents_ext {R : Type u} [CommRing R] {W : WeierstrassCurve R} {G : Law R W}
    {L : ℕ} {Z : LevelScheme R W G L} (hZ : Represents R W G Z)
    {T : Scheme.{u}} {t : T ⟶ Base R} (a c : T ⟶ Z.space)
    (ha : a ≫ Z.projection = t) (hc : c ≫ Z.projection = t)
    (hx : a ≫ Z.level.x.val = c ≫ Z.level.x.val)
    (hy : a ≫ Z.level.y.val = c ≫ Z.level.y.val) : a = c := by
  obtain ⟨q, _, hu⟩ := hZ T t (restrict Z.level c hc)
  have h₁ : (⟨a,ha⟩ : SchemeHomOver t Z.projection) = q := hu _ ⟨hx,hy⟩
  have h₂ : (⟨c,hc⟩ : SchemeHomOver t Z.projection) = q := hu _ ⟨rfl,rfl⟩
  exact congrArg Subtype.val (h₁.trans h₂.symm)

lemma up_x {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ}
    (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    (A : FullLevel R W G L (t ≫ baseMap R S ι)) :
    (up hb hG hGs A).x.val ≫ b = A.x.val := hb.1.lift_fst _ _ _
lemma up_y {T : Scheme.{u}} {t : T ⟶ Base S} {L : ℕ}
    (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    (A : FullLevel R W G L (t ≫ baseMap R S ι)) :
    (up hb hG hGs A).y.val ≫ b = A.y.val := hb.1.lift_fst _ _ _

include hb in
/-- Representing objects inherit the Cartesian comparison of the full marking functors. -/
lemma representing_cartesian (hG : IsOriginLaw R W G) (hGs : IsOriginLaw S Ws Gs)
    {L : ℕ} (Z : LevelScheme R W G L) (hZ : Represents R W G Z)
    (Zs : LevelScheme S Ws Gs L) (hZs : Represents S Ws Gs Zs) :
    ∃! β : Zs.space ⟶ Z.space,
      IsPullback β Zs.projection Z.projection (baseMap R S ι) ∧
      Zs.level.x.val ≫ b = β ≫ Z.level.x.val ∧
      Zs.level.y.val ≫ b = β ≫ Z.level.y.val := by
  obtain ⟨β, hβ, hβu⟩ := hZ Zs.space (Zs.projection ≫ baseMap R S ι)
    (down hb hG hGs Zs.level)
  have hx : β.val ≫ Z.level.x.val = Zs.level.x.val ≫ b := hβ.1
  have hy : β.val ≫ Z.level.y.val = Zs.level.y.val ≫ b := hβ.2
  have cart : IsPullback β.val Zs.projection Z.projection (baseMap R S ι) := by
    let mark (s : PullbackCone Z.projection (baseMap R S ι)) :=
      up hb hG hGs (restrict Z.level s.fst s.condition)
    have lifts (s : PullbackCone Z.projection (baseMap R S ι)) :
        ∃ q : SchemeHomOver s.snd Zs.projection,
          q.val ≫ Zs.level.x.val = (mark s).x.val ∧
          q.val ≫ Zs.level.y.val = (mark s).y.val := (hZs s.pt s.snd (mark s)).exists
    let q (s : PullbackCone Z.projection (baseMap R S ι)) := (lifts s).choose
    have qx (s : PullbackCone Z.projection (baseMap R S ι)) :
        (q s).val ≫ Zs.level.x.val = (mark s).x.val := (lifts s).choose_spec.1
    have qy (s : PullbackCone Z.projection (baseMap R S ι)) :
        (q s).val ≫ Zs.level.y.val = (mark s).y.val := (lifts s).choose_spec.2
    have mx (s : PullbackCone Z.projection (baseMap R S ι)) :
        (mark s).x.val ≫ b = s.fst ≫ Z.level.x.val := up_x hb hG hGs _
    have my (s : PullbackCone Z.projection (baseMap R S ι)) :
        (mark s).y.val ≫ b = s.fst ≫ Z.level.y.val := up_y hb hG hGs _
    have qβ (s : PullbackCone Z.projection (baseMap R S ι)) : (q s).val ≫ β.val = s.fst := by
      apply represents_ext hZ _ _ (t := s.snd ≫ baseMap R S ι)
      · rw [Category.assoc, β.property, ← Category.assoc, (q s).property]
      · exact s.condition
      · rw [Category.assoc, hx, ← Category.assoc, qx, mx]
      · rw [Category.assoc, hy, ← Category.assoc, qy, my]
    apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk β.property
      (fun s => (q s).val) qβ (fun s => (q s).property) ?_)
    intro s m hm hn
    apply represents_ext hZs _ _ hn (q s).property
    · apply hb.1.hom_ext
      · rw [Category.assoc, hx.symm, ← Category.assoc, hm,
          qx, mx]
      · rw [Category.assoc, Zs.level.x.property, Category.assoc, Zs.level.x.property,
          hn, (q s).property]
    · apply hb.1.hom_ext
      · rw [Category.assoc, hy.symm, ← Category.assoc, hm,
          qy, my]
      · rw [Category.assoc, Zs.level.y.property, Category.assoc, Zs.level.y.property,
          hn, (q s).property]
  refine ⟨β.val, ⟨cart, hx.symm, hy.symm⟩, ?_⟩
  intro β' hβ'
  exact congrArg Subtype.val (hβu ⟨β', hβ'.1.w⟩ ⟨hβ'.2.1.symm, hβ'.2.2.symm⟩)

end BaseChange
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169

/-- Both universal sections and the actual representing cover commute with arbitrary base change. -/
theorem full_level_arbitrary_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b) (L : ℕ) (hL : 0 < L) (Z : ArithmeticThetaFullLevelCoverR0175.LevelScheme R W G L) (hZ : ArithmeticThetaFullLevelCoverR0175.Represents R W G Z) (Zs : ArithmeticThetaFullLevelCoverR0175.LevelScheme S Ws Gs L) (hZs : ArithmeticThetaFullLevelCoverR0175.Represents S Ws Gs Zs), ∃! β : Quiver.Hom Zs.space Z.space, CategoryTheory.IsPullback β Zs.projection Z.projection (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) ∧ CategoryTheory.CategoryStruct.comp Zs.level.x.val b = CategoryTheory.CategoryStruct.comp β Z.level.x.val ∧ CategoryTheory.CategoryStruct.comp Zs.level.y.val b = CategoryTheory.CategoryStruct.comp β Z.level.y.val := by
  intro R _ _ _ _ _ W _ G hG S _ _ _ _ _ Ws _ Gs hGs ι b hb L hL Z hZ Zs hZs
  exact BaseChange.representing_cartesian hb hG hGs Z hZ Zs hZs

#print axioms full_level_arbitrary_base_change
end ArithmeticThetaFullLevelCoverR0175
