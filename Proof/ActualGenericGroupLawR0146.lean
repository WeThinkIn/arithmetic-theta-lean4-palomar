module

public import MarkedGroupLawDefinitionsR0146
public import AlgebraicTateCoordinatesR0143
public import ProjectiveCubicChartR0145
public import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
public import CompactifiedCoordinateIsomorphismR0145

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
namespace ActualGenericGroupLaw
variable {R : Type u} [CommRing R] {A B : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}

def pointsEquiv (e : A ≅ B) (he : e.hom ≫ g = f)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t f ≃ SchemeHomOver t g where
  toFun x := ⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩
  invFun y := ⟨y.val ≫ e.inv, by rw [← he, Category.assoc, Iso.inv_hom_id_assoc, y.property]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

lemma pointsEquiv_natural (e : A ≅ B) (he : e.hom ≫ g = f)
    {V V' : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (t' : V' ⟶ Spec (CommRingCat.of R)) (ψ : V' ⟶ V) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    pointsEquiv e he t' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ hψ (pointsEquiv e he t x) :=
  Subtype.ext (Category.assoc _ _ _)

def transport (e : A ≅ B) (he : e.hom ≫ g = f)
    (G : RelativeGroupLaw R g) : RelativeGroupLaw R f where
  mul t x y := (pointsEquiv e he t).symm (G.mul t (pointsEquiv e he t x) (pointsEquiv e he t y))
  one t := (pointsEquiv e he t).symm (G.one t)
  inv t x := (pointsEquiv e he t).symm (G.inv t (pointsEquiv e he t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, G.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, G.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (pointsEquiv e he t').injective
    rw [pointsEquiv_natural]
    simp only [Equiv.apply_symm_apply, G.mul_natural, pointsEquiv_natural]

lemma law_ext (G H : RelativeGroupLaw R f)
    (hm : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f), G.mul t x y = H.mul t x y)
    (ho : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)), G.one t = H.one t) :
    G = H := by
  have hi : @G.inv = @H.inv := by
    funext V t x
    letI := H.pointGroup t
    symm
    apply inv_eq_of_mul_eq_one_left
    change H.mul t (G.inv t x) x = H.one t
    rw [← hm, G.inv_mul_cancel, ho]
  have hm' : @G.mul = @H.mul := by funext V t x y; exact hm t x y
  have ho' : @G.one = @H.one := by funext V t; exact ho t
  cases G; cases H
  simp_all

end ActualGenericGroupLaw
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ActualGenericGroupLaw

/-- The unique natural commutative law on the actual generic curve, with its marked origin. -/
theorem actual_generic_group_law :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
    ∃! G : Law k M, IsOriginLaw k M s hs.1 G := by
  intro k _ _ r hr h3 T he M hM s hs
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨e, hec, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : Invertible (2 : LaurentSeries k) := invertibleOfNonzero (by norm_num)
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  letI := CompactifiedCoordinateIsomorphism.projective_relative_one k h3 he
  have hsm : Smooth (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r) := inferInstance
  have hgi : GeometricallyIntegral (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso (curve k r)
      (projModel_pullback_iso_baseChange (curve k r).toProjective)
  obtain ⟨_, _, _, G, _, hGo, hGc⟩ := relativeGroupLaw_exists (curve k r) hsm hgi
    (WeierstrassCurve.IsElliptic.isUnit (W := curve k r))
  let L : Law k M := transport e hec.1 G
  have hLo : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k))),
      L.one t = pointOver k M t s hs.1 := by
    intro V t
    apply Subtype.ext
    change (G.one t).val ≫ e.inv = t ≫ genericPoint k M s hs.1
    rw [hGo]
    change (t ≫ origin k r) ≫ e.inv = _
    rw [← hec.2.2]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hL : IsOriginLaw k M s hs.1 L := ⟨hLo, by
    intro V t x y
    change (pointsEquiv e hec.1 t).symm (G.mul t _ _) = (pointsEquiv e hec.1 t).symm (G.mul t _ _)
    rw [hGc]⟩
  refine ⟨L, hL, ?_⟩
  intro H hH
  have hei : e.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hec.1, Iso.inv_hom_id_assoc]
  let H' := transport e.symm hei H
  let L' := transport e.symm hei L
  have hone : (H'.one (𝟙 _)).val = (L'.one (𝟙 _)).val := by
    change (H.one (𝟙 _)).val ≫ e.hom = (L.one (𝟙 _)).val ≫ e.hom
    rw [hH.1, hLo]
  apply law_ext H L
  · intro V t x y
    have hh := RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
      (curve k r).toProjective H' L' hone t
      (pointsEquiv e hec.1 t x) (pointsEquiv e hec.1 t y)
    have hb : ∀ z : SchemeHomOver t (genericStructure k M),
        pointsEquiv e.symm hei t (pointsEquiv e hec.1 t z) = z := by
      intro z; apply Subtype.ext; simp [pointsEquiv]
    change (pointsEquiv e.symm hei t).symm (H.mul t _ _) =
      (pointsEquiv e.symm hei t).symm (L.mul t _ _) at hh
    rw [hb, hb] at hh
    exact (pointsEquiv e.symm hei t).symm.injective hh
  · intro V t
    exact (hH.1 t).trans (hLo t).symm

#print axioms actual_generic_group_law
end ArithmeticThetaMarkedGroupLawR0146
