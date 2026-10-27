import TateCuspDefinitionsR0181
import SplitMarkedTorsionCompletenessR0146

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
namespace TateFullLevelMarking
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw

lemma elliptic (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (hL : 3 ≤ L) (heven : Even L) : (TateCurve k L).IsElliptic :=
  ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.curve_elliptic
    k hL heven

variable {R : Type u} [CommRing R] {A B : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}

lemma transport_nsmul (e : A ≅ B) (he : e.hom ≫ g = f)
    (G : WeierstrassProjModel.RelativeGroupLaw R g)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    pointsEquiv e he t ((transport e he G).nsmul t n x) =
      G.nsmul t n (pointsEquiv e he t x) := by
  induction n with
  | zero => exact (pointsEquiv e he t).apply_symm_apply _
  | succ n ih =>
    simp only [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ]
    change pointsEquiv e he t ((pointsEquiv e he t).symm
      (G.mul t _ _)) = _
    rw [Equiv.apply_symm_apply, ih]

lemma transport_nsmul_symm (e : A ≅ B) (he : e.hom ≫ g = f)
    (G : WeierstrassProjModel.RelativeGroupLaw R g)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t g) :
    (transport e he G).nsmul t n ((pointsEquiv e he t).symm x) =
      (pointsEquiv e he t).symm (G.nsmul t n x) := by
  apply (pointsEquiv e he t).injective
  rw [transport_nsmul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177

lemma coordinates_avoid {K : Type u} [Field K] (W : WeierstrassCurve K)
    (P : Base K ⟶ Curve K W) (x y : K) (h : HasCoordinates K W P x y) :
    Disjoint (Set.range P) (Set.range (origin K W)) := by
  obtain ⟨_, χ, hχ, _, _⟩ := h
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ hz
  have hn := (TwoTorsionAffineCoordinates.not_mem_basicOpen_iff_mem_range_kwZeroSect
    W (P p)).mpr hz
  apply hn
  rw [hχ]
  change (chartInclusion K W) ((Spec.map (CommRingCat.ofHom χ)) p) ∈ _
  rw [← Proj.opensRange_awayι _ _ (WeierstrassCurve.DrinfeldGlobal.coord_mem W.toProjective 2) one_pos]
  exact ⟨_, rfl⟩

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146

lemma model_exists (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (hL : 3 ≤ L) (hpos : 0 < L) :
    ∃ (T : Tower k L hpos) (M : Model k T), IsModel k T M := by
  let T := TowerAssemblyR0130.assembledTower k L hpos hL
  obtain ⟨b, hb, hbr, _⟩ := ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis
    k L hpos hL T (fun _ => 1) 3 (by decide)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k L hpos hL T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k L hpos hL T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩

end TateFullLevelMarking

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaRelativeDiscriminantR0171

/-- The literal two Tate directions give a full marking on the accepted cubic. -/
theorem tate_full_level_marking :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L),
      ∀ (ζ : k), IsPrimitiveRoot ζ L → ∃ E : TateLevel k L, CanonicalMarking k L ζ E := by
  intro k _ _ L hL heven ζ hζ
  have hpos : 0 < L := by omega
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k L hL hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k L hpos hL T M hM (zeroIndex L hpos) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k L hpos hL T heven M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k L
  obtain ⟨e, hec, _⟩ := compactified_coordinate_isomorphism k L hpos hL T heven M hM s hs X Y hX hY a ha c hc
  obtain ⟨G, hG, _⟩ := actual_generic_group_law k L hpos hL T heven M hM s hs
  have hei : e.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k L := by
    rw [← hec.1, Iso.inv_hom_id_assoc]
  let H := transport e.symm hei G
  let F := (pointsEquiv e.symm hei (𝟙 _)).symm
  have hHo : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k L) H := by
    constructor
    · intro V t
      change (G.one t).val ≫ e.hom = _
      rw [hG.1]
      change (t ≫ genericPoint k M s hs.1) ≫ e.hom = _
      rw [Category.assoc, hec.2.2]
      rfl
    · intro V t x y
      change (pointsEquiv e.symm hei t).symm (G.mul t _ _) =
        (pointsEquiv e.symm hei t).symm (G.mul t _ _)
      rw [hG.2]
  let z : kˣ := (hζ.isUnit hpos.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hpos.ne').unit_spec
  have hzL : z ^ L = 1 := Units.ext (by simpa [hz] using hζ.pow_eq_one)
  let p := MarkedPointAddition.point k hL M hM
  let ix : Fin L := ⟨0, hpos⟩
  let iy : Fin L := ⟨1, by omega⟩
  let px := p ix z
  let py := p iy 1
  have hone : p (zeroIndex L hpos) 1 = G.one (𝟙 _) :=
    MarkedExactTorsion.point_one k M hM hL s hs G hG
  have hkillx : H.nsmul (𝟙 _) L (F px) = H.one (𝟙 _) := by
    rw [TateFullLevelMarking.transport_nsmul_symm]
    change F (G.nsmul (𝟙 _) L (p ix z)) = F (G.one (𝟙 _))
    rw [MarkedExactTorsion.point_nsmul k M hM hL heven s hs G hG]
    simpa [ix, hzL, zeroIndex] using congrArg F hone
  have hkilly : H.nsmul (𝟙 _) L (F py) = H.one (𝟙 _) := by
    rw [TateFullLevelMarking.transport_nsmul_symm]
    change F (G.nsmul (𝟙 _) L (p iy 1)) = F (G.one (𝟙 _))
    rw [MarkedExactTorsion.point_nsmul k M hM hL heven s hs G hG]
    simpa [iy, zeroIndex] using congrArg F hone
  have hcomb (i j : Fin L) :
      H.mul (𝟙 _) (H.nsmul (𝟙 _) i.val (F px)) (H.nsmul (𝟙 _) j.val (F py)) =
        F (p j (z ^ i.val)) := by
    rw [TateFullLevelMarking.transport_nsmul_symm, TateFullLevelMarking.transport_nsmul_symm]
    change F (G.mul (𝟙 _) ((pointsEquiv e.symm hei (𝟙 _)) (F _))
      ((pointsEquiv e.symm hei (𝟙 _)) (F _))) = _
    simp only [F, Equiv.apply_symm_apply]
    rw [MarkedExactTorsion.point_nsmul k M hM hL heven s hs G hG,
      MarkedExactTorsion.point_nsmul k M hM hL heven s hs G hG,
      MarkedExactTorsion.point_mul k M hM hL heven s hs G hG]
    congr 2
    · apply Fin.ext
      simp [ix, iy, sumIndex, Nat.mod_eq_of_lt j.isLt]
    · simp
  have hcoord (i j : Fin L) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
      ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k L)
        (F (p j (z ^ i.val))).val
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L j.val (ζ ^ i.val)))
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L j.val (ζ ^ i.val))) := by
    have hn : j.val ≠ 0 ∨ ((z ^ i.val : kˣ) : k) ≠ 1 := by
      rcases hne with hi | hj
      · exact Or.inr (by simpa [hz] using hζ.pow_ne_one_of_pos_of_lt hi i.isLt)
      · exact Or.inl hj
    have hh := ArithmeticThetaHodgeFourTorsionR0147.marked_coordinate_chart
      k L hpos hL T heven M hM s hs X Y hX hY a ha c hc e hec j (z^i.val)
      (MarkedPointAddition.sectionAt k hL M hM j (z^i.val))
      (MarkedPointAddition.sectionAt_spec k hL M hM j (z^i.val)) hn
    refine ⟨(F (p j (z ^ i.val))).property, ?_⟩
    obtain ⟨χ, hχ, hx, hy⟩ := hh
    refine ⟨χ, hχ, ?_, ?_⟩
    · simpa only [Units.val_pow_eq_pow_val, hz] using hx
    · simpa only [Units.val_pow_eq_pow_val, hz] using hy
  let marking : FullLevel (LaurentSeries k) (TateCurve k L) H L (𝟙 (Puncture k)) :=
    { x := F px
      y := F py
      killed_x := hkillx
      killed_y := hkilly
      avoids := by
        intro i j hne
        rw [hcomb]
        exact TateFullLevelMarking.coordinates_avoid _ _ _ _ (hcoord i j hne) }
  refine ⟨⟨TateFullLevelMarking.elliptic k L hL heven, H, hHo, marking⟩, ?_⟩
  intro i j hne
  change ArithmeticThetaLegendreComparisonR0177.HasCoordinates _ _
    (H.mul (𝟙 _) (H.nsmul (𝟙 _) i.val (F px)) (H.nsmul (𝟙 _) j.val (F py))).val _ _
  rw [hcomb]
  exact hcoord i j hne

#print axioms tate_full_level_marking
end ArithmeticThetaTateCuspsR0181
