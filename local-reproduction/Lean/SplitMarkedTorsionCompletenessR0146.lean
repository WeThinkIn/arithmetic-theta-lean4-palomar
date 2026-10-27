import MarkedExactTorsionR0146
import ProjectivePointsEvaluationR0146
import Theorems.Thm_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
namespace SplitMarkedTorsionCompleteness
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ActualGenericGroupLaw

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma extension_epi (F : Type u) [Field F] [Algebra (LaurentSeries k) F] :
    Epi (extensionBase k F) := by
  apply Flat.epi_of_flat_of_surjective

lemma pointOver_injective (M : Model k T) (hM : IsModel k T M)
    (F : Type u) [Field F] [Algebra (LaurentSeries k) F]
    {i j : Fin r} {a b : kˣ} (p q : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (hq : MarkedLift k M j b q)
    (h : pointOver k M (extensionBase k F) p hp.1 =
      pointOver k M (extensionBase k F) q hq.1) : i = j ∧ a = b := by
  letI := extension_epi k F
  apply MarkedExactTorsion.labels_eq k M hM p q hp hq
  apply Subtype.ext
  have hh := (cancel_epi (extensionBase k F)).mp (congrArg Subtype.val h)
  simpa only [pointOver, Category.id_comp] using hh

lemma marked_torsion_over (h3 : 3 ≤ r) (he : Even r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (G : Law k M)
    (hG : IsOriginLaw k M s hs.1 G) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (F : Type u) [Field F] [Algebra (LaurentSeries k) F]
    (i j : Fin r) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i (ζ^j.val) p) :
    G.nsmul (extensionBase k F) r (pointOver k M (extensionBase k F) p hp.1) =
      G.one (extensionBase k F) := by
  have hz : ζ^r = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  have ht := (marked_exact_torsion k r hr h3 T he M hM s hs G hG i (ζ^j.val) p hp r).2
    ⟨dvd_mul_right r i.val, by rw [← pow_mul, Nat.mul_comm j.val r, pow_mul, hz, one_pow]⟩
  have hnat := G.nsmul_natural (𝟙 _) (extensionBase k F) (extensionBase k F)
    (Category.comp_id _) r (pointOver k M (𝟙 _) p hp.1)
  rw [ht, G.one_natural] at hnat
  simpa only [schemeHomOverComp, pointOver, Category.comp_id, Category.id_comp] using hnat.symm

lemma exhaustive_of_card_bound {A B : Type*} [Fintype A] (P : B → Prop)
    (f : A → B) (hf : Function.Injective f) (hp : ∀ a, P (f a))
    (hb : ∀ S : Finset B, (∀ b ∈ S, P b) → S.card ≤ Fintype.card A) :
    ∀ b, P b ↔ ∃! a, b = f a := by
  classical
  intro b
  constructor
  · intro hpb
    have hmem : b ∈ Finset.univ.image f := by
      by_contra hn
      have hc := hb (insert b (Finset.univ.image f)) (by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hpb
        · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy; exact hp a)
      rw [Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ hf,
        Finset.card_univ] at hc
      omega
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
    exact ⟨a, ha.symm, fun a' ha' ↦ hf (ha'.symm.trans ha.symm)⟩
  · rintro ⟨a, rfl, _⟩
    exact hp a

/-- Transport to the actual projective cubic and its coordinate points. -/
lemma evaluation_exists (h3 : 3 ≤ r) (he : Even r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (G : Law k M)
    (hG : IsOriginLaw k M s hs.1 G)
    (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F] :
    ∃ E : SchemeHomOver (extensionBase k F) (genericStructure k M) ≃
        ((curve k r).toProjective.baseChange F).toAffine.Point,
      E (G.one (extensionBase k F)) = 0 ∧
      ∀ n x, E (G.nsmul (extensionBase k F) n x) = n • E x := by
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨e, hec, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  have hei : e.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hec.1, Iso.inv_hom_id_assoc]
  let H := transport e.symm hei G
  have hH : (H.one (𝟙 _)).val = origin k r := by
    change (G.one (𝟙 _)).val ≫ e.hom = _
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hec.2.2
  obtain ⟨ev, hev⟩ := projective_points_evaluation k r h3 he H hH
  let q := pointsEquiv e hec.1 (extensionBase k F)
  let E := q.trans (ev F)
  have hb : ∀ z, pointsEquiv e.symm hei (extensionBase k F) (q z) = z := by
    intro z; apply Subtype.ext; simp [pointsEquiv, q]
  have hmul : ∀ x y, E (G.mul (extensionBase k F) x y) = E x + E y := by
    intro x y
    have hh := hev.1.1 F (q x) (q y)
    change ev F ((pointsEquiv e.symm hei (extensionBase k F)).symm
      (G.mul (extensionBase k F) _ _)) = _ at hh
    erw [hb, hb] at hh
    exact hh
  have hzero : E (G.one (extensionBase k F)) = 0 := by
    have hh := hmul (G.one (extensionBase k F)) (G.one (extensionBase k F))
    rw [G.one_mul] at hh
    exact (add_left_cancel (hh.symm.trans (add_zero _).symm))
  refine ⟨E, hzero, ?_⟩
  intro n x
  induction n with
  | zero => exact hzero.trans (zero_nsmul _).symm
  | succ n ih => erw [RelativeGroupLaw.nsmul_succ, hmul, ih, succ_nsmul]
                 rfl

lemma torsion_card_bound (h3 : 3 ≤ r) (he : Even r) (M : Model k T)
    (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (G : Law k M)
    (hG : IsOriginLaw k M s hs.1 G)
    (F : Type u) [Field F] [Algebra (LaurentSeries k) F]
    (S : Finset (SchemeHomOver (extensionBase k F) (genericStructure k M)))
    (hS : ∀ x ∈ S, G.nsmul (extensionBase k F) r x = G.one (extensionBase k F)) :
    S.card ≤ r^2 := by
  classical
  obtain ⟨E, hzero, hmul⟩ := evaluation_exists k h3 he M hM s hs G hG F
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  let W : WeierstrassCurve F := (curve k r).map (algebraMap (LaurentSeries k) F)
  haveI : W.IsElliptic := inferInstance
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have hn : (r : F) ≠ 0 := by
    rw [← map_natCast (algebraMap (LaurentSeries k) F)]
    exact (map_ne_zero (algebraMap (LaurentSeries k) F)).2 (Nat.cast_ne_zero.mpr hr.ne')
  have hh := WeierstrassCurve.Affine.Point.card_le_sq_of_forall_nsmul_eq_zero W r hn
    (S.image E) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [← hmul, hS x hx, hzero])
  rwa [Finset.card_image_of_injective _ E.injective] at hh

end SplitMarkedTorsionCompleteness
open SplitMarkedTorsionCompleteness CategoryTheory NeronModelInfra

/-- Every r-torsion point over every extension field is uniquely an actual mark. -/
theorem split_marked_torsion_completeness :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) r → ∀ (p : Fin r → kˣ → (Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)) (hp : ∀ i a, ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M i a (p i a)) (F : Type u) [Field F] [Algebra (LaurentSeries k) F] (x : NeronModelInfra.SchemeHomOver (ArithmeticThetaMarkedGroupLawR0146.extensionBase k F) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)), G.nsmul (ArithmeticThetaMarkedGroupLawR0146.extensionBase k F) r x = G.one (ArithmeticThetaMarkedGroupLawR0146.extensionBase k F) ↔ ∃! ij : Fin r × Fin r, x = ArithmeticThetaMarkedGroupLawR0146.pointOver k M (ArithmeticThetaMarkedGroupLawR0146.extensionBase k F) (p ij.1 (ζ^ij.2.val)) (hp ij.1 (ζ^ij.2.val)).1 := by
  intro k _ _ r hr h3 T he M hM s hs G hG ζ hζ p hp F _ _ x
  classical
  let f : Fin r × Fin r → SchemeHomOver (extensionBase k F)
      (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) :=
    fun ij ↦ pointOver k M (extensionBase k F) (p ij.1 (ζ^ij.2.val)) (hp ij.1 (ζ^ij.2.val)).1
  have hf : Function.Injective f := by
    intro ij ij' hh
    obtain ⟨hi, hj⟩ := pointOver_injective k M hM F _ _
      (hp ij.1 (ζ^ij.2.val)) (hp ij'.1 (ζ^ij'.2.val)) hh
    apply Prod.ext hi
    apply Fin.ext
    apply hζ.pow_inj ij.2.isLt ij'.2.isLt
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hj
  apply exhaustive_of_card_bound
    (fun y ↦ G.nsmul (extensionBase k F) r y = G.one (extensionBase k F)) f hf
    (fun ij ↦ marked_torsion_over k h3 he M hM s hs G hG ζ hζ F ij.1 ij.2 _ (hp _ _))
    (fun S hS ↦ ?_) x
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    torsion_card_bound k h3 he M hM s hs G hG F S hS

#print axioms split_marked_torsion_completeness
end ArithmeticThetaMarkedGroupLawR0146
