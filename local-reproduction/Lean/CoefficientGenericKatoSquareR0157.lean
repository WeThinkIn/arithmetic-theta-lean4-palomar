import CoefficientModelBaseChangeR0157

/-! The generic coefficient square, its marked origin, and all multiplication maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace CoefficientGenericKatoSquareR0157
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaRamifiedPeriodR0155.RamifiedKatoBaseChange

private lemma section_ext (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (b : baseScheme l ⟶ baseScheme k)
    (f g : baseScheme l ⟶ M.X) (hf : f ≫ M.p = b) (hg : g ≫ M.p = b)
    (h : ∀ n, baseInclusion l n ≫ f = baseInclusion l n ≫ g) : f = g := by
  letI : IsProper M.p := hM.1
  let F : baseScheme l ⟶ pullback M.p b := pullback.lift f (𝟙 _) (by simpa using hf)
  let G : baseScheme l ⟶ pullback M.p b := pullback.lift g (𝟙 _) (by simpa using hg)
  have he : F = G := by
    apply eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
      (PowerSeries l) (Ideal.span {PowerSeries.X}) (𝟙 _) (pullback.snd M.p b)
      (baseInclusion l) (fun _ => rfl) F G (pullback.lift_snd ..) (pullback.lift_snd ..)
    intro n
    apply pullback.hom_ext
    · simp only [Category.assoc, F, G, pullback.lift_fst]
      have hh : pullback.fst (𝟙 (Spec (.of (PowerSeries l)))) (baseInclusion l n) =
          pullback.snd (𝟙 (Spec (.of (PowerSeries l)))) (baseInclusion l n) ≫ baseInclusion l n := by
        simpa using (pullback.condition (f := 𝟙 (Spec (.of (PowerSeries l)))) (g := baseInclusion l n))
      rw [hh, Category.assoc, Category.assoc, h]
    · simp only [Category.assoc, F, G, pullback.lift_snd]
  simpa only [F, G, pullback.lift_fst] using
    congrArg (fun z => z ≫ pullback.fst M.p b) he

lemma multiplication_compatible (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    {r rb : ℕ} {hr : 0 < r} {hrb : 0 < rb}
    {T : Tower k r hr} {Tb : Tower l rb hrb}
    (h3b : 3 ≤ rb) (heb : Even rb)
    (M : Model k T) (Mb : Model l Tb) (hMb : IsModel l Tb Mb)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (sb : baseScheme l ⟶ Mb.X) (hsb : MarkedLift l Mb (zeroIndex rb hrb) 1 sb)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (Gb : Law l Mb) (hGb : IsOriginLaw l Mb sb hsb.1 Gb)
    (i : Spec (.of (LaurentSeries l)) ⟶ Spec (.of (LaurentSeries k)))
    (b : genericScheme l Mb ⟶ genericScheme k M)
    (H : IsPullback b (genericStructure l Mb) (genericStructure k M) i)
    (ho : genericPoint l Mb sb hsb.1 ≫ b = i ≫ genericPoint k M s hs.1) :
    ∀ n, multiplication l Mb Gb n ≫ b = b ≫ multiplication k M G n := by
  have hL : IsOriginLaw l Mb sb hsb.1 (law H G) := by
    constructor
    · intro V t
      apply (points H t).injective
      change points H t ((points H t).symm _) = _
      rw [Equiv.apply_symm_apply, hG.1]
      apply Subtype.ext
      change (t ≫ i) ≫ genericPoint k M s hs.1 =
        (t ≫ genericPoint l Mb sb hsb.1) ≫ b
      rw [Category.assoc, Category.assoc, ho]
    · intro V t x y
      change (points H t).symm (G.mul _ _ _) = (points H t).symm (G.mul _ _ _)
      rw [hG.2]
  obtain ⟨L, hL', hu⟩ := actual_generic_group_law l rb hrb h3b Tb heb Mb hMb sb hsb
  have heq : Gb = law H G := (hu Gb hGb).trans (hu _ hL).symm
  intro n
  rw [heq]
  have hn := congrArg Subtype.val (points_nsmul H G (genericStructure l Mb) (universalPoint l Mb) n)
  change multiplication l Mb (law H G) n ≫ b = _ at hn
  rw [hn]
  have hc := MultiplicationDifferential.comp_schemeNsmul G
    (genericStructure l Mb ≫ i) (points H (genericStructure l Mb) (universalPoint l Mb)) n
  change (𝟙 _ ≫ b) ≫ multiplication k M G n = _ at hc
  simpa only [Category.id_comp] using hc.symm


variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable (ι : k →+* l)
variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (Tl : Tower l r hr)
variable (M : Model k T) (Ml : Model l Tl)
variable (F : Ml.X ⟶ M.X) (hF : F ≫ M.p = Ml.p ≫ baseMorphism k l ι)
variable (ell : LaurentSeries k →+* LaurentSeries l) (hell : IsLaurentMap k l ι ell)

include hell in
lemma base_square : Spec.map (CommRingCat.ofHom ell) ≫ genericBase k =
    genericBase l ≫ baseMorphism k l ι := by
  simp only [genericBase, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext hell

def lift : genericScheme l Ml ⟶ genericScheme k M :=
  pullback.lift (genericInclusion l Ml ≫ F)
    (genericStructure l Ml ≫ Spec.map (CommRingCat.ofHom ell)) (by
      rw [Category.assoc, hF, ← Category.assoc]
      change (pullback.fst Ml.p (genericBase l) ≫ Ml.p) ≫ _ = _
      rw [pullback.condition, Category.assoc, Category.assoc, base_square k l ι ell hell]
      rfl)

lemma lift_inclusion : IsGenericLift k l T Tl M Ml F (lift k l ι T Tl M Ml F hF ell hell) :=
  pullback.lift_fst ..

lemma lift_structure : lift k l ι T Tl M Ml F hF ell hell ≫ genericStructure k M =
    genericStructure l Ml ≫ Spec.map (CommRingCat.ofHom ell) := pullback.lift_snd ..

lemma lift_unique (b : genericScheme l Ml ⟶ genericScheme k M)
    (hb : IsGenericLift k l T Tl M Ml F b) :
    b = lift k l ι T Tl M Ml F hF ell hell := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  exact hb.trans (lift_inclusion k l ι T Tl M Ml F hF ell hell).symm

lemma lift_cartesian (H : IsPullback F Ml.p M.p (baseMorphism k l ι)) :
    IsPullback (lift k l ι T Tl M Ml F hF ell hell) (genericStructure l Ml)
      (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)) := by
  have hh := (IsPullback.of_hasPullback Ml.p (genericBase l)).paste_horiz H
  rw [← base_square k l ι ell hell] at hh
  apply IsPullback.of_right (h₁₂ := genericInclusion k M) ?_
    (lift_structure k l ι T Tl M Ml F hF ell hell)
    (IsPullback.of_hasPullback M.p (genericBase k))
  rw [show lift k l ι T Tl M Ml F hF ell hell ≫ genericInclusion k M =
    genericInclusion l Ml ≫ F from lift_inclusion k l ι T Tl M Ml F hF ell hell]
  exact hh


open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137
open CoefficientPolygonTowerR0157

lemma point_coefficient (n : ℕ) (ρ : Chart k →+* Chart l) (hρ : IsChartMap k l ι ρ) :
    (markedPoint l n 1).comp (nodeMap k l ι ρ hρ n) =
      (coefficientMap k l ι n).comp (markedPoint k n 1) := by
  apply point_ext
  · ext z
    simp only [RingHom.comp_apply, nodeMap_base, point_base_apply]
  · simp only [RingHom.comp_apply, nodeMap_x, point_x]
    simp [markedUnit]
  · simp only [RingHom.comp_apply, nodeMap_y, point_y]
    simp [markedUnit, coefficientMap_parameter]

include hF in
lemma marked_origin (hM : IsModel k T M)
    (ρ : Chart k →+* Chart l) (hρ : IsChartMap k l ι ρ)
    (χ : Fin r → (chartScheme k ⟶ M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (χl : Fin r → (chartScheme l ⟶ Ml.X))
    (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j))
    (hFc : ∀ j, χl j ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ j)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (sl : baseScheme l ⟶ Ml.X) (hsl : MarkedLift l Ml (zeroIndex r hr) 1 sl) :
    sl ≫ F = baseMorphism k l ι ≫ s := by
  apply section_ext k l M hM (baseMorphism k l ι)
  · rw [Category.assoc, hF, ← Category.assoc, hsl.1, Category.id_comp]
  · rw [Category.assoc, hs.1, Category.comp_id]
  · intro n
    let j := zeroIndex r hr
    have hc : (Tl.atlas n).chart j ≫ Ml.inclusion n ≫ F =
        Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n)) ≫
          (T.atlas n).chart j ≫ M.inclusion n := by
      have hh := congrArg (fun z => Spec.map (CommRingCat.ofHom (reduction l n)) ≫ z) (hFc j)
      rw [← Category.assoc, (hχl j).2, Category.assoc] at hh
      have he : Spec.map (CommRingCat.ofHom (reduction l n)) ≫
          Spec.map (CommRingCat.ofHom ρ) =
          Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n)) ≫
            Spec.map (CommRingCat.ofHom (reduction k n)) := by
        simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun z => Spec.map (CommRingCat.ofHom z))
          (nodeMap_reduction k l ι ρ hρ n).symm
      calc
        _ = Spec.map (CommRingCat.ofHom (reduction l n)) ≫
            Spec.map (CommRingCat.ofHom ρ) ≫ χ j := by
          simpa only [Category.assoc] using hh
        _ = _ := by rw [← Category.assoc, he, Category.assoc, (hχ j).2]
    rw [← Category.assoc, hsl.2, Category.assoc]
    rw [markedSection, Category.assoc, hc]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      point_coefficient k l ι n ρ hρ, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    rw [← Category.assoc (baseInclusion l n), ← CoefficientModelBaseChangeR0157.stage_base,
      Category.assoc, hs.2]
    rfl

end CoefficientGenericKatoSquareR0157
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open CoefficientGenericKatoSquareR0157

/-- The unique generic coefficient lift preserves the marked origin and every
natural multiplication map, including multiplication by zero. -/
theorem coefficient_generic_kato_square :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (Tl : ArithmeticThetaInfinitesimalPolygonR0129.Tower l r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (Ml : ArithmeticThetaProjectiveEffectivityR0135.Model l Tl) (hMl : ArithmeticThetaProjectiveEffectivityR0135.IsModel l Tl Ml) (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l) (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (χl : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme l) Ml.X) (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j)) (F : Quiver.Hom Ml.X M.X) (hF : ArithmeticThetaCoefficientNormDescentR0157.IsModelMap k l ι T Tl M Ml ρ χ χl F) (ell : LaurentSeries k →+* LaurentSeries l) (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell) (he : Even r) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (sl : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme l) Ml.X) (hsl : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift l Ml (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 sl) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) (Gl : ArithmeticThetaMarkedGroupLawR0146.Law l Ml) (hGl : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw l Ml sl hsl.1 Gl) , ∃! b : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme l Ml) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M), ArithmeticThetaCoefficientNormDescentR0157.IsGenericLift k l T Tl M Ml F b ∧ ArithmeticThetaKatoExistenceR0151.IsTateBaseChange k l M Ml s hs.1 sl hsl.1 G Gl ell b := by
  intro k l _ _ _ _ ι r hr h3 T Tl M hM Ml hMl ρ hρ χ hχ χl hχl F hF ell hell he s hs sl hsl G hG Gl hGl
  let b := lift k l ι T Tl M Ml F hF.1.w ell hell
  have hb := lift_inclusion k l ι T Tl M Ml F hF.1.w ell hell
  have H := lift_cartesian k l ι T Tl M Ml F hF.1.w ell hell hF.1
  have hsF := marked_origin k l ι T Tl M Ml F hF.1.w hM ρ hρ χ hχ χl hχl hF.2 s hs sl hsl
  have ho : genericPoint l Ml sl hsl.1 ≫ b =
      Spec.map (CommRingCat.ofHom ell) ≫ genericPoint k M s hs.1 := by
    letI : IsOpenImmersion (genericInclusion k M) :=
      AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
    apply (cancel_mono (genericInclusion k M)).mp
    rw [Category.assoc, hb]
    change genericPoint l Ml sl hsl.1 ≫ pullback.fst Ml.p (genericBase l) ≫ F =
      Spec.map (CommRingCat.ofHom ell) ≫ genericPoint k M s hs.1 ≫ pullback.fst M.p (genericBase k)
    simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [Category.assoc, hsF, ← Category.assoc, ← base_square k l ι ell hell, Category.assoc]
  refine ⟨b, ⟨hb, H, ho, ?_⟩, fun b' hb' => ?_⟩
  · exact multiplication_compatible k l h3 he M Ml hMl s hs sl hsl G hG Gl hGl
      (Spec.map (CommRingCat.ofHom ell)) b H ho
  · exact lift_unique k l ι T Tl M Ml F hF.1.w ell hell b' hb'.1

end ArithmeticThetaCoefficientNormDescentR0157
#print axioms ArithmeticThetaCoefficientNormDescentR0157.coefficient_generic_kato_square
