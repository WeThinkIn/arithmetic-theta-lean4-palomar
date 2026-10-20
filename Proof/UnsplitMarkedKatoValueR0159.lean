module

public import SplitMarkedKatoValueR0159
public import RationalValueFieldDescentR0159

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaMarkedKatoValuesR0159
namespace UnsplitMarkedKatoValueR0159
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLaurentNormR0064
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaUnsplitExpansionR0158

private lemma exists_model (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) :
    ∃ (T : Tower k r hr) (M : Model k T), IsModel k T M := by
  obtain ⟨T, _⟩ := ArithmeticThetaInfinitesimalPolygonR0129.proper_flat_polygon_tower k r hr h3
  obtain ⟨b, hb, hbr, _⟩ :=
    ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis k r hr h3 T (fun _ => 1) 3 (by omega)
  obtain ⟨j, hj⟩ := compatible_projective_embeddings k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩
  obtain ⟨M, hM, _⟩ := projective_tower_effectivity k r hr h3 T (fun _ => 1) b ⟨hb, hbr⟩ j hj
  exact ⟨T, M, hM⟩

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

private lemma generic_point_square
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    {r rb : ℕ} {hr : 0 < r} {hrb : 0 < rb}
    {T : Tower k r hr} {Tb : Tower l rb hrb} (M : Model k T) (Mb : Model l Tb)
    (B : baseScheme l ⟶ baseScheme k) (ell : LaurentSeries k →+* LaurentSeries l)
    (he : Spec.map (CommRingCat.ofHom ell) ≫ genericBase k = genericBase l ≫ B)
    (F : Mb.X ⟶ M.X) (f : genericScheme l Mb ⟶ genericScheme k M)
    (hf : f ≫ genericInclusion k M = genericInclusion l Mb ≫ F)
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (q : baseScheme l ⟶ Mb.X) (hq : q ≫ Mb.p = 𝟙 _)
    (hs : q ≫ F = B ≫ p) :
    ArithmeticThetaGenericEvaluationR0140.genericPoint l Mb q hq ≫ f =
      Spec.map (CommRingCat.ofHom ell) ≫ ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, hf]
  change ArithmeticThetaGenericEvaluationR0140.genericPoint l Mb q hq ≫ pullback.fst Mb.p (genericBase l) ≫ F =
    Spec.map (CommRingCat.ofHom ell) ≫ ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp ≫ pullback.fst M.p (genericBase k)
  simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, pullback.lift_fst, pullback.lift_fst_assoc]
  rw [Category.assoc, hs, ← Category.assoc, ← he, Category.assoc]

private lemma coefficient_literal (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell)
    (r c j : ℕ) (a : k) (g h : LaurentSeries k) :
    ell (literalValue k r c j a g h) = literalValue l r c j (ι a) (ell g) (ell h) := by
  have hs (e : ℤ) (a : k) : ell (HahnSeries.single e a) = HahnSeries.single e (ι a) := by
    rw [GammaBaseChangeNaturalityR0158.coefficientHom_eq _ _ ι ell hell]
    exact GammaBaseChangeNaturalityR0158.coefficientHom_single _ _ ι e a
  simp only [literalValue, map_mul, map_div₀, map_zpow₀, map_pow, map_neg,
    HahnSeries.C_apply, t, hs, map_one]

private lemma ramified_literal (k : Type) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell)
    (r c j : ℕ) (a : k) (g h : LaurentSeries k) :
    ell (literalValue k r c j a g h) = literalValue k (r*d) c (j*d) a (ell g) (ell h) := by
  have hs (e : ℤ) (a : k) : ell (HahnSeries.single e a) = HahnSeries.single ((d : ℤ)*e) a := by
    rw [GammaBaseChangeNaturalityR0158.ramificationHom_eq _ d hd ell hell]
    exact GammaBaseChangeNaturalityR0158.ramificationHom_single _ d hd e a
  have hC (a : k) : ell (HahnSeries.C a) = HahnSeries.C a := by
    simpa only [HahnSeries.C_apply, mul_zero] using hs 0 a
  have ht : ell (t k) = t k^d := by
    simpa [t, HahnSeries.single_pow] using hs 1 1
  simp only [literalValue, map_mul, map_div₀, map_zpow₀, map_pow, map_neg, hC, ht,
    ← pow_mul, Nat.mul_comm d]

namespace CoefficientSections
open ArithmeticThetaCoefficientNormDescentR0157
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137
open CoefficientPolygonTowerR0157
variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l)
private lemma point_coefficient (n : ℕ) (ρ : Chart k →+* Chart l)
    (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ) (a : kˣ) :
    (markedPoint l n (Units.map ι.toMonoidHom a)).comp (nodeMap k l ι ρ hρ n) =
      (coefficientMap k l ι n).comp (markedPoint k n a) := by
  have hu (a : kˣ) : coefficientMap k l ι n (markedUnit k n a : R k n) =
      (markedUnit l n (Units.map ι.toMonoidHom a) : R l n) := by
    change trunc _ PowerSeries.X n (PowerSeries.map ι (PowerSeries.C (a : k))) =
      trunc _ PowerSeries.X n (PowerSeries.C (ι (a : k)))
    rw [PowerSeries.map_C]
  apply point_ext
  · ext z
    simp only [RingHom.comp_apply, nodeMap_base, point_base_apply]
  · simp only [RingHom.comp_apply, nodeMap_x, point_x, hu]
  · simp only [RingHom.comp_apply, nodeMap_y, point_y, map_mul, coefficientMap_parameter]
    congr 1
    simpa only [markedUnit, map_inv] using (hu a⁻¹).symm

variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (Tl : Tower l r hr)
variable (M : Model k T) (Ml : Model l Tl)
variable (F : Ml.X ⟶ M.X) (hF : F ≫ M.p = Ml.p ≫ baseMorphism k l ι)
include hF in
private lemma marked_section (hM : IsModel k T M)
    (ρ : Chart k →+* Chart l) (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)
    (χ : Fin r → (chartScheme k ⟶ M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (χl : Fin r → (chartScheme l ⟶ Ml.X))
    (hχl : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap l Ml j (χl j))
    (hFc : ∀ j, χl j ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ j)
    (j : Fin r) (a : kˣ)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M j a s)
    (sl : baseScheme l ⟶ Ml.X) (hsl : MarkedLift l Ml j (Units.map ι.toMonoidHom a) sl) :
    sl ≫ F = baseMorphism k l ι ≫ s := by
  apply section_ext k l M hM (baseMorphism k l ι)
  · rw [Category.assoc, hF, ← Category.assoc, hsl.1, Category.id_comp]
  · rw [Category.assoc, hs.1, Category.comp_id]
  · intro n
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
      point_coefficient k l ι n ρ hρ a, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    rw [← Category.assoc (baseInclusion l n), ← CoefficientModelBaseChangeR0157.stage_base,
      Category.assoc, hs.2]
    rfl

end CoefficientSections

private theorem split_field_value :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) c) (j : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j a p) (N : ℕ) (hN : 0 < N) (hcopN : Nat.Coprime c N) (hidx : r ∣ N*j.val) (haN : (a : k)^N = 1) (hne : j.val ≠ 0 ∨ (a : k) ≠ 1) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g → ∀ (γ δ : LaurentSeries k), ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ → ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ → ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g (ArithmeticThetaMarkedKatoValuesR0159.literalValue k r c j.val (a : k) γ δ) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ c hc hcop ζ hζ j a p hp N hN hcopN hidx haN hne g hg γ δ hγ hδ
  classical
  have Hχ0 : ∀ j : Fin r, ∃ χj, IsChartMap k M j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k r hr h3 T M hM j
    exact ⟨χj, hj⟩
  choose χ hχ using Hχ0
  have Hφ0 : ∀ j : Fin r, ∃ φj, IsChartFieldMap k M (χ j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k r hr h3 T M hM j (χ j) (hχ j)
    exact ⟨φj, hj.1⟩
  choose φ hφ using Hφ0
  let d := 2*c
  have hd : 0 < d := by dsimp [d]; omega
  have hrd : 0 < r*d := Nat.mul_pos hr hd
  have h3d : 3 ≤ r*d := h3.trans (Nat.le_mul_of_pos_right r hd)
  have hed : Even (r*d) := he.mul_right d
  have hcr : c ∣ r*d := by dsimp [d]; exact dvd_mul_of_dvd_right (dvd_mul_left c 2) r
  obtain ⟨Tb, Mb, hMb⟩ := exists_model k (r*d) hrd h3d
  letI : AlgebraicGeometry.IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3d Mb hMb
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k Mb hMb
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme k Mb) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Mb)
  obtain ⟨sb, hsb, _⟩ := marked_section_algebraization k (r*d) hrd h3d Tb Mb hMb
    (zeroIndex (r*d) hrd) 1
  obtain ⟨Gb, hGb, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb
  have Hχ : ∀ j : Fin (r*d), ∃ χj, IsChartMap k Mb j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k (r*d) hrd h3d Tb Mb hMb j
    exact ⟨χj, hj⟩
  choose χb hχb using Hχ
  have Hφ : ∀ j : Fin (r*d), ∃ φj, IsChartFieldMap k Mb (χb j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k (r*d) hrd h3d Tb Mb hMb j (χb j) (hχb j)
    exact ⟨φj, hj.1⟩
  choose φb hφb using Hφ
  have Hρ : ∀ q : Fin d, ∃ (ρq : Chart k →+* Chart k) (Eq : ChartField k →+* ChartField k),
      ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q ρq ∧
      ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k ρq Eq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := ArithmeticThetaRamifiedPeriodR0154.completed_chart_ramification k d hd q
    obtain ⟨Eq, hEq, _⟩ := hρq.2.2
    exact ⟨ρq, Eq, hρq.1, hEq⟩
  choose ρ E hρ hE using Hρ
  obtain ⟨F, hF, _⟩ := ArithmeticThetaRamifiedPeriodR0154.ramified_model_morphism k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k d hd
  obtain ⟨b, hb, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_generic_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1
  obtain ⟨α, hα, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_function_field_expansion k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    φ hφ φb hφb E hE
  have hbase := ArithmeticThetaRamifiedPeriodR0155.ramified_kato_base_change k d hd r hr h3 hrd
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    he hed s hs sb hsb G hG Gb hGb
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    k (r*d) hrd h3d Tb hed Mb hMb sb hsb Gb hGb ell b hbase α hα.1 c hc hcop).2 g hg
  let jb := ArithmeticThetaRamifiedPeriodR0154.markedIndex r d hd j
  obtain ⟨pb, hpb, _⟩ := marked_section_algebraization k (r*d) hrd h3d Tb Mb hMb jb a
  have hpF := ArithmeticThetaRamifiedPeriodR0154.ramified_marked_sections
    k d hd r hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 j a p hp pb hpb
  have hpq := generic_point_square k k M Mb
    (ArithmeticThetaRamifiedPeriodR0154.baseMorphism k d hd) ell
    (ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.base_square k d hd ell hell.1)
    F b hb.1 p hp.1 pb hpb.1 hpF
  have hidxb : r*d ∣ N*jb.val := by
    change r*d ∣ N*(j.val*d)
    simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul_right hidx d
  have hneb : jb.val ≠ 0 ∨ (a : k) ≠ 1 := by
    rcases hne with hj | ha
    · exact Or.inl (Nat.mul_ne_zero hj (Nat.ne_of_gt hd))
    · exact Or.inr ha
  have hγb := gamma_base_change_naturality.2 k d hd ell hell.1 r j.val (a : k) γ hr (Units.ne_zero a) hγ
  have hδb : IsGamma k (r*d) (c*jb.val) ((a : k)^c) (ell δ) := by
    simpa only [jb, ArithmeticThetaRamifiedPeriodR0154.markedIndex, Nat.mul_assoc] using
      gamma_base_change_naturality.2 k d hd ell hell.1 r (c*j.val) ((a : k)^c) δ hr
        (pow_ne_zero _ (Units.ne_zero a)) hδ
  have hv := split_marked_kato_value k (r*d) hrd h3d hed Tb Mb hMb sb hsb Gb hGb
    c hc hcop hcr ζ hζ χb hχb φb hφb jb a pb hpb N hN hcopN hidxb haN hneb
    (α g) hK (ell γ) (ell δ) hγb hδb
  apply (rational_value_field_descent (LaurentSeries k) (LaurentSeries k) ell
    (genericScheme k M) (genericScheme k Mb) (genericStructure k M) (genericStructure k Mb)
    b hbase.1 α hα.1 (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1)
    (ArithmeticThetaGenericEvaluationR0140.genericPoint k Mb pb hpb.1)
    (pullback.lift_snd ..) (pullback.lift_snd ..) hpq g _).mpr
  rw [ramified_literal k d hd ell hell.1]
  exact hv

end UnsplitMarkedKatoValueR0159
open UnsplitMarkedKatoValueR0159
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLaurentNormR0064
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaUnsplitExpansionR0158

/-- The actual marked Kato value over the original field and period. -/
theorem unsplit_marked_kato_value :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (c : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (j : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j a p) (N : ℕ) (hN : 0 < N) (hcopN : Nat.Coprime c N) (hidx : r ∣ N*j.val) (haN : (a : k)^N = 1) (hne : j.val ≠ 0 ∨ (a : k) ≠ 1) (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G c g → ∀ (γ δ : LaurentSeries k), ArithmeticThetaLaurentNormR0064.IsGamma k r j.val (a : k) γ → ArithmeticThetaLaurentNormR0064.IsGamma k r (c*j.val) ((a : k)^c) δ → ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g (ArithmeticThetaMarkedKatoValuesR0159.literalValue k r c j.val (a : k) γ δ) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ c hc hcop j a p hp N hN hcopN hidx haN hne g hg γ δ hγ hδ
  classical
  have Hχ0 : ∀ j : Fin r, ∃ χj, IsChartMap k M j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k r hr h3 T M hM j
    exact ⟨χj, hj⟩
  choose χ hχ using Hχ0
  have Hφ0 : ∀ j : Fin r, ∃ φj, IsChartFieldMap k M (χ j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k r hr h3 T M hM j (χ j) (hχ j)
    exact ⟨φj, hj.1⟩
  choose φ hφ using Hφ0
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  letI : NeZero c := ⟨by omega⟩
  letI : NeZero (c : k) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot l c
  let ζ : lˣ := Units.mk0 z (hz.ne_zero (by omega))
  have hζ : IsPrimitiveRoot (ζ : l) c := hz
  obtain ⟨Tl, Ml, hMl⟩ := exists_model l r hr h3
  letI : AlgebraicGeometry.IsIntegral (genericScheme l Ml) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral l h3 Ml hMl
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation l Ml hMl
  letI : AlgebraicGeometry.IsLocallyNoetherian (genericScheme l Ml) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (genericStructure l Ml)
  obtain ⟨sl, hsl, _⟩ := marked_section_algebraization l r hr h3 Tl Ml hMl (zeroIndex r hr) 1
  obtain ⟨Gl, hGl, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    l r hr h3 Tl he Ml hMl sl hsl
  have Hχ : ∀ j : Fin r, ∃ χj, IsChartMap l Ml j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps l r hr h3 Tl Ml hMl j
    exact ⟨χj, hj⟩
  choose χl hχl using Hχ
  have Hφ : ∀ j : Fin r, ∃ φj, IsChartFieldMap l Ml (χl j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps l r hr h3 Tl Ml hMl j (χl j) (hχl j)
    exact ⟨φj, hj.1⟩
  choose φl hφl using Hφ
  obtain ⟨Hell, Hρ, HE⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι
  obtain ⟨ell, hell, _⟩ := Hell
  obtain ⟨ρ, hρ, _⟩ := Hρ
  obtain ⟨E, hE, _⟩ := HE ρ hρ.1
  obtain ⟨F, hF, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_model_base_change
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl
  obtain ⟨b, hb, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_generic_kato_square
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 χ hχ χl hχl F hF ell hell
    he s hs sl hsl G hG Gl hGl
  obtain ⟨α, hα, _⟩ := ArithmeticThetaCoefficientNormDescentR0157.coefficient_function_field_expansion
    k l ι r hr h3 T Tl M hM Ml hMl ρ hρ.1 E hE χ hχ χl hχl F hF ell hell b hb.1 φ hφ φl hφl
  have hK := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    l r hr h3 Tl he Ml hMl sl hsl Gl hGl ell b hb.2 α hα.1 c hc hcop).2 g hg
  let al : lˣ := Units.map ι.toMonoidHom a
  obtain ⟨pl, hpl, _⟩ := marked_section_algebraization l r hr h3 Tl Ml hMl j al
  have hpF := CoefficientSections.marked_section k l ι T Tl M Ml F hF.1.w hM
    ρ hρ.1 χ hχ χl hχl hF.2 j a p hp pl hpl
  have hpq := generic_point_square k l M Ml
    (ArithmeticThetaCoefficientNormDescentR0157.baseMorphism k l ι) ell
    (ArithmeticThetaCoefficientNormDescentR0157.CoefficientGenericKatoSquareR0157.base_square k l ι ell hell)
    F b hb.1 p hp.1 pl hpl.1 hpF
  have hal : (al : l) = ι (a : k) := rfl
  have haNl : (al : l)^N = 1 := by rw [hal, ← map_pow, haN, map_one]
  have hnel : j.val ≠ 0 ∨ (al : l) ≠ 1 := by
    rcases hne with hj | ha
    · exact Or.inl hj
    · right
      rw [hal, ← map_one ι]
      exact fun h => ha (ι.injective h)
  have hγl : IsGamma l r j.val (al : l) (ell γ) :=
    gamma_base_change_naturality.1 k l ι ell hell r j.val (a : k) γ hr (Units.ne_zero a) hγ
  have hδl : IsGamma l r (c*j.val) ((al : l)^c) (ell δ) := by
    rw [hal, ← map_pow]
    exact gamma_base_change_naturality.1 k l ι ell hell r (c*j.val) ((a : k)^c) δ hr
      (pow_ne_zero _ (Units.ne_zero a)) hδ
  have hv := split_field_value l r hr h3 he Tl Ml hMl sl hsl Gl hGl c hc hcop ζ hζ
    j al pl hpl N hN hcopN hidx haNl hnel (α g) hK (ell γ) (ell δ) hγl hδl
  apply (rational_value_field_descent (LaurentSeries k) (LaurentSeries l) ell
    (genericScheme k M) (genericScheme l Ml) (genericStructure k M) (genericStructure l Ml)
    b hb.2.1 α hα.1 (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1)
    (ArithmeticThetaGenericEvaluationR0140.genericPoint l Ml pl hpl.1)
    (pullback.lift_snd ..) (pullback.lift_snd ..) hpq g _).mpr
  rw [coefficient_literal k l ι ell hell]
  exact hv

#print axioms unsplit_marked_kato_value
end ArithmeticThetaMarkedKatoValuesR0159
