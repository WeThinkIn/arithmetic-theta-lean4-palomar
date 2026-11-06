module

public import RamifiedModelMorphismR0154

@[expose] public section

/-! Marked sections under the actual ramified contraction. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0154
namespace RamifiedMarkedSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaModelSymmetriesR0137.AlgebraizedMarkedTransportR0137
open RamifiedPolygonTower
variable (k : Type u) [Field k] [CharZero k]

lemma coefficient_parameter (d : ℕ) (hd : 0 < d) (n : ℕ) :
    coefficientMap k d hd n (parameter k n) = parameter k n ^ d := by
  change trunc _ PowerSeries.X n (baseMap k d hd PowerSeries.X) = _
  simp only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_X, map_pow]
  rfl

lemma coefficient_unit (d : ℕ) (hd : 0 < d) (n : ℕ) (a : kˣ) :
    coefficientMap k d hd n (markedUnit k n a : R k n) = markedUnit k n a := by
  change trunc _ PowerSeries.X n (baseMap k d hd (PowerSeries.C (a : k))) = _
  simp only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_C]
  rfl

lemma point_ramification (d : ℕ) (hd : 0 < d) (n : ℕ) (a : kˣ)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd ⟨0, hd⟩ ρ) :
    (markedPoint k n a).comp (nodeMap k ρ hρ n) =
      (coefficientMap k d hd n).comp (markedPoint k n a) := by
  apply point_ext
  · ext z
    simp only [RingHom.comp_apply, nodeMap_base, point_base_apply]
  · simp only [RingHom.comp_apply, nodeMap_x, pow_zero, one_mul, point_x,
      coefficient_unit]
  · simp only [RingHom.comp_apply, nodeMap_y, Nat.sub_zero, map_mul, map_pow,
      tau, point_base_apply, point_y, coefficient_parameter]
    have ha : coefficientMap k d hd n (↑((markedUnit k n a)⁻¹) : R k n) =
        ↑((markedUnit k n a)⁻¹) := by
      simpa only [markedUnit, map_inv] using coefficient_unit k d hd n a⁻¹
    rw [ha, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]

lemma coarse_marked (r d : ℕ) (hd : 0 < d) (i : Fin r) :
    coarseIndex r d hd (markedIndex r d hd i) = i := by
  apply Fin.ext
  exact Nat.mul_div_cancel i.val hd

lemma residue_marked (r d : ℕ) (hd : 0 < d) (i : Fin r) :
    residueIndex r d hd (markedIndex r d hd i) = ⟨0, hd⟩ := by
  apply Fin.ext
  exact Nat.mul_mod_left i.val d

/-- Formal faithfulness for two maps into a separated target over the specified
ramified base map, obtained by using the ordinary base change of the target. -/
private lemma section_ext {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (b : baseScheme k ⟶ baseScheme k)
    (f g : baseScheme k ⟶ M.X) (hf : f ≫ M.p = b) (hg : g ≫ M.p = b)
    (h : ∀ n, baseInclusion k n ≫ f = baseInclusion k n ≫ g) : f = g := by
  letI : IsProper M.p := hM.1
  let F : baseScheme k ⟶ pullback M.p b := pullback.lift f (𝟙 _) (by simpa using hf)
  let G : baseScheme k ⟶ pullback M.p b := pullback.lift g (𝟙 _) (by simpa using hg)
  have he : F = G := by
    apply eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
      (PowerSeries k) (Ideal.span {PowerSeries.X}) (𝟙 _) (pullback.snd M.p b)
      (baseInclusion k) (fun _ => rfl) F G (pullback.lift_snd ..) (pullback.lift_snd ..)
    intro n
    apply pullback.hom_ext
    · simp only [Category.assoc, F, G, pullback.lift_fst]
      have hh : pullback.fst (𝟙 (Spec (.of (PowerSeries k)))) (baseInclusion k n) =
          pullback.snd (𝟙 (Spec (.of (PowerSeries k)))) (baseInclusion k n) ≫ baseInclusion k n := by
        simpa using (pullback.condition (f := 𝟙 (Spec (.of (PowerSeries k)))) (g := baseInclusion k n))
      rw [hh, Category.assoc, Category.assoc, h]
    · simp only [Category.assoc, F, G, pullback.lift_snd]
  simpa only [F, G, pullback.lift_fst] using
    congrArg (fun z => z ≫ pullback.fst M.p b) he

end RamifiedMarkedSections
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaKatoAnnularR0152
open RamifiedPolygonTower RamifiedMarkedSections

/-- Every unit-marked algebraized section has its prescribed ramified image. -/
theorem ramified_marked_sections :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d) (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (hrd : 0 < r*d) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model k Tb) (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel k Tb Mb) (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k)) (hρ : ∀ q, ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q (ρ q)) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) (M.X)) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (χb : Fin (r*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) (Mb.X)) (hχb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j (χb j)) (F : Quiver.Hom (Mb.X) (M.X)) (hF : ArithmeticThetaRamifiedPeriodR0154.IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F) (i : Fin r) (a : kˣ) (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) (M.X)) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M i a p) (pb : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) (Mb.X)) (hpb : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k Mb (ArithmeticThetaRamifiedPeriodR0154.markedIndex r d hd i) a pb), CategoryTheory.CategoryStruct.comp pb F = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRamifiedPeriodR0154.baseMorphism k d hd) p := by
  intro k _ _ d hd r hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF i a p hp pb hpb
  apply RamifiedMarkedSections.section_ext k M hM (baseMorphism k d hd)
  · rw [Category.assoc, hF.1, ← Category.assoc, hpb.1, Category.id_comp]
  · rw [Category.assoc, hp.1, Category.comp_id]
  · intro n
    let j := markedIndex r d hd i
    let q : Fin d := ⟨0, hd⟩
    have hc : (Tb.atlas n).chart j ≫ Mb.inclusion n ≫ F =
        Spec.map (CommRingCat.ofHom (nodeMap k (ρ q) (hρ q) n)) ≫
          (T.atlas n).chart i ≫ M.inclusion n := by
      have hh := congrArg (fun z => Spec.map (CommRingCat.ofHom (reduction k n)) ≫ z) (hF.2 j)
      rw [← Category.assoc, (hχb j).2, Category.assoc] at hh
      rw [show coarseIndex r d hd j = i from coarse_marked r d hd i,
        show residueIndex r d hd j = q from residue_marked r d hd i] at hh
      have he : Spec.map (CommRingCat.ofHom (reduction k n)) ≫
          Spec.map (CommRingCat.ofHom (ρ q)) =
          Spec.map (CommRingCat.ofHom (nodeMap k (ρ q) (hρ q) n)) ≫
            Spec.map (CommRingCat.ofHom (reduction k n)) := by
        simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun z => Spec.map (CommRingCat.ofHom z))
          (nodeMap_reduction k (ρ q) (hρ q) n).symm
      calc
        _ = Spec.map (CommRingCat.ofHom (reduction k n)) ≫
            Spec.map (CommRingCat.ofHom (ρ q)) ≫ χ i := by
          simpa only [Category.assoc] using hh
        _ = _ := by rw [← Category.assoc, he, Category.assoc, (hχ i).2]
    rw [← Category.assoc, hpb.2, Category.assoc]
    rw [markedSection, Category.assoc, hc]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      point_ramification k d hd n a (ρ q) (hρ q), CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    rw [← Category.assoc (baseInclusion k n), ← RamifiedModelMorphism.stage_base,
      Category.assoc, hp.2]
    rfl

end ArithmeticThetaRamifiedPeriodR0154
#print axioms ArithmeticThetaRamifiedPeriodR0154.ramified_marked_sections
