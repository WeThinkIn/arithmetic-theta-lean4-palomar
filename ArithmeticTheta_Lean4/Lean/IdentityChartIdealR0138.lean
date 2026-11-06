import IdentityThetaSectionsDefinitionsR0138

/-! Local equations of the single identity section, at every thickness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace IdentityChartIdealR0138
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
open GlobalMarkedIdealChartsR0133

private lemma regular_neg {S : Type*} [CommRing S] {x : S} (h : IsRegular x) :
    IsRegular (-x) := by
  have hl : IsLeftRegular (-x) := by
    intro a b hab
    apply h.1
    simpa only [neg_mul, neg_inj] using hab
  exact ⟨hl, fun a b hab => hl (by simpa only [mul_comm] using hab)⟩

variable (k : Type u) [Field k] [CharZero k]

lemma right_equation (n : ℕ) :
    RingHom.ker (markedPoint k n 1) = Ideal.span ({1 - coordX k n} : Set (A k n)) ∧
    IsRegular (1 - coordX k n) := by
  have h := marked_cartier_equation k n 1
  have he : markedEquation k n 1 = coordX k n - 1 := by
    simp [markedEquation, markedUnit]
  rw [he] at h
  constructor
  · exact h.2.trans (by simpa only [neg_sub] using
      (Ideal.span_singleton_neg (x := coordX k n - 1)).symm)
  · simpa only [neg_sub] using regular_neg h.1

lemma left_equation (n : ℕ) :
    RingHom.ker (leftMarkedPoint k n 1) = Ideal.span ({1 - coordY k n} : Set (A k n)) ∧
    IsRegular (1 - coordY k n) := by
  have he : coordY k n - base k n (↑((markedUnit k n (1 : kˣ))⁻¹)) =
      coordY k n - 1 := by simp [markedUnit]
  have hk := LocalMarkedPairR0133.left_kernel k n 1
  have hr := LocalMarkedPairR0133.left_regular k n 1
  rw [he] at hk hr
  constructor
  · exact hk.trans (by simpa only [neg_sub] using
      (Ideal.span_singleton_neg (x := coordY k n - 1)).symm)
  · simpa only [neg_sub] using regular_neg hr

lemma next_zero_iff (r : ℕ) (hr : 0 < r) (i : Fin r) :
    next r hr i = zeroIndex r hr ↔ i.val + 1 = r := by
  constructor
  · intro h
    have hm : (i.val + 1) % r = 0 := congrArg Fin.val h
    have hi := i.isLt
    by_contra hn
    have hl : i.val + 1 < r := by omega
    rw [Nat.mod_eq_of_lt hl] at hm
    omega
  · intro h
    apply Fin.ext
    simp [next, zeroIndex, h]

lemma chart_result (r n : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (i : Fin r) :
    ArithmeticThetaIdentitySectionsR0138.chartIdeal k D i =
      Ideal.span ({equation k r n i} : Set (A k n)) ∧ IsRegular (equation k r n i) := by
  let : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  let : IsOpenImmersion (D.chart i) := D.chart_open i
  let : IsSeparated D.p := D.isSeparated hE
  let s := markedSection k r n hr D (zeroIndex r hr) 1
  have hs : s ≫ D.p = 𝟙 _ := SmoothMarkedSections.section_over k r n hr D _ _
  let : IsClosedImmersion (s ≫ D.p) := by rw [hs]; infer_instance
  let : IsClosedImmersion s := IsClosedImmersion.of_comp s D.p
  by_cases hi : i.val = 0
  · have hi0 : i = zeroIndex r hr := Fin.ext hi
    have hin : i.val + 1 ≠ r := by omega
    have he : equation k r n i = 1 - coordX k n := by simp only [equation, if_pos hi, if_neg hin, mul_one]
    rw [he]
    refine ⟨?_, (right_equation k n).2⟩
    have hf : (stageIdeal k D).comap (D.chart i) =
        (Spec.map (CommRingCat.ofHom (markedPoint k n 1))).ker := by
      exact comap_kernel_factor (D.chart i) s _ (by dsimp [s, markedSection]; rw [hi0])
    unfold ArithmeticThetaIdentitySectionsR0138.chartIdeal
    rw [hf, spec_kernel, (right_equation k n).1]
  · by_cases hn : i.val + 1 = r
    · have hni : next r hr i = zeroIndex r hr := (next_zero_iff r hr i).2 hn
      have he : equation k r n i = 1 - coordY k n := by simp [equation, hi, hn]
      rw [he]
      refine ⟨?_, (left_equation k n).2⟩
      have hf : (stageIdeal k D).comap (D.chart i) =
          (Spec.map (CommRingCat.ofHom (leftMarkedPoint k n 1))).ker := by
        apply comap_kernel_factor (D.chart i) s
        simpa only [hni] using left_factor k r n hr hE D i 1
      unfold ArithmeticThetaIdentitySectionsR0138.chartIdeal
      rw [hf, spec_kernel, (left_equation k n).1]
    · have hj : zeroIndex r hr ≠ i := by
        intro h
        exact hi (congrArg Fin.val h.symm)
      have hjn : zeroIndex r hr ≠ next r hr i := fun h =>
        hn ((next_zero_iff r hr i).1 h.symm)
      have hf : (stageIdeal k D).comap (D.chart i) = ⊤ :=
        comap_kernel_disjoint (D.chart i) s (chart_disjoint_other k r n hr D i _ hj hjn 1)
      have he : equation k r n i = 1 := by simp [equation, hi, hn]
      rw [he]
      constructor
      · unfold ArithmeticThetaIdentitySectionsR0138.chartIdeal
        rw [hf]
        simp only [Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.span_singleton_one]
        exact Ideal.map_top _
      · exact isRegular_one

end IdentityChartIdealR0138

/-- The actual single marked kernel has its prescribed regular equation on every chart. -/
theorem identity_chart_ideal :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E, ∀ i : Fin r,
    ArithmeticThetaIdentitySectionsR0138.chartIdeal k D i = Ideal.span
      ({ArithmeticThetaIdentitySectionsR0138.equation k r n i} :
        Set (ArithmeticThetaInfinitesimalPolygonR0129.A k n)) ∧
    IsRegular (ArithmeticThetaIdentitySectionsR0138.equation k r n i) := by
  intro k _ _ r n hr hr3 E hE D i
  exact IdentityChartIdealR0138.chart_result k r n hr hr3 E hE D i

end ArithmeticThetaIdentitySectionsR0138
