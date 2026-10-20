module

public import GlobalMarkedIdealChartsR0133

@[expose] public section

/-! Pullback of the actual marked ideal through every truncation in the tower. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace MarkedIdealTowerBaseChangeR0133
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131

lemma affine_comap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  apply eq_of_forall_ge_iff
  intro J
  let K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop J
  have hK : K.ideal ⟨⊤, isAffineOpen_top X⟩ = J := by simp [K]
  have h1 : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ ≤ J ↔ I.comap f ≤ K := by
    rw [← hK]
    exact ⟨Scheme.IdealSheafData.le_of_isAffine, fun h => h _⟩
  rw [h1, ← Scheme.IdealSheafData.le_map_iff_comap_le]
  rw [Ideal.map_le_iff_le_comap]
  have hm : (K.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ = J.comap f.appTop.hom := by
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simp [K, Scheme.Hom.appTop]
  rw [← hm]
  exact ⟨fun h => h _, Scheme.IdealSheafData.le_of_isAffine⟩

def specIdeal {S : Type u} [CommRing S] (I : (Spec (CommRingCat.of S)).IdealSheafData) :
    Ideal S := Ideal.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      (I.ideal ⟨⊤, isAffineOpen_top _⟩)

lemma specIdeal_injective {S : Type u} [CommRing S] :
    Function.Injective (specIdeal (S := S)) := by
  intro I J h
  apply Scheme.IdealSheafData.ext_of_isAffine
  have he := congrArg (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom) h
  have hi : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom = RingHom.id _ := by
    ext x
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id x
  simpa only [specIdeal, Ideal.map_map, hi, Ideal.map_id] using he

lemma specIdeal_comap {S Q : Type u} [CommRing S] [CommRing Q]
    (f : S →+* Q) (I : (Spec (CommRingCat.of S)).IdealSheafData) :
    specIdeal (I.comap (Spec.map (CommRingCat.ofHom f))) = (specIdeal I).map f := by
  unfold specIdeal
  rw [affine_comap, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

lemma atlas_ext (k : Type u) [Field k] [CharZero k] (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    {I J : D.X.IdealSheafData}
    (h : ∀ i, I.comap (D.chart i) = J.comap (D.chart i)) : I = J := by
  let : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  let : ∀ i, IsOpenImmersion (D.chart i) := D.chart_open
  let U : Fin r → D.X.affineOpens := fun i =>
    ⟨D.chart i ''ᵁ ⊤, (isAffineOpen_top (specA k n)).image_of_isOpenImmersion _⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    obtain ⟨i, p, rfl⟩ := D.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, p, trivial, rfl⟩
  · intro i
    have hh := congrArg (fun K : (specA k n).IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top _⟩) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hh
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((D.chart i).appIso ⊤).inv).2 hh

lemma pairEquation_reduction (k : Type u) [Field k] [CharZero k]
    (n N : ℕ) (h : n ≤ N) (a b : kˣ) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      (pairEquation k N a b) = pairEquation k n a b := by
  simp [pairEquation, markedEquation, coordX, coordY, base, markedUnit,
    truncReduce, truncMap, trunc]
  simp only [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.factor_mk]

end MarkedIdealTowerBaseChangeR0133

open AlgebraicGeometry ArithmeticThetaInfinitesimalPolygonR0129
/-- The intersection ideal of all marked sections commutes with every tower reduction. -/
theorem marked_ideal_tower_base_change :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ),
    ∀ (n N : ℕ) (h : n ≤ N),
      (markedIdeal k r N hr (T.atlas N) a).comap (T.transition n N h) =
        markedIdeal k r n hr (T.atlas n) a := by
  intro k _ _ r hr hr3 T a n N h
  apply MarkedIdealTowerBaseChangeR0133.atlas_ext k r n hr (T.atlas n)
  intro i
  rw [← Scheme.IdealSheafData.comap_comp, (T.transition_spec n N h).2 i,
    Scheme.IdealSheafData.comap_comp]
  apply MarkedIdealTowerBaseChangeR0133.specIdeal_injective
  rw [chartReduction, MarkedIdealTowerBaseChangeR0133.specIdeal_comap]
  change Ideal.map _ (chartIdeal k r N hr (T.atlas N) a i) =
    chartIdeal k r n hr (T.atlas n) a i
  rw [global_marked_ideal_charts k r N hr hr3 _ (T.overlap_spec N),
    global_marked_ideal_charts k r n hr hr3 _ (T.overlap_spec n),
    Ideal.map_span, Set.image_singleton,
    MarkedIdealTowerBaseChangeR0133.pairEquation_reduction]

end ArithmeticThetaPolygonCartierR0133
