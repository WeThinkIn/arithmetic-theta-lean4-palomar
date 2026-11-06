import ModelSymmetriesDefinitionsR0137

/-! Scalar translations on the actual cyclic infinitesimal atlas. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
namespace TowerScalarTranslation
open CategoryTheory AlgebraicGeometry ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]

@[simp] lemma scalar_one (n : ℕ) : scalar k n 1 = 1 := by simp [scalar]
@[simp] lemma scalar_mul (n : ℕ) (a b : k) :
    scalar k n (a*b) = scalar k n a * scalar k n b := by simp [scalar]
lemma scalar_unit (n : ℕ) (a : kˣ) : IsUnit (scalar k n (a : k)) :=
  ((a.isUnit.map PowerSeries.C).map (trunc _ PowerSeries.X n)).map (base k n)
@[simp] lemma scalar_inv_mul (n : ℕ) (a : kˣ) :
    scalar k n (↑a⁻¹) * scalar k n (↑a) = 1 := by rw [← scalar_mul]; simp
@[simp] lemma scalar_mul_inv (n : ℕ) (a : kˣ) :
    scalar k n (↑a) * scalar k n (↑a⁻¹) = 1 := by rw [← scalar_mul]; simp

def ringMap (n : ℕ) (a : kˣ) : A k n →+* A k n :=
  mkPoint (base k n) (scalar k n a * coordX k n)
    (scalar k n (↑a⁻¹) * coordY k n) (by
      calc
        _ = (scalar k n a * scalar k n (↑a⁻¹)) *
            (coordX k n * coordY k n) := by ring
        _ = _ := by rw [scalar_mul_inv, one_mul, coordX_mul_coordY])
@[simp] lemma ringMap_x (n : ℕ) (a : kˣ) :
    ringMap k n a (coordX k n) = scalar k n a * coordX k n := mkPoint_x ..
@[simp] lemma ringMap_y (n : ℕ) (a : kˣ) :
    ringMap k n a (coordY k n) = scalar k n (↑a⁻¹) * coordY k n := mkPoint_y ..
@[simp] lemma ringMap_base (n : ℕ) (a : kˣ) (b : R k n) :
    ringMap k n a (base k n b) = base k n b := by
  have h : (ringMap k n a).comp (base k n) = base k n := mkPoint_base ..
  exact RingHom.congr_fun h b
@[simp] lemma ringMap_scalar (n : ℕ) (a : kˣ) (b : k) :
    ringMap k n a (scalar k n b) = scalar k n b := ringMap_base ..
lemma coordinates (n : ℕ) (a : kˣ) : CoordinateMap k n a false (ringMap k n a) :=
  ⟨ringMap_base k n a, ringMap_x k n a, ringMap_y k n a⟩
lemma coordinates_unique (n : ℕ) (a : kˣ) (f : A k n →+* A k n)
    (hf : CoordinateMap k n a false f) : f = ringMap k n a := by
  apply point_ext
  · ext b; exact (hf.1 b).trans (ringMap_base k n a b).symm
  · exact hf.2.1.trans (ringMap_x k n a).symm
  · exact hf.2.2.trans (ringMap_y k n a).symm
lemma ringMap_inv (n : ℕ) (a : kˣ) :
    (ringMap k n a).comp (ringMap k n a⁻¹) = RingHom.id _ := by
  apply point_ext
  · ext b; simp
  · simp [RingHom.comp_apply, ← mul_assoc, ← scalar_mul]
  · simp [RingHom.comp_apply, ← mul_assoc, ← scalar_mul]

def chartMap (n : ℕ) (a : kˣ) : specA k n ⟶ specA k n :=
  Spec.map (CommRingCat.ofHom (ringMap k n a))
lemma chartMap_inv (n : ℕ) (a : kˣ) :
    chartMap k n a ≫ chartMap k n a⁻¹ = 𝟙 _ := by
  rw [chartMap, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ringMap_inv]; exact Spec.map_id _
lemma chartMap_over (n : ℕ) (a : kˣ) :
    chartMap k n a ≫ structureMap k n = structureMap k n := by
  rw [chartMap, structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b
  exact ringMap_base k n a b


lemma restriction_x_unit (n : ℕ) : IsUnit (restriction k n true (coordX k n)) :=
  (IsLocalization.Away.algebraMap_isUnit (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k true)).map
    (trunc _ (openParameter k true) n)

def overlapMap (n : ℕ) (a : kˣ) : B k n true →+* B k n true :=
  openPoint ((restriction k n true).comp (ringMap k n a)) true (by
    change IsUnit (restriction k n true (ringMap k n a (coordX k n)))
    rw [ringMap_x, map_mul]
    exact ((scalar_unit k n a).map _).mul (restriction_x_unit k n))
lemma overlap_right (n : ℕ) (a : kˣ) :
    (overlapMap k n a).comp (restriction k n true) =
      (restriction k n true).comp (ringMap k n a) := openPoint_restriction ..
lemma overlap_right_apply (n : ℕ) (a : kˣ) (z : A k n) :
    overlapMap k n a (restriction k n true z) = restriction k n true (ringMap k n a z) :=
  RingHom.congr_fun (overlap_right k n a) z

lemma overlap_left (n : ℕ) (a : kˣ) (E : B k n false ≃+* B k n true)
    (hE : IsAdjacent k n E) :
    (overlapMap k n a).comp (E.toRingHom.comp (restriction k n false)) =
      (E.toRingHom.comp (restriction k n false)).comp (ringMap k n a) := by
  let L := E.toRingHom.comp (restriction k n false)
  let R := restriction k n true
  let o := overlapMap k n a
  have hb (b : ArithmeticThetaInfinitesimalPolygonR0129.R k n) : L (base k n b) = R (base k n b) :=
    RingHom.congr_fun (adjacent_base hE) b
  have hs (b : k) : L (scalar k n b) = R (scalar k n b) := hb _
  have hor (z : A k n) : o (R z) = R (ringMap k n a z) := overlap_right_apply k n a z
  have hxy : L (coordY k n) * R (coordX k n) = 1 := adjacent_y_mul_x hE
  have hy : o (L (coordY k n)) = L (ringMap k n a (coordY k n)) := by
    apply (((scalar_unit k n a).map R).mul (restriction_x_unit k n)).mul_right_cancel
    calc
      o (L (coordY k n)) * (R (scalar k n a) * R (coordX k n)) =
          o (L (coordY k n) * R (coordX k n)) := by rw [map_mul, hor, ringMap_x, map_mul]
      _ = 1 := by rw [hxy, map_one]
      _ = L (ringMap k n a (coordY k n)) *
          (R (scalar k n a) * R (coordX k n)) := by
        rw [ringMap_y, map_mul, hs]
        calc
          1 = R (scalar k n (↑a⁻¹) * scalar k n a) *
              (L (coordY k n) * R (coordX k n)) := by rw [scalar_inv_mul, map_one, hxy, one_mul]
          _ = _ := by rw [map_mul]; ring
  apply point_ext
  · ext b
    change o (L (base k n b)) = L (ringMap k n a (base k n b))
    rw [hb, hor, ringMap_base, hb]
  · change o (L (coordX k n)) = L (ringMap k n a (coordX k n))
    have hu : IsUnit (L (ringMap k n a (coordY k n))) := by
      rw [ringMap_y, map_mul]
      exact ((scalar_unit k n a⁻¹).map L).mul (IsUnit.of_mul_eq_one _ hxy)
    apply hu.mul_right_cancel
    rw [← hy, ← map_mul, ← map_mul, coordX_mul_coordY, hb, hor, ringMap_base]
    rw [hy, ← map_mul, ← map_mul, coordX_mul_coordY, ringMap_base, hb]
  · exact hy



lemma right_square (n : ℕ) (a : kˣ) :
    rightLeg k n ≫ chartMap k n a =
      Spec.map (CommRingCat.ofHom (overlapMap k n a)) ≫ rightLeg k n := by
  simp only [rightLeg, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (overlap_right k n a).symm
lemma left_square (n : ℕ) (a : kˣ) (E : B k n false ≃+* B k n true)
    (hE : IsAdjacent k n E) :
    leftLeg k n E ≫ chartMap k n a =
      Spec.map (CommRingCat.ofHom (overlapMap k n a)) ≫ leftLeg k n E := by
  simp only [leftLeg, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (overlap_left k n a E hE).symm

variable {k} {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
def stageHom (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ) : D.X ⟶ D.X :=
  D.desc (fun i => chartMap k n a ≫ D.chart i) (by
    intro i
    rw [← Category.assoc, left_square k n a E hE, Category.assoc,
      (D.adjacent i).w, ← Category.assoc, ← right_square, Category.assoc])
@[reassoc (attr := simp)] lemma stageHom_chart (D : Atlas k r n hr E)
    (hE : IsAdjacent k n E) (a : kˣ) (i : Fin r) :
    D.chart i ≫ stageHom D hE a = chartMap k n a ≫ D.chart i :=
  D.chart_desc _ _ i
lemma stageHom_over (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ) :
    stageHom D hE a ≫ D.p = D.p := by
  apply D.hom_ext
  intro i
  rw [stageHom_chart_assoc, D.chart_over, chartMap_over]
lemma stageHom_inv (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ) :
    stageHom D hE a ≫ stageHom D hE a⁻¹ = 𝟙 D.X := by
  apply D.hom_ext
  intro i
  rw [stageHom_chart_assoc, stageHom_chart, ← Category.assoc, chartMap_inv]
  simp

def stageIso (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ) : D.X ≅ D.X where
  hom := stageHom D hE a
  inv := stageHom D hE a⁻¹
  hom_inv_id := stageHom_inv D hE a
  inv_hom_id := by simpa using stageHom_inv D hE a⁻¹
lemma stageIso_spec (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ) :
    StageAction k D id a false (stageIso D hE a) :=
  ⟨stageHom_over D hE a, ringMap k n a, coordinates k n a, stageHom_chart D hE a⟩
lemma stage_unique (D : Atlas k r n hr E) (hE : IsAdjacent k n E) (a : kˣ)
    (g : D.X ≅ D.X) (hg : StageAction k D id a false g) : g = stageIso D hE a := by
  apply Iso.ext
  apply D.hom_ext
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [coordinates_unique k n a f hf] at hc
  intro i
  exact (hc i).trans (stageHom_chart D hE a i).symm

variable (k)
lemma ringMap_reduce (n N : ℕ) (h : n ≤ N) (a : kˣ) :
    (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h).comp (ringMap k N a) =
      (ringMap k n a).comp (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h) := by
  apply point_ext
  · apply Ideal.Quotient.ringHom_ext
    ext b
    change truncReduce _ _ n N h (ringMap k N a (base k N (trunc _ _ N b))) =
      ringMap k n a (base k n (trunc _ _ n b))
    rw [ringMap_base, ringMap_base]
    rfl
  · change truncReduce _ _ n N h (ringMap k N a (coordX k N)) =
      ringMap k n a (coordX k n)
    rw [ringMap_x, map_mul, ringMap_x]
    rfl
  · change truncReduce _ _ n N h (ringMap k N a (coordY k N)) =
      ringMap k n a (coordY k n)
    rw [ringMap_y, map_mul, ringMap_y]
    rfl
lemma chartMap_reduce (n N : ℕ) (h : n ≤ N) (a : kˣ) :
    chartReduction k n N h ≫ chartMap k N a =
      chartMap k n a ≫ chartReduction k n N h := by
  simp only [chartReduction, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (ringMap_reduce k n N h a)

def towerIso (T : Tower k r hr) (a : kˣ) (n : ℕ) : (T.atlas n).X ≅ (T.atlas n).X :=
  stageIso (T.atlas n) (T.overlap_spec n) a
lemma towerIso_spec (T : Tower k r hr) (a : kˣ) :
    TowerAction k T id a false (towerIso k T a) := by
  refine ⟨⟨fun n => stageHom_over (T.atlas n) (T.overlap_spec n) a, ?_⟩,
    fun n => stageIso_spec (T.atlas n) (T.overlap_spec n) a⟩
  intro n N h
  apply (T.atlas n).hom_ext
  intro i
  change (T.atlas n).chart i ≫ T.transition n N h ≫ stageHom (T.atlas N) (T.overlap_spec N) a =
    (T.atlas n).chart i ≫ stageHom (T.atlas n) (T.overlap_spec n) a ≫ T.transition n N h
  rw [← Category.assoc, (T.transition_spec n N h).2 i, Category.assoc,
    stageHom_chart, stageHom_chart_assoc, (T.transition_spec n N h).2 i,
    ← Category.assoc, chartMap_reduce, Category.assoc]

end TowerScalarTranslation
open CategoryTheory ArithmeticThetaInfinitesimalPolygonR0129

theorem tower_scalar_translation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (T : Tower k r hr), ∀ a : kˣ,
        ∃! g : ∀ n : ℕ, (T.atlas n).X ≅ (T.atlas n).X,
          TowerAction k T id a false g := by
  intro k _ _ r hr _ T a
  refine ⟨TowerScalarTranslation.towerIso k T a,
    TowerScalarTranslation.towerIso_spec k T a, ?_⟩
  intro g hg
  funext n
  exact TowerScalarTranslation.stage_unique (T.atlas n) (T.overlap_spec n) a (g n) (hg.2 n)
end ArithmeticThetaModelSymmetriesR0137
