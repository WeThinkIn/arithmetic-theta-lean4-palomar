module

public import ModelSymmetriesDefinitionsR0137

@[expose] public section

/-! Inversion on every actual infinitesimal polygon, by descent of the node swap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
namespace TowerInversionR0137
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]

def swap (n : ℕ) : A k n →+* A k n :=
  mkPoint (base k n) (coordY k n) (coordX k n)
    (by rw [mul_comm, coordX_mul_coordY])

@[simp] lemma swap_x (n : ℕ) : swap k n (coordX k n) = coordY k n := mkPoint_x _ _ _ _
@[simp] lemma swap_y (n : ℕ) : swap k n (coordY k n) = coordX k n := mkPoint_y _ _ _ _
@[simp] lemma swap_base (n : ℕ) : (swap k n).comp (base k n) = base k n :=
  mkPoint_base _ _ _ _
@[simp] lemma swap_base_apply (n : ℕ) (b : R k n) :
    swap k n (base k n b) = base k n b := RingHom.congr_fun (swap_base k n) b

lemma swap_sq (n : ℕ) : (swap k n).comp (swap k n) = RingHom.id _ := by
  apply point_ext
  · rw [RingHom.comp_assoc, swap_base, swap_base, RingHom.id_comp]
  · simp
  · simp

lemma swap_coordinates (n : ℕ) : CoordinateMap k n 1 true (swap k n) := by
  refine ⟨swap_base_apply k n, ?_, ?_⟩
  · simpa [chartX, chartY, scalar, coordX, coordY] using swap_x k n
  · simpa [chartX, chartY, scalar, coordX, coordY] using swap_y k n

lemma swap_unique (n : ℕ) (f : A k n →+* A k n)
    (hf : CoordinateMap k n 1 true f) : f = swap k n := by
  apply point_ext
  · rw [swap_base]; exact RingHom.ext hf.1
  · rw [swap_x]; simpa [chartX, chartY, scalar, coordX, coordY] using hf.2.1
  · rw [swap_y]; simpa [chartX, chartY, scalar, coordX, coordY] using hf.2.2

variable {k} {n : ℕ} {E : B k n false ≃+* B k n true}

lemma edge_unit (hE : IsAdjacent k n E) :
    IsUnit (E (restriction k n false (coordY k n))) := by
  exact isUnit_iff_exists_inv.mpr ⟨restriction k n true (coordX k n), adjacent_y_mul_x hE⟩

def edgeSwap (hE : IsAdjacent k n E) : B k n true →+* B k n true :=
  openPoint ((E.toRingHom.comp (restriction k n false)).comp (swap k n)) true
    (by simpa using edge_unit hE)

lemma edgeSwap_right (hE : IsAdjacent k n E) :
    (edgeSwap hE).comp (restriction k n true) =
      (E.toRingHom.comp (restriction k n false)).comp (swap k n) :=
  openPoint_restriction _ _ _

lemma edgeSwap_base (hE : IsAdjacent k n E) :
    (edgeSwap hE).comp ((restriction k n true).comp (base k n)) =
      (restriction k n true).comp (base k n) := by
  rw [← RingHom.comp_assoc, edgeSwap_right, RingHom.comp_assoc, swap_base]
  exact adjacent_base hE

lemma edgeSwap_x (hE : IsAdjacent k n E) :
    edgeSwap hE (restriction k n true (coordX k n)) =
      E (restriction k n false (coordY k n)) := by
  simpa using RingHom.congr_fun (edgeSwap_right hE) (coordX k n)

lemma edgeSwap_left_y (hE : IsAdjacent k n E) :
    edgeSwap hE (E (restriction k n false (coordY k n))) =
      restriction k n true (coordX k n) := by
  apply (edge_unit hE).mul_right_cancel
  calc
    _ = edgeSwap hE (E (restriction k n false (coordY k n)) *
        restriction k n true (coordX k n)) := by rw [map_mul, edgeSwap_x hE]
    _ = 1 := by rw [adjacent_y_mul_x hE, map_one]
    _ = _ := by rw [mul_comm, adjacent_y_mul_x hE]

lemma edgeSwap_left (hE : IsAdjacent k n E) :
    (edgeSwap hE).comp (E.toRingHom.comp (restriction k n false)) =
      (restriction k n true).comp (swap k n) := by
  apply point_ext
  · simp only [RingHom.comp_assoc]
    rw [adjacent_base hE, edgeSwap_base, swap_base]
  · change edgeSwap hE (E (restriction k n false (coordX k n))) =
      restriction k n true (swap k n (coordX k n))
    rw [swap_x]
    have hu : IsUnit (restriction k n true (coordX k n)) := by
      exact isUnit_iff_exists_inv.mpr
        ⟨E (restriction k n false (coordY k n)), by rw [mul_comm, adjacent_y_mul_x hE]⟩
    apply hu.mul_right_cancel
    calc
      edgeSwap hE (E (restriction k n false (coordX k n))) *
          restriction k n true (coordX k n) =
        edgeSwap hE (E (restriction k n false (base k n (parameter k n)))) := by
          rw [← edgeSwap_left_y hE, ← map_mul, ← map_mul, ← map_mul, coordX_mul_coordY]
      _ = restriction k n true (base k n (parameter k n)) := by
        have hb : E (restriction k n false (base k n (parameter k n))) =
            restriction k n true (base k n (parameter k n)) :=
          RingHom.congr_fun (adjacent_base hE) (parameter k n)
        rw [hb]
        exact RingHom.congr_fun (edgeSwap_base hE) (parameter k n)
      _ = restriction k n true (coordY k n) * restriction k n true (coordX k n) := by
        rw [← map_mul, mul_comm, coordX_mul_coordY]
  · simpa using edgeSwap_left_y hE

variable (k)

def chartSwap (n : ℕ) : specA k n ⟶ specA k n :=
  Spec.map (CommRingCat.ofHom (swap k n))

lemma chartSwap_sq (n : ℕ) : chartSwap k n ≫ chartSwap k n = 𝟙 _ := by
  rw [chartSwap, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((swap k n).comp (swap k n))) = _
  rw [swap_sq]
  exact Spec.map_id _

lemma chartSwap_over (n : ℕ) : chartSwap k n ≫ structureMap k n = structureMap k n := by
  rw [chartSwap, structureMap, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (swap_base k n)

variable {k}
lemma legs_swap (hE : IsAdjacent k n E) :
    leftLeg k n E ≫ chartSwap k n = Spec.map (CommRingCat.ofHom (edgeSwap hE)) ≫ rightLeg k n ∧
    rightLeg k n ≫ chartSwap k n = Spec.map (CommRingCat.ofHom (edgeSwap hE)) ≫ leftLeg k n E := by
  constructor
  · simp only [leftLeg, rightLeg, chartSwap, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (edgeSwap_right hE).symm
  · simp only [leftLeg, rightLeg, chartSwap, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (edgeSwap_left hE).symm

lemma rev_next (r : ℕ) (hr : 0 < r) (i : Fin r) :
    next r hr (Fin.rev (next r hr i)) = Fin.rev i := by
  apply Fin.ext
  simp only [next, Fin.rev, Fin.val_mk]
  have hi := i.isLt
  by_cases h : i.val + 1 < r
  · rw [Nat.mod_eq_of_lt h]
    rw [Nat.mod_eq_of_lt (show r - (i.val + 1 + 1) + 1 < r by omega)]
    omega
  · have hh : i.val + 1 = r := by omega
    rw [hh, Nat.mod_self]
    simp only [Nat.zero_add]
    have hh' : r - 1 + 1 = r := by omega
    rw [hh', Nat.mod_self]
    omega

variable {r : ℕ} {hr : 0 < r}
def stageHom (D : Atlas k r n hr E) (hE : IsAdjacent k n E) : D.X ⟶ D.X :=
  D.desc (fun i => chartSwap k n ≫ D.chart (Fin.rev i)) (by
    intro i
    rw [← Category.assoc, (legs_swap hE).1, Category.assoc,
      ← rev_next r hr i, ← (D.adjacent (Fin.rev (next r hr i))).w,
      ← Category.assoc, ← (legs_swap hE).2, Category.assoc])

@[reassoc (attr := simp)] lemma chart_stageHom (D : Atlas k r n hr E)
    (hE : IsAdjacent k n E) (i : Fin r) :
    D.chart i ≫ stageHom D hE = chartSwap k n ≫ D.chart (Fin.rev i) :=
  D.chart_desc _ _ i

lemma stageHom_sq (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    stageHom D hE ≫ stageHom D hE = 𝟙 _ := by
  apply D.hom_ext
  intro i
  rw [chart_stageHom_assoc, chart_stageHom, Fin.rev_rev, ← Category.assoc,
    chartSwap_sq, Category.id_comp, Category.comp_id]

lemma stageHom_over (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    stageHom D hE ≫ D.p = D.p := by
  apply D.hom_ext
  intro i
  rw [chart_stageHom_assoc, D.chart_over, chartSwap_over, D.chart_over]

def stageIso (D : Atlas k r n hr E) (hE : IsAdjacent k n E) : D.X ≅ D.X where
  hom := stageHom D hE
  inv := stageHom D hE
  hom_inv_id := stageHom_sq D hE
  inv_hom_id := stageHom_sq D hE

lemma stageIso_action (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    StageAction k D Fin.rev 1 true (stageIso D hE) :=
  ⟨stageHom_over D hE, swap k n, swap_coordinates k n, chart_stageHom D hE⟩

lemma swap_reduce (n N : ℕ) (h : n ≤ N) :
    (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h).comp (swap k N) =
      (swap k n).comp (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h) := by
  apply point_ext
  · have hn := truncReduce_natural
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
      PowerSeries.X (ArithmeticThetaNodeCharts.t k) rfl n N h
    change (truncReduce _ _ n N h).comp (base k N) =
      (base k n).comp (truncReduce _ _ n N h) at hn
    simp only [RingHom.comp_assoc, swap_base]
    rw [hn, ← RingHom.comp_assoc, swap_base]
  · change truncReduce _ _ n N h (swap k N (coordX k N)) = swap k n (coordX k n)
    rw [swap_x, swap_x]; rfl
  · change truncReduce _ _ n N h (swap k N (coordY k N)) = swap k n (coordY k n)
    rw [swap_y, swap_y]; rfl

lemma chartSwap_reduce (n N : ℕ) (h : n ≤ N) :
    chartReduction k n N h ≫ chartSwap k N = chartSwap k n ≫ chartReduction k n N h := by
  simp only [chartReduction, chartSwap, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (swap_reduce n N h)

def towerIso (T : Tower k r hr) (n : ℕ) : (T.atlas n).X ≅ (T.atlas n).X :=
  stageIso (T.atlas n) (T.overlap_spec n)

lemma towerIso_action (T : Tower k r hr) :
    TowerAction k T Fin.rev 1 true (towerIso T) := by
  refine ⟨⟨fun n => stageHom_over (T.atlas n) (T.overlap_spec n), ?_⟩,
    fun n => stageIso_action (T.atlas n) (T.overlap_spec n)⟩
  intro n N h
  apply (T.atlas n).hom_ext
  intro i
  change (T.atlas n).chart i ≫ T.transition n N h ≫ stageHom (T.atlas N) (T.overlap_spec N) =
    (T.atlas n).chart i ≫ stageHom (T.atlas n) (T.overlap_spec n) ≫ T.transition n N h
  rw [← Category.assoc, (T.transition_spec n N h).2 i, Category.assoc,
    chart_stageHom, chart_stageHom_assoc, (T.transition_spec n N h).2,
    ← Category.assoc, chartSwap_reduce, Category.assoc]

lemma stage_unique (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    (g : D.X ≅ D.X) (hg : StageAction k D Fin.rev 1 true g) : g = stageIso D hE := by
  obtain ⟨_, f, hf, hc⟩ := hg
  have he := swap_unique k n f hf
  subst f
  apply CategoryTheory.Iso.ext
  apply D.hom_ext
  intro i
  exact (hc i).trans (chart_stageHom D hE i).symm

end TowerInversionR0137
open ArithmeticThetaInfinitesimalPolygonR0129 TowerInversionR0137
open CategoryTheory

/-- Unique inversion on the entire compatible tower with the prescribed annular coordinates. -/
theorem tower_inversion :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
      ∃! g : ∀ n : ℕ, (T.atlas n).X ≅ (T.atlas n).X,
        ArithmeticThetaModelSymmetriesR0137.TowerAction k T Fin.rev 1 true g := by
  intro k _ _ r hr _ T
  refine ⟨towerIso T, towerIso_action T, ?_⟩
  intro g hg
  funext n
  exact stage_unique (T.atlas n) (T.overlap_spec n) (g n) (hg.2 n)

end ArithmeticThetaModelSymmetriesR0137
