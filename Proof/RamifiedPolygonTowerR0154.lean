module

public import CompletedChartRamificationR0154
public import RamifiedPeriodDefinitionsR0154
public import CompletedChartFieldMapsR0152

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The ramified morphism of the specified infinitesimal polygon towers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0154
namespace RamifiedPolygonTower
open CategoryTheory AlgebraicGeometry ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaKatoAnnularR0152
variable (k : Type u) [Field k] [CharZero k]

lemma power_stable {S : Type u} [CommRing S] (t : S)
    (f : S →+* S) (d : ℕ) (hd : 0 < d) (ht : f t = t^d) (n : ℕ) :
    (Ideal.span {t})^n ≤ Ideal.comap f ((Ideal.span {t})^n) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  apply pow_le_pow_left'
  rw [Ideal.map_span, Set.image_singleton, ht, Ideal.span_singleton_le_iff_mem]
  exact Ideal.mem_span_singleton.mpr (dvd_pow_self _ (Nat.ne_of_gt hd))

def coefficientMap (d : ℕ) (hd : 0 < d) (n : ℕ) : R k n →+* R k n :=
  Ideal.quotientMap _ (baseMap k d hd)
    (power_stable PowerSeries.X (baseMap k d hd) d hd (PowerSeries.expand_X ..) (n+1))

lemma coefficientMap_trunc (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (coefficientMap k d hd n).comp (trunc _ PowerSeries.X n) =
      (trunc _ PowerSeries.X n).comp (baseMap k d hd) := rfl

private lemma reduction_complete (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
        (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec
    (Classical.choose_spec (finite_stage_completion_comparison k n))).1 a

lemma reduction_base (n : ℕ) (b : PowerSeries k) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      base k n (trunc _ PowerSeries.X n b) := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (algebraMap (PowerSeries k) (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) b)) = _
  rw [reduction_complete]
  rfl

lemma reduction_x (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_complete]
  rfl

lemma reduction_y (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [reduction_complete]
  rfl

abbrev tau (n : ℕ) : A k n := base k n (parameter k n)
lemma reduction_tau (n : ℕ) :
    ArithmeticThetaKatoAnnularR0152.reduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = tau k n :=
  reduction_base k n PowerSeries.X

variable {d : ℕ} {hd : 0 < d} {q : Fin d}
variable (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)

include hρ in
lemma chart_parameter : ρ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ d := by
  have h := hρ.1 PowerSeries.X
  simp only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    PowerSeries.expand_X, map_pow] at h
  exact h

include hρ in
lemma reduction_kernel_le (n : ℕ) :
    RingHom.ker (ArithmeticThetaKatoAnnularR0152.reduction k n) ≤ RingHom.ker ((ArithmeticThetaKatoAnnularR0152.reduction k n).comp ρ) := by
  rw [← RingHom.comap_ker, CompletedChartFieldMaps.reduction_kernel]
  exact power_stable _ ρ d hd (chart_parameter k ρ hρ) (n+1)

def nodeMap (n : ℕ) : A k n →+* A k n :=
  (ArithmeticThetaKatoAnnularR0152.reduction k n).liftOfSurjective (CompletedChartFieldMaps.reduction_surjective k n)
    ⟨(ArithmeticThetaKatoAnnularR0152.reduction k n).comp ρ, reduction_kernel_le k ρ hρ n⟩

lemma nodeMap_reduction (n : ℕ) :
    (nodeMap k ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n) = (ArithmeticThetaKatoAnnularR0152.reduction k n).comp ρ :=
  RingHom.liftOfSurjective_comp ..

lemma nodeMap_base (n : ℕ) (b : R k n) :
    nodeMap k ρ hρ n (base k n b) = base k n (coefficientMap k d hd n b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change nodeMap k ρ hρ n (base k n (trunc _ _ n b)) = _
  rw [← reduction_base]
  change ((nodeMap k ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) = _
  rw [hρ.1, reduction_base]
  rfl

lemma nodeMap_x (n : ℕ) :
    nodeMap k ρ hρ n (coordX k n) = tau k n ^ q.val * coordX k n := by
  rw [← reduction_x]
  change ((nodeMap k ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = _
  rw [hρ.2.1, map_mul, map_pow, reduction_tau]

lemma nodeMap_y (n : ℕ) :
    nodeMap k ρ hρ n (coordY k n) = tau k n ^ (d-q.val-1) * coordY k n := by
  rw [← reduction_y]
  change ((nodeMap k ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction k n (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = _
  rw [hρ.2.2, map_mul, map_pow, reduction_tau]

lemma nodeMap_unique (n : ℕ) (η : A k n →+* A k n)
    (hη : η.comp (ArithmeticThetaKatoAnnularR0152.reduction k n) = (ArithmeticThetaKatoAnnularR0152.reduction k n).comp ρ) :
    η = nodeMap k ρ hρ n := by
  apply RingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := CompletedChartFieldMaps.reduction_surjective k n z
  exact RingHom.congr_fun (hη.trans (nodeMap_reduction k ρ hρ n).symm) z

lemma nodeMap_reduce (n N : ℕ) (h : n ≤ N) :
    (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h).comp (nodeMap k ρ hρ N) =
      (nodeMap k ρ hρ n).comp (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h) := by
  apply point_ext
  · apply Ideal.Quotient.ringHom_ext
    ext b
    change truncReduce _ _ n N h (nodeMap k ρ hρ N (base k N (trunc _ _ N b))) =
      nodeMap k ρ hρ n (base k n (trunc _ _ n b))
    rw [nodeMap_base, nodeMap_base]
    rfl
  · change truncReduce _ _ n N h (nodeMap k ρ hρ N (coordX k N)) =
      nodeMap k ρ hρ n (coordX k n)
    rw [nodeMap_x, map_mul, map_pow, nodeMap_x]
    rfl
  · change truncReduce _ _ n N h (nodeMap k ρ hρ N (coordY k N)) =
      nodeMap k ρ hρ n (coordY k n)
    rw [nodeMap_y, map_mul, map_pow, nodeMap_y]
    rfl

section Overlaps
variable {k} {n r : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}

lemma overlap_x (hE : IsAdjacent k n E) :
    E (restriction k n false (coordX k n)) =
      restriction k n true (tau k n) * restriction k n true (coordX k n) := by
  let L := E.toRingHom.comp (restriction k n false)
  let R := restriction k n true
  have hb : L (tau k n) = R (tau k n) := RingHom.congr_fun (adjacent_base hE) (parameter k n)
  have hxy : L (coordY k n) * R (coordX k n) = 1 := adjacent_y_mul_x hE
  change L (coordX k n) = R (tau k n) * R (coordX k n)
  calc
    _ = L (coordX k n) * (L (coordY k n) * R (coordX k n)) := by rw [hxy, mul_one]
    _ = L (tau k n) * R (coordX k n) := by rw [← mul_assoc, ← map_mul, coordX_mul_coordY]
    _ = _ := by rw [hb]

lemma overlap_y (hE : IsAdjacent k n E) :
    restriction k n true (coordY k n) =
      restriction k n true (tau k n) * E (restriction k n false (coordY k n)) := by
  let L := E.toRingHom.comp (restriction k n false)
  let R := restriction k n true
  have hxy : L (coordY k n) * R (coordX k n) = 1 := adjacent_y_mul_x hE
  change R (coordY k n) = R (tau k n) * L (coordY k n)
  calc
    _ = (L (coordY k n) * R (coordX k n)) * R (coordY k n) := by rw [hxy, one_mul]
    _ = L (coordY k n) * R (tau k n) := by rw [mul_assoc, ← map_mul, coordX_mul_coordY]
    _ = _ := mul_comm ..

/-- A pair of nodal points satisfying the actual inverse-coordinate equation
factors through the specified overlap, over any commutative ring. -/
lemma adjacent_points (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    {S : Type u} [CommRing S] (i : Fin r) (f g : A k n →+* S)
    (hb : f.comp (base k n) = g.comp (base k n))
    (hxy : f (coordY k n) * g (coordX k n) = 1) :
    Spec.map (CommRingCat.ofHom f) ≫ D.chart i =
      Spec.map (CommRingCat.ofHom g) ≫ D.chart (next r hr i) := by
  have hu : IsUnit (g (coordX k n)) := IsUnit.of_mul_eq_one_right _ hxy
  let o := openPoint g true hu
  have hor : o.comp (restriction k n true) = g := openPoint_restriction ..
  let l := o.comp (E.toRingHom.comp (restriction k n false))
  have hlb : l.comp (base k n) = f.comp (base k n) := by
    apply RingHom.ext
    intro b
    change o (E (restriction k n false (base k n b))) = f (base k n b)
    rw [show E (restriction k n false (base k n b)) = restriction k n true (base k n b) from
      RingHom.congr_fun (adjacent_base hE) b]
    exact (RingHom.congr_fun hor _).trans (RingHom.congr_fun hb b).symm
  have hly : l (coordY k n) = f (coordY k n) := by
    apply hu.mul_right_cancel
    rw [hxy]
    change o (E (restriction k n false (coordY k n))) * g (coordX k n) = 1
    rw [← RingHom.congr_fun hor (coordX k n), RingHom.comp_apply, ← map_mul,
      adjacent_y_mul_x hE, map_one]
  have hl : l = f := by
    apply point_ext hlb _ hly
    have huy : IsUnit (f (coordY k n)) := IsUnit.of_mul_eq_one _ hxy
    apply huy.mul_right_cancel
    rw [← hly, ← map_mul, coordX_mul_coordY]
    rw [hly, ← map_mul, coordX_mul_coordY]
    exact RingHom.congr_fun hlb (parameter k n)
  have hlgeom : Spec.map (CommRingCat.ofHom o) ≫ leftLeg k n E =
      Spec.map (CommRingCat.ofHom f) := by
    rw [leftLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hl
  have hrgeom : Spec.map (CommRingCat.ofHom o) ≫ rightLeg k n =
      Spec.map (CommRingCat.ofHom g) := by
    rw [rightLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hor]
  rw [← hlgeom, Category.assoc, (D.adjacent i).w, ← Category.assoc, hrgeom]
end Overlaps

section Indices
variable {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hrd : 0 < r*d) (i : Fin (r*d))
lemma indices_internal (hq : (residueIndex r d hd i).val + 1 < d) :
    coarseIndex r d hd (next (r*d) hrd i) = coarseIndex r d hd i ∧
    (residueIndex r d hd (next (r*d) hrd i)).val = (residueIndex r d hd i).val + 1 := by
  dsimp only [residueIndex] at hq
  have hm : (i.val+1)%d = i.val%d+1 := by
    rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hq]
  constructor
  · apply Fin.ext
    change (i.val+1)%(r*d)/d = i.val/d
    rw [Nat.mod_mul_left_div_self, Nat.succ_div_of_mod_ne_zero (by omega)]
    exact Nat.mod_eq_of_lt (coarseIndex r d hd i).isLt
  · change (i.val+1)%(r*d)%d = i.val%d+1
    rw [Nat.mod_mul_left_mod, hm]

lemma indices_boundary (hq : (residueIndex r d hd i).val + 1 = d) :
    coarseIndex r d hd (next (r*d) hrd i) = next r hr (coarseIndex r d hd i) ∧
    (residueIndex r d hd (next (r*d) hrd i)).val = 0 := by
  dsimp only [residueIndex] at hq
  have hm : (i.val+1)%d = 0 := by
    rw [← Nat.mod_add_mod, hq, Nat.mod_self]
  constructor
  · apply Fin.ext
    change (i.val+1)%(r*d)/d = (i.val/d+1)%r
    rw [Nat.mod_mul_left_div_self, Nat.succ_div_of_mod_eq_zero hm]
  · change (i.val+1)%(r*d)%d = 0
    rw [Nat.mod_mul_left_mod, hm]
end Indices

section Gluing
variable {r d n : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
variable (rs : Fin d → (Chart k →+* Chart k))
    (hs : ∀ q, IsChartRamification k d hd q (rs q))
variable {E Eb : B k n false ≃+* B k n true}
variable (D : Atlas k r n hr E) (Db : Atlas k (r*d) n hrd Eb)
    (hE : IsAdjacent k n E) (hEb : IsAdjacent k n Eb)

def localMap (i : Fin (r*d)) : specA k n ⟶ D.X :=
  Spec.map (CommRingCat.ofHom (nodeMap k (rs (residueIndex r d hd i))
    (hs _) n)) ≫ D.chart (coarseIndex r d hd i)

include hE hEb in
lemma localMap_compatible (i : Fin (r*d)) :
    leftLeg k n Eb ≫ localMap k rs hs D i =
      rightLeg k n ≫ localMap k rs hs D (next (r*d) hrd i) := by
  let j := coarseIndex r d hd i
  let j' := coarseIndex r d hd (next (r*d) hrd i)
  let q := residueIndex r d hd i
  let q' := residueIndex r d hd (next (r*d) hrd i)
  let L := Eb.toRingHom.comp (restriction k n false)
  let R := restriction k n true
  let f := L.comp (nodeMap k (rs q) (hs q) n)
  let g := R.comp (nodeMap k (rs q') (hs q') n)
  have hb (b : ArithmeticThetaInfinitesimalPolygonR0129.R k n) :
      L (base k n b) = R (base k n b) := RingHom.congr_fun (adjacent_base hEb) b
  have hbt : L (tau k n) = R (tau k n) := hb _
  have hfgb : f.comp (base k n) = g.comp (base k n) := by
    apply RingHom.ext
    intro b
    change L (nodeMap k (rs q) (hs q) n (base k n b)) =
      R (nodeMap k (rs q') (hs q') n (base k n b))
    rw [nodeMap_base, nodeMap_base, hb]
  change leftLeg k n Eb ≫ (Spec.map (CommRingCat.ofHom _) ≫ D.chart j) =
    rightLeg k n ≫ (Spec.map (CommRingCat.ofHom _) ≫ D.chart j')
  rw [← Category.assoc, ← Category.assoc, leftLeg, rightLeg,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom f) ≫ D.chart j =
    Spec.map (CommRingCat.ofHom g) ≫ D.chart j'
  by_cases hq : q.val+1 < d
  · have hj : j' = j := (indices_internal hd hrd i hq).1
    have hq' : q'.val = q.val+1 := (indices_internal hd hrd i hq).2
    have hfg : f = g := by
      apply point_ext hfgb
      · change L (nodeMap k (rs q) (hs q) n (coordX k n)) =
          R (nodeMap k (rs q') (hs q') n (coordX k n))
        rw [nodeMap_x, nodeMap_x, map_mul, map_mul, map_pow, map_pow, hbt, hq']
        have hx : L (coordX k n) = R (tau k n) * R (coordX k n) := overlap_x hEb
        rw [hx, pow_succ (R (tau k n))]
        ring
      · change L (nodeMap k (rs q) (hs q) n (coordY k n)) =
          R (nodeMap k (rs q') (hs q') n (coordY k n))
        rw [nodeMap_y, nodeMap_y, map_mul, map_mul, map_pow, map_pow, hbt]
        have hy : R (coordY k n) = R (tau k n) * L (coordY k n) := overlap_y hEb
        rw [hy, show d-q.val-1 = (d-q'.val-1)+1 by omega, pow_succ (R (tau k n))]
        ring
    rw [hj, hfg]
  · have hlast : q.val+1 = d := by have := q.isLt; omega
    have hj : j' = next r hr j := (indices_boundary hr hd hrd i hlast).1
    have hq' : q'.val = 0 := (indices_boundary hr hd hrd i hlast).2
    rw [hj]
    apply adjacent_points D hE j f g hfgb
    change L (nodeMap k (rs q) (hs q) n (coordY k n)) *
      R (nodeMap k (rs q') (hs q') n (coordX k n)) = 1
    rw [nodeMap_y, nodeMap_x, hq', show d-q.val-1 = 0 by omega,
      pow_zero, one_mul]
    simp only [one_mul]
    exact adjacent_y_mul_x hEb

def stageHom : Db.X ⟶ D.X :=
  Db.desc (localMap k rs hs D) (localMap_compatible k rs hs D hE hEb)

@[reassoc (attr := simp)] lemma stageHom_chart (i : Fin (r*d)) :
    Db.chart i ≫ stageHom k rs hs D Db hE hEb = localMap k rs hs D i :=
  Db.chart_desc _ _ i

lemma stageHom_over :
    stageHom k rs hs D Db hE hEb ≫ D.p =
      Db.p ≫ Spec.map (CommRingCat.ofHom (coefficientMap k d hd n)) := by
  apply Db.hom_ext
  intro i
  rw [stageHom_chart_assoc, ← Category.assoc, Db.chart_over]
  dsimp only [localMap]
  rw [Category.assoc, D.chart_over, structureMap,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  exact nodeMap_base k (rs (residueIndex r d hd i)) (hs _) n
end Gluing

section Towers
variable {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
variable (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
variable (rs : Fin d → (Chart k →+* Chart k))
    (hs : ∀ q, IsChartRamification k d hd q (rs q))

def towerHom (n : ℕ) : (Tb.atlas n).X ⟶ (T.atlas n).X :=
  stageHom k rs hs (T.atlas n) (Tb.atlas n) (T.overlap_spec n) (Tb.overlap_spec n)

lemma chartMap_reduce (q : Fin d) (n N : ℕ) (h : n ≤ N) :
    chartReduction k n N h ≫ Spec.map (CommRingCat.ofHom (nodeMap k (rs q) (hs q) N)) =
      Spec.map (CommRingCat.ofHom (nodeMap k (rs q) (hs q) n)) ≫ chartReduction k n N h := by
  simp only [chartReduction, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (nodeMap_reduce k (rs q) (hs q) n N h)

lemma towerHom_transition (n N : ℕ) (h : n ≤ N) :
    Tb.transition n N h ≫ towerHom k T Tb rs hs N =
      towerHom k T Tb rs hs n ≫ T.transition n N h := by
  apply (Tb.atlas n).hom_ext
  intro i
  dsimp only [towerHom]
  rw [← Category.assoc, (Tb.transition_spec n N h).2 i, Category.assoc,
    stageHom_chart, stageHom_chart_assoc]
  dsimp only [localMap]
  rw [Category.assoc, (T.transition_spec n N h).2,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun z : specA k n ⟶ specA k N =>
    z ≫ (T.atlas N).chart (coarseIndex r d hd i))
    (chartMap_reduce k rs hs (residueIndex r d hd i) n N h)

lemma towerHom_spec : IsTowerRamification k (hd := hd) T Tb rs (towerHom k T Tb rs hs) := by
  refine ⟨fun n => ?_, towerHom_transition k T Tb rs hs⟩
  refine ⟨coefficientMap k d hd n, coefficientMap_trunc k d hd n,
    stageHom_over k rs hs (T.atlas n) (Tb.atlas n) (T.overlap_spec n) (Tb.overlap_spec n), ?_⟩
  intro i
  refine ⟨nodeMap k (rs (residueIndex r d hd i)) (hs _) n, nodeMap_reduction k _ (hs _) n, ?_⟩
  exact stageHom_chart k rs hs (T.atlas n) (Tb.atlas n) (T.overlap_spec n) (Tb.overlap_spec n) i

lemma towerHom_unique (f : ∀ n, (Tb.atlas n).X ⟶ (T.atlas n).X)
    (hf : IsTowerRamification k (hd := hd) T Tb rs f) : f = towerHom k T Tb rs hs := by
  funext n
  apply (Tb.atlas n).hom_ext
  intro i
  obtain ⟨β, _, _, hcharts⟩ := hf.1 n
  obtain ⟨η, hη, hi⟩ := hcharts i
  rw [hi, nodeMap_unique k _ (hs _) n η hη]
  exact (stageHom_chart k rs hs (T.atlas n) (Tb.atlas n)
    (T.overlap_spec n) (Tb.overlap_spec n) i).symm
end Towers

end RamifiedPolygonTower

/-- The prescribed inter-period morphism, at every thickness and across every seam. -/
theorem ramified_polygon_tower :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
      (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (hrd : 0 < r*d)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd)
      (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k))
      (hρ : ∀ q, IsChartRamification k d hd q (ρ q)),
      ∃! f : ∀ n, Quiver.Hom ((Tb.atlas n).X) ((T.atlas n).X),
        IsTowerRamification k (hd := hd) T Tb ρ f := by
  intro k _ _ d hd r hr _ hrd T Tb ρ hρ
  exact ⟨RamifiedPolygonTower.towerHom k T Tb ρ hρ,
    RamifiedPolygonTower.towerHom_spec k T Tb ρ hρ,
    RamifiedPolygonTower.towerHom_unique k T Tb ρ hρ⟩

end ArithmeticThetaRamifiedPeriodR0154

#print axioms ArithmeticThetaRamifiedPeriodR0154.ramified_polygon_tower
