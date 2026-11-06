import FiniteStageAdjacentR0129
import Mathlib.AlgebraicGeometry.Gluing

/-! Construction of the cyclic infinitesimal atlas from the specified coordinate opens. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private lemma trunc_parameter_pow (S : Type u) [CommRing S] (t : S) (n : ℕ) :
    trunc S t n t ^ (n+1) = 0 := by
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _

private def truncAwayEquiv (S : Type u) [CommRing S] (t x : S) (n : ℕ) :
    Trunc (Localization.Away x) (algebraMap S _ t) n ≃+*
      Localization.Away (trunc S t n x) := by
  let Q := Trunc S t n
  let L := Localization.Away x
  let T := Trunc L (algebraMap S L t) n
  let W := Localization.Away (trunc S t n x)
  let q := trunc S t n
  let a : Q →+* W := algebraMap Q W
  let b : S →+* L := algebraMap S L
  let v := trunc L (b t) n
  let f : L →+* W := IsLocalization.Away.lift x
    (show IsUnit ((a.comp q) x) from IsLocalization.Away.algebraMap_isUnit (q x))
  have hf (z : S) : f (b z) = a (q z) := IsLocalization.Away.lift_eq _ _ z
  have hkill : (Ideal.span {b t}) ^ (n+1) ≤ RingHom.ker f := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    change f (b t ^ (n+1)) = 0
    rw [map_pow, hf, ← map_pow, trunc_parameter_pow, map_zero]
  let F : T →+* W := Ideal.Quotient.lift _ f (fun z hz => hkill hz)
  let c : Q →+* T := truncMap b t (b t) rfl n
  have hc (z : S) : c (q z) = v (b z) := rfl
  let G : W →+* T := IsLocalization.Away.lift (q x)
    (show IsUnit (c (q x)) from
      (IsLocalization.Away.algebraMap_isUnit x (S := L)).map v)
  have hg (z : Q) : G (a z) = c z := IsLocalization.Away.lift_eq _ _ z
  have hGF : G.comp F = RingHom.id T := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers x)
    apply RingHom.ext
    intro z
    change G (f (b z)) = v (b z)
    rw [hf, hg, hc]
  have hFG : F.comp G = RingHom.id W := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q x))
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change F (G (a (q z))) = a (q z)
    rw [hg, hc]
    exact hf z
  exact { F with invFun := G
                 left_inv := fun z => RingHom.congr_fun hGF z
                 right_inv := fun z => RingHom.congr_fun hFG z }

private lemma truncAwayEquiv_restriction (S : Type u) [CommRing S] (t x : S) (n : ℕ) :
    (truncAwayEquiv S t x n).toRingHom.comp
      (truncMap (algebraMap S (Localization.Away x)) t
        (algebraMap S (Localization.Away x) t) rfl n) =
      algebraMap (Trunc S t n) (Localization.Away (trunc S t n x)) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro z
  exact IsLocalization.Away.lift_eq (S := Localization.Away x)
    (g := (algebraMap (Trunc S t n) (Localization.Away (trunc S t n x))).comp
      (trunc S t n)) x
    (IsLocalization.Away.algebraMap_isUnit (trunc S t n x)) z

private lemma truncAway_open (S : Type u) [CommRing S] (t x : S) (n : ℕ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (truncMap (algebraMap S (Localization.Away x)) t
        (algebraMap S (Localization.Away x) t) rfl n))) := by
  let e := truncAwayEquiv S t x n
  have hf : truncMap (algebraMap S (Localization.Away x)) t
        (algebraMap S (Localization.Away x) t) rfl n = e.symm.toRingHom.comp
      (algebraMap (Trunc S t n) (Localization.Away (trunc S t n x))) := by
    rw [← truncAwayEquiv_restriction]
    apply RingHom.ext
    intro z
    exact (e.symm_apply_apply _).symm
  rw [hf, CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.inv)
  infer_instance

variable (k : Type u) [Field k] [CharZero k]

private def coordinate (n : ℕ) (side : Bool) : A k n :=
  trunc _ (ArithmeticThetaNodeCharts.t k) n
    (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side)

private instance restriction_open (n : ℕ) (side : Bool) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (restriction k n side))) :=
  truncAway_open (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
    (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side) n

instance rightLeg_open (n : ℕ) : IsOpenImmersion (rightLeg k n) :=
  restriction_open k n true

instance leftLeg_open (n : ℕ) (E : B k n false ≃+* B k n true) :
    IsOpenImmersion (leftLeg k n E) := by
  have := restriction_open k n false
  unfold leftLeg
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsIso (CommRingCat.ofHom E.toRingHom) :=
    inferInstanceAs (IsIso E.toCommRingCatIso.hom)
  infer_instance

omit [CharZero k] in
private lemma coordinate_product (n : ℕ) :
    coordinate k n true * coordinate k n false =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (ArithmeticThetaNodeCharts.t k) := by
  have h := ArithmeticThetaNodeCharts.node_xy k
  simpa [coordinate, ArithmeticThetaIndexedOverlapsR0058.nodeCoord, ← map_mul] using
    congrArg (trunc _ (ArithmeticThetaNodeCharts.t k) n) h

omit [CharZero k] in
private lemma coordinate_unit (n : ℕ) (side : Bool) :
    IsUnit (restriction k n side (coordinate k n side)) := by
  exact (IsLocalization.Away.algebraMap_isUnit
    (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side)).map
      (trunc _ (openParameter k side) n)

/-- Nilpotence separates the actual opposite coordinate opens. -/
lemma legs_disjoint (n : ℕ) (E : B k n false ≃+* B k n true) :
    Disjoint (Set.range (leftLeg k n E)) (Set.range (rightLeg k n)) := by
  rw [Set.disjoint_left]
  rintro p ⟨a, rfl⟩ ⟨b, hb⟩
  have hnil : IsNilpotent (coordinate k n true * coordinate k n false) := by
    rw [coordinate_product]
    exact ⟨n+1, trunc_parameter_pow _ _ n⟩
  have hp : coordinate k n true * coordinate k n false ∈
      ((leftLeg k n E) a).asIdeal := by
    obtain ⟨m, hm⟩ := hnil
    exact ((leftLeg k n E) a).isPrime.mem_of_pow_mem m (hm ▸ Ideal.zero_mem _)
  rcases ((leftLeg k n E) a).isPrime.mem_or_mem hp with hx | hy
  · rw [← hb] at hx
    exact (b.isPrime.ne_top) (Ideal.eq_top_of_isUnit_mem _ hx (coordinate_unit k n true))
  · exact (a.isPrime.ne_top) (Ideal.eq_top_of_isUnit_mem _ hy
      ((coordinate_unit k n false).map E.toRingHom))

private lemma next_injective (r : ℕ) (hr : 0 < r) : Function.Injective (next r hr) := by
  intro i j h
  have h' : (i.val+1)%r = (j.val+1)%r := congrArg Fin.val h
  clear h
  apply Fin.ext
  by_cases hi : i.val+1 < r <;> by_cases hj : j.val+1 < r
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
    omega
  · have hjr : j.val+1 = r := by omega
    rw [Nat.mod_eq_of_lt hi, hjr, Nat.mod_self] at h'
    omega
  · have hir : i.val+1 = r := by omega
    rw [hir, Nat.mod_self, Nat.mod_eq_of_lt hj] at h'
    omega
  · omega

private lemma legs_over (n : ℕ) (E : B k n false ≃+* B k n true)
    (hE : IsAdjacent k n E) :
    leftLeg k n E ≫ structureMap k n = rightLeg k n ≫ structureMap k n := by
  unfold leftLeg rightLeg structureMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro z
  have hn : ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k z) =
      algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z := by
    unfold ArithmeticThetaIndexedOverlapsR0058.nodeEquiv
      ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase
    exact AlgEquiv.commutes _ _
  have ha := congrArg (fun f => f z)
    (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates k 1 0
      (by decide) (by decide)).1
  have hb := congrArg (fun f => f
    (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false)
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z))) hE
  change E (trunc _ (openParameter k false) n
      (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false)
        (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z))) = _
  dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hb
  rw [hb]
  apply congrArg (trunc _ (openParameter k true) n)
  simpa [rawAdjacent, ArithmeticThetaIndexedOverlapsR0058.openBase,
    ArithmeticThetaIndexedOverlapsR0058.openMap, hn] using ha

/- The incidence category has an edge below each of its two vertices.
   Its scheme diagram uses only the prescribed overlap legs. -/
private def Cycle (r : ℕ) (_hr : 0 < r) := Sum (Fin r) (Fin r)

private def cycleLE {r : ℕ} (hr : 0 < r) : Cycle r hr → Cycle r hr → Prop
  | .inl i, .inl j => i = j
  | .inl i, .inr j => i = j ∨ next r hr i = j
  | .inr _, .inl _ => False
  | .inr i, .inr j => i = j

private instance cycleOrder {r : ℕ} (hr : 0 < r) : PartialOrder (Cycle r hr) where
  le := cycleLE hr
  le_refl a := by cases a <;> exact rfl
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp_all [cycleLE]
    aesop
  le_antisymm a b := by
    cases a <;> cases b <;> simp_all [cycleLE]

private def cycleObj (r n : ℕ) (hr : 0 < r) : Cycle r hr → Scheme
  | .inl _ => specB k n true
  | .inr _ => specA k n

private def cycleMap (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    {i j : Cycle r hr} (h : i ≤ j) : cycleObj k r n hr i ⟶ cycleObj k r n hr j :=
  match i, j with
  | .inl _, .inl _ => 𝟙 _
  | .inl a, .inr b => if a = b then leftLeg k n E else rightLeg k n
  | .inr _, .inl _ => False.elim h
  | .inr _, .inr _ => 𝟙 _

private def cycleDiagram (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) : Cycle r hr ⥤ Scheme where
  obj := cycleObj k r n hr
  map f := cycleMap k r n hr E (leOfHom f)
  map_id i := by cases i <;> rfl
  map_comp {i j l} f g := by
    have hf := leOfHom f
    have hg := leOfHom g
    cases i <;> cases j <;> cases l <;>
      simp_all [cycleMap, LE.le, cycleLE, Category.comp_id, Category.id_comp]

private instance cycle_maps_open (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) {i j : Cycle r hr} (f : i ⟶ j) :
    IsOpenImmersion ((cycleDiagram k r n hr E).map f) := by
  have hf := leOfHom f
  cases i <;> cases j <;> simp only [cycleDiagram, cycleMap]
  · infer_instance
  · split_ifs <;> infer_instance
  · exact False.elim hf
  · infer_instance

private instance cycle_locally_directed (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) :
    (cycleDiagram k r n hr E ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j v fi fj xi xj h
  have hi := leOfHom fi
  have hj := leOfHom fj
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      cases v with
      | inl v =>
        change i = v at hi
        change j = v at hj
        subst i; subst j
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, h⟩
      | inr v =>
        change i = v ∨ next r hr i = v at hi
        change j = v ∨ next r hr j = v at hj
        change (if i = v then leftLeg k n E else rightLeg k n) xi =
          (if j = v then leftLeg k n E else rightLeg k n) xj at h
        by_cases hiv : i = v <;> by_cases hjv : j = v
        · subst i; subst j
          simp only [ite_true] at h
          have he := (leftLeg k n E).isOpenEmbedding.injective h
          exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, he⟩
        · simp only [if_pos hiv, if_neg hjv] at h
          exact False.elim (Set.disjoint_left.mp (legs_disjoint k n E)
            ⟨xi, rfl⟩ ⟨xj, h.symm⟩)
        · simp only [if_neg hiv, if_pos hjv] at h
          exact False.elim (Set.disjoint_left.mp (legs_disjoint k n E)
            ⟨xj, rfl⟩ ⟨xi, h⟩)
        · have hij := next_injective r hr ((hi.resolve_left hiv).trans
            (hj.resolve_left hjv).symm)
          subst j
          simp only [if_neg hiv] at h
          have he := (rightLeg k n).isOpenEmbedding.injective h
          exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, he⟩
    | inr j =>
      cases v with
      | inl v => exact False.elim hj
      | inr v =>
        change j = v at hj
        subst j
        exact ⟨_, 𝟙 _, fi, xi, rfl, h⟩
  | inr i =>
    cases v with
    | inl v => exact False.elim hi
    | inr v =>
      change i = v at hi
      subst i
      exact ⟨_, fj, 𝟙 _, xj, h.symm, by simp⟩

private def cycleChart (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (i : Fin r) :
    specA k n ⟶ colimit (cycleDiagram k r n hr E) :=
  colimit.ι (cycleDiagram k r n hr E) (.inr i)

private instance cycleChart_open (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (i : Fin r) :
    IsOpenImmersion (cycleChart k r n hr E i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (cycleDiagram k r n hr E) (.inr i)))

private lemma cycleChart_eq (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (i j : Fin r) (a b : specA k n)
    (h : cycleChart k r n hr E i a = cycleChart k r n hr E j b) :
    i = j ∨
      (∃ z, next r hr i = j ∧ leftLeg k n E z = a ∧ rightLeg k n z = b) ∨
      (∃ z, next r hr j = i ∧ rightLeg k n z = a ∧ leftLeg k n E z = b) := by
  obtain ⟨v, fi, fj, z, ha, hb⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (cycleDiagram k r n hr E)).mp h
  have hi := leOfHom fi
  have hj := leOfHom fj
  cases v with
  | inr v =>
    change v = i at hi
    change v = j at hj
    exact Or.inl (hi.symm.trans hj)
  | inl v =>
    change v = i ∨ next r hr v = i at hi
    change v = j ∨ next r hr v = j at hj
    change (if v = i then leftLeg k n E else rightLeg k n) z = a at ha
    change (if v = j then leftLeg k n E else rightLeg k n) z = b at hb
    by_cases hvi : v = i <;> by_cases hvj : v = j
    · exact Or.inl (hvi.symm.trans hvj)
    · subst v
      exact Or.inr (Or.inl ⟨z, hj.resolve_left hvj,
        by simpa using ha, by simpa [hvj] using hb⟩)
    · subst v
      exact Or.inr (Or.inr ⟨z, hi.resolve_left hvi,
        by simpa [hvi] using ha, by simpa using hb⟩)
    · exact Or.inl ((hi.resolve_left hvi).symm.trans (hj.resolve_left hvj))

private lemma next_ne (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (i : Fin r) :
    next r hr i ≠ i := by
  intro h
  have hv : (i.val+1)%r = i.val := congrArg Fin.val h
  clear h
  by_cases hi : i.val+1 < r
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hir : i.val+1 = r := by omega
    rw [hir, Nat.mod_self] at hv
    omega

private lemma next_next_ne (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (i : Fin r) :
    next r hr (next r hr i) ≠ i := by
  intro h
  have hv : (((i.val+1)%r)+1)%r = i.val := congrArg Fin.val h
  clear h
  by_cases hi : i.val+1 < r
  · rw [Nat.mod_eq_of_lt hi] at hv
    by_cases hj : i.val+1+1 < r
    · rw [Nat.mod_eq_of_lt hj] at hv
      omega
    · have hir : i.val+1+1 = r := by omega
      rw [hir, Nat.mod_self] at hv
      omega
  · have hir : i.val+1 = r := by omega
    rw [hir, Nat.mod_self] at hv
    simp only [zero_add, Nat.mod_eq_of_lt (show 1 < r by omega)] at hv
    omega

private lemma cycle_edge_left (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (i : Fin r) :
    leftLeg k n E ≫ cycleChart k r n hr E i =
      colimit.ι (cycleDiagram k r n hr E) (.inl i) := by
  simpa [cycleDiagram, cycleMap, cycleChart] using
    colimit.w (cycleDiagram k r n hr E)
      (homOfLE (show cycleLE hr (.inl i) (.inr i) from Or.inl rfl))

private lemma cycle_edge_right (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (i : Fin r) :
    rightLeg k n ≫ cycleChart k r n hr E (next r hr i) =
      colimit.ι (cycleDiagram k r n hr E) (.inl i) := by
  simpa [cycleDiagram, cycleMap, cycleChart, (next_ne r hr h3 i).symm] using
    colimit.w (cycleDiagram k r n hr E)
      (homOfLE (show cycleLE hr (.inl i) (.inr (next r hr i)) from Or.inr rfl))

/- The range computation is upgraded to a categorical scheme pullback. -/
private lemma cycle_adjacent (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (i : Fin r) :
    IsPullback (leftLeg k n E) (rightLeg k n)
      (cycleChart k r n hr E i) (cycleChart k r n hr E (next r hr i)) := by
  have hcomm : rightLeg k n ≫ cycleChart k r n hr E (next r hr i) =
      leftLeg k n E ≫ cycleChart k r n hr E i := by
    rw [cycle_edge_left, cycle_edge_right k r n hr h3]
  apply IsOpenImmersion.isPullback _ _ _ _ hcomm
  apply TopologicalSpace.Opens.ext
  ext a
  change (∃ b, cycleChart k r n hr E i b = cycleChart k r n hr E (next r hr i) a) ↔
    ∃ z, rightLeg k n z = a
  constructor
  · rintro ⟨b, hb⟩
    rcases cycleChart_eq k r n hr E i (next r hr i) b a hb with hi | hf | hb
    · exact False.elim (next_ne r hr h3 i hi.symm)
    · obtain ⟨z, _, _, hz⟩ := hf
      exact ⟨z, hz⟩
    · obtain ⟨z, hz, _⟩ := hb
      exact False.elim (next_next_ne r hr h3 i hz)
  · rintro ⟨z, rfl⟩
    refine ⟨leftLeg k n E z, ?_⟩
    exact congrArg (fun f : specB k n true ⟶ _ => f z) hcomm.symm

private def cycleBaseCocone (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E) :
    Cocone (cycleDiagram k r n hr E) where
  pt := specR k n
  ι.app i := match i with
    | .inl _ => leftLeg k n E ≫ structureMap k n
    | .inr _ => structureMap k n
  ι.naturality {i j} f := by
    have hf := leOfHom f
    cases i <;> cases j <;> simp only [cycleDiagram, cycleMap,
      Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Category.id_comp]
    · split_ifs
      · rfl
      · exact (legs_over k n E hE).symm
    · exact False.elim hf

/-- The specified cyclic affine atlas exists at every nilpotent thickness. -/
theorem infinitesimal_polygon_atlas :
    ∀ (k : Type u) [Field k] [CharZero k],
      ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (n : ℕ) (E : B k n false ≃+* B k n true),
      IsAdjacent k n E → Nonempty (Atlas k r n hr E) := by
  intro k _ _ r hr h3 n E hE
  refine ⟨{
    X := colimit (cycleDiagram k r n hr E)
    p := colimit.desc (cycleDiagram k r n hr E) (cycleBaseCocone k r n hr E hE)
    chart := cycleChart k r n hr E
    chart_open := fun i => cycleChart_open k r n hr E i
    covers := ?_
    chart_over := ?_
    adjacent := cycle_adjacent k r n hr h3 E
    disjoint := ?_
  }⟩
  · intro x
    obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
      (cycleDiagram k r n hr E) x
    cases i with
    | inr i => exact ⟨i, a, ha⟩
    | inl i =>
      refine ⟨i, leftLeg k n E a, ?_⟩
      rw [← Scheme.Hom.comp_apply, cycle_edge_left]
      exact ha
  · intro i
    exact colimit.ι_desc (cycleBaseCocone k r n hr E hE) (.inr i)
  · intro i j hij hnext hprev
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    rcases cycleChart_eq k r n hr E i j a b (ha.trans hb.symm) with h | h | h
    · exact hij h
    · obtain ⟨z, hz, _⟩ := h
      exact hnext hz
    · obtain ⟨z, hz, _⟩ := h
      exact hprev hz

end ArithmeticThetaInfinitesimalPolygonR0129
