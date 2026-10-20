module

public import PositiveGlobalGenerationR0134

@[expose] public section

/-! Multiplication of positive divisor sections, by special-fiber generators and
nilpotent lifting. Helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace PositiveSectionMultiplicationR0134
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCohomologyR0131 PolygonCechObstructionR0131
open PositiveSectionsReductionR0134 LaurentPolynomial
variable (k : Type u) [Field k] [CharZero k]

lemma compatible_neg (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s : Fin r → A k n) (hs : Compatible k r n hr E a d s) :
    Compatible k r n hr E a d (-s) := by
  intro i
  simpa only [Pi.neg_apply, map_neg, neg_mul] using congrArg Neg.neg (hs i)

lemma compatible_mul (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d e : ℕ)
    (s v : Fin r → A k n) (hs : Compatible k r n hr E a d s)
    (hv : Compatible k r n hr E a e v) :
    Compatible k r n hr E a (d+e) (s*v) := by
  intro i
  simp only [Pi.mul_apply, map_mul, pow_add]
  calc
    _ = (E (restriction k n false (s i)) * restriction k n true (equation k r n hr a (next r hr i))^d) *
        (E (restriction k n false (v i)) * restriction k n true (equation k r n hr a (next r hr i))^e) := by ring
    _ = _ := by rw [hs i, hv i]; ring

def products (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d e : ℕ) :
    AddSubgroup (Fin r → A k n) where
  carrier := {s | ∃ (l : ℕ) (v : Fin l → Sections k r n hr E a d)
    (w : Fin l → Sections k r n hr E a e), ∀ i, s i = ∑ j, (v j).val i * (w j).val i}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  add_mem' := by
    rintro s t ⟨l,v,w,h⟩ ⟨m,v',w',h'⟩
    refine ⟨l+m, Fin.addCases v v', Fin.addCases w w', ?_⟩
    intro i
    simp only [Pi.add_apply, h i, h' i, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  neg_mem' := by
    rintro s ⟨l,v,w,h⟩
    refine ⟨l, fun j => ⟨-(v j).val, compatible_neg k r n hr E a d _ (v j).property⟩, w, ?_⟩
    intro i
    simp only [Pi.neg_apply, h i, neg_mul, Finset.sum_neg_distrib]

lemma product_mem (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d e : ℕ)
    (s : Sections k r n hr E a d) (v : Sections k r n hr E a e) :
    s.val * v.val ∈ products k r n hr E a d e := by
  exact ⟨1, fun _ => s, fun _ => v, by simp⟩

lemma products_base_mul (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d e : ℕ) (c : R k n) (s : Fin r → A k n)
    (hs : s ∈ products k r n hr E a d e) :
    (fun i => base k n c * s i) ∈ products k r n hr E a d e := by
  obtain ⟨l,v,w,h⟩ := hs
  refine ⟨l, fun j => ⟨fun i => base k n c * (v j).val i,
    compatible_base_mul k r n hr E hE a d c _ (v j).property⟩, w, ?_⟩
  intro i
  simp only [h i, Finset.mul_sum, mul_assoc]

lemma products_compatible (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d e : ℕ)
    (s : Fin r → A k n) (hs : s ∈ products k r n hr E a d e) :
    Compatible k r n hr E a (d+e) s := by
  obtain ⟨l,v,w,h⟩ := hs
  have he : s = ∑ j : Fin l, (v j).val * (w j).val := by ext i; simpa using h i
  rw [he]
  apply Finset.sum_induction
  · intro x y hx hy
    exact compatible_add k r n hr E a (d+e) x y hx hy
  · exact compatible_zero k r n hr E a (d+e)
  · intro j _
    exact compatible_mul k r n hr E a d e _ _ (v j).property (w j).property

lemma special_pair_injective
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (x : A k 0) (hx : rx L x = 0) (hy : ry E L x = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := PolygonCechKernelR0131.exists_expansion k 0 x
  have hz : c = 0 := by
    ext j
    by_cases hj : 0 ≤ j
    · have h := congrArg (fun p : LaurentPolynomial (R k 0) => p.coeff j) hx
      erw [hc, PolygonCechKernelR0131.right_coeff L hL] at h
      simpa [Int.toNat_of_nonpos (show -j ≤ 0 by omega)] using h
    · have h := congrArg (fun p : LaurentPolynomial (R k 0) => p.coeff j) hy
      erw [hc, PolygonCechKernelR0131.left_coeff L hL E hE] at h
      simpa [Int.toNat_of_nonpos (show j ≤ 0 by omega)] using h
  rw [hc, hz]
  simp

lemma special_rx_negative
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (x : A k 0) (j : ℤ) (hj : j < 0) : (rx L x).coeff j = 0 := by
  obtain ⟨c, hc⟩ := PolygonCechKernelR0131.exists_expansion k 0 x
  erw [hc, PolygonCechKernelR0131.right_coeff L hL, parameter_zero,
    zero_pow (show (-j).toNat ≠ 0 by omega), mul_zero]

lemma special_ry_positive
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (x : A k 0) (j : ℤ) (hj : 0 < j) : (ry E L x).coeff j = 0 := by
  obtain ⟨c, hc⟩ := PolygonCechKernelR0131.exists_expansion k 0 x
  erw [hc, PolygonCechKernelR0131.left_coeff L hL E hE, parameter_zero,
    zero_pow (show j.toNat ≠ 0 by omega), mul_zero]

def ratio (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) : (R k 0)ˣ :=
  leftConstant k r hr a i * (rightConstant k r hr a i)⁻¹

lemma special_compatible_iff (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k 0) :
    Compatible k r 0 hr E a d s ↔ ∀ i,
      ry E L (s i) = rx L (s (next r hr i)) *
        (C ((ratio k r hr a i : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ))) := by
  rw [compatible_iff_normalized_zero k r 0 hr E hE]
  apply forall_congr'
  intro i
  rw [← L.map_eq_zero_iff, normalized_special k r hr a d E hE L hL]
  simp only [specialMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [sub_eq_zero]
  have hu := ((rightConstant k r hr a i).isUnit.pow d).map C
  have hc : C ((leftConstant k r hr a i : R k 0)^d) =
      C ((ratio k r hr a i : R k 0)^d) * C ((rightConstant k r hr a i : R k 0)^d) := by
    rw [← map_mul, ← mul_pow]
    congr 2
    simp [ratio, mul_assoc]
  rw [hc]
  constructor
  · intro h
    apply hu.mul_right_cancel
    calc
      _ = _ := h
      _ = _ := by ring
  · intro h
    rw [h]
    ring

section Special
variable {k}
variable {r : ℕ} (hr : 0 < r) (h3 : 3 ≤ r)
variable (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
variable (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
variable (q : Fin r → (R k 0)ˣ)

def vertex (d : ℕ) (i j : Fin r) : A k 0 :=
  (if j = i then 1 else 0) +
  (if next r hr j = i then base k 0 ((q j : R k 0)^d) * coordY k 0^d else 0) +
  (if j = next r hr i then base k 0 ((↑((q i)⁻¹) : R k 0)^d) * coordX k 0^d else 0)

def edge (d p : ℕ) (i j : Fin r) : A k 0 :=
  (if j = i then base k 0 ((q i : R k 0)^d) * coordY k 0^p else 0) +
  (if j = next r hr i then coordX k 0^(d-p) else 0)

include hL

lemma vertex_rx (d : ℕ) (hd : 0 < d) (i j : Fin r) :
    rx L (vertex hr q d i j) =
      (if j=i then 1 else 0) +
      (if j=next r hr i then C ((↑((q i)⁻¹) : R k 0)^d) * LaurentPolynomial.T (d : ℤ) else 0) := by
  simp only [vertex, map_add, apply_ite (rx L), map_one, map_zero, map_mul, map_pow,
    rx_base hL, rx_x hL, rx_y hL, parameter_zero, map_zero, zero_mul,
    zero_pow hd.ne', mul_zero, ite_self, add_zero, LaurentPolynomial.T_pow, mul_one]

include hE in
lemma vertex_ry (d : ℕ) (hd : 0 < d) (i j : Fin r) :
    ry E L (vertex hr q d i j) =
      (if j=i then 1 else 0) +
      (if next r hr j=i then C ((q j : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ)) else 0) := by
  simp only [vertex, map_add, apply_ite (ry E L), map_one, map_zero, map_mul, map_pow,
    ry_base hE hL, ry_y hE hL, ry_x hE hL, parameter_zero, map_zero, zero_mul,
    zero_pow hd.ne', mul_zero, ite_self, add_zero, LaurentPolynomial.T_pow, mul_neg, mul_one]

lemma edge_rx (d p : ℕ) (hp : 0 < p) (i j : Fin r) :
    rx L (edge hr q d p i j) =
      if j=next r hr i then LaurentPolynomial.T ((d-p : ℕ) : ℤ) else 0 := by
  simp only [edge, map_add, apply_ite (rx L), map_zero, map_mul, map_pow,
    rx_base hL, rx_x hL, rx_y hL, parameter_zero, map_zero, zero_mul,
    zero_pow hp.ne', mul_zero, ite_self, zero_add, LaurentPolynomial.T_pow, mul_one]

include hE in
lemma edge_ry (d p : ℕ) (hp : p < d) (i j : Fin r) :
    ry E L (edge hr q d p i j) =
      if j=i then C ((q i : R k 0)^d) * LaurentPolynomial.T (-(p : ℤ)) else 0 := by
  simp only [edge, map_add, apply_ite (ry E L), map_zero, map_mul, map_pow,
    ry_base hE hL, ry_y hE hL, ry_x hE hL, parameter_zero, map_zero, zero_mul,
    zero_pow (show d-p ≠ 0 by omega), ite_self, add_zero, LaurentPolynomial.T_pow, mul_neg, mul_one]

include hE h3 in
lemma vertex_transition (d : ℕ) (hd : 0 < d) (i j : Fin r) :
    ry E L (vertex hr q d i j) = rx L (vertex hr q d i (next r hr j)) *
      (C ((q j : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ))) := by
  rw [vertex_ry hr E hE L hL q d hd, vertex_rx hr L hL q d hd]
  have hinj : next r hr j = next r hr i ↔ j=i := (shift r hr).injective.eq_iff
  simp only [hinj, add_mul]
  by_cases hj : j=i
  · subst j
    have hn := PositiveGlobalGenerationR0134.next_ne r hr h3 i
    simp only [hn, if_false, if_true, zero_mul, zero_add, add_zero]
    symm
    calc
      _ = C (((↑((q i)⁻¹) : R k 0)^d) * (q i : R k 0)^d) *
          (LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.T (-(d : ℤ))) := by rw [map_mul]; ring
      _ = 1 := by
        rw [← mul_pow]
        simp only [Units.inv_mul, one_pow, map_one, ← LaurentPolynomial.T_add,
          add_neg_cancel, LaurentPolynomial.T_zero, one_mul]
  · simp only [hj, if_false, zero_add, zero_mul, add_zero]
    split_ifs <;> simp

include hE in
lemma edge_transition (d p : ℕ) (hp : 0 < p) (hpd : p < d) (i j : Fin r) :
    ry E L (edge hr q d p i j) = rx L (edge hr q d p i (next r hr j)) *
      (C ((q j : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ))) := by
  rw [edge_ry hr E hE L hL q d p hpd, edge_rx hr L hL q d p hp]
  have hinj : next r hr j = next r hr i ↔ j=i := (shift r hr).injective.eq_iff
  simp only [hinj]
  by_cases hj : j=i
  · subst j
    simp only [if_true]
    rw [mul_left_comm, ← LaurentPolynomial.T_add]
    congr 2
    omega
  · simp [hj]

end Special

lemma special_sections_ext (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (a : Fin r → kˣ) (d : ℕ) (s v : Fin r → A k 0)
    (hs : Compatible k r 0 hr E a d s) (hv : Compatible k r 0 hr E a d v)
    (hy : ∀ i, ry E L (s i) = ry E L (v i)) : s=v := by
  have hs' := (special_compatible_iff k r hr E hE L hL a d s).mp hs
  have hv' := (special_compatible_iff k r hr E hE L hL a d v).mp hv
  funext i
  apply sub_eq_zero.mp
  apply special_pair_injective k E hE L hL
  · obtain ⟨j, rfl⟩ := next_surjective r hr i
    rw [map_sub, sub_eq_zero]
    apply ((((ratio k r hr a j).isUnit.pow d).map C).mul (isUnit_T _)).mul_right_cancel
    rw [← hs' j, ← hv' j, hy j]
  · rw [map_sub, hy i, sub_self]

section ActualSpecial
variable {k} {r : ℕ} (hr : 0 < r) (h3 : 3 ≤ r)
variable (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
variable (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
variable (a : Fin r → kˣ)

include hE hL h3 in
lemma vertex_compatible (d : ℕ) (hd : 0 < d) (i : Fin r) :
    Compatible k r 0 hr E a d (vertex hr (ratio k r hr a) d i) := by
  rw [special_compatible_iff k r hr E hE L hL]
  exact vertex_transition hr h3 E hE L hL (ratio k r hr a) d hd i

include hE hL in
lemma edge_compatible (d p : ℕ) (hp : 0 < p) (hpd : p < d) (i : Fin r) :
    Compatible k r 0 hr E a d (edge hr (ratio k r hr a) d p i) := by
  rw [special_compatible_iff k r hr E hE L hL]
  exact edge_transition hr E hE L hL (ratio k r hr a) d p hp hpd i

include hE hL h3 in
lemma vertex_product (d e : ℕ) (hd : 0 < d) (he : 0 < e) (i : Fin r) :
    vertex hr (ratio k r hr a) (d+e) i =
      vertex hr (ratio k r hr a) d i * vertex hr (ratio k r hr a) e i := by
  let q := ratio k r hr a
  apply special_sections_ext k r hr E hE L hL a (d+e)
    _ _ (vertex_compatible hr h3 E hE L hL a _ (by omega) i)
    (compatible_mul k r 0 hr E a d e _ _
      (vertex_compatible hr h3 E hE L hL a d hd i)
      (vertex_compatible hr h3 E hE L hL a e he i))
  intro j
  simp only [Pi.mul_apply, map_mul,
    vertex_ry hr E hE L hL _ (d+e) (by omega),
    vertex_ry hr E hE L hL _ d hd, vertex_ry hr E hE L hL _ e he]
  by_cases hj : j=i
  · subst j
    simp [PositiveGlobalGenerationR0134.next_ne r hr h3 i]
  · simp only [hj, if_false, zero_add]
    split_ifs <;> try simp
    simp only [pow_add, map_mul, Nat.cast_add, neg_add, LaurentPolynomial.T_add]
    ring

include hE hL h3 in
lemma vertex_mem (d e : ℕ) (hd : 0 < d) (he : 0 < e) (i : Fin r) :
    vertex hr (ratio k r hr a) (d+e) i ∈ products k r 0 hr E a d e := by
  rw [vertex_product hr h3 E hE L hL a d e hd he]
  exact product_mem k r 0 hr E a d e
    ⟨_, vertex_compatible hr h3 E hE L hL a d hd i⟩
    ⟨_, vertex_compatible hr h3 E hE L hL a e he i⟩

include hE hL in
lemma edge_product (d e p q : ℕ) (hp : 0 < p) (hpd : p < d)
    (hq : 0 < q) (hqe : q < e) (i : Fin r) :
    edge hr (ratio k r hr a) (d+e) (p+q) i =
      edge hr (ratio k r hr a) d p i * edge hr (ratio k r hr a) e q i := by
  apply special_sections_ext k r hr E hE L hL a (d+e)
    _ _ (edge_compatible hr E hE L hL a _ _ (by omega) (by omega) i)
    (compatible_mul k r 0 hr E a d e _ _
      (edge_compatible hr E hE L hL a d p hp hpd i)
      (edge_compatible hr E hE L hL a e q hq hqe i))
  intro j
  simp only [Pi.mul_apply, map_mul,
    edge_ry hr E hE L hL _ (d+e) (p+q) (by omega),
    edge_ry hr E hE L hL _ d p hpd, edge_ry hr E hE L hL _ e q hqe]
  split_ifs <;> try simp
  simp only [pow_add, map_mul, Nat.cast_add, neg_add, LaurentPolynomial.T_add]
  ring

include hE hL h3 in
lemma edge_low_product (d e p : ℕ) (hd : 0 < d) (hp : 0 < p) (hpe : p < e)
    (i : Fin r) :
    edge hr (ratio k r hr a) (d+e) p i =
      fun j => base k 0 ((ratio k r hr a i : R k 0)^d) *
        (vertex hr (ratio k r hr a) d i j * edge hr (ratio k r hr a) e p i j) := by
  apply special_sections_ext k r hr E hE L hL a (d+e)
    _ _ (edge_compatible hr E hE L hL a _ _ hp (by omega) i)
    (compatible_base_mul k r 0 hr E hE a (d+e) _ _
      (compatible_mul k r 0 hr E a d e _ _
        (vertex_compatible hr h3 E hE L hL a d hd i)
        (edge_compatible hr E hE L hL a e p hp hpe i)))
  intro j
  simp only [Pi.mul_apply, map_mul, ry_base hE hL,
    edge_ry hr E hE L hL _ (d+e) p (by omega),
    vertex_ry hr E hE L hL _ d hd, edge_ry hr E hE L hL _ e p hpe]
  by_cases hj : j=i
  · subst j
    simp only [if_true, PositiveGlobalGenerationR0134.next_ne r hr h3 i,
      if_false, add_zero, one_mul, pow_add, map_mul, mul_assoc]
  · simp [hj]

include hE hL h3 in
lemma edge_high_product (d e p : ℕ) (hd : 0 < d) (hp : 0 < p) (hpe : p < e)
    (i : Fin r) :
    edge hr (ratio k r hr a) (d+e) (d+p) i =
      vertex hr (ratio k r hr a) d (next r hr i) * edge hr (ratio k r hr a) e p i := by
  apply special_sections_ext k r hr E hE L hL a (d+e)
    _ _ (edge_compatible hr E hE L hL a _ _ (by omega) (by omega) i)
    (compatible_mul k r 0 hr E a d e _ _
      (vertex_compatible hr h3 E hE L hL a d hd (next r hr i))
      (edge_compatible hr E hE L hL a e p hp hpe i))
  intro j
  simp only [Pi.mul_apply, map_mul,
    edge_ry hr E hE L hL _ (d+e) (d+p) (by omega),
    vertex_ry hr E hE L hL _ d hd, edge_ry hr E hE L hL _ e p hpe]
  by_cases hj : j=i
  · subst j
    simp only [if_true, Ne.symm (PositiveGlobalGenerationR0134.next_ne r hr h3 i),
      if_false, zero_add, pow_add, map_mul, Nat.cast_add, neg_add, LaurentPolynomial.T_add]
    ring
  · simp [hj]

include hE hL h3 in
lemma edge_mem (d e : ℕ) (hd : 3 ≤ d) (he : 3 ≤ e)
    (p : ℕ) (hp : 0 < p) (hpd : p < d+e) (i : Fin r) :
    edge hr (ratio k r hr a) (d+e) p i ∈ products k r 0 hr E a d e := by
  by_cases hlo : p=1
  · subst p
    rw [edge_low_product hr h3 E hE L hL a d e 1 (by omega) (by omega) (by omega)]
    exact products_base_mul k r 0 hr E hE a d e _ _
      (product_mem k r 0 hr E a d e
        ⟨_, vertex_compatible hr h3 E hE L hL a d (by omega) i⟩
        ⟨_, edge_compatible hr E hE L hL a e 1 (by omega) (by omega) i⟩)
  by_cases hhi : p=d+e-1
  · have heq : p=d+(e-1) := by omega
    rw [heq, edge_high_product hr h3 E hE L hL a d e (e-1) (by omega) (by omega) (by omega)]
    exact product_mem k r 0 hr E a d e
      ⟨_, vertex_compatible hr h3 E hE L hL a d (by omega) (next r hr i)⟩
      ⟨_, edge_compatible hr E hE L hL a e (e-1) (by omega) (by omega) i⟩
  have hsplit : ∃ b c : ℕ, 0 < b ∧ b < d ∧ 0 < c ∧ c < e ∧ p=b+c := by
    by_cases h : p ≤ d
    · exact ⟨p-1, 1, by omega⟩
    · exact ⟨d-1, p-(d-1), by omega⟩
  obtain ⟨b,c,hb,hbd,hc,hce,rfl⟩ := hsplit
  rw [edge_product hr E hE L hL a d e b c hb hbd hc hce]
  exact product_mem k r 0 hr E a d e
    ⟨_, edge_compatible hr E hE L hL a d b hb hbd i⟩
    ⟨_, edge_compatible hr E hE L hL a e c hc hce i⟩

end ActualSpecial

lemma coeff_monomial {S : Type*} [CommRing S] (c : S) (m j : ℤ) :
    (C c * LaurentPolynomial.T m).coeff j = if m=j then c else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma coeff_mul_monomial {S : Type*} [CommRing S]
    (f : LaurentPolynomial S) (c : S) (m j : ℤ) :
    (f * (C c * LaurentPolynomial.T m)).coeff j = f.coeff (j-m) * c := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  apply AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul
  intro x _
  omega

lemma negative_expansion {S : Type*} [CommRing S] (D : ℕ) (f : LaurentPolynomial S)
    (hf : ∀ j : ℤ, j ≤ -(D : ℤ) ∨ 0 ≤ j → f.coeff j = 0) :
    f = ∑ p ∈ Finset.Ioo 0 D, C (f.coeff (-(p : ℤ))) * LaurentPolynomial.T (-(p : ℤ)) := by
  classical
  apply LaurentPolynomial.ext
  intro j
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_monomial]
  by_cases hj : -(D : ℤ) < j ∧ j < 0
  · have hm : (-j).toNat ∈ Finset.Ioo 0 D := by simp only [Finset.mem_Ioo]; omega
    rw [Finset.sum_eq_single (-j).toNat]
    · simp only [show -(((-j).toNat : ℕ) : ℤ) = j by omega, if_true]
    · intro p hp hne
      simp only [if_neg (show -(p : ℤ) ≠ j by omega)]
    · exact fun h => (h hm).elim
  · rw [hf j (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_Ioo] at hp
    exact if_neg (by omega)

section Spanning
variable {k} {r : ℕ} (hr : 0 < r) (h3 : 3 ≤ r)
variable (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
variable (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
variable (a : Fin r → kˣ)

include hE hL in
lemma vertex_constant (d : ℕ) (hd : 0 < d) (i j : Fin r) :
    (ry E L (vertex hr (ratio k r hr a) d i j)).coeff 0 = if j=i then 1 else 0 := by
  rw [vertex_ry hr E hE L hL _ d hd]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, apply_ite (fun p : LaurentPolynomial (R k 0) => p.coeff 0),
    coeff_monomial, if_neg (show -(d : ℤ) ≠ 0 by omega), ite_self, add_zero]
  split_ifs <;> simp

include hE hL in
lemma special_support (d : ℕ) (s : Sections k r 0 hr E a d)
    (hzero : ∀ i, (ry E L (s.val i)).coeff 0 = 0) (i : Fin r) (j : ℤ)
    (hj : j ≤ -(d : ℤ) ∨ 0 ≤ j) : (ry E L (s.val i)).coeff j = 0 := by
  rcases hj with hj | hj
  · have h := congrArg (fun f : LaurentPolynomial (R k 0) => f.coeff j)
      ((special_compatible_iff k r hr E hE L hL a d s.val).mp s.property i)
    rw [coeff_mul_monomial] at h
    rw [h]
    have hz : (rx L (s.val (next r hr i))).coeff (j - -(d : ℤ)) = 0 := by
      by_cases he : j = -(d : ℤ)
      · rw [he, sub_self, ← coeff_zero_agree hE hL]
        exact hzero _
      · exact special_rx_negative k L hL _ _ (by omega)
    rw [hz, zero_mul]
  · rcases eq_or_lt_of_le hj with hj | hj
    · rw [← hj]; exact hzero i
    · exact special_ry_positive k E hE L hL _ _ hj

include hE hL h3 in
lemma zero_constants_mem (d e : ℕ) (hd : 3 ≤ d) (he : 3 ≤ e)
    (s : Sections k r 0 hr E a (d+e))
    (hzero : ∀ i, (ry E L (s.val i)).coeff 0 = 0) :
    s.val ∈ products k r 0 hr E a d e := by
  classical
  let q := ratio k r hr a
  let f := fun i => ry E L (s.val i)
  let c := fun i p => (f i).coeff (-(p : ℤ)) * (↑((q i)⁻¹) : R k 0)^(d+e)
  let v := fun i => ∑ p ∈ Finset.Ioo 0 (d+e),
    (fun j => base k 0 (c i p) * edge hr q (d+e) p i j)
  have hv (i : Fin r) : v i ∈ products k r 0 hr E a d e := by
    apply (products k r 0 hr E a d e).sum_mem
    intro p hp
    exact products_base_mul k r 0 hr E hE a d e (c i p) _
      (edge_mem hr h3 E hE L hL a d e hd he p
        (Finset.mem_Ioo.mp hp).1 (Finset.mem_Ioo.mp hp).2 i)
  have himage (i j : Fin r) : ry E L (v i j) = if j=i then f i else 0 := by
    simp only [v, Finset.sum_apply, map_sum]
    have hterm (p : ℕ) (hp : p ∈ Finset.Ioo 0 (d+e)) :
        ry E L (base k 0 (c i p) * edge hr q (d+e) p i j) =
        if j=i then C ((f i).coeff (-(p : ℤ))) * LaurentPolynomial.T (-(p : ℤ)) else 0 := by
      rw [map_mul, ry_base hE hL, edge_ry hr E hE L hL q (d+e) p (Finset.mem_Ioo.mp hp).2]
      by_cases hj : j=i
      · simp only [hj, if_true, ← mul_assoc, ← map_mul]
        congr 2
        dsimp [c]
        rw [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
      · simp only [hj, if_false, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hj : j=i
    · simp only [hj, if_true]
      exact (negative_expansion (d+e) (f i)
        (special_support hr E hE L hL a (d+e) s hzero i)).symm
    · simp only [hj, if_false, Finset.sum_const_zero]
  have hvsum : (∑ i : Fin r, v i) ∈ products k r 0 hr E a d e :=
    (products k r 0 hr E a d e).sum_mem (fun i _ => hv i)
  have hs : s.val = ∑ i : Fin r, v i := by
    apply special_sections_ext k r hr E hE L hL a (d+e) _ _ s.property
      (products_compatible k r 0 hr E a d e _ hvsum)
    intro j
    simp only [Finset.sum_apply, map_sum, himage]
    simp [f]
  rwa [hs]

include hE hL h3 in
lemma special_multiplication (d e : ℕ) (hd : 3 ≤ d) (he : 3 ≤ e) :
    MultiplicationSurjective k r 0 hr E a d e := by
  classical
  intro s
  let c := fun i => (ry E L (s.val i)).coeff 0
  let v : Fin r → A k 0 := ∑ i : Fin r,
    (fun j => base k 0 (c i) * vertex hr (ratio k r hr a) (d+e) i j)
  have hv : v ∈ products k r 0 hr E a d e := by
    apply (products k r 0 hr E a d e).sum_mem
    intro i _
    exact products_base_mul k r 0 hr E hE a d e (c i) _
      (vertex_mem hr h3 E hE L hL a d e (by omega) (by omega) i)
  have hc (j : Fin r) : (ry E L (v j)).coeff 0 = c j := by
    simp only [v, Finset.sum_apply, map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      map_mul, ry_base hE hL, ← LaurentPolynomial.smul_eq_C_mul,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      vertex_constant hr E hE L hL a (d+e) (by omega)]
    simp
  have hs : Compatible k r 0 hr E a (d+e) (s.val-v) := by
    simpa only [sub_eq_add_neg, Pi.add_def] using
      compatible_add k r 0 hr E a (d+e) s.val (-v) s.property
        (compatible_neg k r 0 hr E a (d+e) v (products_compatible k r 0 hr E a d e v hv))
  have hm := zero_constants_mem hr h3 E hE L hL a d e hd he ⟨s.val-v, hs⟩ (by
    intro i
    change (ry E L (s.val i-v i)).coeff 0 = 0
    rw [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hc i]
    exact sub_self _)
  change s.val ∈ products k r 0 hr E a d e
  simpa only [sub_add_cancel] using (products k r 0 hr E a d e).add_mem hm hv

end Spanning

/-- Products at thickness zero can be lifted factor by factor. -/
lemma lift_products (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d e N : ℕ) (hd : 0 < d) (he : 0 < e)
    (s : Fin r → A k 0) (hs : s ∈ products k r 0 hr (T.overlap 0) a d e) :
    ∃ v ∈ products k r N hr (T.overlap N) a d e, ∀ i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        0 N (Nat.zero_le N) (v i) = s i := by
  obtain ⟨l, v, w, hs⟩ := hs
  choose v' hv using fun j =>
    (positive_sections_reduction k r hr h3 T a d hd 0 N (Nat.zero_le N)).2.1 (v j)
  choose w' hw using fun j =>
    (positive_sections_reduction k r hr h3 T a e he 0 N (Nat.zero_le N)).2.1 (w j)
  refine ⟨∑ j : Fin l, (v' j).val * (w' j).val, ?_, ?_⟩
  · exact (products k r N hr (T.overlap N) a d e).sum_mem
      (fun j _ => product_mem k r N hr (T.overlap N) a d e (v' j) (w' j))
  · intro i
    simp only [Finset.sum_apply, Pi.mul_apply, map_sum, map_mul, hv, hw, hs i]

lemma approximate_products (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d e N : ℕ) (hd : 0 < d) (he : 0 < e)
    (hzero : MultiplicationSurjective k r 0 hr (T.overlap 0) a d e)
    (s : Sections k r N hr (T.overlap N) a (d+e)) :
    ∃ x ∈ products k r N hr (T.overlap N) a d e,
      ∃ v : Sections k r N hr (T.overlap N) a (d+e),
        ∀ i, s.val i = x i + base k N (parameter k N) * v.val i := by
  let red := truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
    0 N (Nat.zero_le N)
  let s0 : Sections k r 0 hr (T.overlap 0) a (d+e) :=
    ⟨fun i => red (s.val i), compatible_reduction k r hr T a (d+e) 0 N (Nat.zero_le N) s⟩
  obtain ⟨x, hx, hred⟩ := lift_products k r hr h3 T a d e N hd he s0.val (hzero s0)
  have hsx : Compatible k r N hr (T.overlap N) a (d+e) (s.val-x) := by
    simpa only [sub_eq_add_neg, Pi.add_def] using
      compatible_add k r N hr (T.overlap N) a (d+e) s.val (-x) s.property
        (compatible_neg k r N hr (T.overlap N) a (d+e) x
          (products_compatible k r N hr (T.overlap N) a d e x hx))
  obtain ⟨v, hv⟩ := (positive_sections_reduction k r hr h3 T a (d+e) (by omega)
    0 N (Nat.zero_le N)).2.2 ⟨s.val-x, hsx⟩ |>.mp (by
      intro i
      change red (s.val i - x i) = 0
      rw [map_sub, hred i]
      exact sub_self _)
  refine ⟨x, hx, v, fun i => ?_⟩
  have hi := hv i
  change s.val i - x i = base k N (parameter k N ^ (0+1)) * v.val i at hi
  simpa only [Nat.zero_add, pow_one, add_comm] using sub_eq_iff_eq_add.mp hi

/-- Finite nilpotence upgrades surjectivity on the special fiber to every stage. -/
lemma multiplication_of_special (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d e N : ℕ) (hd : 0 < d) (he : 0 < e)
    (hzero : MultiplicationSurjective k r 0 hr (T.overlap 0) a d e) :
    MultiplicationSurjective k r N hr (T.overlap N) a d e := by
  let P := products k r N hr (T.overlap N) a d e
  let t := base k N (parameter k N)
  have haux : ∀ m (s : Sections k r N hr (T.overlap N) a (d+e)),
      ∃ x ∈ P, ∃ v : Sections k r N hr (T.overlap N) a (d+e),
        ∀ i, s.val i = x i + t^m * v.val i := by
    intro m
    induction m with
    | zero => intro s; exact ⟨0, P.zero_mem, s, by simp⟩
    | succ m ih =>
      intro s
      obtain ⟨x, hx, v, hv⟩ := ih s
      obtain ⟨y, hy, w, hw⟩ := approximate_products k r hr h3 T a d e N hd he hzero v
      refine ⟨x + (fun i => t^m * y i), P.add_mem hx ?_, w, ?_⟩
      · simpa only [t, map_pow] using products_base_mul k r N hr (T.overlap N)
          (T.overlap_spec N) a d e (parameter k N ^ m) y hy
      · intro i
        rw [hv i, hw i]
        simp only [Pi.add_apply, pow_succ]
        ring
  intro s
  obtain ⟨x, hx, v, hv⟩ := haux (N+1) s
  have ht : t^(N+1) = 0 := by
    dsimp [t]
    rw [← map_pow, parameter_pow, map_zero]
  have hs : s.val = x := funext fun i => by simpa only [ht, zero_mul, add_zero] using hv i
  change s.val ∈ P
  rwa [hs]

end PositiveSectionMultiplicationR0134
/-- Every positive section of degree d+e is a finite sum of actual numerator
products in degrees d and e, at every infinitesimal thickness. -/
theorem positive_section_multiplication :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (a : Fin r → kˣ), ∀ d e : ℕ, 3 ≤ d → 3 ≤ e →
      ArithmeticThetaPositiveLineR0134.MultiplicationSurjective k r n hr E a d e := by
  intro k _ _ r n hr h3 E hE a d e hd he
  let T := ArithmeticThetaInfinitesimalPolygonR0129.TowerAssemblyR0130.assembledTower k r hr h3
  have hEq : T.overlap n = E :=
    (ArithmeticThetaInfinitesimalPolygonR0129.finite_stage_adjacent k n).unique
      (T.overlap_spec n) hE
  rw [← hEq]
  apply PositiveSectionMultiplicationR0134.multiplication_of_special k r hr h3 T a d e n
    (by omega) (by omega)
  obtain ⟨L, hL, _⟩ := ArithmeticThetaPolygonCohomologyR0131.truncated_laurent_presentation k 0
  exact PositiveSectionMultiplicationR0134.special_multiplication hr h3
    (T.overlap 0) (T.overlap_spec 0) L hL a d e hd he

end ArithmeticThetaPositiveLineR0134
