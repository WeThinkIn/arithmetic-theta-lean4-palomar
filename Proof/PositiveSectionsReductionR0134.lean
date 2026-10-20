module

public import PositiveLineSectionsDefinitionsR0134

@[expose] public section

/-! Reduction of positive divisor numerators on the actual infinitesimal polygon.
All auxiliary declarations are scoped to this module. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace PositiveSectionsReductionR0134
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCartierR0133

variable (k : Type u) [Field k] [CharZero k]

lemma reduce_restriction (n N : ℕ) (h : n ≤ N) (side : Bool) (z : A k N) :
    truncReduce (RawOpen k side) (openParameter k side) n N h
      (restriction k N side z) =
    restriction k n side
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h z) :=
  RingHom.congr_fun (truncReduce_natural _ _ _ rfl n N h) z

lemma reduce_base (n N : ℕ) (h : n ≤ N) (c : R k N) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (base k N c) =
    base k n (truncReduce (PowerSeries k) PowerSeries.X n N h c) :=
  RingHom.congr_fun (truncReduce_natural _ _ _ rfl n N h) c

lemma reduce_equation (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    (a : Fin r → kˣ) (i : Fin r) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (equation k r N hr a i) = equation k r n hr a i :=
  MarkedIdealTowerBaseChangeR0133.pairEquation_reduction k n N h _ _

lemma compatible_reduction (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N)
    (s : Sections k r N hr (T.overlap N) a d) :
    Compatible k r n hr (T.overlap n) a d (fun i =>
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (s.val i)) := by
  intro i
  have ha (z : B k N false) :
      T.overlap n (truncReduce (RawOpen k false) (openParameter k false) n N h z) =
      truncReduce (RawOpen k true) (openParameter k true) n N h (T.overlap N z) :=
    RingHom.congr_fun
      (adjacent_reduction k n N h (T.overlap n) (T.overlap N)
        (T.overlap_spec n) (T.overlap_spec N)) z
  have he := congrArg (truncReduce (RawOpen k true) (openParameter k true) n N h)
    (s.property i)
  simp only [map_mul, map_pow] at he
  simp only [← ha, reduce_restriction, reduce_equation] at he
  exact he

lemma compatible_zero (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ) :
    Compatible k r n hr E a d (fun _ => 0) := by
  intro i
  simp only [map_zero, zero_mul]

lemma compatible_add (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s v : Fin r → A k n) (hs : Compatible k r n hr E a d s)
    (hv : Compatible k r n hr E a d v) :
    Compatible k r n hr E a d (fun i => s i + v i) := by
  intro i
  simp only [map_add, add_mul, hs i, hv i]

lemma compatible_base_mul (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d : ℕ) (c : R k n)
    (s : Fin r → A k n) (hs : Compatible k r n hr E a d s) :
    Compatible k r n hr E a d (fun i => base k n c * s i) := by
  intro i
  simp only [map_mul, mul_assoc]
  rw [show E (restriction k n false (base k n c)) =
      restriction k n true (base k n c) from
    RingHom.congr_fun (adjacent_base hE) c, hs i]

lemma reduce_self {S : Type u} [CommRing S] (t : S) (n : ℕ)
    (h : n ≤ n) (z : Trunc S t n) : truncReduce S t n n h z = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

lemma reduce_parameter (n N : ℕ) (h : n ≤ N) :
    truncReduce (PowerSeries k) PowerSeries.X n N h (parameter k N) =
      parameter k n := rfl

lemma parameter_multiple_reduces_zero (n N : ℕ) (h : n ≤ N) (z : A k N) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (base k N (parameter k N ^ (n+1)) * z) = 0 := by
  rw [map_mul, reduce_base, map_pow, reduce_parameter, parameter_pow, map_zero, zero_mul]

/-- The easy kernel inclusion needs no lifting assertion. -/
lemma kernel_of_parameter_multiple (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N)
    (s : Sections k r N hr (T.overlap N) a d)
    (hv : ∃ v : Sections k r N hr (T.overlap N) a d,
      ∀ i, s.val i = base k N (parameter k N ^ (n+1)) * v.val i) :
    ∀ i, truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (s.val i) = 0 := by
  obtain ⟨v, hv⟩ := hv
  intro i
  rw [hv i]
  exact parameter_multiple_reduces_zero k n N h _

/-- The full equal-stage boundary case, including degree zero. -/
lemma reduction_self (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n : ℕ) (h : n ≤ n) :
    ReductionFacts k r hr T a d n n h := by
  refine ⟨compatible_reduction k r hr T a d n n h, ?_, ?_⟩
  · intro s
    exact ⟨s, fun i => reduce_self _ _ _ _⟩
  · intro s
    constructor
    · intro hs
      refine ⟨⟨fun _ => 0, compatible_zero k r n hr (T.overlap n) a d⟩, ?_⟩
      intro i
      simpa only [reduce_self, mul_zero] using hs i
    · exact kernel_of_parameter_multiple k r hr T a d n n h s

/-- The coordinate kernel is the expected principal ideal, without flatness. -/
lemma truncReduce_eq_zero_iff {S : Type u} [CommRing S] (t : S)
    (n N : ℕ) (h : n ≤ N) (z : Trunc S t N) :
    truncReduce S t n N h z = 0 ↔
      ∃ w : Trunc S t N, z = trunc S t N (t ^ (n+1)) * w := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  constructor
  · intro hz
    change trunc S t n z = 0 at hz
    have hz' := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz'
    obtain ⟨w, hw⟩ := hz'
    refine ⟨trunc S t N w, ?_⟩
    change trunc S t N z = _
    rw [hw, map_mul]
  · rintro ⟨w, hw⟩
    rw [hw, map_mul]
    change trunc S t n (t ^ (n+1)) * _ = 0
    rw [trunc_parameter_zero, zero_mul]

lemma node_parameter_power (n m : ℕ) :
    trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
      (ArithmeticThetaNodeCharts.t k ^ m) = base k n (parameter k n ^ m) := by
  rw [map_pow, map_pow]
  rfl

/-- Coordinate divisibility follows immediately; compatibility of the quotient
is the extra global assertion still needed for exactness on sections. -/
lemma coordinate_kernel (r n N : ℕ) (h : n ≤ N) (s : Fin r → A k N) :
    (∀ i, truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (s i) = 0) ↔
    ∃ v : Fin r → A k N, ∀ i, s i = base k N (parameter k N ^ (n+1)) * v i := by
  simp only [truncReduce_eq_zero_iff, node_parameter_power]
  exact Classical.skolem

/-- Cancellation of a parameter power is performed before taking the quotient,
where regularity is available. No inverse of the nilpotent parameter is used. -/
lemma trunc_mul_pow_eq_zero_iff {S : Type u} [CommRing S] (t : S)
    (ht : IsRegular t) (a m : ℕ) (z : S) :
    trunc S t (a+m) (t^a * z) = 0 ↔ trunc S t m z = 0 := by
  simp only [trunc, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, (ht.pow a).left ?_⟩
    calc
      t^a * z = t^(a+m+1) * w := hw
      _ = t^a * (t^(m+1) * w) := by rw [← mul_assoc, ← pow_add]; congr 2
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [hw, ← mul_assoc, ← pow_add]
    congr 2

lemma trunc_pow_mul_eq_zero_iff {S : Type u} [CommRing S] (t : S)
    (ht : IsRegular t) (a m : ℕ) (z : Trunc S t (a+m)) :
    trunc S t (a+m) (t^a) * z = 0 ↔
      truncReduce S t m (a+m) (Nat.le_add_left m a) z = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  change trunc S t (a+m) (t^a) * trunc S t (a+m) z = 0 ↔ _
  rw [← map_mul]
  exact trunc_mul_pow_eq_zero_iff t ht a m z

lemma trunc_pow_mul_eq_iff {S : Type u} [CommRing S] (t : S)
    (ht : IsRegular t) (a m : ℕ) (x y : Trunc S t (a+m)) :
    trunc S t (a+m) (t^a) * x = trunc S t (a+m) (t^a) * y ↔
      truncReduce S t m (a+m) (Nat.le_add_left m a) x =
      truncReduce S t m (a+m) (Nat.le_add_left m a) y := by
  rw [← sub_eq_zero, ← mul_sub, trunc_pow_mul_eq_zero_iff t ht, map_sub, sub_eq_zero]

lemma node_parameter_regular : IsRegular (ArithmeticThetaNodeCharts.t k) := by
  let := (ArithmeticThetaNodeCharts.node_flat_domain_parameter k).1
  exact IsRegular.of_ne_zero (ArithmeticThetaNodeCharts.node_flat_domain_parameter k).2.2.1

lemma open_parameter_regular (side : Bool) : IsRegular (openParameter k side) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap
    (Submonoid.powers (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side))
    (RawOpen k side) (isRegular_iff_mem_nonZeroDivisors.mp (node_parameter_regular k))

/-- The cross-multiplied Cech defect, before cancelling any marked equation. -/
def defect (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k n) (i : Fin r) : B k n true :=
  E (restriction k n false (s i)) *
      restriction k n true (equation k r n hr a (next r hr i)) ^ d -
    restriction k n true (s (next r hr i)) *
      E (restriction k n false (equation k r n hr a i)) ^ d

lemma compatible_iff_defect_zero (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s : Fin r → A k n) :
    Compatible k r n hr E a d s ↔ ∀ i, defect k r n hr E a d s i = 0 := by
  simp only [Compatible, defect, sub_eq_zero]

lemma defect_reduction (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N) (s : Fin r → A k N) (i : Fin r) :
    truncReduce (RawOpen k true) (openParameter k true) n N h
      (defect k r N hr (T.overlap N) a d s i) =
    defect k r n hr (T.overlap n) a d (fun j =>
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (s j)) i := by
  have ha (z : B k N false) :
      T.overlap n (truncReduce (RawOpen k false) (openParameter k false) n N h z) =
      truncReduce (RawOpen k true) (openParameter k true) n N h (T.overlap N z) :=
    RingHom.congr_fun (adjacent_reduction k n N h _ _
      (T.overlap_spec n) (T.overlap_spec N)) z
  simp only [defect, map_sub, map_mul, map_pow, ← ha, reduce_restriction, reduce_equation]

lemma defect_base_mul (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d : ℕ) (c : R k n) (s : Fin r → A k n) (i : Fin r) :
    defect k r n hr E a d (fun j => base k n c * s j) i =
      restriction k n true (base k n c) * defect k r n hr E a d s i := by
  simp only [defect, map_mul, mul_assoc]
  rw [show E (restriction k n false (base k n c)) =
      restriction k n true (base k n c) from RingHom.congr_fun (adjacent_base hE) c]
  ring

lemma open_parameter_power (n m : ℕ) (side : Bool) :
    restriction k n side (base k n (parameter k n ^ m)) =
      trunc (RawOpen k side) (openParameter k side) n (openParameter k side ^ m) := by
  rw [map_pow, map_pow, map_pow]
  rfl

/-- A compatible parameter multiple has a compatible quotient at the shorter
stage where cancellation is legitimate. -/
lemma compatible_quotient_reduction (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d q m : ℕ) (s : Fin r → A k (q+m))
    (hs : Compatible k r (q+m) hr (T.overlap (q+m)) a d
      (fun j => base k (q+m) (parameter k (q+m)^q) * s j)) :
    Compatible k r m hr (T.overlap m) a d (fun j =>
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        m (q+m) (Nat.le_add_left m q) (s j)) := by
  rw [compatible_iff_defect_zero] at hs ⊢
  intro i
  rw [← defect_reduction]
  apply (trunc_pow_mul_eq_zero_iff _ (open_parameter_regular k true) q m _).mp
  have hi := hs i
  rw [defect_base_mul k _ _ _ _ (T.overlap_spec _) a d _ s i,
    open_parameter_power] at hi
  exact hi

/-- Once section lifting is proved, the kernel assertion follows by regular
parameter cancellation on the raw node and raw overlap rings. -/
lemma kernel_from_section_lifting (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d : ℕ)
    (hlift : ∀ (m N : ℕ) (h : m ≤ N),
      ∀ s : Sections k r m hr (T.overlap m) a d,
      ∃ v : Sections k r N hr (T.overlap N) a d, ∀ i,
        truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
          m N h (v.val i) = s.val i)
    (n N : ℕ) (h : n ≤ N) (s : Sections k r N hr (T.overlap N) a d) :
    (∀ i, truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (s.val i) = 0) ↔
    ∃ v : Sections k r N hr (T.overlap N) a d, ∀ i,
      s.val i = base k N (parameter k N ^ (n+1)) * v.val i := by
  constructor
  · intro hs
    by_cases heq : n = N
    · subst N
      exact (reduction_self k r hr T a d n h).2.2 s |>.mp hs
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show n+1 ≤ N by omega)
    obtain ⟨w, hw⟩ := (coordinate_kernel k r n (n+1+m) h s.val).mp hs
    have hc : Compatible k r (n+1+m) hr (T.overlap (n+1+m)) a d
        (fun j => base k (n+1+m) (parameter k (n+1+m)^(n+1)) * w j) := by
      have he : (fun j => base k (n+1+m) (parameter k (n+1+m)^(n+1)) * w j) = s.val :=
        funext fun j => (hw j).symm
      rw [he]
      exact s.property
    let v : Sections k r m hr (T.overlap m) a d :=
      ⟨_, compatible_quotient_reduction k r hr T a d (n+1) m w hc⟩
    obtain ⟨vN, hvN⟩ := hlift m (n+1+m) (Nat.le_add_left m (n+1)) v
    refine ⟨vN, fun i => (hw i).trans ?_⟩
    rw [← node_parameter_power]
    apply (trunc_pow_mul_eq_iff _ (node_parameter_regular k) (n+1) m _ _).mpr
    exact (hvN i).symm
  · exact kernel_of_parameter_multiple k r hr T a d n N h s

open ArithmeticThetaPolygonCohomologyR0131
open PolygonCechObstructionR0131 LaurentPolynomial

/-- Marked linear factors stay regular in the actual overlap ring. -/
lemma overlap_marked_regular (n : ℕ) (L : B k n true ≃+* LaurentPolynomial (R k n))
    (hL : LaurentPresentation k n L) (a : kˣ) :
    IsRegular (restriction k n true (markedEquation k n a)) := by
  have hp : IsRegular (Polynomial.X - Polynomial.C (markedUnit k n a : R k n)) :=
    (Polynomial.monic_X_sub_C _).isRegular
  have hq : IsRegular (LaurentPolynomial.T 1 -
      LaurentPolynomial.C (markedUnit k n a : R k n)) := by
    have hh := IsLocalization.nonZeroDivisors_le_comap
      (Submonoid.powers (Polynomial.X : Polynomial (R k n)))
      (LaurentPolynomial (R k n)) (isRegular_iff_mem_nonZeroDivisors.mp hp)
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    simpa only [Submonoid.mem_comap, LaurentPolynomial.algebraMap_eq_toLaurent,
      map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C] using hh
  have he : L (restriction k n true (markedEquation k n a)) =
      LaurentPolynomial.T 1 - LaurentPolynomial.C (markedUnit k n a : R k n) := by
    simp only [markedEquation, map_sub]
    rw [hL.2]
    congr 1
    exact rx_base hL (markedUnit k n a : R k n)
  constructor
  · intro x y hxy
    apply L.injective
    apply hq.left
    simpa only [← he, ← map_mul] using congrArg L hxy
  · intro x y hxy
    apply L.injective
    apply hq.right
    simpa only [← he, ← map_mul] using congrArg L hxy

/-- The two unit factors left after the shared marked factor is cancelled. -/
def rightWeight (r n : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) : B k n true :=
  restriction k n true
    (coordY k n - base k n (↑((markedUnit k n (a (next r hr (next r hr i))))⁻¹)))

def leftWeight (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (a : Fin r → kˣ) (i : Fin r) : B k n true :=
  -(restriction k n true (base k n (↑((markedUnit k n (a (next r hr i)))⁻¹)))) *
    E (restriction k n false (markedEquation k n (a i))) *
    E (restriction k n false (coordY k n))

lemma right_equation_factor (r n : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) :
    restriction k n true (equation k r n hr a (next r hr i)) =
      restriction k n true (markedEquation k n (a (next r hr i))) *
        rightWeight k r n hr a i := by
  simp only [equation, pairEquation, map_mul, rightWeight]

lemma left_equation_factor (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (i : Fin r) :
    E (restriction k n false (equation k r n hr a i)) =
      restriction k n true (markedEquation k n (a (next r hr i))) *
        leftWeight k r n hr E a i := by
  let x := restriction k n true (coordX k n)
  let y := E (restriction k n false (coordY k n))
  let b := restriction k n true (base k n (markedUnit k n (a (next r hr i)) : R k n))
  let v := restriction k n true (base k n (↑((markedUnit k n (a (next r hr i)))⁻¹)))
  have hxy : y*x = 1 := adjacent_y_mul_x hE
  have hb : b*v = 1 := by
    dsimp only [b, v]
    rw [← map_mul, ← map_mul]
    simp
  have he : y - v = (x-b)*(-v)*y := by
    calc
      y-v = (b*v)*y-v*(y*x) := by rw [hb, hxy]; ring
      _ = (x-b)*(-v)*y := by ring
  simp only [equation, pairEquation, map_mul, map_sub, leftWeight, markedEquation]
  rw [show E (restriction k n false (base k n (↑((markedUnit k n (a (next r hr i)))⁻¹)))) = v from
    by
      dsimp [v]
      exact RingHom.congr_fun (adjacent_base hE) (↑((markedUnit k n (a (next r hr i)))⁻¹) : R k n)]
  change (E (restriction k n false (coordX k n)) -
      E (restriction k n false (base k n (markedUnit k n (a i))))) * (y-v) = _
  rw [he]
  ring

/-- This normalized defect takes values in the ordinary overlap ring. -/
def normalizedDefect (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k n) (i : Fin r) : B k n true :=
  E (restriction k n false (s i)) * rightWeight k r n hr a i ^ d -
    restriction k n true (s (next r hr i)) * leftWeight k r n hr E a i ^ d

lemma defect_factor (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k n) (i : Fin r) :
    defect k r n hr E a d s i =
      restriction k n true (markedEquation k n (a (next r hr i))) ^ d *
        normalizedDefect k r n hr E a d s i := by
  rw [defect, right_equation_factor, left_equation_factor k r n hr E hE]
  simp only [mul_pow, normalizedDefect]
  ring

lemma compatible_iff_normalized_zero (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k n) :
    Compatible k r n hr E a d s ↔ ∀ i, normalizedDefect k r n hr E a d s i = 0 := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  rw [compatible_iff_defect_zero]
  apply forall_congr'
  intro i
  rw [defect_factor k r n hr E hE]
  constructor
  · intro h
    apply ((overlap_marked_regular k n L hL _).pow d).left
    simpa only [mul_zero] using h
  · intro h
    rw [h, mul_zero]

lemma reduce_marked_equation (n N : ℕ) (h : n ≤ N) (a : kˣ) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (markedEquation k N a) = markedEquation k n a := by
  rw [← MarkedCartierEquationR0131.trunc_equation,
    ← MarkedCartierEquationR0131.trunc_equation]
  rfl

lemma normalized_reduction (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N) (s : Fin r → A k N) (i : Fin r) :
    truncReduce (RawOpen k true) (openParameter k true) n N h
      (normalizedDefect k r N hr (T.overlap N) a d s i) =
    normalizedDefect k r n hr (T.overlap n) a d (fun j =>
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (s j)) i := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  apply ((overlap_marked_regular k n L hL (a (next r hr i))).pow d).left
  have hh := defect_reduction k r hr T a d n N h s i
  rw [defect_factor k r N hr _ (T.overlap_spec N),
    defect_factor k r n hr _ (T.overlap_spec n), map_mul, map_pow,
    reduce_restriction, reduce_marked_equation] at hh
  exact hh

lemma normalized_zero (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ) (i : Fin r) :
    normalizedDefect k r n hr E a d (fun _ => 0) i = 0 := by
  simp [normalizedDefect]

lemma normalized_add (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s v : Fin r → A k n) (i : Fin r) :
    normalizedDefect k r n hr E a d (fun j => s j + v j) i =
      normalizedDefect k r n hr E a d s i + normalizedDefect k r n hr E a d v i := by
  simp only [normalizedDefect, map_add]
  ring

lemma normalized_sub (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ)
    (s v : Fin r → A k n) (i : Fin r) :
    normalizedDefect k r n hr E a d (fun j => s j - v j) i =
      normalizedDefect k r n hr E a d s i - normalizedDefect k r n hr E a d v i := by
  simp only [normalizedDefect, map_sub]
  ring

lemma normalized_base_mul (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (a : Fin r → kˣ) (d : ℕ) (c : R k n) (s : Fin r → A k n) (i : Fin r) :
    normalizedDefect k r n hr E a d (fun j => base k n c * s j) i =
      restriction k n true (base k n c) * normalizedDefect k r n hr E a d s i := by
  simp only [normalizedDefect, map_mul, mul_assoc]
  rw [show E (restriction k n false (base k n c)) =
      restriction k n true (base k n c) from RingHom.congr_fun (adjacent_base hE) c]
  ring

/-- Onto-ness of the normalized Cech map corrects arbitrary coordinate lifts. -/
lemma section_lifting_of_normalized_surjective (r : ℕ) (hr : 0 < r)
    (T : Tower k r hr) (a : Fin r → kˣ) (d n N : ℕ) (h : n ≤ N)
    (honto : Function.Surjective (normalizedDefect k r N hr (T.overlap N) a d))
    (s : Sections k r n hr (T.overlap n) a d) :
    ∃ v : Sections k r N hr (T.overlap N) a d, ∀ i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (v.val i) = s.val i := by
  choose v hv using (fun i => truncReduce_surjective
    (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h (s.val i))
  have hdef (i : Fin r) :
      truncReduce (RawOpen k true) (openParameter k true) n N h
        (normalizedDefect k r N hr (T.overlap N) a d v i) = 0 := by
    rw [normalized_reduction k r hr T a d n N h v i]
    have he : (fun j => truncReduce (ArithmeticThetaNodeCharts.Node k)
        (ArithmeticThetaNodeCharts.t k) n N h (v j)) = s.val := funext hv
    rw [he]
    exact (compatible_iff_normalized_zero k r n hr _ (T.overlap_spec n) a d s.val).mp s.property i
  choose b hb using fun i =>
    (truncReduce_eq_zero_iff (openParameter k true) n N h _).mp (hdef i)
  obtain ⟨w, hw⟩ := honto b
  let v' : Fin r → A k N := fun i => v i - base k N (parameter k N ^ (n+1)) * w i
  have hc : Compatible k r N hr (T.overlap N) a d v' := by
    rw [compatible_iff_normalized_zero k r N hr _ (T.overlap_spec N)]
    intro i
    dsimp only [v']
    rw [normalized_sub, normalized_base_mul k r N hr _ (T.overlap_spec N),
      open_parameter_power, hb i, congrFun hw i, sub_self]
  refine ⟨⟨v', hc⟩, ?_⟩
  intro i
  change truncReduce _ _ n N h (v i - base k N (parameter k N ^ (n+1)) * w i) = _
  rw [map_sub, parameter_multiple_reduces_zero, hv i, sub_zero]

/-- A purely additive nilpotent lifting argument; no finiteness hypothesis is
needed because the parameter has a fixed nilpotence exponent. -/
lemma surjective_of_nilpotent_approximation {M V : Type*} [AddCommGroup M] [AddCommGroup V]
    (D : M →+ V) (tM : M →+ M) (tV : V →+ V)
    (hcomm : ∀ x, D (tM x) = tV (D x))
    (happrox : ∀ b, ∃ x c, b = D x + tV c)
    (q : ℕ) (hq : ∀ b, (tV^[q]) b = 0) : Function.Surjective D := by
  have hiter : ∀ j x, D ((tM^[j]) x) = (tV^[j]) (D x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      simp only [Function.iterate_succ_apply', hcomm, ih]
  have haux : ∀ j b, ∃ x c, b = D x + (tV^[j]) c := by
    intro j
    induction j with
    | zero => intro b; exact ⟨0, b, by simp⟩
    | succ j ih =>
      intro b
      obtain ⟨x, c, hc⟩ := ih b
      obtain ⟨y, e, he⟩ := happrox c
      refine ⟨x + (tM^[j]) y, e, ?_⟩
      rw [map_add, hiter, hc, he]
      have hadd : ∀ j (v w : V), (tV^[j]) (v+w) = (tV^[j]) v + (tV^[j]) w := by
        intro j
        induction j with
        | zero => intros; rfl
        | succ j hj => intros; simp only [Function.iterate_succ_apply', map_add, hj]
      rw [hadd, ← add_assoc, Function.iterate_succ_apply]
  intro b
  obtain ⟨x, c, hc⟩ := haux q b
  exact ⟨x, by simpa only [hq c, add_zero] using hc.symm⟩

/-- The actual normalized defect as an additive homomorphism. -/
def normalizedMap (r n : ℕ) (hr : 0 < r)
    (E : B k n false ≃+* B k n true) (a : Fin r → kˣ) (d : ℕ) :
    (Fin r → A k n) →+ (Fin r → B k n true) where
  toFun := normalizedDefect k r n hr E a d
  map_zero' := funext fun i => normalized_zero k r n hr E a d i
  map_add' s v := funext fun i => normalized_add k r n hr E a d s v i

/-- Surjectivity at thickness zero implies surjectivity at every nilpotent stage. -/
lemma normalized_surjective_of_zero (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d N : ℕ)
    (hzero : Function.Surjective (normalizedDefect k r 0 hr (T.overlap 0) a d)) :
    Function.Surjective (normalizedDefect k r N hr (T.overlap N) a d) := by
  let tA : A k N := base k N (parameter k N)
  let tB : B k N true := restriction k N true tA
  let tM : (Fin r → A k N) →+ (Fin r → A k N) :=
    { toFun := fun v i => tA * v i
      map_zero' := by ext; exact mul_zero _
      map_add' := by intros; ext; exact mul_add _ _ _ }
  let tV : (Fin r → B k N true) →+ (Fin r → B k N true) :=
    { toFun := fun v i => tB * v i
      map_zero' := by ext; exact mul_zero _
      map_add' := by intros; ext; exact mul_add _ _ _ }
  refine surjective_of_nilpotent_approximation (normalizedMap k r N hr (T.overlap N) a d)
    tM tV ?_ ?_ (N+1) ?_
  · intro v
    exact funext fun i => normalized_base_mul k r N hr _ (T.overlap_spec N) a d _ v i
  · intro b
    obtain ⟨s, hs⟩ := hzero (fun i =>
      truncReduce (RawOpen k true) (openParameter k true) 0 N (Nat.zero_le N) (b i))
    choose v hv using (fun i => truncReduce_surjective
      (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      0 N (Nat.zero_le N) (s i))
    have hred (i : Fin r) :
        truncReduce (RawOpen k true) (openParameter k true) 0 N (Nat.zero_le N)
          (b i - normalizedDefect k r N hr (T.overlap N) a d v i) = 0 := by
      rw [map_sub, normalized_reduction k r hr T a d 0 N (Nat.zero_le N)]
      have he : (fun i => truncReduce (ArithmeticThetaNodeCharts.Node k)
          (ArithmeticThetaNodeCharts.t k) 0 N (Nat.zero_le N) (v i)) = s := funext hv
      rw [he, congrFun hs i, sub_self]
    choose c hc using fun i =>
      (truncReduce_eq_zero_iff (openParameter k true) 0 N (Nat.zero_le N) _).mp (hred i)
    refine ⟨v, c, funext fun i => ?_⟩
    have hci := hc i
    rw [pow_one] at hci
    have ht : ArithmeticThetaInfinitesimalPolygonR0129.trunc (RawOpen k true)
        (openParameter k true) N (openParameter k true) = tB := rfl
    rw [ht] at hci
    exact sub_eq_iff_eq_add.mp hci |>.trans (add_comm _ _)
  · intro b
    have hi : ∀ q i, (tV^[q]) b i = tB^q * b i := by
      intro q
      induction q with
      | zero => intro i; simp
      | succ q ih =>
        intro i
        rw [Function.iterate_succ_apply']
        change tB * (tV^[q]) b i = _
        simp only [ih, pow_succ]
        ring
    ext i
    rw [hi]
    have hz : tB^(N+1) = 0 := by
      change (restriction k N true (base k N (parameter k N)))^(N+1) = 0
      rw [← map_pow, ← map_pow, parameter_pow, map_zero, map_zero]
    change tB^(N+1) * b i = 0
    rw [hz, zero_mul]

def rightConstant (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) : (R k 0)ˣ :=
  -(markedUnit k 0 (a (next r hr (next r hr i))))⁻¹

def leftConstant (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (i : Fin r) : (R k 0)ˣ :=
  markedUnit k 0 (a i) * (markedUnit k 0 (a (next r hr i)))⁻¹

lemma parameter_zero : parameter k 0 = 0 := by simpa using parameter_pow k 0

lemma rightWeight_zero (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (i : Fin r) :
    L (rightWeight k r 0 hr a i) = C (rightConstant k r hr a i : R k 0) := by
  change rx L (coordY k 0 - base k 0 _) = _
  rw [map_sub, rx_y hL, rx_base hL, parameter_zero, map_zero, zero_mul, zero_sub]
  simp only [rightConstant, Units.val_neg, map_neg]

lemma leftWeight_zero (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (i : Fin r) :
    L (leftWeight k r 0 hr E a i) =
      C (leftConstant k r hr a i : R k 0) * LaurentPolynomial.T (-1) := by
  simp only [leftWeight, map_mul, map_neg, markedEquation, map_sub]
  change -(rx L (base k 0 _)) *
    (ry E L (coordX k 0) - ry E L (base k 0 _)) * ry E L (coordY k 0) = _
  rw [rx_base hL, ry_x hE hL, ry_base hE hL, ry_y hE hL,
    parameter_zero, map_zero, zero_mul, zero_sub, neg_mul_neg, ← map_mul]
  congr 2
  exact mul_comm _ _

/-- The special-fiber operator, allowing arbitrary unit weights. -/
def specialMap (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0))
    (u v : Fin r → (R k 0)ˣ) (d : ℕ) :
    (Fin r → A k 0) →+ (Fin r → LaurentPolynomial (R k 0)) where
  toFun s i := ry E L (s i) * C ((u i : R k 0)^d) -
    rx L (s (next r hr i)) *
      (C ((v i : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ)))
  map_zero' := by ext i; simp
  map_add' s w := by ext i; simp only [Pi.add_apply, map_add, add_mul]; ring

lemma normalized_special (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (s : Fin r → A k 0) (i : Fin r) :
    L (normalizedDefect k r 0 hr E a d s i) =
      specialMap k r hr E L (rightConstant k r hr a) (leftConstant k r hr a) d s i := by
  simp only [normalizedDefect, map_sub, map_mul, map_pow,
    rightWeight_zero k r hr a L hL, leftWeight_zero k r hr a E hE L hL,
    mul_pow, LaurentPolynomial.T_pow, mul_neg, mul_one]
  simp only [specialMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ry, rx,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_pow]

lemma special_y (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (u v : Fin r → (R k 0)ˣ) (d p : ℕ) (hp : 0 < p) (i : Fin r) (c : R k 0) :
    specialMap k r hr E L u v d
      (Pi.single i (base k 0 c * coordY k 0 ^ p)) =
      Pi.single i (C (c * (u i : R k 0)^d) * LaurentPolynomial.T (-(p : ℤ))) := by
  classical
  have hx : rx L (base k 0 c * coordY k 0 ^ p) = 0 := by
    rw [(images_y hE hL c p).1, parameter_zero, zero_pow hp.ne', zero_mul,
      map_zero, zero_mul]
  have hy := (images_y hE hL c p).2
  funext j
  simp only [specialMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hright : rx L ((Pi.single i (base k 0 c * coordY k 0 ^ p) : Fin r → A k 0) (next r hr j)) = 0 := by
    by_cases h : next r hr j = i <;> simp [h, hx]
  rw [hright, zero_mul, sub_zero]
  by_cases hj : j = i
  · subst j
    simp only [Pi.single_eq_same, hy]
    rw [map_mul]
    ring
  · simp [hj]

lemma special_x (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (u v : Fin r → (R k 0)ˣ) (d p : ℕ) (hp : 0 < p) (i : Fin r) (c : R k 0) :
    specialMap k r hr E L u v d
      (Pi.single (next r hr i) (base k 0 c * coordX k 0 ^ p)) =
      Pi.single i (C (-(c * (v i : R k 0)^d)) *
        LaurentPolynomial.T ((p : ℤ) - (d : ℤ))) := by
  classical
  have hx := (images_x hE hL c p).1
  have hy : ry E L (base k 0 c * coordX k 0 ^ p) = 0 := by
    rw [(images_x hE hL c p).2, parameter_zero, zero_pow hp.ne', zero_mul,
      map_zero, zero_mul]
  funext j
  simp only [specialMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hleft : ry E L ((Pi.single (next r hr i) (base k 0 c * coordX k 0 ^ p) : Fin r → A k 0) j) = 0 := by
    by_cases h : j = next r hr i <;> simp [h, hy]
  rw [hleft, zero_mul, zero_sub]
  by_cases hj : j = i
  · subst j
    simp only [Pi.single_eq_same, hx]
    rw [map_neg, map_mul]
    rw [show C c * LaurentPolynomial.T (p : ℤ) *
        (C ((v i : R k 0)^d) * LaurentPolynomial.T (-(d : ℤ))) =
        (C c * C ((v i : R k 0)^d)) *
          (LaurentPolynomial.T (p : ℤ) * LaurentPolynomial.T (-(d : ℤ))) by ring]
    rw [← LaurentPolynomial.T_add, ← neg_mul, sub_eq_add_neg]
  · have hn : next r hr j ≠ next r hr i := by
      intro hh
      exact hj ((shift r hr).injective hh)
    simp [hj, hn]

lemma special_surjective (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (L : B k 0 true ≃+* LaurentPolynomial (R k 0)) (hL : LaurentPresentation k 0 L)
    (u v : Fin r → (R k 0)ˣ) (d : ℕ) (hd : 0 < d) :
    Function.Surjective (specialMap k r hr E L u v d) := by
  classical
  let F := specialMap k r hr E L u v d
  have hmono (i : Fin r) (j : ℤ) (c : R k 0) :
      Pi.single i (C c * LaurentPolynomial.T j) ∈ F.range := by
    by_cases hj : j < 0
    · let p := (-j).toNat
      have hp : 0 < p := by dsimp [p]; omega
      have hjp : -(p : ℤ) = j := by dsimp [p]; omega
      refine ⟨Pi.single i (base k 0 (c * (↑((u i)^d)⁻¹ : R k 0)) * coordY k 0 ^ p), ?_⟩
      rw [special_y k r hr E hE L hL u v d p hp i, hjp]
      have hc : (c * (↑((u i)^d)⁻¹ : R k 0)) * (u i : R k 0)^d = c := by
        simp only [← Units.val_pow_eq_pow_val, mul_assoc, Units.inv_mul, mul_one]
      rw [hc]
    · let p := j.toNat + d
      have hp : 0 < p := by dsimp [p]; omega
      have hjp : (p : ℤ) - (d : ℤ) = j := by dsimp [p]; omega
      refine ⟨Pi.single (next r hr i)
        (base k 0 (-c * (↑((v i)^d)⁻¹ : R k 0)) * coordX k 0 ^ p), ?_⟩
      rw [special_x k r hr E hE L hL u v d p hp i, hjp]
      have hc : (-c * (↑((v i)^d)⁻¹ : R k 0)) * (v i : R k 0)^d = -c := by
        simp only [← Units.val_pow_eq_pow_val, mul_assoc, Units.inv_mul, mul_one]
      rw [hc, neg_neg]
  have hsingle (i : Fin r) (b : LaurentPolynomial (R k 0)) : Pi.single i b ∈ F.range := by
    induction b using LaurentPolynomial.induction_on' with
    | add b c hb hc => rw [Pi.single_add]; exact F.range.add_mem hb hc
    | C_mul_T j c => exact hmono i j c
  intro b
  have hb : b ∈ F.range := by
    rw [← Finset.univ_sum_single b]
    exact F.range.sum_mem (fun i _ => hsingle i (b i))
  exact hb

lemma normalized_surjective_zero (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (a : Fin r → kˣ) (d : ℕ) (hd : 0 < d) :
    Function.Surjective (normalizedDefect k r 0 hr E a d) := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k 0
  intro b
  obtain ⟨s, hs⟩ := special_surjective k r hr E hE L hL
    (rightConstant k r hr a) (leftConstant k r hr a) d hd (fun i => L (b i))
  refine ⟨s, funext fun i => L.injective ?_⟩
  rw [normalized_special k r hr a d E hE L hL]
  exact congrFun hs i

end PositiveSectionsReductionR0134

open ArithmeticThetaInfinitesimalPolygonR0129 PositiveSectionsReductionR0134

/-- Exact coefficient reduction of positive divisor sections at every thickness. -/
theorem positive_sections_reduction :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ),
    ∀ d : ℕ, 0 < d → ∀ (n N : ℕ) (h : n ≤ N),
      ArithmeticThetaPositiveLineR0134.ReductionFacts k r hr T a d n N h := by
  intro k _ _ r hr _ T a d hd n N h
  have hlift : ∀ (m P : ℕ) (hm : m ≤ P),
      ∀ s : Sections k r m hr (T.overlap m) a d,
      ∃ v : Sections k r P hr (T.overlap P) a d, ∀ i,
        truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
          m P hm (v.val i) = s.val i := by
    intro m P hm s
    exact section_lifting_of_normalized_surjective k r hr T a d m P hm
      (normalized_surjective_of_zero k r hr T a d P
        (normalized_surjective_zero k r hr _ (T.overlap_spec 0) a d hd)) s
  exact ⟨compatible_reduction k r hr T a d n N h, hlift n N h,
    kernel_from_section_lifting k r hr T a d hlift n N h⟩

end ArithmeticThetaPositiveLineR0134
