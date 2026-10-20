module

public import PolygonCartierDefinitionsR0133
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! The two adjacent markings on a truncated node. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace LocalMarkedPairR0133
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

def swap : A k n →+* A k n :=
  mkPoint (base k n) (coordY k n) (coordX k n)
    (by rw [mul_comm, coordX_mul_coordY])

@[simp] lemma swap_base (c : R k n) : swap k n (base k n c) = base k n c :=
  RingHom.congr_fun (show (swap k n).comp (base k n) = base k n from
    mkPoint_base _ _ _ _) c
@[simp] lemma swap_x : swap k n (coordX k n) = coordY k n := mkPoint_x _ _ _ _
@[simp] lemma swap_y : swap k n (coordY k n) = coordX k n := mkPoint_y _ _ _ _

lemma swap_involutive : Function.Involutive (swap k n) := by
  have h : (swap k n).comp (swap k n) = RingHom.id _ := by
    apply point_ext
    · ext c
      simp
    · simp
    · simp
  exact fun z => RingHom.congr_fun h z

@[simp] lemma swap_swap (z : A k n) : swap k n (swap k n z) = z :=
  swap_involutive k n z

@[simp] lemma marked_base (a : kˣ) (c : R k n) :
    markedPoint k n a (base k n c) = c :=
  RingHom.congr_fun (show (markedPoint k n a).comp (base k n) = RingHom.id _ from
    mkPoint_base _ _ _ _) c
@[simp] lemma left_base (b : kˣ) (c : R k n) :
    leftMarkedPoint k n b (base k n c) = c :=
  RingHom.congr_fun (show (leftMarkedPoint k n b).comp (base k n) = RingHom.id _ from
    mkPoint_base _ _ _ _) c

lemma left_swap (b : kˣ) :
    leftMarkedPoint k n b = (markedPoint k n b⁻¹).comp (swap k n) := by
  apply point_ext
  · ext c
    simp
  · simp [leftMarkedPoint, markedPoint, markedUnit]
  · simp [leftMarkedPoint, markedPoint, markedUnit]

lemma swap_equation (b : kˣ) :
    swap k n (markedEquation k n b⁻¹) =
      coordY k n - base k n (↑((markedUnit k n b)⁻¹)) := by
  simp [markedEquation, markedUnit]

lemma left_regular (b : kˣ) :
    IsRegular (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) := by
  have hi := (swap_involutive k n).injective
  have hr := (marked_cartier_equation k n b⁻¹).1
  rw [← swap_equation]
  have hl : IsLeftRegular (swap k n (markedEquation k n b⁻¹)) := by
    intro z w h
    apply hi
    apply hr.1
    have hh := congrArg (swap k n) h
    simpa only [map_mul, swap_swap] using hh
  exact ⟨hl, fun z w h => hl (by simpa only [mul_comm] using h)⟩

lemma left_kernel (b : kˣ) : RingHom.ker (leftMarkedPoint k n b) =
    Ideal.span ({coordY k n - base k n (↑((markedUnit k n b)⁻¹))} : Set (A k n)) := by
  apply le_antisymm
  · intro z hz
    have hz' : swap k n z ∈ RingHom.ker (markedPoint k n b⁻¹) := by
      change markedPoint k n b⁻¹ (swap k n z) = 0
      exact (RingHom.congr_fun (left_swap k n b) z).symm.trans hz
    rw [(marked_cartier_equation k n b⁻¹).2, Ideal.mem_span_singleton] at hz'
    obtain ⟨w, hw⟩ := hz'
    apply Ideal.mem_span_singleton.mpr
    refine ⟨swap k n w, ?_⟩
    have hh := congrArg (swap k n) hw
    simpa only [map_mul, swap_swap, swap_equation] using hh
  · rw [Ideal.span_singleton_le_iff_mem]
    change leftMarkedPoint k n b (_ - _) = 0
    rw [map_sub, left_base]
    simp [leftMarkedPoint]

lemma cross_unit (a b : kˣ) : IsUnit (leftMarkedPoint k n b (markedEquation k n a)) := by
  have hn : IsNilpotent (parameter k n * (markedUnit k n b : R k n)) := by
    refine ⟨n+1, ?_⟩
    rw [mul_pow, parameter_pow, zero_mul]
  have h := hn.isUnit_add_right_of_commute (markedUnit k n a).isUnit.neg (Commute.all _ _)
  rw [markedEquation, map_sub, left_base]
  simpa only [leftMarkedPoint, mkPoint_x, sub_eq_add_neg] using h

@[simp] lemma marked_equation_zero (a : kˣ) :
    markedPoint k n a (markedEquation k n a) = 0 := by
  rw [markedEquation, map_sub, marked_base]
  simp [markedPoint]

@[simp] lemma left_equation_zero (b : kˣ) :
    leftMarkedPoint k n b (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) = 0 := by
  rw [map_sub, left_base]
  simp [leftMarkedPoint]

lemma pair_kernel (a b : kˣ) : RingHom.ker (pairEvaluation k n a b) =
    Ideal.span ({pairEquation k n a b} : Set (A k n)) := by
  apply le_antisymm
  · intro z hz
    have hp : markedPoint k n a z = 0 := congrArg Prod.fst hz
    have hq : leftMarkedPoint k n b z = 0 := congrArg Prod.snd hz
    have hzp : z ∈ Ideal.span ({markedEquation k n a} : Set (A k n)) := by
      rw [← (marked_cartier_equation k n a).2]
      exact hp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hzp
    have hwq : leftMarkedPoint k n b w = 0 := by
      apply (cross_unit k n a b).mul_right_eq_zero.mp
      rw [← map_mul, ← hw]
      exact hq
    have hwj : w ∈ Ideal.span
        ({coordY k n - base k n (↑((markedUnit k n b)⁻¹))} : Set (A k n)) := by
      rw [← left_kernel]
      exact hwq
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hwj
    apply Ideal.mem_span_singleton.mpr
    exact ⟨v, by rw [hw, hv, pairEquation, mul_assoc]⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    change pairEvaluation k n a b (pairEquation k n a b) = 0
    apply Prod.ext
    · change markedPoint k n a (pairEquation k n a b) = 0
      simp only [pairEquation, map_mul, marked_equation_zero, zero_mul]
    · change leftMarkedPoint k n b (pairEquation k n a b) = 0
      simp only [pairEquation, map_mul, left_equation_zero, mul_zero]

lemma pair_surjective (a b : kˣ) : Function.Surjective (pairEvaluation k n a b) := by
  obtain ⟨v, hv⟩ := cross_unit k n a b
  rintro ⟨c, d⟩
  refine ⟨base k n c + markedEquation k n a * base k n (↑v⁻¹ * (d - c)), ?_⟩
  apply Prod.ext
  · change markedPoint k n a (_ + _) = c
    simp only [map_add, map_mul, marked_base, marked_equation_zero, zero_mul, add_zero]
  · change leftMarkedPoint k n b (_ + _) = d
    simp only [map_add, map_mul, left_base, ← hv]
    simp [← mul_assoc]

end LocalMarkedPairR0133

/-- The product equation is regular, and the prescribed evaluations induce
an isomorphism to two copies of the truncated base, including at thickness zero. -/
theorem local_marked_pair :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (n : ℕ) (a b : kˣ),
      IsRegular (ArithmeticThetaPolygonCartierR0133.pairEquation k n a b) ∧
      ∃ e : (ArithmeticThetaInfinitesimalPolygonR0129.A k n ⧸
        Ideal.span ({ArithmeticThetaPolygonCartierR0133.pairEquation k n a b} :
          Set (ArithmeticThetaInfinitesimalPolygonR0129.A k n))) ≃+*
          (ArithmeticThetaInfinitesimalPolygonR0129.R k n ×
            ArithmeticThetaInfinitesimalPolygonR0129.R k n),
        e.toRingHom.comp (Ideal.Quotient.mk
          (Ideal.span ({ArithmeticThetaPolygonCartierR0133.pairEquation k n a b} :
            Set (ArithmeticThetaInfinitesimalPolygonR0129.A k n)))) =
          ArithmeticThetaPolygonCartierR0133.pairEvaluation k n a b := by
  intro k _ _ n a b
  refine ⟨(ArithmeticThetaPolygonCohomologyR0131.marked_cartier_equation k n a).1.mul
    (LocalMarkedPairR0133.left_regular k n b), ?_⟩
  let e := (Ideal.quotEquivOfEq (LocalMarkedPairR0133.pair_kernel k n a b).symm).trans
    (RingHom.quotientKerEquivOfSurjective (LocalMarkedPairR0133.pair_surjective k n a b))
  refine ⟨e, ?_⟩
  apply RingHom.ext
  intro z
  change e (Ideal.Quotient.mk _ z) = pairEvaluation k n a b z
  simp [e]

end ArithmeticThetaPolygonCartierR0133
