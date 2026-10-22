module

public import ProjectiveEffectivityDefinitionsR0135
public import PositiveSectionMultiplicationR0134
public import CompatibleFormalSectionBasisR0134

@[expose] public section

/-! Homogeneous presentation by one polynomial over the complete base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace ArithmeticThetaProjectiveEffectivityR0135
namespace FormalHomogeneousPresentationR0135
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open PositiveSectionsReductionR0134
open CompatibleFormalSectionBasisR0134
open MvPolynomial
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

/-- A presentation polynomial together with its actual section property at all stages. -/
def Good (d : ℕ) (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) : Prop :=
  p.IsHomogeneous d ∧ ∀ n,
    Compatible k r n hr (T.overlap n) a (3*d) (fun i => evaluate k b n i p)

lemma eval_C (n : ℕ) (i : Fin r) (c : PowerSeries k) :
    evaluate k b n i (C c) = base k n (trunc (PowerSeries k) PowerSeries.X n c) := by
  simp [evaluate]

lemma eval_X (n : ℕ) (i : Fin r) (j : Fin (3*r)) :
    evaluate k b n i (X j) = (b n j).val i := by
  simp [evaluate]

lemma good_zero (d : ℕ) : Good k b d 0 := by
  refine ⟨isHomogeneous_zero _ _ d, fun n => ?_⟩
  simpa only [map_zero] using compatible_zero k r n hr (T.overlap n) a (3*d)

lemma good_add {d : ℕ} {p q : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : Good k b d p) (hq : Good k b d q) : Good k b d (p+q) := by
  refine ⟨hp.1.add hq.1, fun n => ?_⟩
  simpa only [map_add] using compatible_add k r n hr (T.overlap n) a (3*d)
    _ _ (hp.2 n) (hq.2 n)

lemma good_sum {J : Type*} (s : Finset J) (p : J → MvPolynomial (Fin (3*r)) (PowerSeries k))
    (d : ℕ) (hp : ∀ j ∈ s, Good k b d (p j)) : Good k b d (∑ j ∈ s, p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero k b d
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact good_add k b (hp j (Finset.mem_insert_self _ _))
      (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)))

lemma good_C_mul {d : ℕ} {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : Good k b d p) (c : PowerSeries k) : Good k b d (C c * p) := by
  refine ⟨hp.1.C_mul c, fun n => ?_⟩
  simpa only [map_mul, eval_C] using compatible_base_mul k r n hr (T.overlap n)
    (T.overlap_spec n) a (3*d) (trunc (PowerSeries k) PowerSeries.X n c) _ (hp.2 n)

lemma good_X (j : Fin (3*r)) : Good k b 1 (X j) := by
  refine ⟨isHomogeneous_X _ j, fun n => ?_⟩
  simpa only [eval_X, mul_one] using (b n j).property

lemma good_mul {d e : ℕ} {p q : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hp : Good k b d p) (hq : Good k b e q) : Good k b (d+e) (p*q) := by
  refine ⟨hp.1.mul hq.1, fun n => ?_⟩
  simpa only [map_mul, Nat.mul_add, Pi.mul_def] using
    PositiveSectionMultiplicationR0134.compatible_mul k r n hr (T.overlap n) a
      (3*d) (3*e) _ _ (hp.2 n) (hq.2 n)

/-- Finite presentation, with every chosen polynomial defining sections at all thicknesses. -/
lemma finite_presentation (h3 : 3 ≤ r) (hb : ∀ n, IsBasis k r n hr (T.overlap n) a 3 (b n)) :
    ∀ d : ℕ, 0 < d → ∀ n (s : Sections k r n hr (T.overlap n) a (3*d)),
      ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), Good k b d p ∧
        ∀ i, evaluate k b n i p = s.val i := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    intro n s
    by_cases h : d=0
    · subst d
      obtain ⟨c, hc, _⟩ := hb n s
      choose v hv using fun j => Ideal.Quotient.mk_surjective (c j)
      refine ⟨∑ j, C (v j) * X j, good_sum k b _ _ 1 (fun j _ =>
        good_C_mul k b (good_X k b j) (v j)), fun i => ?_⟩
      simp only [map_sum, map_mul, eval_C, eval_X]
      exact (Finset.sum_congr rfl (fun j _ => by rw [show
        trunc (PowerSeries k) PowerSeries.X n (v j) = c j from hv j])).trans (hc i).symm
    · have hd' : 0 < d := Nat.pos_of_ne_zero h
      have heq : 3*(d+1) = 3 + 3*d := by omega
      let s' : Sections k r n hr (T.overlap n) a (3+3*d) :=
        ⟨s.val, by simpa only [heq] using s.property⟩
      obtain ⟨l, v, w, hw⟩ := positive_section_multiplication k r n hr h3
        (T.overlap n) (T.overlap_spec n) a 3 (3*d) (by omega) (by omega) s'
      obtain ⟨p, hp⟩ : ∃ p : Fin l → MvPolynomial (Fin (3*r)) (PowerSeries k),
          ∀ j, Good k b 1 (p j) ∧ ∀ i, evaluate k b n i (p j) = (v j).val i := by
        choose p hp using fun j => ih 1 (by omega) (by omega) n (v j)
        exact ⟨p, hp⟩
      choose q hq using fun j => ih d (by omega) hd' n (w j)
      refine ⟨∑ j, p j * q j, ?_, fun i => ?_⟩
      · simpa only [Nat.add_comm 1 d] using
          good_sum k b Finset.univ (fun j => p j * q j) (1+d)
            (fun j _ => good_mul k b (hp j).1 (hq j).1)
      · simp only [map_sum, map_mul, (hp _).2, (hq _).2]
        exact (hw i).symm

/-- Evaluation commutes with every prescribed quotient map. -/
lemma eval_reduce (hb : CompatibleBases k T a b) (n N : ℕ) (h : n ≤ N)
    (i : Fin r) (p : MvPolynomial (Fin (3*r)) (PowerSeries k)) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (evaluate k b N i p) = evaluate k b n i p := by
  have he : (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h).comp (evaluate k b N i) = evaluate k b n i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval_C, reduce_base]
      rfl
    · intro j
      simp only [RingHom.comp_apply, eval_X]
      exact hb.2 n N h j i
  exact RingHom.congr_fun he p

/-- Homogeneous lifts of a special-fiber basis form bases at every thickness. -/
lemma polynomial_bases (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (d : ℕ) (hd : 0 < d) :
    ∃ p : Fin ((3*d)*r) → MvPolynomial (Fin (3*r)) (PowerSeries k),
      ∃ hp : ∀ j, Good k b d (p j),
      ∀ n, IsBasis k r n hr (T.overlap n) a (3*d)
        (fun j => ⟨fun i => evaluate k b n i (p j), (hp j).2 n⟩) := by
  classical
  obtain ⟨v, hv⟩ := positive_section_basis k r 0 hr h3
    (T.overlap 0) (T.overlap_spec 0) a (3*d) (by omega)
  choose p hp he using fun j => finite_presentation k b h3 hb.1 d hd 0 (v j)
  refine ⟨p, hp, ?_⟩
  intro n
  induction n with
  | zero =>
    have heq : (fun j => (⟨fun i => evaluate k b 0 i (p j), (hp j).2 0⟩ :
        Sections k r 0 hr (T.overlap 0) a (3*d))) = v := by
      funext j
      exact Subtype.ext (funext (he j))
    rwa [heq]
  | succ n ih =>
    apply lifted_basis k r hr T a (3*d) h3 (by omega) n _ ih
    intro j
    apply Subtype.ext
    funext i
    exact eval_reduce k b hb n (n+1) (Nat.le_succ n) i (p j)

lemma formal_presentation (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (d : ℕ) (hd : 0 < d) (s : FormalSection k r hr T a (3*d)) :
    ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), p.IsHomogeneous d ∧
      ∀ n i, evaluate k b n i p = (s.val n).val i := by
  classical
  obtain ⟨p, hp, hbas⟩ := polynomial_bases k b h3 hb d hd
  let v : ∀ n, Fin ((3*d)*r) → Sections k r n hr (T.overlap n) a (3*d) :=
    fun n j => ⟨fun i => evaluate k b n i (p j), (hp j).2 n⟩
  have hred : ∀ n N (h : n ≤ N) j i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((v N j).val i) = (v n j).val i :=
    fun n N h j i => eval_reduce k b hb n N h i (p j)
  obtain ⟨c, hc, _⟩ := formal_coordinates k r hr T a (3*d) v hbas hred s.val s.property
  refine ⟨∑ j, C (c j) * p j,
    (good_sum k b Finset.univ _ d (fun j _ => good_C_mul k b (hp j) (c j))).1, ?_⟩
  intro n i
  simp only [map_sum, map_mul, eval_C]
  exact (hc n i).symm

end FormalHomogeneousPresentationR0135

/-- One homogeneous polynomial presents an entire compatible section system;
the same assertion holds separately at every finite stage. -/
theorem formal_homogeneous_presentation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ)
      (b : ArithmeticThetaProjectiveEffectivityR0135.CubicBases k r hr T a),
    ArithmeticThetaProjectiveEffectivityR0135.CompatibleBases k T a b →
      ArithmeticThetaProjectiveEffectivityR0135.HomogeneousPresentation k b := by
  intro k _ _ r hr h3 T a b hb
  constructor
  · exact FormalHomogeneousPresentationR0135.formal_presentation k b h3 hb
  · intro d hd n s
    obtain ⟨p, hp, he⟩ := FormalHomogeneousPresentationR0135.finite_presentation k b h3 hb.1 d hd n s
    exact ⟨p, hp.1, he⟩

end ArithmeticThetaProjectiveEffectivityR0135
