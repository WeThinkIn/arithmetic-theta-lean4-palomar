import GlobalPositiveSectionRealizationR0134
import PositiveSectionsReductionR0134

/-! Explicit generation on the special fiber and lifting through nilpotent thickenings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace PositiveGlobalGenerationR0134
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCohomologyR0131 PolygonCechObstructionR0131
open PositiveSectionsReductionR0134 LaurentPolynomial
variable (k : Type u) [Field k] [CharZero k]

lemma next_ne (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (i : Fin r) : next r hr i ≠ i := by
  intro h
  have hv : (i.val+1)%r = i.val := congrArg Fin.val h
  by_cases hi : i.val+1 < r
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hir : i.val+1 = r := by omega
    rw [hir, Nat.mod_self] at hv
    omega

/-- A section supported on the two charts incident to a component. -/
def bridge (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ) (i : Fin r) :
    Fin r → A k 0 :=
  Pi.single i (base k 0 ((leftConstant k r hr a i : R k 0)^d) * coordY k 0 ^ (d-1)) +
  Pi.single (next r hr i)
    (base k 0 ((rightConstant k r hr a i : R k 0)^d) * coordX k 0)

lemma bridge_compatible (r : ℕ) (hr : 0 < r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (a : Fin r → kˣ) (d : ℕ) (hd : 2 ≤ d) (i : Fin r) :
    Compatible k r 0 hr E a d (bridge k r hr a d i) := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k 0
  rw [compatible_iff_normalized_zero k r 0 hr E hE]
  intro j
  apply L.injective
  rw [normalized_special k r hr a d E hE L hL, map_zero]
  have hs : specialMap k r hr E L (rightConstant k r hr a) (leftConstant k r hr a)
      d (bridge k r hr a d i) = 0 := by
    unfold bridge
    rw [map_add, special_y k r hr E hE L hL _ _ d (d-1) (by omega)]
    have hx := special_x k r hr E hE L hL (rightConstant k r hr a)
      (leftConstant k r hr a) d 1 (by omega) i ((rightConstant k r hr a i : R k 0)^d)
    simp only [pow_one] at hx
    rw [hx]
    have he : -((d-1 : ℕ) : ℤ) = (1 : ℤ) - (d : ℤ) := by omega
    rw [he]
    funext z
    simp only [Pi.add_apply, Pi.zero_apply]
    by_cases hz : z = i
    · subst z
      simp only [Pi.single_eq_same, map_neg, neg_mul]
      simp only [Nat.cast_one]
      rw [mul_comm ((leftConstant k r hr a i : R k 0)^d), add_neg_cancel]
    · simp [hz]
  exact congrFun hs j

lemma unit_cancel_mem {S : Type*} [CommRing S] (I : Ideal S) (v : Sˣ) (x : S)
    (h : (v : S) * x ∈ I) : x ∈ I := by
  have := I.mul_mem_left (↑v⁻¹) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using this

lemma special_generated (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k 0 false ≃+* B k 0 true) (hE : IsAdjacent k 0 E)
    (a : Fin r → kˣ) (d : ℕ) (hd : 2 ≤ d) : GloballyGenerated k r 0 hr E a d := by
  classical
  intro i
  let I : Ideal (A k 0) := Ideal.span (Set.range
    (fun s : Sections k r 0 hr E a d => s.val i))
  have hb (j : Fin r) : bridge k r hr a d j i ∈ I :=
    Ideal.subset_span ⟨⟨_, bridge_compatible k r hr E hE a d hd j⟩, rfl⟩
  have hy : coordY k 0 ^ (d-1) ∈ I := by
    have h := hb i
    simp only [bridge, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (next_ne r hr h3 i).symm, add_zero] at h
    apply unit_cancel_mem I (Units.map (base k 0).toMonoidHom ((leftConstant k r hr a i)^d))
    simpa using h
  have hx : coordX k 0 ∈ I := by
    obtain ⟨j, hj⟩ := (shift r hr).surjective i
    change next r hr j = i at hj
    have h := hb j
    have hij : i ≠ j := by rw [← hj]; exact next_ne r hr h3 j
    simp only [bridge, Pi.add_apply, Pi.single_eq_of_ne hij, hj, Pi.single_eq_same,
      zero_add] at h
    apply unit_cancel_mem I (Units.map (base k 0).toMonoidHom ((rightConstant k r hr a j)^d))
    simpa using h
  have hq : equation k r 0 hr a i ^ d ∈ I := by
    apply Ideal.subset_span
    refine ⟨⟨fun j => equation k r 0 hr a j ^ d, ?_⟩, rfl⟩
    intro j
    simp only [map_pow]
    exact mul_comm _ _
  have hx' : coordX k 0 ∈ I.radical := Ideal.le_radical hx
  have hy' : coordY k 0 ∈ I.radical := ⟨d-1, hy⟩
  have hq' : equation k r 0 hr a i ∈ I.radical := ⟨d, hq⟩
  have hc : base k 0 (markedUnit k 0 (a i) : R k 0) *
      base k 0 (↑((markedUnit k 0 (a (next r hr i)))⁻¹)) ∈ I.radical := by
    have hh := I.radical.add_mem (I.radical.sub_mem hq'
      (I.radical.mul_mem_right (coordY k 0 - base k 0 (↑((markedUnit k 0 (a (next r hr i)))⁻¹))) hx'))
      (I.radical.mul_mem_left (base k 0 (markedUnit k 0 (a i) : R k 0)) hy')
    convert hh using 1 <;> simp only [equation, pairEquation, markedEquation] <;> ring
  have hu : IsUnit (base k 0 (markedUnit k 0 (a i) : R k 0) *
      base k 0 (↑((markedUnit k 0 (a (next r hr i)))⁻¹))) :=
    ((markedUnit k 0 (a i)).isUnit.map (base k 0)).mul
      (((markedUnit k 0 (a (next r hr i)))⁻¹).isUnit.map (base k 0))
  exact Ideal.radical_eq_top.mp (Ideal.eq_top_of_isUnit_mem _ hc hu)

/-- Unit ideals lift through a quotient with nilpotent kernel. -/
lemma ideal_top_of_reduction {S : Type u} [CommRing S] (t : S) (n : ℕ)
    (I : Ideal (Trunc S t n))
    (hI : Ideal.map (truncReduce S t 0 n (Nat.zero_le n)) I = ⊤) : I = ⊤ := by
  let f := truncReduce S t 0 n (Nat.zero_le n)
  have h1 : (1 : Trunc S t 0) ∈ Ideal.map f I := by rw [hI]; trivial
  obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective f
    (truncReduce_surjective S t 0 n (Nat.zero_le n))).mp h1
  have hz : f (x - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
  obtain ⟨w, hw⟩ := (truncReduce_eq_zero_iff t 0 n (Nat.zero_le n) (x-1)).mp hz
  have hn : IsNilpotent (x-1) := by
    refine ⟨n+1, ?_⟩
    rw [hw, mul_pow, ← map_pow]
    simp only [zero_add, pow_one]
    rw [trunc_parameter_zero, zero_mul]
  have hu := hn.isUnit_add_right_of_commute isUnit_one (Commute.all _ _)
  apply I.eq_top_of_isUnit_mem hx
  simpa only [sub_add_cancel] using hu

lemma tower_generated (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (a : Fin r → kˣ) (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    GloballyGenerated k r n hr (T.overlap n) a d := by
  intro i
  let I : Ideal (A k n) := Ideal.span (Set.range
    (fun s : Sections k r n hr (T.overlap n) a d => s.val i))
  let f := truncReduce (ArithmeticThetaNodeCharts.Node k)
    (ArithmeticThetaNodeCharts.t k) 0 n (Nat.zero_le n)
  apply ideal_top_of_reduction (ArithmeticThetaNodeCharts.t k) n I
  apply top_unique
  rw [← special_generated k r hr h3 (T.overlap 0) (T.overlap_spec 0) a d hd i]
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  obtain ⟨v, hv⟩ := (positive_sections_reduction k r hr h3 T a d (by omega)
    0 n (Nat.zero_le n)).2.1 s
  exact (Ideal.mem_map_iff_of_surjective f
    (truncReduce_surjective _ _ 0 n (Nat.zero_le n))).mpr
      ⟨v.val i, Ideal.subset_span ⟨v, rfl⟩, hv i⟩

end PositiveGlobalGenerationR0134

/-- Every positive divisor power of degree at least two is generated on every chart. -/
theorem positive_global_generation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (a : Fin r → kˣ), ∀ d : ℕ, 2 ≤ d →
      ArithmeticThetaPositiveLineR0134.GloballyGenerated k r n hr E a d := by
  intro k _ _ r n hr h3 E hE a d hd
  let T := ArithmeticThetaInfinitesimalPolygonR0129.TowerAssemblyR0130.assembledTower k r hr h3
  have he : T.overlap n = E :=
    (ArithmeticThetaInfinitesimalPolygonR0129.finite_stage_adjacent k n).unique
      (T.overlap_spec n) hE
  rw [← he]
  exact PositiveGlobalGenerationR0134.tower_generated k r hr h3 T a d hd n

end ArithmeticThetaPositiveLineR0134
