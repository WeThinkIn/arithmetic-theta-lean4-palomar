module

public import PolygonCohomologyDefinitionsR0131

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! The marked equation on every finite nodal thickening. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
namespace MarkedCartierEquationR0131
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaNodeCharts

/-- Eliminating the second coordinate uses only the node equation and a unit. -/
lemma other_difference {S T : Type u} [CommRing S] [CommRing T]
    (b : S →+* T) (v : Sˣ) (s : S) (X Y : T) (hxy : X * Y = b s) :
    Y - b (s * ↑v⁻¹) ∈ Ideal.span ({X - b (v : S)} : Set T) := by
  have hu : b (v : S) * b (↑v⁻¹ : S) = 1 := by rw [← map_mul]; simp
  have he : Y - b (s * ↑v⁻¹) = -(b (↑v⁻¹ : S) * Y) * (X - b (v : S)) := by
    rw [map_mul, ← hxy]
    calc
      Y - X * Y * b (↑v⁻¹ : S) = Y * (b (v : S) * b (↑v⁻¹ : S)) -
          X * Y * b (↑v⁻¹ : S) := by rw [hu]; ring
      _ = _ := by ring
  rw [he]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable (k : Type u) [Field k] [CharZero k]

def rawUnit (a : kˣ) : (PowerSeries k)ˣ := Units.map (PowerSeries.C (R := k)).toMonoidHom a

def rawEquation (a : kˣ) : Node k :=
  x k - algebraMap (PowerSeries k) (Node k) (rawUnit k a : PowerSeries k)

def rawPoint (a : kˣ) : Node k →+* PowerSeries k :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (RingHom.id _) (fun j : Fin 2 =>
      if j = 0 then (rawUnit k a : PowerSeries k)
      else PowerSeries.X * (↑((rawUnit k a)⁻¹) : PowerSeries k))) (by
        change relationIdeal k ≤ RingHom.ker _
        apply Ideal.span_le.mpr
        intro p hp
        rcases Set.mem_singleton_iff.mp hp with rfl
        simp [relation, ArithmeticThetaNodeCharts.parameter, mul_left_comm])

@[simp] lemma rawPoint_base (a : kˣ) (c : PowerSeries k) :
    rawPoint k a (algebraMap (PowerSeries k) (Node k) c) = c := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) = c
  simp

@[simp] lemma rawPoint_x (a : kˣ) : rawPoint k a (x k) = ↑(rawUnit k a) := by
  simp [rawPoint, x, quotientMap]

@[simp] lemma rawPoint_y (a : kˣ) : rawPoint k a (y k) =
    PowerSeries.X * (↑((rawUnit k a)⁻¹) : PowerSeries k) := by
  simp [rawPoint, y, quotientMap]

@[simp] lemma rawPoint_equation (a : kˣ) : rawPoint k a (rawEquation k a) = 0 := by
  simp [rawEquation]

@[simp] lemma rawPoint_t (a : kˣ) : rawPoint k a (t k) = PowerSeries.X := by
  exact rawPoint_base k a _

lemma raw_kernel (a : kˣ) : RingHom.ker (rawPoint k a) =
    Ideal.span ({rawEquation k a} : Set (Node k)) := by
  let J := Ideal.span ({rawEquation k a} : Set (Node k))
  let q := Ideal.Quotient.mk J
  let b := algebraMap (PowerSeries k) (Node k)
  have hq : q = (q.comp b).comp (rawPoint k a) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      change q (b c) = q (b (rawPoint k a (b c)))
      rw [rawPoint_base]
    · intro j
      fin_cases j
      · change q (x k) = q (b (rawPoint k a (x k)))
        rw [rawPoint_x]
        exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)
      · change q (y k) = q (b (rawPoint k a (y k)))
        rw [rawPoint_y]
        exact Ideal.Quotient.eq.mpr
          (other_difference b (rawUnit k a) PowerSeries.X (x k) (y k) (node_xy k))
  apply le_antisymm
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q z = 0
    rw [hq]
    change q (b (rawPoint k a z)) = 0
    rw [show rawPoint k a z = 0 from hz, map_zero, map_zero]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact rawPoint_equation k a

lemma raw_equation_ne_zero (a : kˣ) : rawEquation k a ≠ 0 := by
  intro h
  have hh := congrArg (nodeOrigin k) h
  have hx : nodeOrigin k (x k) = 0 := by simp [nodeOrigin, x, quotientMap]
  have hb (c : PowerSeries k) : nodeOrigin k (algebraMap _ (Node k) c) =
      PowerSeries.constantCoeff c := by
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) = _
    simp
  have ha : (a : k) = 0 := by
    simpa [rawEquation, map_sub, hx, hb, rawUnit] using hh
  exact Units.ne_zero a ha

lemma raw_trunc_regular (n : ℕ) (a : kˣ) :
    IsRegular (trunc (Node k) (t k) n (rawEquation k a)) := by
  letI : IsDomain (Node k) := (node_flat_domain_parameter k).1
  have hzero : ∀ z : A k n,
      trunc (Node k) (t k) n (rawEquation k a) * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hm : rawEquation k a * w ∈ (Ideal.span {t k}) ^ (n+1) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (map_mul (trunc (Node k) (t k) n) _ _).trans hz
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    obtain ⟨v, hv⟩ := hm
    have hv0 : rawPoint k a v = 0 := by
      have h := congrArg (rawPoint k a) hv
      simp only [map_mul, map_pow, rawPoint_equation, rawPoint_t, zero_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
    have hvJ : v ∈ Ideal.span ({rawEquation k a} : Set (Node k)) := by
      rw [← raw_kernel]
      exact hv0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hvJ
    have hw : w = t k ^ (n+1) * c := by
      apply mul_left_cancel₀ (raw_equation_ne_zero k a)
      calc
        rawEquation k a * w = t k ^ (n+1) * v := hv
        _ = rawEquation k a * (t k ^ (n+1) * c) := by rw [hc]; ring
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, hw⟩
  have hl : IsLeftRegular (trunc (Node k) (t k) n (rawEquation k a)) := by
    intro z w h
    apply sub_eq_zero.mp
    apply hzero
    dsimp only at h
    rw [mul_sub, h, sub_self]
  exact ⟨hl, fun z w h => hl (by simpa only [mul_comm] using h)⟩

lemma trunc_equation (n : ℕ) (a : kˣ) :
    trunc (Node k) (t k) n (rawEquation k a) = markedEquation k n a := by
  rw [rawEquation, map_sub]
  rfl

lemma marked_kernel (n : ℕ) (a : kˣ) :
    RingHom.ker (markedPoint k n a) = Ideal.span ({markedEquation k n a} : Set (A k n)) := by
  let J := Ideal.span ({markedEquation k n a} : Set (A k n))
  let q := Ideal.Quotient.mk J
  have hb : (markedPoint k n a).comp (base k n) = RingHom.id _ := by
    exact mkPoint_base _ _ _ _
  have hx : markedPoint k n a (coordX k n) = ↑(markedUnit k n a) := by
    simp [markedPoint]
  have hy : markedPoint k n a (coordY k n) =
      ArithmeticThetaInfinitesimalPolygonR0129.parameter k n * ↑((markedUnit k n a)⁻¹) := by
    simp [markedPoint]
  have hq : q = (q.comp (base k n)).comp (markedPoint k n a) := by
    apply point_ext
    · ext c
      change q (base k n c) = q (base k n (markedPoint k n a (base k n c)))
      rw [show markedPoint k n a (base k n c) = c from RingHom.congr_fun hb c]
    · change q (coordX k n) = q (base k n (markedPoint k n a (coordX k n)))
      rw [hx]
      exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)
    · change q (coordY k n) = q (base k n (markedPoint k n a (coordY k n)))
      rw [hy]
      exact Ideal.Quotient.eq.mpr (other_difference (base k n) (markedUnit k n a)
        _ _ _ (coordX_mul_coordY k n))
  apply le_antisymm
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q z = 0
    rw [hq]
    change q (base k n (markedPoint k n a z)) = 0
    rw [show markedPoint k n a z = 0 from hz, map_zero, map_zero]
  · rw [Ideal.span_singleton_le_iff_mem]
    change markedPoint k n a (markedEquation k n a) = 0
    rw [markedEquation, map_sub, hx]
    rw [show markedPoint k n a (base k n (markedUnit k n a)) = markedUnit k n a from
      by exact RingHom.congr_fun hb (markedUnit k n a : R k n)]
    exact sub_self _

end MarkedCartierEquationR0131

/-- The actual marked section has a principal regular equation at every finite level. -/
theorem marked_cartier_equation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (n : ℕ) (a : kˣ),
      IsRegular (ArithmeticThetaPolygonCohomologyR0131.markedEquation k n a) ∧
      RingHom.ker (ArithmeticThetaPolygonCohomologyR0131.markedPoint k n a) =
        Ideal.span ({ArithmeticThetaPolygonCohomologyR0131.markedEquation k n a} :
          Set (ArithmeticThetaInfinitesimalPolygonR0129.A k n)) := by
  intro k _ _ n a
  constructor
  · rw [← MarkedCartierEquationR0131.trunc_equation]
    exact MarkedCartierEquationR0131.raw_trunc_regular k n a
  · exact MarkedCartierEquationR0131.marked_kernel k n a

end ArithmeticThetaPolygonCohomologyR0131
