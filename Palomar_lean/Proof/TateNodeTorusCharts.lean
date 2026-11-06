module

public import TateNodeChartDefinitions
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat

@[expose] public section

/-! Algebraic coordinate-open charts, with their full polynomial squares. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaNodeCharts

private theorem laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

variable (k : Type u) [Field k]

private theorem coordinate_product (i j : Fin 2) (h : i ≠ j) :
    quotientMap k (MvPolynomial.X i) * quotientMap k (MvPolynomial.X j) =
      quotientMap k (MvPolynomial.C (parameter k)) := by
  have hr : quotientMap k (relation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxy := sub_eq_zero.mp (show
    quotientMap k (MvPolynomial.X 0) * quotientMap k (MvPolynomial.X 1) -
      quotientMap k (MvPolynomial.C (parameter k)) = 0 by
        simpa [relation, map_sub, map_mul] using hr)
  fin_cases i <;> fin_cases j <;> simp_all [mul_comm]

/-- A common universal-property construction for the two coordinate choices. -/
private theorem coordinate_chart (i : Fin 2) (f : PolynomialChart k →+* Torus k)
    (hC : ∀ a, f (MvPolynomial.C a) = LaurentPolynomial.C a)
    (hX : ∀ j, f (MvPolynomial.X j) = if j = i then LaurentPolynomial.T 1
      else LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) :
    ∃! e : Localization.Away (quotientMap k (MvPolynomial.X i)) ≃+* Torus k,
      e.toRingHom.comp ((algebraMap (Node k) _).comp (quotientMap k)) = f := by
  let v := quotientMap k (MvPolynomial.X i)
  let S := Localization.Away v
  let a : Node k →+* S := algebraMap _ _
  let p : PolynomialChart k →+* S := a.comp (quotientMap k)
  have hfrel : f (relation k) = 0 := by
    simp only [relation, map_sub, map_mul, hC, hX]
    fin_cases i
    · change LaurentPolynomial.T 1 *
        (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) -
          LaurentPolynomial.C (parameter k) = 0
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      norm_num
    · change (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) *
        LaurentPolynomial.T 1 - LaurentPolynomial.C (parameter k) = 0
      rw [mul_assoc, ← LaurentPolynomial.T_add]
      norm_num
  have hkill : relationIdeal k ≤ RingHom.ker f := by
    rw [relationIdeal, Ideal.span_singleton_le_iff_mem]
    exact hfrel
  let g : Node k →+* Torus k := Ideal.Quotient.lift _ f (fun z hz => hkill hz)
  have hg (z) : g (quotientMap k z) = f z := rfl
  have hgv : g v = LaurentPolynomial.T 1 := by simp [v, hg, hX]
  let F : S →+* Torus k := IsLocalization.Away.lift v
    (show IsUnit (g v) by rw [hgv]; exact LaurentPolynomial.isUnit_T 1)
  have hF (z) : F (a z) = g z := IsLocalization.Away.lift_eq _ _ z
  have hFp (z) : F (p z) = f z := by change F (a (quotientMap k z)) = _; rw [hF, hg]
  let U : Sˣ := (IsLocalization.Away.algebraMap_isUnit v (S := S)).unit
  have hU : (U : S) = p (MvPolynomial.X i) := IsUnit.unit_spec _
  let G : Torus k →+* S := LaurentPolynomial.eval₂ (p.comp MvPolynomial.C) U
  have hGC (z) : G (LaurentPolynomial.C z) = p (MvPolynomial.C z) :=
    LaurentPolynomial.eval₂_C _ _ _
  have hGT : G (LaurentPolynomial.T 1) = p (MvPolynomial.X i) := by
    simpa [G] using hU
  have hGX (j : Fin 2) : G (f (MvPolynomial.X j)) = p (MvPolynomial.X j) := by
    rw [hX]
    split_ifs with h
    · subst j; exact hGT
    · have hprod : p (MvPolynomial.X i) * p (MvPolynomial.X j) =
          p (MvPolynomial.C (parameter k)) := by
        change a (quotientMap k (MvPolynomial.X i)) * a (quotientMap k (MvPolynomial.X j)) = _
        rw [← map_mul, coordinate_product k i j (Ne.symm h)]
        rfl
      change G (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) = _
      rw [map_mul, hGC]
      have hneg : G (LaurentPolynomial.T (-1)) = ↑(U⁻¹) := by simp [G]
      rw [hneg, ← hprod, ← hU]
      rw [mul_right_comm, Units.mul_inv, one_mul]
  have hGFp : G.comp f = p := MvPolynomial.ringHom_ext
    (fun z => by simp only [RingHom.comp_apply, hC, hGC]) hGX
  have hGF : G.comp F = RingHom.id S := by
    apply IsLocalization.ringHom_ext (Submonoid.powers v)
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change G (F (p z)) = p z
    rw [hFp]
    exact RingHom.congr_fun hGFp z
  have hFG : F.comp G = RingHom.id (Torus k) := by
    apply laurent_hom_ext
    · intro z
      change F (G (LaurentPolynomial.C z)) = LaurentPolynomial.C z
      rw [hGC, hFp, hC]
    · change F (G (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
      rw [hGT, hFp, hX]; simp
  let e : S ≃+* Torus k :=
    { F with
      invFun := G
      left_inv := fun z => RingHom.congr_fun hGF z
      right_inv := fun z => RingHom.congr_fun hFG z }
  have he : e.toRingHom.comp p = f := RingHom.ext hFp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers v)
  apply Ideal.Quotient.ringHom_ext
  exact he'.trans he.symm

/-- The two coordinate-open charts, uniquely characterized by their entire polynomial square. -/
theorem node_torus_chart_equivalences :
    ∀ (k : Type u) [Field k] [CharZero k],
    (∃! e : XChart k ≃+* Torus k,
      e.toRingHom.comp ((toXChart k).comp (quotientMap k)) = torusMap k) ∧
    (∃! e : YChart k ≃+* Torus k,
      e.toRingHom.comp ((toYChart k).comp (quotientMap k)) = oppositeTorusMap k) := by
  intro k _ _
  constructor
  · exact coordinate_chart k 0 (torusMap k)
      (fun z => by simp [torusMap]) (fun j => by simp [torusMap])
  · apply coordinate_chart k 1 (oppositeTorusMap k)
    · intro z; simp [oppositeTorusMap]
    · intro j; fin_cases j <;> simp [oppositeTorusMap]

end ArithmeticThetaNodeCharts
