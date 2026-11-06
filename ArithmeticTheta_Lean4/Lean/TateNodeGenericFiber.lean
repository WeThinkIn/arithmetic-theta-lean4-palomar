import TateNodeNormalForm
import TateNodeFiniteType
import TateNodeTorusCharts

/-! The algebraic generic node, with its prescribed coefficient action. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaNodeCharts

private theorem generic_laurent_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

/-- Inverting the parameter gives the Laurent polynomial ring over Laurent series. -/
theorem node_generic_torus_equivalence :
    ∀ (k : Type u) [Field k] [CharZero k],
    ∃! e : GenericNode k ≃+* GenericTorus k,
      e.toRingHom.comp ((toGeneric k).comp (quotientMap k)) = genericTorusMap k := by
  intro k _ _
  obtain ⟨eX, heX, _⟩ := (node_torus_chart_equivalences k).1
  let b : Base k →+* LaurentSeries k := algebraMap _ _
  let V : (GenericTorus k)ˣ := (LaurentPolynomial.isUnit_T (R := LaurentSeries k) 1).unit
  have hV : (V : GenericTorus k) = LaurentPolynomial.T 1 := IsUnit.unit_spec _
  let H : Torus k →+* GenericTorus k :=
    LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp b) V
  have hHC (r) : H (LaurentPolynomial.C r) = LaurentPolynomial.C (b r) := by
    simp [H]
  have hHT : H (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
    simpa [H] using hV
  have hHTneg : H (LaurentPolynomial.T (-1)) = LaurentPolynomial.T (-1) := by
    apply (LaurentPolynomial.isUnit_T (R := LaurentSeries k) 1).mul_right_inj.mp
    calc
      LaurentPolynomial.T 1 * H (LaurentPolynomial.T (-1)) =
          H (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by rw [map_mul, hHT]
      _ = 1 := by rw [← LaurentPolynomial.T_add]; norm_num
      _ = LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) := by
        rw [← LaurentPolynomial.T_add]; norm_num
  let g : Node k →+* GenericTorus k := H.comp (eX.toRingHom.comp (toXChart k))
  have hg : g.comp (quotientMap k) = genericTorusMap k := by
    have hh : H.comp (torusMap k) = genericTorusMap k := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [torusMap, genericTorusMap, hHC, b]
      · intro i; fin_cases i <;> simp [torusMap, genericTorusMap, hHT, hHTneg, hHC, b]
    simpa only [g, RingHom.comp_assoc, heX] using hh
  let a := toGeneric k
  let p : PolynomialChart k →+* GenericNode k := a.comp (quotientMap k)
  have ht : IsUnit (a (t k)) := IsLocalization.Away.algebraMap_isUnit (t k)
  have hgt : g (t k) = LaurentPolynomial.C (b (parameter k)) := by
    rw [t, ← quotient_C, ← RingHom.comp_apply, hg]
    simp [genericTorusMap, b]
  have hb : IsUnit (b (parameter k)) :=
    IsLocalization.Away.algebraMap_isUnit (PowerSeries.X : Base k)
  let F : GenericNode k →+* GenericTorus k := IsLocalization.Away.lift (t k)
    (show IsUnit (g (t k)) by rw [hgt]; exact hb.map LaurentPolynomial.C)
  have hF (z) : F (a z) = g z := IsLocalization.Away.lift_eq _ _ z
  have hFp (z) : F (p z) = genericTorusMap k z := by
    change F (a (quotientMap k z)) = _
    rw [hF]; exact RingHom.congr_fun hg z
  have hxy : a (x k) * a (y k) = a (t k) := by rw [← map_mul, node_xy]
  have hcoords : IsUnit (a (x k)) ∧ IsUnit (a (y k)) :=
    ⟨isUnit_of_mul_isUnit_left (hxy ▸ ht), isUnit_of_mul_isUnit_right (hxy ▸ ht)⟩
  let U : (GenericNode k)ˣ := hcoords.1.unit
  have hU : (U : GenericNode k) = a (x k) := IsUnit.unit_spec _
  let c : Base k →+* GenericNode k := a.comp (algebraMap (Base k) (Node k))
  letI : IsLocalization.Away (parameter k) (LaurentSeries k) :=
    inferInstanceAs (IsLocalization.Away (PowerSeries.X : Base k) (LaurentSeries k))
  let B : LaurentSeries k →+* GenericNode k := IsLocalization.Away.lift (parameter k)
    (show IsUnit (c (parameter k)) from ht)
  have hB (r) : B (b r) = c r := IsLocalization.Away.lift_eq _ _ r
  let G : GenericTorus k →+* GenericNode k := LaurentPolynomial.eval₂ B U
  have hGC (r) : G (LaurentPolynomial.C r) = B r := LaurentPolynomial.eval₂_C _ _ _
  have hGT : G (LaurentPolynomial.T 1) = a (x k) := by simpa [G] using hU
  have hGneg : G (LaurentPolynomial.T (-1)) = ↑(U⁻¹) := by simp [G]
  have hGy : G (genericTorusMap k (MvPolynomial.X 1)) = p (MvPolynomial.X 1) := by
    have hy : genericTorusMap k (MvPolynomial.X 1) =
        LaurentPolynomial.C (b (parameter k)) * LaurentPolynomial.T (-1) := by
      simp [genericTorusMap, b]
    rw [hy, map_mul, hGC, hB, hGneg]
    change a (t k) * ↑(U⁻¹) = a (y k)
    rw [← hxy, ← hU, mul_right_comm, Units.mul_inv, one_mul]
  have hGx : G (genericTorusMap k (MvPolynomial.X 0)) = p (MvPolynomial.X 0) := by
    simpa [genericTorusMap, p, x] using hGT
  have hGFp : G.comp (genericTorusMap k) = p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, genericTorusMap, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      change G (LaurentPolynomial.C (b r)) = p (MvPolynomial.C r)
      rw [hGC, hB]
      simp [c, p, quotient_C]
    · intro i
      fin_cases i
      · exact hGx
      · exact hGy
  have hGF : G.comp F = RingHom.id (GenericNode k) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (t k))
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change G (F (p z)) = p z
    rw [hFp]; exact RingHom.congr_fun hGFp z
  have hFB : F.comp B = LaurentPolynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (parameter k))
    apply RingHom.ext
    intro r
    change F (B (b r)) = LaurentPolynomial.C (b r)
    rw [hB]
    change F (p (MvPolynomial.C r)) = _
    rw [hFp]; simp [genericTorusMap, b]
  have hFG : F.comp G = RingHom.id (GenericTorus k) := by
    apply generic_laurent_ext
    · intro r
      change F (G (LaurentPolynomial.C r)) = LaurentPolynomial.C r
      rw [hGC]; exact RingHom.congr_fun hFB r
    · change F (G (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
      rw [hGT]
      change F (p (MvPolynomial.X 0)) = _
      rw [hFp]; simp [genericTorusMap]
  let e : GenericNode k ≃+* GenericTorus k :=
    { F with
      invFun := G
      left_inv := fun z => RingHom.congr_fun hGF z
      right_inv := fun z => RingHom.congr_fun hFG z }
  have he : e.toRingHom.comp p = genericTorusMap k := RingHom.ext hFp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (t k))
  apply Ideal.Quotient.ringHom_ext
  exact he'.trans he.symm

/-- Algebraic properties over the actual power-series base. -/
theorem node_generic_properties :
    ∀ (k : Type u) [Field k] [CharZero k],
    IsDomain (GenericNode k) ∧ IsNoetherianRing (GenericNode k) ∧
      IsIntegrallyClosed (GenericNode k) ∧ Algebra.FiniteType (Base k) (GenericNode k) ∧
      Module.Flat (Base k) (GenericNode k) := by
  intro k _ _
  obtain ⟨hd, hf, ht, _⟩ := node_flat_domain_parameter k
  obtain ⟨hn, hft⟩ := node_noetherian_finite_type k
  letI := hd
  letI := hf
  letI := hn
  letI := hft
  have hdom : IsDomain (GenericNode k) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hnoeth : IsNoetherianRing (GenericNode k) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (t k)) _ hn
  have hnormal : IsIntegrallyClosed (GenericTorus k) :=
    isIntegrallyClosed_of_isLocalization _
      (Submonoid.powers (Polynomial.X : Polynomial (LaurentSeries k)))
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)
  letI := hnormal
  obtain ⟨e, _, _⟩ := node_generic_torus_equivalence k
  refine ⟨hdom, hnoeth, IsIntegrallyClosed.of_equiv e.symm, inferInstance, ?_⟩
  exact Module.Flat.trans (Base k) (Node k) (GenericNode k)

end ArithmeticThetaNodeCharts
