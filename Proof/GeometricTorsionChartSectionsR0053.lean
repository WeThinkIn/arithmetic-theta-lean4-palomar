module

public import AnnularTorsionPrerequisiteDefinitionsR0053
public import CompletedSectionKernelsR0053
public import RGonRepresentativesR0053
public import TateNodeTorusCharts

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

open ArithmeticThetaNodeCharts

variable (k : Type u) [Field k] [CharZero k]

private lemma smooth_torus : Algebra.Smooth (Base k) (LaurentPolynomial (Base k)) := by
  letI : IsLocalization.Away (Polynomial.X : Polynomial (Base k))
      (LaurentPolynomial (Base k)) := inferInstance
  letI : IsScalarTower (Base k) (Polynomial (Base k)) (LaurentPolynomial (Base k)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      simp [LaurentPolynomial.algebraMap_eq_toLaurent])
  letI : Algebra.FormallySmooth (Polynomial (Base k)) (LaurentPolynomial (Base k)) :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers Polynomial.X)
  letI : Algebra.FinitePresentation (Polynomial (Base k)) (LaurentPolynomial (Base k)) :=
    IsLocalization.Away.finitePresentation Polynomial.X
  have hfs : Algebra.FormallySmooth (Base k) (LaurentPolynomial (Base k)) :=
    Algebra.FormallySmooth.comp (Base k) (Polynomial (Base k)) (LaurentPolynomial (Base k))
  have hfp : Algebra.FinitePresentation (Base k) (LaurentPolynomial (Base k)) :=
    Algebra.FinitePresentation.trans (Base k) (Polynomial (Base k))
      (LaurentPolynomial (Base k))
  exact ⟨hfs, hfp⟩

private lemma smooth_xchart : Algebra.Smooth (Base k) (ArithmeticThetaNodeCharts.XChart k) := by
  obtain ⟨e, he, _⟩ := (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
  letI : Algebra.Smooth (Base k) (LaurentPolynomial (Base k)) := smooth_torus k
  let ae : ArithmeticThetaNodeCharts.XChart k ≃ₐ[Base k]
      LaurentPolynomial (Base k) := AlgEquiv.ofRingEquiv (R := Base k) (f := e) (by
    intro z
    have hz := congrArg (fun f => f (MvPolynomial.C z)) he
    change e ((ArithmeticThetaNodeCharts.toXChart k).comp
      (ArithmeticThetaNodeCharts.quotientMap k) (MvPolynomial.C z)) =
      LaurentPolynomial.C z
    simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using hz)
  exact Algebra.Smooth.of_equiv ae.symm

private lemma smooth_ychart : Algebra.Smooth (Base k) (ArithmeticThetaNodeCharts.YChart k) := by
  obtain ⟨e, he, _⟩ := (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).2
  letI : Algebra.Smooth (Base k) (LaurentPolynomial (Base k)) := smooth_torus k
  let ae : ArithmeticThetaNodeCharts.YChart k ≃ₐ[Base k]
      LaurentPolynomial (Base k) := AlgEquiv.ofRingEquiv (R := Base k) (f := e) (by
    intro z
    have hz := congrArg (fun f => f (MvPolynomial.C z)) he
    change e ((ArithmeticThetaNodeCharts.toYChart k).comp
      (ArithmeticThetaNodeCharts.quotientMap k) (MvPolynomial.C z)) =
      LaurentPolynomial.C z
    simpa [ArithmeticThetaNodeCharts.oppositeTorusMap, RingHom.comp_apply] using hz)
  exact Algebra.Smooth.of_equiv ae.symm

private lemma smooth_scaled_xchart : Algebra.Smooth (Base k)
    (Localization.Away (ArithmeticThetaScaledTateBridgeR0046.x k 1)) := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relation k 1 =
      ArithmeticThetaNodeCharts.relation k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter, pow_one]
  have hideal : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaNodeCharts.relationIdeal, hrel]
  let e0 : ArithmeticThetaScaledTateBridgeR0046.Node k 1 ≃ₐ[Base k]
      ArithmeticThetaNodeCharts.Node k :=
    Ideal.quotientEquivAlgOfEq (Base k) hideal
  have hx : e0 (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
      ArithmeticThetaNodeCharts.x k := by
    change (Ideal.quotientEquivAlgOfEq (Base k) hideal)
        (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      Ideal.Quotient.mk _ (MvPolynomial.X 0)
    rw [Ideal.quotientEquivAlgOfEq_mk]
  let ae : Localization.Away (ArithmeticThetaScaledTateBridgeR0046.x k 1) ≃ₐ[Base k]
      ArithmeticThetaNodeCharts.XChart k :=
    IsLocalization.algEquivOfAlgEquiv
      (Localization.Away (ArithmeticThetaScaledTateBridgeR0046.x k 1))
      (ArithmeticThetaNodeCharts.XChart k) e0 (by
        rw [Submonoid.map_powers, hx])
  letI : Algebra.Smooth (Base k) (ArithmeticThetaNodeCharts.XChart k) :=
    smooth_xchart k
  exact Algebra.Smooth.of_equiv ae.symm

private lemma smooth_scaled_ychart : Algebra.Smooth (Base k)
    (Localization.Away (ArithmeticThetaScaledTateBridgeR0046.y k 1)) := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relation k 1 =
      ArithmeticThetaNodeCharts.relation k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter, pow_one]
  have hideal : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaNodeCharts.relationIdeal, hrel]
  let e0 : ArithmeticThetaScaledTateBridgeR0046.Node k 1 ≃ₐ[Base k]
      ArithmeticThetaNodeCharts.Node k :=
    Ideal.quotientEquivAlgOfEq (Base k) hideal
  have hy : e0 (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
      ArithmeticThetaNodeCharts.y k := by
    change (Ideal.quotientEquivAlgOfEq (Base k) hideal)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1)) =
      Ideal.Quotient.mk _ (MvPolynomial.X 1)
    rw [Ideal.quotientEquivAlgOfEq_mk]
  let ae : Localization.Away (ArithmeticThetaScaledTateBridgeR0046.y k 1) ≃ₐ[Base k]
      ArithmeticThetaNodeCharts.YChart k :=
    IsLocalization.algEquivOfAlgEquiv
      (Localization.Away (ArithmeticThetaScaledTateBridgeR0046.y k 1))
      (ArithmeticThetaNodeCharts.YChart k) e0 (by
        rw [Submonoid.map_powers, hy])
  letI : Algebra.Smooth (Base k) (ArithmeticThetaNodeCharts.YChart k) :=
    smooth_ychart k
  exact Algebra.Smooth.of_equiv ae.symm

private lemma section_chart_x (α : k) (hα : α ≠ 0)
    (σ : Chart k →+* Base k) (hσ : SectionAt k true α σ) (j : ℕ) :
    σ (chartCoordinate k j) = PowerSeries.C α * PowerSeries.X ^ j := by
  have ht : σ (tau k) = PowerSeries.X := by
    change σ (base k (PowerSeries.X)) = PowerSeries.X
    exact DFunLike.congr_fun hσ.1 (PowerSeries.X)
  rw [chartCoordinate, map_mul, map_pow, ht]
  have hcx : σ (cx k) = PowerSeries.C α := by
    simpa [coord] using hσ.2.1
  rw [hcx]
  ring

private lemma section_chart_y (α : k) (hα : α ≠ 0)
    (τ : Chart k →+* Base k) (hτ : SectionAt k false α τ) (j : ℕ) :
    τ (chartCoordinate k j) = PowerSeries.C α⁻¹ * PowerSeries.X ^ (j + 1) := by
  have ht : τ (tau k) = PowerSeries.X := by
    change τ (base k (PowerSeries.X)) = PowerSeries.X
    exact DFunLike.congr_fun hτ.1 (PowerSeries.X)
  rw [chartCoordinate, map_mul, map_pow, ht]
  have hcx : τ (cx k) = PowerSeries.C α⁻¹ * PowerSeries.X := by
    simpa [coord] using hτ.2.2.1
  rw [hcx, pow_succ]
  ring

private lemma section_closed_immersions (side : Bool) (α : k) (hα : α ≠ 0)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    AlgebraicGeometry.IsClosedImmersion (sectionMorphism k σ) ∧
      AlgebraicGeometry.IsClosedImmersion (algebraicSectionMorphism k σ) := by
  have hs : Function.Surjective σ :=
    (completed_section_kernels k side α hα).2 σ hσ |>.1
  have hc : Function.Surjective (σ.comp (complete k)) := by
    intro z
    refine ⟨ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.C z), ?_⟩
    change σ (complete k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.C z))) = z
    change σ (base k z) = z
    exact DFunLike.congr_fun hσ.1 z
  refine ⟨AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom σ) hs, ?_⟩
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (σ.comp (complete k))) hc

private lemma section_compositions (side : Bool) (α : k)
    (σ : Chart k →+* Base k) (hσ : SectionAt k side α σ) :
    CategoryTheory.CategoryStruct.comp (sectionMorphism k σ) (structureMorphism k) =
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (Base k))) ∧
    CategoryTheory.CategoryStruct.comp (algebraicSectionMorphism k σ)
        (algebraicStructureMorphism k) =
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (Base k))) := by
  have hbase : σ.comp (base k) = RingHom.id (Base k) := hσ.1
  have hnode : (σ.comp (complete k)).comp (nodeBase k) = RingHom.id (Base k) := by
    apply RingHom.ext
    intro z
    exact DFunLike.congr_fun hσ.1 z
  constructor
  · change CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (base k))) = _
    rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hbase,
      CommRingCat.ofHom_id, AlgebraicGeometry.Spec.map_id]
  · change CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ.comp (complete k))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (nodeBase k))) = _
    rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hnode,
      CommRingCat.ofHom_id, AlgebraicGeometry.Spec.map_id]

private lemma torsion_exp_lt (r c a : ℕ) (hr : 0 < r) (hc : 0 < c)
    (hdiv : c ∣ r) (ha : a < c) : r * a / c < r := by
  exact (Nat.div_lt_iff_lt_mul hc).2 (Nat.mul_lt_mul_of_pos_left ha hr)

private lemma boundary_index (r c a : ℕ) (hr : 0 < r) (hc : 0 < c)
    (hdiv : c ∣ r) (ha : a < c) :
    (torsionExponent r c a + r - 1) % r =
      if a = 0 then r - 1 else torsionExponent r c a - 1 := by
  by_cases ha0 : a = 0
  · subst a
    simp [torsionExponent, hr.ne']
  · have he : 0 < torsionExponent r c a := by
      have hca : c ∣ r * a := dvd_mul_of_dvd_left hdiv a
      have heq : torsionExponent r c a * c = r * a := by
        unfold torsionExponent
        exact Nat.div_mul_cancel hca
      by_contra hn
      have hz : torsionExponent r c a = 0 := Nat.eq_zero_of_not_pos hn
      rw [hz, zero_mul] at heq
      have hpos : 0 < r * a := Nat.mul_pos hr (Nat.pos_of_ne_zero ha0)
      omega
    have hlt := torsion_exp_lt r c a hr hc hdiv ha
    have hrewrite : torsionExponent r c a + r - 1 =
        (torsionExponent r c a - 1) + r := by omega
    rw [hrewrite, Nat.add_mod]
    have hsub : torsionExponent r c a - 1 < r :=
      lt_of_le_of_lt (Nat.sub_le _ _) hlt
    simpa [ha0] using (Nat.mod_eq_of_lt hsub)

private lemma alpha_nonzero (ζ : k) (c : ℕ) (hc : 1 < c)
    (hζ : IsPrimitiveRoot ζ c) : ζ ≠ 0 :=
  hζ.ne_zero (by omega)

theorem geometric_torsion_chart_sections :
    ∀ (k : Type u) [Field k] [CharZero k] (r c : ℕ) (ζ : k),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 →
      IsPrimitiveRoot ζ c →
      ∀ a b : Fin c,
        ∃ σ : Chart k →+* Base k,
          SectionAt k true (ζ ^ b.val) σ ∧
          AlgebraicGeometry.IsClosedImmersion (sectionMorphism k σ) ∧
          AlgebraicGeometry.IsClosedImmersion (algebraicSectionMorphism k σ) ∧
          CategoryTheory.CategoryStruct.comp (sectionMorphism k σ)
            (structureMorphism k) =
            CategoryTheory.CategoryStruct.id
              (AlgebraicGeometry.Spec (CommRingCat.of (Base k))) ∧
          CategoryTheory.CategoryStruct.comp (algebraicSectionMorphism k σ)
            (algebraicStructureMorphism k) =
            CategoryTheory.CategoryStruct.id
              (AlgebraicGeometry.Spec (CommRingCat.of (Base k))) ∧
          Algebra.Smooth (Base k) (CoordinateOpen k true) ∧
          IsUnit ((σ.comp (complete k)) (nodeCoord k true)) ∧
          torsionExponent r c a.val < r ∧
          σ (chartCoordinate k (torsionExponent r c a.val)) =
            torsionScalar k r c a.val b.val ζ := by
  intro k _ _ r c ζ hr hc hdiv hcop hζ a b
  let α : k := ζ ^ b.val
  have hα : α ≠ 0 := pow_ne_zero _ (alpha_nonzero k ζ c hc hζ)
  obtain ⟨σ, hσ, hσuniq⟩ := (completed_section_kernels k true α hα).1
  have hci := section_closed_immersions k true α hα σ hσ
  have hcomp := section_compositions k true α σ hσ
  have hexp : torsionExponent r c a.val < r :=
    torsion_exp_lt r c a.val hr (by omega) hdiv a.isLt
  have heval := section_chart_x k α hα σ hσ (torsionExponent r c a.val)
  refine ⟨σ, hσ, hci.1, hci.2, hcomp.1, hcomp.2,
    ?_, ?_, hexp, ?_⟩
  · change Algebra.Smooth (Base k) (Localization.Away
      (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
        (MvPolynomial.X 0)))
    exact smooth_scaled_xchart k
  · change IsUnit ((σ.comp (complete k))
      (ArithmeticThetaScaledTateBridgeR0046.x k 1))
    have hv : (σ.comp (complete k))
        (ArithmeticThetaScaledTateBridgeR0046.x k 1) = PowerSeries.C α := by
      simpa [nodeCoord, complete, coord, cx, cy,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaScaledAnnularR0050.cy] using hσ.2.1
    rw [hv]
    exact (isUnit_iff_ne_zero.mpr hα).map PowerSeries.C
  · simpa [α, torsionScalar] using heval

theorem geometric_torsion_boundary_sections :
    ∀ (k : Type u) [Field k] [CharZero k] (r c : ℕ) (ζ : k),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 →
      IsPrimitiveRoot ζ c →
      ∀ a b : Fin c,
        ∃ τ : Chart k →+* Base k,
          SectionAt k false ((ζ ^ b.val)⁻¹) τ ∧
          AlgebraicGeometry.IsClosedImmersion (sectionMorphism k τ) ∧
          AlgebraicGeometry.IsClosedImmersion (algebraicSectionMorphism k τ) ∧
          Algebra.Smooth (Base k) (CoordinateOpen k false) ∧
          IsUnit ((τ.comp (complete k)) (nodeCoord k false)) ∧
          (torsionExponent r c a.val + r - 1) % r < r ∧
          τ (chartCoordinate k ((torsionExponent r c a.val + r - 1) % r)) =
            (if a.val = 0 then
              (PowerSeries.X : PowerSeries k) ^ r *
                torsionScalar k r c a.val b.val ζ
            else
              torsionScalar k r c a.val b.val ζ) := by
  intro k _ _ r c ζ hr hc hdiv hcop hζ a b
  let α : k := (ζ ^ b.val)⁻¹
  have hα : α ≠ 0 := inv_ne_zero (pow_ne_zero _ (alpha_nonzero k ζ c hc hζ))
  obtain ⟨τ, hτ, hτuniq⟩ := (completed_section_kernels k false α hα).1
  have hci := section_closed_immersions k false α hα τ hτ
  have hcomp := section_compositions k false α τ hτ
  have hexp : torsionExponent r c a.val < r :=
    torsion_exp_lt r c a.val hr (by omega) hdiv a.isLt
  have hidx := boundary_index r c a.val hr (by omega) hdiv a.isLt
  have hjlt : (torsionExponent r c a.val + r - 1) % r < r :=
    Nat.mod_lt _ hr
  refine ⟨τ, hτ, hci.1, hci.2, ?_, ?_, hjlt, ?_⟩
  · change Algebra.Smooth (Base k) (Localization.Away
      (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
        (MvPolynomial.X 1)))
    exact smooth_scaled_ychart k
  · change IsUnit ((τ.comp (complete k))
      (ArithmeticThetaScaledTateBridgeR0046.y k 1))
    have hv : (τ.comp (complete k))
        (ArithmeticThetaScaledTateBridgeR0046.y k 1) = PowerSeries.C α := by
      simpa [nodeCoord, complete, coord, cx, cy,
        ArithmeticThetaScaledAnnularR0050.cx,
        ArithmeticThetaScaledAnnularR0050.cy] using hτ.2.1
    rw [hv]
    exact (isUnit_iff_ne_zero.mpr hα).map PowerSeries.C
  · have heval := section_chart_y k α hα τ hτ
      ((torsionExponent r c a.val + r - 1) % r)
    rw [hidx] at heval
    rw [hidx]
    by_cases ha0 : a.val = 0
    · simp [ha0, α, torsionScalar] at heval ⊢
      have hr1 : 1 ≤ r := hr
      rw [show r = (r - 1) + 1 by omega, pow_succ]
      simpa [torsionExponent, pow_succ, mul_assoc, mul_left_comm, mul_comm] using heval
    · simp [ha0, α, torsionScalar, heval, pow_add, mul_assoc, mul_left_comm,
        mul_comm] at heval ⊢
      have hca : c ∣ r * a.val := dvd_mul_of_dvd_left hdiv a.val
      have heq : torsionExponent r c a.val * c = r * a.val := by
        unfold torsionExponent
        exact Nat.div_mul_cancel hca
      have hepos : 0 < torsionExponent r c a.val := by
        by_contra hn
        have hz : torsionExponent r c a.val = 0 := Nat.eq_zero_of_not_pos hn
        rw [hz, zero_mul] at heq
        have hpos : 0 < r * a.val := Nat.mul_pos hr (Nat.pos_of_ne_zero ha0)
        omega
      rw [show torsionExponent r c a.val =
          (torsionExponent r c a.val - 1) + 1 by omega, pow_succ]
      simpa [torsionExponent, mul_assoc, mul_left_comm, mul_comm] using heval

end ArithmeticThetaAnnularTorsionPrereqR0053
