import Mathlib
import NormalDomainIntersection

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u
noncomputable section

namespace ArithmeticThetaSectionCompletion

private theorem regular_coefficient_order_nonnegative_affine
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (x : X) (hx : x ∈ U) :
    0 ≤ Scheme.ord (X.germToFunctionField U a) x := by
  by_cases ha : a = 0
  · simp [ha]
  · have hone : Scheme.ord (1 : X.functionField) x = 0 := by
      simpa using (Scheme.ord_of_isUnit (X := X)
        (f := (1 : Γ(X, U))) isUnit_one hx)
    have h := Scheme.ord_le_smul hx ha (1 : X.functionField)
    simpa only [hone, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one] using h

/- On a normal affine chart of an integral locally Noetherian scheme, a rational
function is regular exactly when all codimension-one orders on the chart are
nonnegative. -/
set_option backward.isDefEq.respectTransparency false in
theorem normal_affine_order_criterion
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X] (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (g : X.functionField) :
    (∀ x ∈ U, 0 ≤ AlgebraicGeometry.Scheme.ord g x) ↔
      ∃ a : Γ(X, U), X.germToFunctionField U a = g := by
  classical
  let R := Γ(X, U)
  let K := X.functionField
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen X U hU
  constructor
  · intro hg
    by_cases hzero : g = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨a, ha⟩ := normal_domain_height_one_intersection R K g (by
      intro p hp hpheight
      let y : PrimeSpectrum R := ⟨p, hp⟩
      let xU : U := hU.isoSpec.inv y
      let x : X := xU.1
      have hxU : x ∈ U := xU.2
      have hprime : hU.primeIdealOf xU = y := by
        change hU.isoSpec.hom (hU.isoSpec.inv y) = y
        exact congrArg (fun f => f y) hU.isoSpec.inv_hom_id
      let q : Ideal R := (hU.primeIdealOf xU).asIdeal
      have hq : q = p := by
        exact congrArg (fun z : PrimeSpectrum R => z.asIdeal) hprime
      have hcoh : Order.coheight x = 1 := by
        have hcoh' : Order.coheight (xU : X) = q.height := by
          dsimp [q]
          rw [← hU.fromSpec_primeIdealOf xU, coheight_eq_of_isOpenImmersion]
          exact (idealHeight_eq_coheight _ _).symm
        have hqheight : q.height = 1 := by simpa [hq] using hpheight
        simpa [x] using hcoh'.trans hqheight
      have hnonneg : 0 ≤ Scheme.ord g x := hg x hxU
      let S := X.presheaf.stalk x
      letI : Algebra R S := X.presheaf.algebra_section_stalk xU
      letI : IsLocalization.AtPrime S q := by
        simpa [S, q] using hU.isLocalization_stalk xU
      letI : IsNoetherianRing S := IsLocalization.isNoetherianRing q.primeCompl S inferInstance
      letI : IsIntegrallyClosed S :=
        isIntegrallyClosed_of_isLocalization S q.primeCompl q.primeCompl_le_nonZeroDivisors
      letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
      letI : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hcoh.le
      letI : IsDiscreteValuationRing S := by
        letI : Ring.DimensionLEOne S :=
          { maximalOfPrime := fun {I} hI hIp => hIp.isMaximal_of_ne_bot hI }
        have hq0 : q ≠ (⊥ : Ideal R) := Ideal.ne_bot_of_height_eq_one
          (by simpa [hq] using hpheight)
        have hnf : ¬ IsField S := IsLocalization.AtPrime.not_isField R
          hq0 S
        letI : IsDedekindDomain S :=
          (isDedekindDomain_iff S K).mpr
            ⟨inferInstance, inferInstance, inferInstance, fun {z} hz =>
              (isIntegrallyClosed_iff K).mp inferInstance hz⟩
        exact ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).mp (inferInstance : IsDedekindDomain S)
      let v := (IsDiscreteValuationRing.maximalIdeal S).valuation K
      have hord : (1 : WithZero (Multiplicative ℤ)) ≤ Ring.ordFrac S g := by
        have h' := (Scheme.le_ord_iff hcoh hzero (n := (0 : ℤ))).mp hnonneg
        simpa [Scheme.ordHom, v] using h'
      have hv : v g ≤ 1 := by
        rw [Ring.ordFrac_eq_valuation_inv] at hord
        have hvg : 0 < v g := WithZero.pos_iff_ne_zero.mpr ((map_ne_zero v).mpr hzero)
        have := (inv_le_inv₀ (a := (1 : WithZero (Multiplicative ℤ)))
          (b := v g) (by simp) hvg).mp hord
        simpa using this
      have hmem : g ∈ v.valuationSubring :=
        (Valuation.mem_valuationSubring_iff v g).mpr hv
      have hmem' : g ∈ Subring.map (algebraMap S K) ⊤ := by
        rw [IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
        exact hmem
      obtain ⟨s, -, hs⟩ := Subring.mem_map.mp hmem'
      obtain ⟨z, hz⟩ := IsLocalization.surj q.primeCompl s
      refine ⟨z.1, z.2, ?_, ?_⟩
      simpa [hq] using z.2.2
      have hz' := congrArg (algebraMap S K) hz
      have hs' : algebraMap S K s = g := hs
      rw [← hs']
      simpa only [map_mul, IsScalarTower.algebraMap_apply R S K] using hz')
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩ x hx
    exact regular_coefficient_order_nonnegative_affine X U a x hx

end ArithmeticThetaSectionCompletion
