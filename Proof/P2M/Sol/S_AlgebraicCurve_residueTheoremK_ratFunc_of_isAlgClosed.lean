module

public import P2M.Sol.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosedPrelude
import all P2M.Sol.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosedPrelude

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000
namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq ord_prod"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule)
    (haf : a * f ∈ v.simplePoleSubmodule) :
    v.simplePoleResidueAux ⟨a * f, haf⟩
      = IsLocalRing.residue _ ⟨a, ha⟩ * v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [simplePoleResidueAux_apply, simplePoleResidueAux_apply, ← map_mul]
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (mul_left_comm _ _ _))

p2m_export "AlgebraicCurve.Place" "simplePoleResidueAux_mul_of_mem"
private theorem _root_.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    a * f ∈ v.simplePoleSubmodule := by
  rw [mem_simplePoleSubmodule, mul_left_comm]
  exact mul_mem ha hf

p2m_export "AlgebraicCurve.Place" "mul_mem_simplePoleSubmodule_of_mem"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section DerivativeRegular

variable (K)
variable [DecidableEq (RatFunc K)]

theorem denom_notMem_of_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) {f : RatFunc K}
    (hf : f ∈ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring) :
    f.denom ∉ w.asIdeal := by
  intro hd
  have hxval : w.valuation (RatFunc K) f ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hf)
  have hden_ne : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hmul : f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
    ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hnum : f.num ∉ w.asIdeal := by
    intro hn
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom f
    exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
  refine absurd h1 (ne_of_lt ?_)
  calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
      = w.valuation (RatFunc K) f
          * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) := by
        rw [← map_mul, hmul]
    _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w f.denom).mpr hd

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

private theorem differentialCoeff_add' (v : Place K (RatFunc K)) (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_D_algebraMap_polynomial (v : Place K (RatFunc K)) (q : K[X]) :
    v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) q))
      = algebraMap K[X] (RatFunc K) q.derivative * v.differentialCoeff (dX K) := by
  rw [D_algebraMap_polynomial K q, v.differentialCoeff_smul]

theorem differentialCoeff_D_mem_finitePlace [CharZero K] {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr

  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]

  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  ·
    have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge

end DerivativeRegular
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section LeibnizCore

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h

  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, differentialCoeff_add' K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine mul_mem (uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge)

theorem residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _) (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_

  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr

  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    differentialCoeff_D_mem_finitePlace K hpirr (uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section BridgeDischarge

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit (hpirr.separable.isUnit_of_dvd' dvd_rfl hlt')

theorem simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  rw [Place.simplePoleResidueAux_apply, eq_div_iff (residue_algebraMap_derivative_ne_zero K hpirr)]

  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf

  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ComposedEngine

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge K hω₀ heq
    (p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX K) hinf

end ComposedEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField IntermediateField.algebraAdjoinAdjoin P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField.algebraAdjoinAdjoin"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

section AdjoinRingProperties

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.Transcendental.isPrincipalIdealRing_adjoin {t : F} (ht : Transcendental K t) :
    IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isPrincipalIdealRing_adjoin" "Transcendental.isPrincipalIdealRing_adjoin"
private theorem _root_.Transcendental.isDedekindDomain_adjoin {t : F} (ht : Transcendental K t) :
    IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isDedekindDomain_adjoin" "Transcendental.isDedekindDomain_adjoin"
private theorem _root_.Transcendental.isIntegrallyClosed_adjoin {t : F} (ht : Transcendental K t) :
    IsIntegrallyClosed ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isDedekindDomain_adjoin
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isIntegrallyClosed_adjoin" "Transcendental.isIntegrallyClosed_adjoin"
private theorem _root_.Transcendental.isNoetherianRing_adjoin {t : F} (ht : Transcendental K t) :
    IsNoetherianRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isNoetherianRing_adjoin" "Transcendental.isNoetherianRing_adjoin"
private theorem _root_.Algebra.FiniteType.adjoin_singleton (t : F) :
    Algebra.FiniteType K ↥(Algebra.adjoin K ({t} : Set F)) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Algebra.FiniteType.adjoin_singleton" "Algebra.FiniteType.adjoin_singleton"
private theorem _root_.Transcendental.inv {t : F} (ht : Transcendental K t) :
    Transcendental K t⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff]; exact ht

p2m_alias "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.inv" "Transcendental.inv"
end AdjoinRingProperties
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section TranscendentalChart

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def transcendentalChart (t : F) : Subalgebra K F :=
  (integralClosure (Algebra.adjoin K ({t} : Set F)) F).restrictScalars K

theorem coe_transcendentalChart (t : F) :
    (transcendentalChart K t : Set F)
      = ((integralClosure (Algebra.adjoin K ({t} : Set F)) F : Subalgebra _ F) : Set F) :=
  rfl

variable {K}

theorem transcendentalChart_subset_valuationSubring_of_mem (v : Place K F)
    {t : F} (ht : t ∈ v.toValuationSubring) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F) := by
  rw [coe_transcendentalChart]
  exact v.integralClosure_subset_valuationSubring _
    (gate_adjoin_subset_valuationSubring_of_mem v ht)

theorem transcendentalChart_subset_or_inv_subset (v : Place K F) (t : F) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F)
      ∨ (transcendentalChart K t⁻¹ : Set F) ⊆ (v.toValuationSubring : Set F) :=
  (v.toValuationSubring.mem_or_inv_mem t).imp
    (transcendentalChart_subset_valuationSubring_of_mem v)
    (transcendentalChart_subset_valuationSubring_of_mem v)

end TranscendentalChart
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section IsAffineChartEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section

variable (B : Subalgebra K F)

theorem isScalarTower_integralClosure_subalgebra :
    IsScalarTower K B ↥(integralClosure B F) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact Subtype.ext rfl

theorem finiteType_integralClosure_of_moduleFinite (hft : Algebra.FiniteType K B)
    (hfin : Module.Finite B ↥(integralClosure B F)) :
    Algebra.FiniteType K ↥(integralClosure B F) :=
  haveI := isScalarTower_integralClosure_subalgebra B
  haveI := hfin
  Algebra.FiniteType.trans (S := B) hft inferInstance

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

theorem isDedekindDomain_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsDedekindDomain ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isDedekindDomain_adjoin
  exact integralClosure.isDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) ↥(K⟮t⟯) F

theorem isFractionRing_integralClosure_adjoin (t : F) [FiniteDimensional K⟮t⟯ F] :
    IsFractionRing ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) F :=
  integralClosure.isFractionRing_of_finite_extension
    (A := ↥(Algebra.adjoin K ({t} : Set F))) ↥(K⟮t⟯) F

set_option synthInstance.maxHeartbeats 320000 in

theorem moduleFinite_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Module.Finite ↥(Algebra.adjoin K ({t} : Set F))
      ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isIntegrallyClosed_adjoin
  haveI := ht.isNoetherianRing_adjoin
  exact IsIntegralClosure.finite (A := ↥(Algebra.adjoin K ({t} : Set F)))
    (K := ↥(K⟮t⟯)) (L := F) (integralClosure ↥(Algebra.adjoin K ({t} : Set F)) F)

theorem finiteType_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.FiniteType K ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) :=
  finiteType_integralClosure_of_moduleFinite (Algebra.adjoin K {t})
    (Algebra.FiniteType.adjoin_singleton t) (moduleFinite_integralClosure_adjoin ht)

theorem isAffineChart_restrictScalars_integralClosure (B : Subalgebra K F)
    (hft : Algebra.FiniteType K ↥(integralClosure B F))
    (hded : IsDedekindDomain ↥(integralClosure B F))
    (hfrac : IsFractionRing ↥(integralClosure B F) F) :
    IsAffineChart K F ((integralClosure B F).restrictScalars K) :=
  ⟨hft, hded, hfrac⟩

theorem isAffineChart_transcendentalChart {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsAffineChart K F (transcendentalChart K t) :=
  isAffineChart_restrictScalars_integralClosure (Algebra.adjoin K {t})
    (finiteType_integralClosure_adjoin ht)
    (isDedekindDomain_integralClosure_adjoin ht)
    (isFractionRing_integralClosure_adjoin t)

end IsAffineChartEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SeparatingTranscendental

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendental : Prop :=
  ∃ t : F, Transcendental K t
    ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F
    ∧ FiniteDimensional K⟮t⁻¹⟯ F ∧ Algebra.IsSeparable K⟮t⁻¹⟯ F

variable {K F}

theorem valSubringTwoAffineCharts_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringTwoAffineCharts K F := by
  obtain ⟨t, ht, hfin, hsep, hfin', hsep'⟩ := h
  exact ⟨transcendentalChart K t, transcendentalChart K t⁻¹,
    isAffineChart_transcendentalChart ht,
    isAffineChart_transcendentalChart ht.inv,
    fun v => transcendentalChart_subset_or_inv_subset v t⟩

theorem valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendental
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section LowDegRegular

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_dX
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hc : c ≠ 0) :
    (placeInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K))
      = (p.natDegree : ℤ) - c.natDegree - 2 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
  rw [(placeInfty K).ord_mul hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)),
    ord_placeInfty_p1PrincipalPartAtom K hp hc 1, hInfty]
  push_cast; ring

theorem p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree) :
    p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).toValuationSubring := by
  rcases hcdeg with rfl | hcdeg
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (placeInfty K).differentialCoeff (dX K) ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · rcases eq_or_ne c 0 with rfl | hc
    · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K) ∈ _
      rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
    have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
    refine (placeInfty K).mem_of_ord_nonneg
      (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K))) ?_
    rw [ord_placeInfty_mOneAtom_mul_differentialCoeff_dX K hInfty hp hc]
    omega

end LowDegRegular
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section LowDegValue

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_simplePoleResidue_mOne_of_lowDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hpirr : Irreducible p)
    (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree)
    (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1)) := by

  have hreg := p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hcdeg
  have hLHS : (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = 0 :=
    (placeInfty K).simplePoleResidueAux_eq_zero_of_mem hreg
  rw [hLHS, _root_.map_zero]

  rcases hcdeg with rfl | hcdeg
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < p.natDegree - 1), _root_.neg_zero]

end LowDegValue
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section NamedCarriers

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueTopDeg : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c ≠ 0 → c.natDegree + 1 = p.natDegree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

def P1PlaceInftySimplePoleResidueEulerValueMonomial : Prop :=
  ∀ (p : K[X]) (_ : p.Monic) (_ : Irreducible p),
    ∀ (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarriers
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section EraseLeadLinearity

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)] in

theorem p1PrincipalPartAtom_add_mul_differentialCoeff (p c₁ c₂ : K[X]) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (c₁ + c₂) m * v.differentialCoeff ω
      = p1PrincipalPartAtom K p c₁ m * v.differentialCoeff ω
        + p1PrincipalPartAtom K p c₂ m * v.differentialCoeff ω := by
  show algebraMap K[X] (RatFunc K) (c₁ + c₂) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = algebraMap K[X] (RatFunc K) c₁ / (algebraMap K[X] (RatFunc K) p) ^ m * v.differentialCoeff ω
      + algebraMap K[X] (RatFunc K) c₂ / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
  rw [map_add]; ring

omit [DecidableEq (RatFunc K)] in

theorem p1PrincipalPartAtom_C_mul_mul_differentialCoeff (p c : K[X]) (a : K) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (C a * c) m * v.differentialCoeff ω
      = a • (p1PrincipalPartAtom K p c m * v.differentialCoeff ω) := by
  show algebraMap K[X] (RatFunc K) (C a * c) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = a • (algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω)
  rw [map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
    Algebra.smul_def]
  ring

theorem trace_placeInfty_simplePoleResidueAux_mOne_add
    {p c₁ c₂ : K[X]} {ω : Ω[(RatFunc K)⁄K]}
    (h1 : p1PrincipalPartAtom K p c₁ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h2 : p1PrincipalPartAtom K p c₂ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h12 : p1PrincipalPartAtom K p (c₁ + c₂) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, h12⟩)
      = Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, h1⟩)
        + Algebra.trace K (placeInfty K).ResidueField
            ((placeInfty K).simplePoleResidueAux ⟨_, h2⟩) := by
  have heq : (⟨_, h12⟩ : (placeInfty K).simplePoleSubmodule)
      = (⟨_, h1⟩ : (placeInfty K).simplePoleSubmodule) + ⟨_, h2⟩ :=
    Subtype.ext (p1PrincipalPartAtom_add_mul_differentialCoeff K p c₁ c₂ 1 _ ω)
  rw [heq, map_add, map_add]

theorem trace_placeInfty_simplePoleResidueAux_mOne_C_mul
    {p c : K[X]} {a : K} {ω : Ω[(RatFunc K)⁄K]}
    (hc : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (hac : p1PrincipalPartAtom K p (C a * c) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, hac⟩)
      = a * Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, hc⟩) := by
  have heq : (⟨_, hac⟩ : (placeInfty K).simplePoleSubmodule)
      = a • (⟨_, hc⟩ : (placeInfty K).simplePoleSubmodule) :=
    Subtype.ext (p1PrincipalPartAtom_C_mul_mul_differentialCoeff K p c a 1 _ ω)
  rw [heq, map_smul, map_smul, smul_eq_mul]

theorem p1PlaceInftySimplePoleResidueEulerValue_of_topDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (htop : P1PlaceInftySimplePoleResidueEulerValueTopDeg K) :
    P1PlaceInftySimplePoleResidueEulerValue K := by
  intro p c hpmon hpirr hcdeg himem
  rcases eq_or_ne c 0 with rfl | hc
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inl rfl) himem
  have hndeg : c.natDegree < p.natDegree := natDegree_lt_natDegree hc hcdeg
  rcases (by omega : c.natDegree + 2 ≤ p.natDegree ∨ c.natDegree + 1 = p.natDegree) with h | h
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inr h) himem
  · exact htop p c hpmon hpirr hc h himem

theorem p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValueTopDeg K := by
  intro p c hpmon hpirr hc hcnd himem

  have hInfty' : (placeInfty K).ordDifferential (dX K) = -2 := hInfty
  have hXd : (X ^ (p.natDegree - 1) : K[X]).degree < p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpirr.ne_zero]
    exact_mod_cast (by omega : p.natDegree - 1 < p.natDegree)
  have hXmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) hInfty' hpirr (X ^ (p.natDegree - 1)) hXd
  have hCXmem : p1PrincipalPartAtom K p (C c.leadingCoeff * X ^ (p.natDegree - 1)) 1
        * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_C_mul_mul_differentialCoeff K]
    exact (placeInfty K).simplePoleSubmodule.smul_mem _ hXmem
  have hELdeg : c.eraseLead = 0 ∨ c.eraseLead.natDegree + 2 ≤ p.natDegree := by
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero c with h | h
    · exact .inr (by omega)
    · exact .inl h
  have hELmem : p1PrincipalPartAtom K p c.eraseLead 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mem_simplePoleSubmodule_of_mem
      (p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hELdeg)

  have hcnd' : c.natDegree = p.natDegree - 1 := by omega
  have hcdecomp : c = C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow c, add_comm, hcnd']

  have h12mem : p1PrincipalPartAtom K p
        (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead) 1
          * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_add_mul_differentialCoeff K]; exact add_mem hCXmem hELmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, h12mem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K)
      = algebraMap K[X] (RatFunc K) (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead)
          / (algebraMap K[X] (RatFunc K) p) ^ 1 * (placeInfty K).differentialCoeff (dX K)
    rw [← hcdecomp]

  have hELcoeff : c.eraseLead.coeff (p.natDegree - 1) = 0 := by
    rcases hELdeg with h | h
    · rw [h, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hLead : c.leadingCoeff = c.coeff (p.natDegree - 1) := by
    rw [leadingCoeff, hcnd']
  rw [heq, trace_placeInfty_simplePoleResidueAux_mOne_add K hCXmem hELmem,
    trace_placeInfty_simplePoleResidueAux_mOne_C_mul K hXmem,
    hmono p hpmon hpirr hXmem,
    trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr hELdeg hELmem,
    hELcoeff, _root_.neg_zero, add_zero, hLead]
  ring

theorem p1PlaceInftySimplePoleResidueEulerValue_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_topDeg K hInfty
    (p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial K hInfty hmono)

end EraseLeadLinearity
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ComposedEngine

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge K hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hmono)

end ComposedEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

namespace IntermediateField
p2m_export "IntermediateField" "charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map"
p2m_open "IntermediateField"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm (adjoin_simple_le_iff.mpr ?_) (adjoin_simple_le_iff.mpr ?_)
  · exact inv_mem (mem_adjoin_simple_self K t)
  · have h : (t⁻¹)⁻¹ ∈ (K⟮t⁻¹⟯ : IntermediateField K F) :=
      inv_mem (mem_adjoin_simple_self K t⁻¹)
    rwa [inv_inv] at h

theorem algebraMap_comp_equivOfEq {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) := by
  ext x; rfl

theorem finiteDimensional_of_eq {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  Module.Finite.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv (RingEquiv.refl F)
    (algebraMap_comp_equivOfEq h)

theorem isSeparable_of_eq {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  Algebra.IsSeparable.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv
    (RingEquiv.refl F) (algebraMap_comp_equivOfEq h)

theorem finiteDimensional_adjoin_inv (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_of_eq (adjoin_simple_inv t).symm

theorem isSeparable_adjoin_inv (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_of_eq (adjoin_simple_inv t).symm

end IntermediateField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

section CharZeroSeparable

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isSeparable_of_charZero_of_finiteDimensional [CharZero K]
    (S : IntermediateField K F) [FiniteDimensional ↥S F] :
    Algebra.IsSeparable ↥S F :=
  haveI : CharZero ↥S := IntermediateField.charZero S
  Algebra.IsSeparable.of_integral ↥S F

theorem isSeparable_adjoin_of_charZero_of_finiteDimensional [CharZero K] (t : F)
    [FiniteDimensional K⟮t⟯ F] : Algebra.IsSeparable K⟮t⟯ F :=
  isSeparable_of_charZero_of_finiteDimensional K⟮t⟯

end CharZeroSeparable
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SeparatingTranscendentalCore

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendentalCore : Prop :=
  ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F

variable {K F}

theorem hasSeparatingTranscendental_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, ht, hfin⟩ := h
  haveI : Algebra.IsSeparable K⟮t⟯ F :=
    isSeparable_adjoin_of_charZero_of_finiteDimensional t
  exact ⟨t, ht, hfin, ‹_›,
    IntermediateField.finiteDimensional_adjoin_inv t,
    IntermediateField.isSeparable_adjoin_inv t⟩

theorem valSubringKaehlerFinite_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (hasSeparatingTranscendental_of_core h)

end SeparatingTranscendentalCore
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section MonicRatioResidue

theorem ord_placeInfty_X_pow_natDegree_div {p : K[X]} (hp : p ≠ 0) :
    (placeInfty K).ord
        (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd : (X ^ p.natDegree : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hXd
  rw [div_eq_mul_inv, (placeInfty K).ord_mul hXd' (inv_ne_zero hp'),
    (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K hXd, ord_placeInfty_algebraMap' K hp,
    natDegree_X_pow]
  ring

theorem X_pow_natDegree_div_mem_placeInfty {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (pow_ne_zero _ X_ne_zero)
  exact (placeInfty K).mem_of_ord_nonneg (div_ne_zero hXd' hp')
    (ord_placeInfty_X_pow_natDegree_div K hp).ge

theorem degree_X_pow_natDegree_sub_lt_of_monic {p : K[X]} (hpmon : p.Monic) :
    ((X : K[X]) ^ p.natDegree - p).degree < p.degree := by
  have hdeg : ((X : K[X]) ^ p.natDegree).degree = p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpmon.ne_zero]
  refine (Polynomial.degree_sub_lt hdeg (pow_ne_zero _ X_ne_zero) ?_).trans_le hdeg.le
  rw [Polynomial.leadingCoeff_X_pow, hpmon]

theorem residue_placeInfty_X_pow_natDegree_div_monic_eq_one {p : K[X]} (hpmon : p.Monic) :
    IsLocalRing.residue _ ⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
      = (1 : (placeInfty K).ResidueField) := by
  rw [← sub_eq_zero, show (1 : (placeInfty K).ResidueField) = IsLocalRing.residue _ 1 from
      (map_one _).symm, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  set d := p.natDegree
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpmon.ne_zero

  have hsubmem : algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
    rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
    · simp only [h0, _root_.map_zero, zero_div]; exact zero_mem _
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    refine (placeInfty K).mem_of_ord_nonneg (div_ne_zero h0' hp') ?_
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega
  have hcoe : (⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
        - 1 : (placeInfty K).toValuationSubring)
      = ⟨_, hsubmem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) (X ^ d) / algebraMap K[X] (RatFunc K) p - 1
      = algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
    rw [map_sub, sub_div, div_self hp']
  rw [hcoe, Place.mk_mem_maximalIdeal_iff]
  rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
  · exact .inl (by simp [h0])
  · refine .inr ?_
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega

end MonicRatioResidue
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section NamedCarrier

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueX : Prop :=
  ∀ (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarrier
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section MonicRatioReduction

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1MonomialAtom_eq_monicRatio_mul {p : K[X]} (hpdeg : 1 ≤ p.natDegree) :
    p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1 * (placeInfty K).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1
            * (placeInfty K).differentialCoeff (dX K)) := by
  show algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) / algebraMap K[X] (RatFunc K) p ^ 1
        * (placeInfty K).differentialCoeff (dX K)
    = algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
        * (algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
            * (placeInfty K).differentialCoeff (dX K))
  have hXd : algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
      = algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) * algebraMap K[X] (RatFunc K) X := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hpdeg]
  have hX0 : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr X_ne_zero
  rw [pow_one, pow_one, map_one, hXd, one_div]
  field_simp

theorem p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2) :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
  p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K (dX_ne_zero K) hInfty
    irreducible_X 1 (by rw [degree_one, degree_X]; decide)

theorem simplePoleResidueAux_placeInfty_monomial_eq_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    {p : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩
      = (placeInfty K).simplePoleResidueAux
          ⟨_, p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty⟩ := by
  set hXmem := p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty

  have hfact := p1MonomialAtom_eq_monicRatio_mul K hpirr.natDegree_pos
  have hRatioMem := X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero
  have hprodmem : (algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
          / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K))
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mul_mem_simplePoleSubmodule_of_mem hRatioMem hXmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, hprodmem⟩ :=
    Subtype.ext hfact
  rw [heq, (placeInfty K).simplePoleResidueAux_mul_of_mem hRatioMem hXmem,
    residue_placeInfty_X_pow_natDegree_div_monic_eq_one K hpmon, one_mul]

theorem p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K := by
  intro p hpmon hpirr himem
  rw [simplePoleResidueAux_placeInfty_monomial_eq_X K hInfty hpmon hpirr himem]
  exact hX _

end MonicRatioReduction
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ComposedEngine

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyX
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hX)

end ComposedEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Monotonicity

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

namespace IntermediateField
p2m_export "IntermediateField" "charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map"
p2m_open "IntermediateField"

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem finiteDimensional_top : FiniteDimensional ↥(⊤ : IntermediateField K E) E :=
  Module.Finite.of_surjective (Algebra.linearMap (↥(⊤ : IntermediateField K E)) E)
    fun x => ⟨⟨x, mem_top⟩, rfl⟩

theorem adjoin_simple_gen_eq_top (α : E) :
    K⟮AdjoinSimple.gen K α⟯ = (⊤ : IntermediateField K ↥K⟮α⟯) :=
  (K⟮α⟯).lift_injective <| by
    rw [lift_adjoin_simple, AdjoinSimple.coe_gen, lift_top]

theorem transcendental_gen {α : E} (hα : Transcendental K α) :
    Transcendental K (AdjoinSimple.gen K α) := by
  rw [show α = algebraMap K⟮α⟯ E (AdjoinSimple.gen K α) from
    (AdjoinSimple.algebraMap_gen K α).symm] at hα
  exact (transcendental_algebraMap_iff (algebraMap K⟮α⟯ E).injective).mp hα

end IntermediateField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

section PurelyTranscendentalSimple

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsPurelyTranscendentalSimple : Prop :=
  ∃ t : F, Transcendental K t ∧ K⟮t⟯ = (⊤ : IntermediateField K F)

variable {K F}

theorem hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple
    (h : IsPurelyTranscendentalSimple K F) :
    HasSeparatingTranscendentalCore K F := by
  obtain ⟨t, ht, htop⟩ := h
  haveI : FiniteDimensional ↥(⊤ : IntermediateField K F) F :=
    IntermediateField.finiteDimensional_top
  exact ⟨t, ht, IntermediateField.finiteDimensional_of_eq htop.symm⟩

end PurelyTranscendentalSimple
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SelfAdjoinInstance

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem isPurelyTranscendentalSimple_adjoin_simple {α : E} (hα : Transcendental K α) :
    IsPurelyTranscendentalSimple K ↥K⟮α⟯ :=
  ⟨AdjoinSimple.gen K α, IntermediateField.transcendental_gen hα,
    IntermediateField.adjoin_simple_gen_eq_top α⟩

end SelfAdjoinInstance
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AdjoinTowerComposites

variable {K E F' : Type*} [Field K] [Field E] [Field F']
variable [Algebra K E] [Algebra K F']

end AdjoinTowerComposites
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

def CanonicalLocalResidueKSimplePoleCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK),
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1

end NamedRow
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SATGate

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end SATGate
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1XAtom_mul_differentialCoeff_dX_eq_neg :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹) := by
  show algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
        * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹)
  rw [show (dX K) = KaehlerDifferential.D K (RatFunc K) RatFunc.X from rfl,
    differentialCoeff_placeInfty_D_X_eq K, RatFunc.algebraMap_X, map_one, pow_one, inv_inv,
    one_div]
  field_simp [RatFunc.X_ne_zero (K := K), sq, mul_comm]

end XInvCoordinate
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section InftyXDischarge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_residueField_one :
    Algebra.trace K (placeInfty K).ResidueField 1 = 1 := by
  rw [show (1 : (placeInfty K).ResidueField) = algebraMap K _ 1 from (map_one _).symm,
    Algebra.trace_algebraMap, show Module.finrank K (placeInfty K).ResidueField = 1 from
      deg_placeInfty K, one_smul]

theorem simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = -1 := by

  set R := (placeInfty K).canonicalLocalResidueDataKOfExtend
  rw [← (placeInfty K).localResidueData_res_eq_simplePoleResidueAux R.toLocalResidueData himem,
    show R.toLocalResidueData.res = R.res from rfl,
    p1XAtom_mul_differentialCoeff_dX_eq_neg K, _root_.map_neg,
    hsp (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R]

theorem p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PlaceInftySimplePoleResidueEulerValueX K := by
  intro himem
  rw [simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one K hsp himem, _root_.map_neg,
    trace_placeInfty_residueField_one K]

end InftyXDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ComposedEngine

variable (K) [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyX K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K hsp)

end ComposedEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Monotonicity

variable (K) [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

namespace IntermediateField
p2m_export "IntermediateField" "charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map"
p2m_open "IntermediateField"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem adjoin_simple_map_algHom' (e : F →ₐ[K] F') (t : F) :
    (K⟮t⟯).map e = K⟮e t⟯ := by
  rw [adjoin_map, Set.image_singleton]

theorem adjoin_simple_eq_top_of_algEquiv (e : F ≃ₐ[K] F') {t : F}
    (htop : K⟮t⟯ = (⊤ : IntermediateField K F)) :
    K⟮e t⟯ = (⊤ : IntermediateField K F') := by
  have key : K⟮(e : F →ₐ[K] F') t⟯ = (⊤ : IntermediateField K F') := by
    rw [← adjoin_simple_map_algHom' (e : F →ₐ[K] F') t, htop,
      ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top]
  exact key

end IntermediateField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem IsPurelyTranscendentalSimple.congr (e : F ≃ₐ[K] F')
    (h : IsPurelyTranscendentalSimple K F) : IsPurelyTranscendentalSimple K F' := by
  obtain ⟨t, ht, htop⟩ := h
  refine ⟨e t, ?_, IntermediateField.adjoin_simple_eq_top_of_algEquiv e htop⟩
  unfold Transcendental at ht ⊢
  rw [show (e t : F') = (e : F →ₐ[K] F') t from rfl,
    isAlgebraic_algHom_iff (e : F →ₐ[K] F') e.injective]
  exact ht

end Congr
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section RatFuncInstance

variable (K : Type*) [Field K]

theorem isPurelyTranscendentalSimple_ratFunc :
    IsPurelyTranscendentalSimple K (RatFunc K) :=
  (isPurelyTranscendentalSimple_adjoin_simple (RatFunc.transcendental_X (K := K))).congr
    (RatFunc.algEquivOfTranscendental (RatFunc.X : RatFunc K)
      (RatFunc.transcendental_X (K := K))).symm

end RatFuncInstance
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Iff

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isPurelyTranscendentalSimple_of_ratFuncAlgEquiv
    (h : Nonempty (RatFunc K ≃ₐ[K] F)) : IsPurelyTranscendentalSimple K F :=
  (isPurelyTranscendentalSimple_ratFunc K).congr h.some

end Iff
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section CharZeroReflection

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CharZeroReflection
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :
    v.DCoordGenerates := by
  constructor
  rw [eq_top_iff,
    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)
      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),
    Submodule.span_le]
  rintro _ ⟨f, rfl⟩

  have hDf : KaehlerDifferential.D K v.toValuationSubring f
      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top
  rw [← hspan v] at hDf
  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘
        KaehlerDifferential.D K v.toValuationSubring) f
      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)
        (Submodule.span v.toValuationSubring _) :=
    Submodule.mem_map_of_mem hDf
  rw [Submodule.map_span, Set.image_singleton,
    v.kaehlerMap_subring_D_uniformizer] at hmap

  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero hfin) v

end AbstractEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ChainComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (h : IsPurelyTranscendentalSimple K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    (valSubringKaehlerFinite_of_core
      (hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple h)) v

end ChainComposites
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

theorem gate_dCoordGenerates_of_ratFunc_sat
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hRat : Nonempty (RatFunc K ≃ₐ[K] F)) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    (isPurelyTranscendentalSimple_of_ratFuncAlgEquiv hRat) v

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace"
p2m_open "AlgebraicCurve.RationalFunctionField"

variable {K : Type*} [Field K]

scoped instance (priority := low) instDCoordGenerates [CharZero K] (v : Place K (RatFunc K)) :
    v.DCoordGenerates :=
  ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section TransportTwoRoutes

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

end TransportTwoRoutes
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ConsumerDemonstrations

variable {K : Type*} [Field K] [CharZero K]

end ConsumerDemonstrations
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

section RatBasePinned

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatBasePinned
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section RatBaseCrossing

end RatBaseCrossing
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudits

end AxiomAudits
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Uniqueness
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Profile

variable (K : Type*) [Field K]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]

theorem ordDifferential_dX_of_ne_placeInfty {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX K v hv

theorem ordDifferential_dX_placeInfty :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K (ordDifferentialWellDefined_ratFunc K)

theorem exists_divisor_smul_dX {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty K hne, Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end ProfileValues
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Instance

variable [CharZero K]

scoped instance instHasCanonicalDivisorRatFunc :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end Instance
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ExactDivisor

variable [CharZero K] [DecidableEq (RatFunc K)]

end ExactDivisor
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end Profile
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section RatDiamond

end RatDiamond
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve IntermediateField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section KaehlerToolbox

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem D_pow_succ_inv (f : F) (m : ℕ) :
    KaehlerDifferential.D K F ((f ^ (m + 1))⁻¹)
      = (-((m + 1 : ℕ) : F) * (f ^ (m + 2))⁻¹) • KaehlerDifferential.D K F f := by
  rw [← inv_pow f (m + 1), Derivation.leibniz_pow, Derivation.leibniz_inv, Nat.add_sub_cancel,
    smul_smul, ← Nat.cast_smul_eq_nsmul F (m + 1), smul_smul, ← inv_pow f (m + 2)]
  congr 1
  push_cast
  ring

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq ord_prod"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_add'' [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

p2m_export "AlgebraicCurve.Place" "differentialCoeff_add''"
private theorem _root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (m : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F ((v.uniformizer ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (v.uniformizer ^ (m + 2))⁻¹ := by
  rw [D_pow_succ_inv, show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
    v.differentialCoeff_smul, v.differentialCoeff_dCoord, mul_one]

p2m_export "AlgebraicCurve.Place" "differentialCoeff_D_uniformizer_pow_inv"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end KaehlerToolbox
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section DXCoeffIntegrality

variable {K : Type*} [Field K]

theorem ratFuncDXCoeff_eq_of_D_eq_smul_dX {f e : RatFunc K}
    (h : KaehlerDifferential.D K (RatFunc K) f = e • dX K) : ratFuncDXCoeff K f = e := by
  have key : (ratFuncDXCoeff K f - e) • dX K = 0 := by
    rw [sub_smul, ← D_eq_ratFuncDXCoeff_smul_dX K f, h, sub_self]
  rcases smul_eq_zero.mp key with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (dX_ne_zero K)

theorem ratFuncDXCoeff_zero : ratFuncDXCoeff K (0 : RatFunc K) = 0 :=
  ratFuncDXCoeff_eq_of_D_eq_smul_dX (by rw [_root_.map_zero, zero_smul])

section FinitePlaces

variable {w : HeightOneSpectrum K[X]}

local notation "vw" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : 0 ≤ (vw).ord f) :
    (vw).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (vw).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (vw).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (vw).ord_mul hnum0 (inv_ne_zero hden0),
    (vw).ord_inv, hordn] at hord
  omega

theorem ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {g : RatFunc K}
    (hg : g ≠ 0) (hord : 0 ≤ (vw).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 0 ≤ (vw).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
    wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hWord : 0 ≤ (vw).ord (algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative)) :=
    (vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)
  have hden : (vw).ord (algebraMap K[X] (RatFunc K) g.denom) = 0 :=
    ord_algebraMap_denom_eq_zero_of_ord_nonneg hp hwp hg hord
  have key : (vw).ord (ratFuncDXCoeff K g)
      = (vw).ord (algebraMap K[X] (RatFunc K)
          (g.num.derivative * g.denom - g.num * g.denom.derivative))
        - 2 * (vw).ord (algebraMap K[X] (RatFunc K) g.denom) := by
    rw [ratFuncDXCoeff_def, div_eq_mul_inv,
      (vw).ord_mul hW' (inv_ne_zero (pow_ne_zero 2 hd')), (vw).ord_inv, ← zpow_natCast,
      (vw).ord_zpow]
    push_cast
    ring
  rw [key, hden]
  omega

end FinitePlaces
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section PlaceInftySide

variable [DecidableEq (RatFunc K)]

theorem ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
    {f : RatFunc K} (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (placeInfty K).ord (ratFuncDXCoeff K f) = 2 := by
  obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hf hord
  rw [ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe]
  exact ⟨he0, heord⟩

theorem ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg
    {g : RatFunc K} (hg : g ≠ 0) (hord : 0 ≤ (placeInfty K).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 2 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  rcases eq_or_lt_of_le hord with heq | hlt
  ·
    obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg heq.symm
    have hee := ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe
    rcases he with rfl | h2
    · exact absurd hee hne
    · rw [hee]; exact h2
  ·
    have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
      wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
    have h := ord_placeInfty_ratFuncDXCoeff_ge hg hW
    omega

end PlaceInftySide
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end DXCoeffIntegrality
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section LemmaA

variable {K : Type*} [Field K] [CharZero K]

theorem ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  ·
    refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        hp.separable (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (placeInfty K).uniformizer)
          ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem differentialCoeff_D_eq_ratFuncDXCoeff_div (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem differentialCoeff_D_mem_of_mem (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ := ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le v hg
  rw [differentialCoeff_D_eq_ratFuncDXCoeff_div v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaA
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ExactDifferentialEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq ord_prod"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (N : ℕ) {g : F} (hg : g ∈ v.poleSubmodule N) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  induction N generalizing g with
  | zero =>

    have hg' : g ∈ v.toValuationSubring := by
      have h := (v.mem_poleSubmodule (n := 0) (f := g)).mp hg
      rwa [pow_zero, one_mul] at h
    exact R.res_of_mem _ (hint g hg')
  | succ N ih =>

    obtain ⟨c, hc⟩ := hsurj (v.laurentTailCoeff (N + 1) ⟨g, hg⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
        = v.laurentTailCoeff (N + 1) ⟨g, hg⟩ := by
      rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ ∈ v.poleSubmodule N := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hg hclift
      rwa [v.coe_algebraMap] at h

    have hpeel : R.res (v.differentialCoeff (KaehlerDifferential.D K F
        (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) = 0 := by
      rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
        v.differentialCoeff_smul, v.differentialCoeff_D_uniformizer_pow_inv,
        show algebraMap K F c * (-((N + 1 : ℕ) : F) * (v.uniformizer ^ (N + 2))⁻¹)
            = algebraMap K F (c * -((N + 1 : ℕ) : K)) * (v.uniformizer ^ ((N + 1) + 1))⁻¹ by
          rw [map_mul, _root_.map_neg, map_natCast]; ring]
      exact R.res_algebraMap_mul_uniformizer_pow_inv v (Nat.le_add_left 1 N) _

    have hsplit : R.res (v.differentialCoeff (KaehlerDifferential.D K F g))
        = R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)))
          + R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) := by
      conv_lhs => rw [show g = (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)
          + algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ by ring]
      rw [map_add, v.differentialCoeff_add'', map_add]
    rw [hsplit, ih hrem, hpeel, add_zero]

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (g : F) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule g
  exact CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule v hsurj hint
    R N hN

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj [CharZero K]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn

  have hres : R.res (v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    omega

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {π' : F} (hπ' : v.ord π' = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1 := by
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero

  set w : F := π' * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hπ'0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul hπ'0 (inv_ne_zero hπv0), v.ord_inv, hπ', v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega

  have hπ'_eq : π' = v.uniformizer * w := by
    rw [hw_def, mul_comm π' (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]

  have hD : KaehlerDifferential.D K F π'
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [hπ'_eq]
    exact Derivation.leibniz _ _ _

  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F π')
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, v.differentialCoeff_add'', v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]

  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, hπ'_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end ExactDifferentialEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section RatFuncClauses

variable {K : Type*} [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc
    (v : Place K (RatFunc K)) (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj v hsurj
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R π' hn

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc
    (v : Place K (RatFunc K)) {π' : RatFunc K} (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π') * (π')⁻¹) = 1 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R hπ'

end RatFuncClauses
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

theorem canonicalLocalResidueKSimplePoleCoordIndep_ratFunc (K : Type*) [Field K] [CharZero K]
    [HasCanonicalLocalResidueKStar K (RatFunc K)] :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R => canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc v hπ' R

section PlaceInftyConsumers

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty
    (π' : RatFunc K) (R : (placeInfty K).CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res ((placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc (placeInfty K)
    (surjective_algebraMap_residueField_placeInfty K) π' R hn

theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty K
    (RatFunc.X : RatFunc K)⁻¹ R (Nat.le_add_left 1 n)

theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (placeInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (placeInfty K)
          * (placeInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply, canonicalLocalResidueDataK_res_X_pow_mul_D_X K R n, _root_.map_zero]

end PlaceInftyConsumers
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem surjective_algebraMap_residueField_of_deg_eq_one {F : Type*} [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem surjective_algebraMap_residueField_ratFunc_of_isAlgClosed [IsAlgClosed K]
    (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine surjective_algebraMap_residueField_of_deg_eq_one K _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

variable [IsAlgClosed K]

theorem canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' _ R _ hn =>
    canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc v
      (surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v) π' R hn

end AlgClosedDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section PerfectDCoord

variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace"
p2m_open "AlgebraicCurve.RationalFunctionField"

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end PerfectDCoord
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Profile

variable (K : Type*) [Field K]

section PerfectProfileValues

variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  p1DifferentialCoeffRegularFinite_of_unitFinite (dX_ne_zero K)
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K)

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end PerfectInstance
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section PerfectExactDivisor

variable [PerfectField K] [DecidableEq (RatFunc K)]

end PerfectExactDivisor
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section CharZeroRoutes

variable [CharZero K]

end CharZeroRoutes
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end Profile
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section FiniteFieldReadings

end FiniteFieldReadings
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option maxHeartbeats 1600000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace ModularCurve

namespace MilneAvAg9bRd13T2CoordIndepChar3

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

private theorem _root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : K) ≠ 0) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hmK : ((m + 1 : ℕ) : K) ≠ 0 := by
    rwa [show m + 1 = 1 + m from by omega]

  have hres : R.res (v.differentialCoeff
      (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    rw [neg_ne_zero, ← map_natCast (algebraMap K F) (m + 1)]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr hmK

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

p2m_export "ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3" "ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero"
end MilneAvAg9bRd13T2CoordIndepChar3
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section ChoiceOpacity

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq ord_prod"
p2m_open "AlgebraicCurve.Place"

section BumpConstruction

variable (v : Place K F)

end BumpConstruction
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end ChoiceOpacity
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section CanonicalKResidueTerm

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section SupportMachinery

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

variable (K F)

variable {K F}

section Bridge

variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]

variable [Nontrivial Ω[F⁄K]]

end Bridge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end SupportMachinery
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end CanonicalKResidueTerm
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section RatFuncPlaceInftyClause

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_placeInfty_clause_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueTermKFam Rfam (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (placeInfty K) = 0 := by
  rw [kaehlerResidueTermKFam_apply]
  exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow K (Rfam (placeInfty K)) n

end RatFuncPlaceInftyClause
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section GenericGates

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end GenericGates
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AlgClosedGate

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]

end AlgClosedGate
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

section EulerPerfectField

variable {p : K[X]} [Fact (Irreducible p)]

theorem ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField (hpmon : p.Monic)
    {k : ℕ} (hk : k < p.natDegree - 1) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p)) = 0 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hpmon.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem ag9b12c_trace_root_pow_div_derivative_self_of_perfectField (hpmon : p.Monic)
    (hd : 0 < p.natDegree) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ (p.natDegree - 1) /
        aeval (AdjoinRoot.root p) (derivative p)) = 1 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hpmon.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

private theorem ag9b12c_aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    ag9b12c_aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]
  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (p.natDegree - 1)]
  · rw [ag9b12c_trace_root_pow_div_derivative_self_of_perfectField K hpmon hpd, mul_one]
  · intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField K hpmon hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerPerfectField
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section DerivativeRegular

private theorem ag9b12c_differentialCoeff_add (v : Place K (RatFunc K))
    (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem ag9b12c_differentialCoeff_D_mem_finitePlace {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  · have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge

end DerivativeRegular
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section LeibnizCore

theorem ag9b12c_uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h
  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, ag9b12c_differentialCoeff_add K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  refine mul_mem (ag9b12c_uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge)

theorem ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _
        ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_
  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr
  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    ag9b12c_differentialCoeff_D_mem_finitePlace K hpirr
      (ag9b12c_uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section BridgeDischarge

theorem ag9b12c_residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit
    ((PerfectField.separable_of_irreducible hpirr).isUnit_of_dvd' dvd_rfl hlt')

theorem ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  rw [Place.simplePoleResidueAux_apply,
    eq_div_iff (ag9b12c_residue_algebraMap_derivative_ne_zero K hpirr)]
  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf
  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section TraceValue

theorem ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField K
    p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField K hpmon hdeg]

theorem ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) := by
  intro p c hpmon hpirr hdeg hfmem himem
  rw [ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField K
      hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end TraceValue
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

section LemmaAPerfect

variable {K : Type*} [Field K] [PerfectField K]

theorem ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField
    (v : Place K (RatFunc K)) {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  · refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (placeInfty K).uniformizer)
          ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField
    (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ :=
    ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField v hg
  rw [ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaAPerfect
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SimplePoleRowPerfect

variable (K : Type*) [Field K] [PerfectField K]

theorem ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R =>
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
      (fun _ hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh) R hπ'

end SimplePoleRowPerfect
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ChainPerfect

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueX K :=
  p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K
    (ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K :=
  p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField K)

end ChainPerfect
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

namespace ModularCurve

namespace MilneAvAg9bRd13X113FourRowUpgrade

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPlaneModel P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroFibreDiamond P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroLiteralChordChain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroPlaceDictionary P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroLitPic0Comparison P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113RiemannRochRows P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MazurTate1973Mt31b P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113PackageHeldRowOne P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd9DictionaryHeld3Closure P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113OrdRowWellDefinedReduction P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd10EllKFinUpperRow P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd11X113TowerPowerBasis P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Ag9b11bX113HwdUnitDischarge P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd11DictionaryBinderShrink P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113AssemblyRetirement P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12T1P1InftyResidue P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113LocalDatumMint P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113FiveRowUpgrade"

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

end MilneAvAg9bRd13X113FourRowUpgrade
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section KernelEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [HasPrincipalDivisors K F]

def kaehlerResidueFunctionalK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehlerK Rfam hω).comp (principalAdele K F)

theorem kaehlerResidueFunctionalK_eq_finsum
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F) :
    kaehlerResidueFunctionalK Rfam hω f
      = ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v := rfl

theorem kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  rw [kaehlerResidueFunctionalK_eq_finsum Rfam hω f,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem kaehlerResidueFunctionalK_eq_zero_of_singleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa using hv)
  · simpa using hv₀

theorem kaehlerResidueFunctionalK_eq_zero_of_pair
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀
      + kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₁ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]
    exact hsum

end KernelEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SimplePoleSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} {f : F} {v : Place K F}
    (hmem : f * v.differentialCoeff ω ∈ v.simplePoleSubmodule) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v
      = Algebra.trace K v.ResidueField
          (v.simplePoleResidueAux ⟨f * v.differentialCoeff ω, hmem⟩) := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply,
    (Rfam v).res_simplePole (f * v.differentialCoeff ω) hmem]
  rfl

end SimplePoleSeam
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section SmulReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTermKFam_smul_diagonal
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (g : F) (ω : Ω[F⁄K]) (f : F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam (g • ω) (diagonalHom K F f) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g * f)) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [v.differentialCoeff_smul,
    show f * (g * v.differentialCoeff ω) = g * f * v.differentialCoeff ω by ring]

variable [HasCanonicalDivisor (K := K) (F := F)]

theorem weilOfKaehlerK_smul_diagonal [HasPrincipalDivisors K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehlerK Rfam hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam hω
          ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [weilOfKaehlerK_apply, weilOfKaehlerK_apply]
  exact finsum_congr fun v => kaehlerResidueTermKFam_smul_diagonal Rfam g ω f v

end SmulReduction
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section PerGenerator

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := placeInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n (p1DifferentialCoeffRegularFinite_dX K v hv)))
  ·
    exact residueTheoremK_placeInfty_clause_X_pow Rfam n

theorem kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ placeInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX K v hvinf)))

theorem kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (placeInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (placeInfty K).differentialCoeff (dX K) ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (placeInfty K) = 0 := by

  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg

  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]

  exact p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep K hwd
    (dX_ne_zero K) rfl hsp p c hpmon hpirr hdeg hfmem himem

theorem kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr c m
      hvp hvinf) ?_

  rcases eq_or_lt_of_le hm with rfl | hm2
  ·
    exact kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hsp hpmon hpirr hdeg
  ·
    rw [kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c hdeg hm2,
      add_zero]

theorem kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by

  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact kaehlerResidueFunctionalK_dX_X_pow Rfam n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hsp hHigh5 hpmon hpirr hdeg hm

  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Engine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_subrows
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f

  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (placeInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hsp hHigh5 (g * f)

end Engine
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_isAlgClosed_main : ResidueTheoremK K (RatFunc K) :=
  residueTheoremK_ratFunc_of_subrows
    (ordDifferentialWellDefined_ratFunc K)
    (canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K)
    (canonicalLocalResidueKSimplePoleCoordIndep_ratFunc K)
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section BridgeCorollary

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

end BridgeCorollary
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section MOnePerfect

theorem p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)] :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) :=
  ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField K
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField K)

end MOnePerfect
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section PerGenerator

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := placeInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n
        (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hv)))
  ·
    rw [kaehlerResidueTermKFam_apply]
    exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep K hwd hcoord
      (Rfam (placeInfty K)) n

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ placeInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hvinf)))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (placeInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (placeInfty K).differentialCoeff (dX K) ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (placeInfty K) = 0 := by
  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX_of_perfectField K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg
  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]
  exact p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField K p c hpmon hpirr hdeg hfmem himem

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr
      c m hvp hvinf) ?_
  rcases eq_or_lt_of_le hm with rfl | hm2
  · exact p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hpmon hpirr hdeg
  · rw [p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c
        hdeg hm2,
      add_zero]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by
  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow Rfam hwd hcoord n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hHigh5 hpmon hpirr
        hdeg hm
  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section EngineCharFree

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f
  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (placeInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hHigh5 (g * f)

theorem p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hcoord hHigh5

end EngineCharFree
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section AlgClosedAnyChar

theorem p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField hcoord
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedAnyChar
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Bc2Carrier

local notation "Qbar" => AlgebraicClosure ℚ

end Bc2Carrier
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section ResidualLocation

theorem p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

end ResidualLocation
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq Place.ord_prod"
p2m_open "AlgebraicCurve"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

section CharFreeToolkit

variable {K : Type*} [Field K] [PerfectField K]

theorem p0n22_cpf_uniformizer_pow_mul_mem_cases
    (v : Place K (RatFunc K))
    {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring) {k : ℕ} (hk : 1 ≤ k) :
    v.uniformizer ^ k * σ = 0 ∨ 1 ≤ v.ord (v.uniformizer ^ k * σ) := by
  rcases eq_or_ne σ 0 with rfl | hσ0
  · exact Or.inl (mul_zero _)
  · right
    rw [v.ord_mul (v.uniformizer_pow_ne_zero k) hσ0, v.ord_uniformizer_pow]
    have := v.ord_nonneg_of_mem hσ
    omega

theorem p0n22_cpf_one_add_ne_zero
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    (1 : RatFunc K) + g ≠ 0 := by
  rcases hg with rfl | hord
  · simp
  · intro h
    rw [eq_neg_of_add_eq_zero_right h] at hord
    have hneg : v.ord (-1 : RatFunc K) = 0 := by
      have h2 : v.ord ((-1 : RatFunc K) * (-1)) = v.ord (-1 : RatFunc K)
          + v.ord (-1 : RatFunc K) :=
        v.ord_mul (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
      rw [neg_mul_neg, one_mul, v.ord_one] at h2
      omega
    omega

theorem p0n22_cpf_ord_one_add_eq_zero
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    v.ord ((1 : RatFunc K) + g) = 0 := by
  rcases hg with rfl | hord
  · rw [add_zero, v.ord_one]
  · have hg0 : g ≠ 0 := by
      intro h
      rw [h, v.ord_zero] at hord
      omega
    have h1 := v.ord_add_eq_min (f := (1 : RatFunc K)) (g := g) one_ne_zero hg0
      (by rw [v.ord_one]; omega)
    rw [v.ord_one] at h1
    omega

theorem p0n22_cpf_one_add_inv_mem
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    ((1 : RatFunc K) + g)⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg (inv_ne_zero (p0n22_cpf_one_add_ne_zero v hg)) ?_
  rw [v.ord_inv, p0n22_cpf_ord_one_add_eq_zero v hg, _root_.neg_zero]

theorem p0n22_cpf_logDeriv_mul
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w₁ w₂ : RatFunc K} (h1 : w₁ ≠ 0) (h2 : w₂ ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) (w₁ * w₂))
        * (w₁ * w₂)⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₁) * w₁⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₂)
            * w₂⁻¹ := by
  rw [Derivation.leibniz, v.differentialCoeff_add'', v.differentialCoeff_smul,
    v.differentialCoeff_smul]
  have hc1 : w₁ * w₁⁻¹ = 1 := mul_inv_cancel₀ h1
  have hc2 : w₂ * w₂⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination
    (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₂) * w₂⁻¹)
      * hc1
    + (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₁) * w₁⁻¹)
      * hc2

theorem p0n22_cpf_logDeriv_mem
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹
      ∈ v.toValuationSubring := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword, _root_.neg_zero]
  exact mul_mem (ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hwmem) hwinv

theorem p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] (a : K) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        ((1 : RatFunc K)
          + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
      = algebraMap K (RatFunc K) a
        * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.map_algebraMap, smul_zero, add_zero, Derivation.leibniz_pow,
    show KaehlerDifferential.D K (RatFunc K) v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul (RatFunc K) k, smul_smul, smul_smul, mul_assoc]

theorem p0n22_cpf_differentialCoeff_D_one_add_pow_mul
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] (σ : RatFunc K) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        ((1 : RatFunc K) + v.uniformizer ^ k * σ))
      = v.uniformizer ^ k
          * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  conv_lhs => rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.leibniz_pow,
    show KaehlerDifferential.D K (RatFunc K) v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul (RatFunc K) k,
    ← v.differentialCoeff_smul_dCoord
      (KaehlerDifferential.D K (RatFunc K) σ),
    smul_smul, smul_smul, smul_smul, ← add_smul]
  exact congrArg (· • v.dCoord) (by ring)

theorem p0n22_cpf_exists_residue_lift_decomp
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {r : RatFunc K} (hr : r ∈ v.toValuationSubring) :
    ∃ (d : K) (r' : RatFunc K), r' ∈ v.toValuationSubring ∧
      r = algebraMap K (RatFunc K) d + v.uniformizer * r' := by
  obtain ⟨d, hd⟩ := hsurj (IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring))
  have hxmem : r - algebraMap K (RatFunc K) d ∈ v.toValuationSubring :=
    sub_mem hr (v.algebraMap_mem' d)
  have hres0 : IsLocalRing.residue _
      (⟨r - algebraMap K (RatFunc K) d, hxmem⟩ : v.toValuationSubring)
      = 0 := by
    have hfact : (⟨r - algebraMap K (RatFunc K) d, hxmem⟩
        : v.toValuationSubring)
        = ⟨r, hr⟩ - algebraMap K v.toValuationSubring d :=
      Subtype.ext (by push_cast [v.coe_algebraMap]; ring)
    have h2 : IsLocalRing.residue _ (algebraMap K v.toValuationSubring d)
        = IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring) := by
      rw [← hd, IsScalarTower.algebraMap_apply K v.toValuationSubring
        v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, h2, sub_self]
  rcases _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
      v hxmem hres0 with hx0 | hxord
  · exact ⟨d, 0, zero_mem _, by rw [mul_zero, add_zero]; exact (sub_eq_zero.mp hx0)⟩
  · have hxne : r - algebraMap K (RatFunc K) d ≠ 0 := by
      intro h0
      rw [h0, v.ord_zero] at hxord
      omega
    refine ⟨d, v.uniformizer⁻¹ * (r - algebraMap K (RatFunc K) d), ?_, ?_⟩
    · refine v.mem_of_ord_nonneg
        (mul_ne_zero (inv_ne_zero v.uniformizer_ne_zero) hxne) ?_
      rw [v.ord_mul (inv_ne_zero v.uniformizer_ne_zero) hxne, v.ord_inv,
        v.ord_uniformizer]
      omega
    · rw [← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
      ring

theorem p0n22_cpf_exists_elementary_peel
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {k : ℕ} (hk : 1 ≤ k) {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring) :
    ∃ (a : K) (τ : RatFunc K), τ ∈ v.toValuationSubring ∧
      (1 : RatFunc K) + v.uniformizer ^ k * σ
        = ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)
          * ((1 : RatFunc K) + v.uniformizer ^ (k + 1) * τ) := by
  obtain ⟨a, σ', hσ', hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hσ
  have hgcase : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have he0 : (1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have heinv : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  refine ⟨a, σ' * ((1 : RatFunc K)
    + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹,
    mul_mem hσ' heinv, ?_⟩
  have hce : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)
      * ((1 : RatFunc K)
          + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ he0
  rw [hdec]
  linear_combination (-(v.uniformizer ^ (k + 1) * σ')) * hce

theorem p0n22_cpf_exists_laurent_expansion_one
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (f : RatFunc K) :
    ∃ (s : Finset ℤ) (c : ℤ → K) (r : RatFunc K),
      r ∈ v.toValuationSubring ∧
      f = (∑ j ∈ s, c j • v.uniformizer ^ j) + v.uniformizer * r := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule f
  obtain ⟨c0, hc0⟩ :=
    _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule
      v hsurj N hN
  obtain ⟨d, r, hr, hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hc0
  refine ⟨insert (0 : ℤ) ((Finset.range N).image fun j : ℕ => -((j : ℤ) + 1)),
    fun t => if t = 0 then d else c0 (-(t + 1)).toNat, r, hr, ?_⟩
  have h0not : (0 : ℤ) ∉ (Finset.range N).image (fun j : ℕ => -((j : ℤ) + 1)) := by
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨j, _, hj⟩
    omega
  have hinj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N,
      -((x : ℤ) + 1) = -((y : ℤ) + 1) → x = y := fun x _ y _ h => by omega
  have himg : ∀ j ∈ Finset.range N,
      (if -((j : ℤ) + 1) = 0 then d else c0 (-(-((j : ℤ) + 1) + 1)).toNat)
          • v.uniformizer ^ (-((j : ℤ) + 1))
        = algebraMap K (RatFunc K) (c0 j)
            * (v.uniformizer ^ (j + 1))⁻¹ := by
    intro j _
    rw [if_neg (by omega : ¬(-((j : ℤ) + 1) = (0 : ℤ))),
      show (-(-((j : ℤ) + 1) + 1)).toNat = j from by omega,
      Algebra.smul_def, _root_.zpow_neg,
      show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  rw [Finset.sum_insert h0not, Finset.sum_image hinj, Finset.sum_congr rfl himg,
    show ((fun t : ℤ => if t = 0 then d else c0 (-(t + 1)).toNat) 0) = d from by simp,
    zpow_zero, Algebra.smul_def, mul_one]
  linear_combination hdec

theorem p0n22_cpf_res_geom_core
    (v : Place K (RatFunc K)) (R : v.CanonicalLocalResidueDataK)
    (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = if k ∣ q
        then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
        else 0 := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hgcase : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have hu0 : (1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have huinv : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  have hgeom : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      = (∑ t ∈ Finset.range q,
          (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t)
        + (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹ := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
    have hgs := geom_sum_mul
      (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) q
    linear_combination -hgs
  rw [hgeom, mul_add, add_mul, map_add]
  have htail : R.res ((algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
      * ((-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹))
      * (v.uniformizer ^ q)⁻¹) = 0 := by
    apply R.res_of_mem
    have hqle : q ≤ k * q := Nat.le_of_dvd (Nat.mul_pos hk hq) (dvd_mul_left q k)
    have hpowsplit : (v.uniformizer : RatFunc K) ^ (k * q)
        = v.uniformizer ^ (k * q - q) * v.uniformizer ^ q := by
      rw [← pow_add, Nat.sub_add_cancel hqle]
    have hxq : (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
        = algebraMap K (RatFunc K) ((-a) ^ q)
          * (v.uniformizer ^ (k * q - q) * v.uniformizer ^ q) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K (RatFunc K) a * v.uniformizer ^ k)
            = -algebraMap K (RatFunc K) a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul, hpowsplit]
    have hcc : (v.uniformizer : RatFunc K) ^ q
        * ((v.uniformizer : RatFunc K) ^ q)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hπ0)
    have heq : (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
        * ((-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
            * ((1 : RatFunc K)
                + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹))
        * (v.uniformizer ^ q)⁻¹
        = algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
          * (algebraMap K (RatFunc K) ((-a) ^ q)
              * v.uniformizer ^ (k * q - q)
              * ((1 : RatFunc K)
                  + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹) := by
      rw [hxq]
      linear_combination (algebraMap K (RatFunc K) a
        * v.uniformizer ^ (k - 1)
        * (algebraMap K (RatFunc K) ((-a) ^ q)
            * v.uniformizer ^ (k * q - q)
            * ((1 : RatFunc K)
                + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹)) * hcc
    rw [heq]
    exact mul_mem (mul_mem (v.algebraMap_mem' a) (pow_mem v.uniformizer_mem _))
      (mul_mem (mul_mem (v.algebraMap_mem' _) (pow_mem v.uniformizer_mem _)) huinv)
  have hterm : (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
      * (∑ t ∈ Finset.range q,
          (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t))
      * (v.uniformizer ^ q)⁻¹
      = ∑ t ∈ Finset.range q, (a * (-a) ^ t)
          • v.uniformizer ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hxt : (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t
        = algebraMap K (RatFunc K) ((-a) ^ t)
          * v.uniformizer ^ (k * t) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K (RatFunc K) a * v.uniformizer ^ k)
            = -algebraMap K (RatFunc K) a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul]
    rw [hxt, Algebra.smul_def, map_mul, map_pow, _root_.map_neg,
      show (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)
          = ((k - 1 : ℕ) : ℤ) + ((k * t : ℕ) : ℤ) + -((q : ℕ) : ℤ) from by
        push_cast [Nat.cast_sub hk]
        ring,
      zpow_add₀ hπ0, zpow_add₀ hπ0, zpow_natCast, zpow_natCast, _root_.zpow_neg, zpow_natCast]
    ring
  rw [hterm, map_sum]
  simp only [map_smul]
  by_cases hdvd : k ∣ q
  · rw [if_pos hdvd, htail, add_zero]
    obtain ⟨e, rfl⟩ := hdvd
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hq
    · rw [Nat.mul_div_cancel_left e hk]
      have he_lt : e - 1 < k * e := by
        have h1 : e ≤ k * e := Nat.le_of_dvd (Nat.mul_pos hk he1) (dvd_mul_left e k)
        omega
      have hother : ∀ t ∈ Finset.range (k * e), t ≠ e - 1 →
          (a * (-a) ^ t) • R.res ((v.uniformizer : RatFunc K)
            ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ))) = 0 := by
        intro t _ htne
        have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) ≠ -1 := by
          intro hcontra
          have h2 : (k : ℤ) * ((t : ℤ) + 1) = (k : ℤ) * (e : ℤ) := by
            push_cast at hcontra
            linarith
          have hk0 : (k : ℤ) ≠ 0 := by omega
          have h3 : (t : ℤ) + 1 = (e : ℤ) := mul_left_cancel₀ hk0 h2
          omega
        rw [_root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R hne, smul_zero]
      rw [Finset.sum_eq_single_of_mem (e - 1) (Finset.mem_range.mpr he_lt) hother,
        show (k : ℤ) * (((e - 1 : ℕ) : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) = -1 from by
          push_cast [Nat.cast_sub he1]
          ring,
        _root_.zpow_neg, zpow_one, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one]
  · rw [if_neg hdvd, htail, add_zero]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ) ≠ -1 := by
      intro hcontra
      have h2 : (k : ℤ) * ((t : ℤ) + 1) = (q : ℤ) := by linarith
      have h3 : k * (t + 1) = q := by exact_mod_cast h2
      exact hdvd ⟨t + 1, h3.symm⟩
    rw [_root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
      v R hne, smul_zero]

theorem p0n22_cpf_res_logDeriv_elementary
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = ((k : ℕ) : K) • (if k ∣ q
          then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
          else 0) := by
  rw [p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow v a k]
  have hsplit : algebraMap K (RatFunc K) a
        * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = ((k : ℕ) : K) • (algebraMap K (RatFunc K) a
          * v.uniformizer ^ (k - 1)
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
          * (v.uniformizer ^ q)⁻¹) := by
    rw [Algebra.smul_def, map_natCast]
    ring
  rw [hsplit, map_smul, p0n22_cpf_res_geom_core v R a hk hq]

theorem p0n22_cpf_res_logDeriv_highLevel_vanish
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK)
    {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring)
    {k q : ℕ} (hbig : q + 1 ≤ k) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K) + v.uniformizer ^ k * σ))
        * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹) = 0 := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hgcase := p0n22_cpf_uniformizer_pow_mul_mem_cases v hσ
    (show 1 ≤ k by omega)
  have huinv := p0n22_cpf_one_add_inv_mem v hgcase
  have hσ' : v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
      ∈ v.toValuationSubring :=
    ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hσ
  have hkF : ((k : ℕ) : RatFunc K) ∈ v.toValuationSubring := by
    rw [← map_natCast (algebraMap K (RatFunc K))]
    exact v.algebraMap_mem' _
  obtain ⟨e, rfl⟩ : ∃ e, k = q + 1 + e := ⟨k - (q + 1), by omega⟩
  apply R.res_of_mem
  rw [p0n22_cpf_differentialCoeff_D_one_add_pow_mul v σ (q + 1 + e)]
  have hcc : (v.uniformizer : RatFunc K) ^ q
      * ((v.uniformizer : RatFunc K) ^ q)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hπ0)
  have heq : (v.uniformizer ^ (q + 1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ (q + 1 + e - 1)))
        * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = (v.uniformizer ^ (1 + e)
          * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
          + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ e))
        * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹ := by
    rw [show q + 1 + e - 1 = q + e from by omega]
    linear_combination ((v.uniformizer ^ (1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ e))
      * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹) * hcc
  rw [heq]
  exact mul_mem (add_mem (mul_mem (pow_mem v.uniformizer_mem _) hσ')
    (mul_mem hσ (mul_mem hkF (pow_mem v.uniformizer_mem _)))) huinv

theorem p0n22_cpf_row_integrand_eq_pow_mul_dlog
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w : RatFunc K} (hw0 : w ≠ 0) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (k + 1))⁻¹
      = (w ^ k * v.uniformizer ^ k)⁻¹
        * ((v.uniformizer)⁻¹
            + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹) := by
  rw [_root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    v w]
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hcw : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hcπ : (v.uniformizer : RatFunc K) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  linear_combination ((w ^ k)⁻¹ * (v.uniformizer ^ (k + 1))⁻¹) * hcw
    + (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
        * (w ^ (k + 1))⁻¹ * (v.uniformizer ^ k)⁻¹) * hcπ

end CharFreeToolkit
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section CharPCartier

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [PerfectField K] [hKp : CharP K p]

theorem p0n22_cpf_res_logDeriv_elementary_cartier
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ (p * n))⁻¹)
      = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  rw [p0n22_cpf_res_logDeriv_elementary v R a hk (Nat.mul_pos hp.out.pos hn),
    p0n22_cpf_res_logDeriv_elementary v R a hk hn]
  by_cases hdn : k ∣ n
  · rw [if_pos (hdn.mul_left p), if_pos hdn]
    obtain ⟨e, rfl⟩ := hdn
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hn
    · rw [show p * (k * e) / k = p * e from by
          rw [show p * (k * e) = k * (p * e) from by ring, Nat.mul_div_cancel_left _ hk],
        Nat.mul_div_cancel_left e hk]
      have key : ∀ m : ℕ, 1 ≤ m → a * (-a) ^ (m - 1) = -((-a) ^ m) := by
        intro m hm
        obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
        rw [show 1 + m' - 1 = m' from by omega, show 1 + m' = m' + 1 from by omega,
          pow_succ]
        ring
      have hneg : (-((-a) ^ e) : K) ^ p = -(((-a) ^ e) ^ p) := by
        rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_char K p, neg_one_mul]
      have hxp : (a * (-a) ^ (e - 1)) ^ p = a * (-a) ^ (p * e - 1) := by
        rw [key e he1, key (p * e) (Nat.mul_pos hp.out.pos he1), hneg, ← pow_mul,
          mul_comm e p]
      have hfix : ((k : ℕ) : v.ResidueField) ^ p = ((k : ℕ) : v.ResidueField) := by
        have h := map_natCast (frobenius v.ResidueField p) k
        rwa [frobenius_def] at h
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast (algebraMap K v.ResidueField) k,
        mul_pow, hfix, ← map_pow, hxp]
  · by_cases hdp : k ∣ p * n
    · have hpk : p ∣ k := by
        by_contra hpk
        exact hdn ((((hp.out.coprime_iff_not_dvd).mpr hpk).symm).dvd_mul_left.mp hdp)
      have hk0 : ((k : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p k).mpr hpk
      rw [hk0, zero_smul, zero_smul, zero_pow hp.out.ne_zero]
    · rw [if_neg hdp, if_neg hdn, smul_zero, zero_pow hp.out.ne_zero]

theorem p0n22_cpf_res_logDeriv_principalUnit_cartier_aux
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    ∀ d k : ℕ, 1 ≤ k → p * n + 1 ≤ k + d →
      ∀ σ : RatFunc K, σ ∈ v.toValuationSubring →
        R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              ((1 : RatFunc K) + v.uniformizer ^ k * σ))
            * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ (p * n))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              ((1 : RatFunc K) + v.uniformizer ^ k * σ))
            * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  intro d
  induction d with
  | zero =>
    intro k hk hbound σ hσ
    have hnp : n ≤ p * n := Nat.le_mul_of_pos_left n hp.out.pos
    rw [p0n22_cpf_res_logDeriv_highLevel_vanish v R hσ (show p * n + 1 ≤ k by omega),
      p0n22_cpf_res_logDeriv_highLevel_vanish v R hσ (show n + 1 ≤ k by omega),
      zero_pow hp.out.ne_zero]
  | succ d ihd =>
    intro k hk hbound σ hσ
    obtain ⟨a, τ, hτ, hfac⟩ := p0n22_cpf_exists_elementary_peel v hsurj hk hσ
    have hgcase1 : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
        ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
      rw [mul_comm]
      exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
    have h1 : (1 : RatFunc K)
        + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase1
    have hgcase2 := p0n22_cpf_uniformizer_pow_mul_mem_cases v hτ
      (show 1 ≤ k + 1 by omega)
    have h2 : (1 : RatFunc K) + v.uniformizer ^ (k + 1) * τ ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase2
    rw [hfac, p0n22_cpf_logDeriv_mul v h1 h2, add_mul, add_mul, LinearMap.map_add,
      LinearMap.map_add, p0n22_cpf_res_logDeriv_elementary_cartier v R a hk hn,
      ihd (k + 1) (by omega) (by omega) τ hτ, ← add_pow_char]

theorem p0n22_cpf_res_zpow_mul_logDeriv_cartier
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) (j : ℤ) :
    R.res (v.uniformizer ^ ((p : ℤ) * j)
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))
      = (R.res (v.uniformizer ^ j
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))) ^ p := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hw0 hword
  rcases le_or_gt 0 j with hj | hj
  · have hmem : ∀ i : ℤ, 0 ≤ i → v.uniformizer ^ i
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹) ∈ v.toValuationSubring := by
      intro i hi
      refine mul_mem ?_ hL
      refine v.mem_of_ord_nonneg (zpow_ne_zero i hπ0) ?_
      rw [v.ord_zpow, v.ord_uniformizer, mul_one]
      exact hi
    rw [R.res_of_mem _ (hmem _ (mul_nonneg (Int.natCast_nonneg p) hj)),
      R.res_of_mem _ (hmem _ hj), zero_pow hp.out.ne_zero]
  · obtain ⟨c, s, hc0, hs, hwfac⟩ :=
      _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj
        v hsurj hw0 hword
    have hcF : algebraMap K (RatFunc K) c ≠ 0 := fun h =>
      hc0 ((algebraMap K (RatFunc K)).injective
        (h.trans (_root_.map_zero _).symm))
    have h1s : (1 : RatFunc K) + s ≠ 0 := by
      intro h0
      exact hw0 (by rw [hwfac, h0, mul_zero])
    have hLw : v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
        * w⁻¹
        = v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
            ((1 : RatFunc K) + s)) * ((1 : RatFunc K) + s)⁻¹ := by
      rw [hwfac, p0n22_cpf_logDeriv_mul v hcF h1s, Derivation.map_algebraMap,
        v.differentialCoeff_zero, zero_mul, zero_add]
    rcases hs with rfl | hsord
    · rw [hLw, add_zero, Derivation.map_one_eq_zero, v.differentialCoeff_zero, zero_mul,
        mul_zero, mul_zero, _root_.map_zero, zero_pow hp.out.ne_zero]
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, v.ord_zero] at hsord
        omega
      have hσmem : v.uniformizer⁻¹ * s ∈ v.toValuationSubring := by
        refine v.mem_of_ord_nonneg (mul_ne_zero (inv_ne_zero hπ0) hs0) ?_
        rw [v.ord_mul (inv_ne_zero hπ0) hs0, v.ord_inv, v.ord_uniformizer]
        omega
      obtain ⟨n', rfl⟩ : ∃ n' : ℕ, j = -(n' : ℤ) := ⟨(-j).toNat, by omega⟩
      have hn1 : 1 ≤ n' := by omega
      rw [hLw, show (p : ℤ) * -(n' : ℤ) = -((p * n' : ℕ) : ℤ) from by push_cast; ring,
        _root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast,
        show s = v.uniformizer ^ 1 * (v.uniformizer⁻¹ * s) from by
          rw [pow_one, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul],
        mul_comm ((v.uniformizer ^ (p * n') : RatFunc K)⁻¹) _,
        mul_comm ((v.uniformizer ^ n' : RatFunc K)⁻¹) _]
      exact p0n22_cpf_res_logDeriv_principalUnit_cartier_aux v hsurj R hn1 (p * n') 1
        le_rfl (by omega) _ hσmem

theorem p0n22_cpf_res_pow_mul_dlog_unit
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) (f : RatFunc K) :
    R.res (f ^ p * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))
      = (R.res (f * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))) ^ p := by
  haveI : CharP (RatFunc K) p :=
    charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hw0 hword
  obtain ⟨s, c, r, hr, hf⟩ := p0n22_cpf_exists_laurent_expansion_one v hsurj f
  have hππ : (v.uniformizer : RatFunc K) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  have hLHS : f ^ p * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) ^ p * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j) ^ p
            * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹)
          + (v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
            + v.uniformizer ^ p * r ^ p
                * (v.differentialCoeff
                    (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹))) := by
    rw [hf, add_pow_char, mul_pow]
    ring
  have hRHS : f * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j)
            * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹)
          + (r + v.uniformizer * r
              * (v.differentialCoeff
                  (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹))) := by
    rw [hf]
    linear_combination r * hππ
  have hπp : (v.uniformizer : RatFunc K) ^ p
      = v.uniformizer ^ (p - 1) * v.uniformizer := by
    conv_lhs => rw [show p = (p - 1) + 1 from by have h2 := hp.out.two_le; omega]
    rw [pow_succ]
  have hm1 : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹ ∈ v.toValuationSubring := by
    have heq : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
        = v.uniformizer ^ (p - 1) * r ^ p := by
      rw [hπp]
      linear_combination v.uniformizer ^ (p - 1) * r ^ p * hππ
    rw [heq]
    exact mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)
  have hm2 : v.uniformizer ^ p * r ^ p
      * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)) hL
  have hm3 : v.uniformizer * r
      * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem v.uniformizer_mem hr) hL
  have hpowp : ∀ j : ℤ, ((v.uniformizer : RatFunc K) ^ j) ^ p
      = v.uniformizer ^ ((p : ℤ) * j) := by
    intro j
    rw [← zpow_natCast ((v.uniformizer : RatFunc K) ^ j) p, ← zpow_mul,
      mul_comm j (p : ℤ)]
  have hPp : (∑ j ∈ s, c j • (v.uniformizer : RatFunc K) ^ j) ^ p
      = ∑ j ∈ s, (c j ^ p) • (v.uniformizer : RatFunc K) ^ ((p : ℤ) * j) := by
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun j _ => by rw [_root_.smul_pow, hpowp j]
  rw [hLHS, hRHS]
  simp only [map_add]
  rw [R.res_of_mem _ hm1, R.res_of_mem _ hm2, R.res_of_mem _ hr, R.res_of_mem _ hm3]
  simp only [add_zero]
  rw [add_pow_char]
  congr 1
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul]
    rcases eq_or_ne j 0 with rfl | hj
    · rw [mul_zero, zpow_zero, one_mul,
        gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]
    · have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
      have h1 : R.res ((v.uniformizer : RatFunc K) ^ ((p : ℤ) * j)
          * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        refine _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R ?_
        intro hcontra
        have hpj : (p : ℤ) * j = 0 := by linarith
        rcases mul_eq_zero.mp hpj with h | h
        · exact hp0 h
        · exact hj h
      have h2 : R.res ((v.uniformizer : RatFunc K) ^ j * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        exact _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R (by omega)
      rw [h1, h2, smul_zero, smul_zero, zero_pow hp.out.ne_zero]
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      p0n22_cpf_res_zpow_mul_logDeriv_cartier v hsurj R hw0 hword j,
      Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow]

include hp hKp in

theorem p0n22_cpf_res_row_at_unit_mul_uniformizer
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    ∀ n : ℕ, 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (n + 1))⁻¹) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hmlt : m < p * m := by
        have h2m : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.out.two_le
        omega
      have hstep : R.res (v.differentialCoeff (KaehlerDifferential.D K
            (RatFunc K) (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (p * m + 1))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (m + 1))⁻¹)) ^ p := by
        rw [p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 (p * m),
          p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 m]
        have hfp : ((w ^ m * v.uniformizer ^ m : RatFunc K)⁻¹) ^ p
            = (w ^ (p * m) * v.uniformizer ^ (p * m))⁻¹ := by
          rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m p]
        rw [← hfp]
        exact p0n22_cpf_res_pow_mul_dlog_unit v hsurj R hw0 hword
          ((w ^ m * v.uniformizer ^ m)⁻¹)
      rw [hstep, ih m hmlt hm1, zero_pow hp.out.ne_zero]
    · have hnK : ((n : ℕ) : K) ≠ 0 := fun h =>
        hpn ((CharP.cast_eq_zero_iff K p n).mp h)
      exact _root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
        v hsurj
        (fun h hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh)
        R (w * v.uniformizer) hn hnK

include hp hKp in

theorem p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 := by
  have hπ'0 : π' ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at hπ'
    omega
  have hw0 : π' * (v.uniformizer)⁻¹ ≠ 0 :=
    mul_ne_zero hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
  have hword : v.ord (π' * (v.uniformizer)⁻¹) = 0 := by
    have h1 := v.ord_mul hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
    rw [v.ord_inv, hπ', v.ord_uniformizer] at h1
    omega
  have hrec : π' * (v.uniformizer)⁻¹ * v.uniformizer = π' := by
    rw [mul_assoc, inv_mul_cancel₀ v.uniformizer_ne_zero, mul_one]
  have h := p0n22_cpf_res_row_at_unit_mul_uniformizer v hsurj R hw0 hword n hn
  rw [← hrec]
  exact h

end CharPCartier
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Headlines

theorem p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' hπ' R n hn =>
    p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj (p := p) v
      (p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v)
      π' hπ' R hn

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep K
    (p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K p)

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    exact p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP K (ringChar K)
  · haveI : CharP K 0 := hzero ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    exact residueTheoremK_ratFunc_of_isAlgClosed_main K

end Headlines
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

section Bc2Carrier

local notation "Qbar" => AlgebraicClosure ℚ

end Bc2Carrier
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main K
