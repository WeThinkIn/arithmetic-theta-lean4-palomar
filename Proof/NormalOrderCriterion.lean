module

public import NormalizedSectionDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaNormalizedSections

universe u
noncomputable section

namespace ArithmeticThetaSectionCompletion

set_option backward.isDefEq.respectTransparency false in
/-- A codimension-one stalk on a normal affine chart is a DVR. -/
theorem normal_stalk_dvr
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (x : X) (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial)
    (show IsOpen ((⊤ : X.Opens) : Set X) from isOpen_univ)
  obtain ⟨U, hU, rfl⟩ := hU
  letI : Nonempty U := ⟨⟨x, hxU.1⟩⟩
  change IsAffineOpen U at hU
  let xU : U := ⟨x, hxU.1⟩
  let p : Ideal Γ(X, U) := (hU.primeIdealOf xU).asIdeal
  have hcoh : Order.coheight x = p.height := by
    have hcohU : Order.coheight (xU : X) = p.height := by
      dsimp [p]
      rw [← hU.fromSpec_primeIdealOf xU, coheight_eq_of_isOpenImmersion]
      exact (idealHeight_eq_coheight _ _).symm
    simpa [xU] using hcohU
  have hpheight : p.height = 1 := by simpa [hcoh] using hx
  have hp0 : p ≠ (⊥ : Ideal Γ(X, U)) := Ideal.ne_bot_of_height_eq_one hpheight
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xU
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk xU
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsIntegrallyClosed Γ(X, U) := hN U hU
  letI : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing p.primeCompl (X.presheaf.stalk x) inferInstance
  letI : IsLocalRing (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.isLocalRing (X.presheaf.stalk x) p
  letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
    isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  letI : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    { maximalOfPrime := fun {I} hI hIp => hIp.isMaximal_of_ne_bot hI }
  have hnf : ¬ IsField (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.not_isField Γ(X, U) hp0 (X.presheaf.stalk x)
  letI : IsDedekindDomain (X.presheaf.stalk x) :=
    (isDedekindDomain_iff (X.presheaf.stalk x) X.functionField).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun {g} hg =>
        (isIntegrallyClosed_iff X.functionField).mp inferInstance hg⟩
  have hd : IsDedekindDomain (X.presheaf.stalk x) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnf).out 3 1).mp hd

end ArithmeticThetaSectionCompletion
