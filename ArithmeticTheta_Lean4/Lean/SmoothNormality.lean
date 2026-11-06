import EtaleNormality
import SmoothPrerequisites

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace ArithmeticThetaSmoothNormality

universe u
noncomputable section

/-- Smooth domain algebras over fields are integrally closed, via standard étale local charts. -/
theorem smoothDomain_integrallyClosed (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.Smooth k A] : IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _hp hpmax
  obtain ⟨g, hgp, n, alg, htower, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let := alg
  let := htower
  let := hstd
  have hg0 : g ≠ 0 := fun h => hgp (h ▸ p.zero_mem)
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  let : IsIntegrallyClosed (Localization.Away g) :=
    etaleDomain_integrallyClosed (MvPolynomial (Fin n) k) (Localization.Away g)
  have hle : Submonoid.powers g ≤ p.primeCompl := Submonoid.powers_le.mpr hgp
  let := IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away g) (Localization.AtPrime p) (.powers g) p.primeCompl hle
  let := IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.Away g) (Localization.AtPrime p) (.powers g) p.primeCompl hle
  let := IsLocalization.isLocalization_of_submonoid_le
    (Localization.Away g) (Localization.AtPrime p) (.powers g) p.primeCompl hle
  apply isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
    (p.primeCompl.map (algebraMap A (Localization.Away g)))
  exact map_le_nonZeroDivisors_of_injective _
    (IsLocalization.injective (Localization.Away g)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)) p.primeCompl_le_nonZeroDivisors

/-- Every actual nonempty affine chart of an integral scheme smooth over a field is normal. -/
theorem smooth_affine_integrallyClosed (X : Scheme.{u}) [IsIntegral X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X,U) := by
  let := (ArithmeticThetaSmoothPrerequisites.constantSectionsMap X k f U).toAlgebra
  let : Algebra.Smooth k Γ(X,U) :=
    ArithmeticThetaSmoothPrerequisites.smooth_affine_structureMap X k f U hU
  exact smoothDomain_integrallyClosed k Γ(X,U)

/-- Actual smooth structure over a characteristic-zero field supplies all base normalization inputs. -/
theorem smooth_normalization_prerequisites (X : Scheme.{u}) [IsIntegral X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [CharZero k] [Smooth f] :
    IsLocallyNoetherian X ∧ CharZero X.functionField ∧
      ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X,U) :=
  ⟨ArithmeticThetaSmoothPrerequisites.smooth_locallyNoetherian X k f,
    ArithmeticThetaSmoothPrerequisites.functionField_charZero X k f,
    fun U hU => smooth_affine_integrallyClosed X k f U hU⟩

end
end ArithmeticThetaSmoothNormality
