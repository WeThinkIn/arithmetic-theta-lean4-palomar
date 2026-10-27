import OneChartRegularRoot
import PullbackLineFrames
import NormalizedPowerCoefficients

open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower
open ArithmeticThetaNormalization ArithmeticThetaKummerCover

universe u
noncomputable section

namespace ArithmeticThetaNormalizedSections

set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization has integrally closed rings on every nonempty affine open. -/
theorem extensionNormalization_normalAffine (X : Scheme.{u}) [IsIntegral X]
    (E : Type u) [Field E] [Algebra X.functionField E] :
    NormalAffine (extensionNormalization X E) := by
  intro V hV _
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let y : PrimeSpectrum Γ(extensionNormalization X E, V) := ⟨P, hP.isPrime⟩
  let x := hV.fromSpec y
  have hx : x ∈ V := (hV.isoSpec.inv y).2
  let := TopCat.Presheaf.algebra_section_stalk
    (extensionNormalization X E).presheaf (⟨x, hx⟩ : V)
  let : IsLocalization.AtPrime ((extensionNormalization X E).presheaf.stalk x) P :=
    hV.isLocalization_stalk' y hx
  let := extensionNormalization_stalk_integrallyClosed X E x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl
      ((extensionNormalization X E).presheaf.stalk x) (Localization.AtPrime P)).toRingEquiv

/-- The exact prescribed roots extend uniquely in the actual pulled-back line. -/
theorem rootCover_regular_sections :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (H : X.Modules),
    ArithmeticThetaNormalizedSections.IsLineBundle X H → ∀ (U : X.Opens) [Nonempty U] (e :
    ArithmeticThetaLineRoot.LocalFrame X H U) (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] (n
    s : ℕ) (hn : 0 < n) (F : Fin s → (((ArithmeticThetaTensorPower.tensorPower X H n)).presheaf.obj
    (Opposite.op (⊤)))) (r : Fin s → Ω) (hr : (∀ j, r j ^ n = algebraMap X.functionField Ω
    (ArithmeticThetaNormalizedSections.powerCoefficient X H U e n (F j)))), ∃ eY :
    ArithmeticThetaLineRoot.LocalFrame (ArithmeticThetaKummerCover.rootCover X Ω s r)
    ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r)).obj H) ((TopologicalSpace.Opens.map (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r).base).obj U), ArithmeticThetaNormalizedSections.FramePullbackCompatible
    (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) H U e eY ∧ ∃! t : Fin s →
    ((((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r)).obj H)).presheaf.obj (Opposite.op (⊤))), ∀ j,
    (ArithmeticThetaNormalizedSections.sectionCoefficient (ArithmeticThetaKummerCover.rootCover X Ω
    s r) ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r)).obj H) ((TopologicalSpace.Opens.map (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r).base).obj U) eY (t j) = ArithmeticThetaKummerCover.coverRoot X Ω n s hn r (fun j =>
    ArithmeticThetaNormalizedSections.powerCoefficient X H U e n (F j)) hr j) ∧
    (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaKummerCover.rootCover X Ω s r)
    ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaKummerCover.rootCoverMap X Ω s
    r)).obj H) n ⊤ (t j) = ArithmeticThetaNormalizedSections.pullbackPowerSection
    (ArithmeticThetaKummerCover.rootCoverMap X Ω s r) H n (F j)) := by
  intro X _ H hH U _ e Ω _ _ n s hn F r hr
  obtain ⟨eY, heY⟩ := exists_pullbackFrame (rootCover X Ω s r) X
    (rootCoverMap X Ω s r) H U e
  refine ⟨eY, heY, ?_⟩
  have hline := pullback_isLineBundle (rootCover X Ω s r) X
    (rootCoverMap X Ω s r) H hH
  have hnormal := extensionNormalization_normalAffine X (generatedRootField X Ω s r)
  have hsections : ∀ j : Fin s, ∃! t :
      Γ((Scheme.Modules.pullback (rootCoverMap X Ω s r)).obj H, ⊤),
      sectionCoefficient (rootCover X Ω s r)
        ((Scheme.Modules.pullback (rootCoverMap X Ω s r)).obj H)
        (rootCoverMap X Ω s r ⁻¹ᵁ U) eY t =
          coverRoot X Ω n s hn r (fun j => powerCoefficient X H U e n (F j)) hr j ∧
      tensorPowerSection (rootCover X Ω s r)
        ((Scheme.Modules.pullback (rootCoverMap X Ω s r)).obj H) n ⊤ t =
          pullbackPowerSection (rootCoverMap X Ω s r) H n (F j) := by
    intro j
    apply existsUnique_root_from_one_chart _ _ hnormal hline _ eY n hn
    rw [normalization_powerCoefficient X (generatedRootField X Ω s r) H U e eY heY]
    exact coverRoot_pow X Ω n s hn r (fun j => powerCoefficient X H U e n (F j)) hr j
  choose t ht using fun j => (hsections j).exists
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  funext j
  exact (hsections j).unique (ht' j) (ht j)

end ArithmeticThetaNormalizedSections
