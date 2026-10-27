import UnaryPowersInCommonSquareLineR0187
import FieldCompactUnaryR0236

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaArithmeticCommonCoverR0238
open ArithmeticThetaSimultaneousUnaryR0187


open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaCompactUnaryR0183
open UnaryPowersInCommonSquareLineR0187
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185


/-- Arithmetic compact unary powers in the prescribed square line and full Tate frame. -/
theorem field_unary_powers_in_common_square_line :
    ∀ (k : Type) [Field k] [CharZero k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin s → ℕ) (ν : Fin s → ℤ), (∀ j, 0 < m j ∧ Even (m j) ∧ m j ∣ N ∧ (-(m j : ℤ) ≤ 2*ν j ∧ 2*ν j < (m j : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (p : Quiver.Hom Z X.space) (J : Z.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower Z (J) (2)) ((AlgebraicGeometry.Scheme.Modules.pullback p).obj (H.line))) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z) (hf : CategoryTheory.CategoryStruct.comp f p = V.disk) (η : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback V.disk).obj (H.line))), ArithmeticThetaBoundaryHodgeR0182.ExtendsGenerator k (ArithmeticThetaCompactUnaryR0183.level N) H V η → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J))), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) ⊤ h → (ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H.line β f V.disk hf).hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) 2 ⊤ h) = η → ∃ F : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections Z (ArithmeticThetaTensorPower.tensorPower Z (J) (ArithmeticThetaCompactUnaryR0183.exponent N)), ArithmeticThetaSimultaneousUnaryR0187.UnaryPowers k N s m ν H p J β F ∧ ∀ j, ArithmeticThetaNormalizedSections.pullbackPowerSection f J (ArithmeticThetaCompactUnaryR0183.exponent N) (F j) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaSimultaneousUnaryR0187.unarySeries k N (m j) (ν j) ^ (ArithmeticThetaCompactUnaryR0183.exponent N)) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (J)) (ArithmeticThetaCompactUnaryR0183.exponent N) ⊤ h := by
  intro k _ _ N s hN hNeven m ν hm D X H hH hgH V ζ hζ hmark Z _ p J hJ β f hf η hη h hh hsquare
  classical
  have hc (j : Fin s) := ArithmeticThetaArithmeticSectionsR0236.field_compact_unary k (m j) N
    (hm j).1 (hm j).2.1 hN hNeven (hm j).2.2.1 D X H hH hgH (ν j) (hm j).2.2.2
  choose a b ha hb A t ht using hc
  let e := comparison Z J ((Scheme.Modules.pullback p).obj H.line) β N
  let F : Fin s → Sections Z (tensorPower Z J (exponent N)) :=
    fun j => e.inv.app ⊤ (pullbackPowerSection p H.line (weight N) (t j))
  have hF (j : Fin s) : e.hom.app ⊤ (F j) =
      pullbackPowerSection p H.line (weight N) (t j) :=
    iso_inv_hom_apply e.symm ⊤ _
  let ed := comparison (Disk k) ((Scheme.Modules.pullback f).obj J)
    ((Scheme.Modules.pullback V.disk).obj H.line) (squareOnDisk k p J H.line β f V.disk hf) N
  have hd (j : Fin s) : ed.hom.app ⊤ (pullbackPowerSection f J (exponent N) (F j)) =
      pullbackPowerSection V.disk H.line (weight N) (t j) :=
    comparison_transport k p J hJ H.line H.invertible β f V.disk hf N (F j) (t j) (hF j)
  have hn (j : Fin s) : F j ≠ 0 := by
    obtain ⟨c, hc, he⟩ := (ht j).1.2.2.1 V
    apply nonzero_of_disk k J f (exponent N) (F j) _ ed
      (tensorPowerSection (Disk k) _ (weight N) ⊤ η)
      (HodgeBaseChange.tensorPower_frame _ η hη.1 (weight N)) c hc
    rw [hd, ← diskPower_eq k N H V]
    exact he η hη
  refine ⟨F, ⟨e, comparison_section Z J _ β N, ?_⟩, ?_⟩
  · intro j
    exact ⟨hn j, a j, b j, ha j, hb j, A j, t j, (ht j).1, hF j⟩
  · intro j
    obtain ⟨c, hc, he⟩ := (ht j).1.2.2.2 V ζ hζ hmark
    have hc' := coefficient_identification k N (m j) (ν j) c hc
    apply (ConcreteCategory.bijective_of_isIso (ed.hom.app ⊤)).injective
    rw [hd, ← diskPower_eq k N H V, he η hη, hc', Scheme.Modules.Hom.app_smul]
    change _ = _ • (comparison (Disk k) _ _ (squareOnDisk k p J H.line β f V.disk hf) N).hom.app ⊤ _
    rw [comparison_section, hsquare]


#print axioms field_unary_powers_in_common_square_line
end ArithmeticThetaArithmeticCommonCoverR0238
