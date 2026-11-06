module

public import ArithmeticFieldDefinitionsR0231
public import MatrixFamilyGlobalSectionsR0188

@[expose] public section

/-! Full coset tensor-section expansions over the displayed coefficient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticFieldR0231
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaLatticeSectionsR0188.MatrixFamilyGlobalSectionsR0188

/-- Pulling back the actual structural scalars and coset tensor polynomials
identifies their full series in the specified common frame, including empty
products, empty families, and zero coefficient vectors. -/
theorem field_coset_section_expansion :
∀ (k : Type) [Field k] [CharZero k] (n h : ℕ) (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h) (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaArithmeticFieldR0231.FormalIdentity k A U → ∀ (Y : AlgebraicGeometry.Scheme.{0}) (b : Quiver.Hom Y (AlgebraicGeometry.Spec (CommRingCat.of k))) (g : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Y), CategoryTheory.CategoryStruct.comp g b = ArithmeticThetaTateCuspsR0181.diskStructure k → ∀ (M : Y.Modules) (e : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ e → ∀ (t : Fin U.count → ArithmeticThetaSimultaneousUnaryR0187.Sections Y M), (∀ j, ArithmeticThetaPullback.pullbackGlobalSection g M (t j) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaSimultaneousUnaryR0187.unarySeries k (ArithmeticThetaLatticeSectionsR0188.commonN A) (U.pair j).1 (U.pair j).2) • e) → ∀ c : Fin h → k, ArithmeticThetaNormalizedSections.pullbackPowerSection g M n (∑ i : Fin h, ArithmeticThetaLatticeSectionsR0188.baseScalar k b (c i) • ∑ a : ArithmeticThetaLatticeSectionsR0188.Cosets A i, ArithmeticThetaTensorPower.tensorProductSection Y M n ⊤ (fun j => t (U.index i a j))) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaArithmeticFieldR0231.expanded k A c) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) n ⊤ e := by
  intro k _ _ n h A U hformal Y b g hgb M e he t ht c
  classical
  have hp (a : Γ(Y, ⊤)) (v : Sections Y (tensorPower Y M n)) :
      pullbackPowerSection g M n (a • v) =
        g.appTop a • pullbackPowerSection g M n v := by
    unfold pullbackPowerSection pullbackGlobalSection
    rw [((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (tensorPower Y M n)).app_smul]
    exact Scheme.Modules.Hom.app_smul _ _ _
  have hc (z : k) : g.appTop (baseScalar k b z) =
      scalar (PowerSeries k) (PowerSeries.C z) := by
    change (g ≫ b).appTop (scalar k z) = _
    rw [hgb]
    exact GlobalFamilyTorsionValueR0180.scalar_natural (algebraMap k (PowerSeries k)) z
  have hs {ι : Type} [Fintype ι] (v : ι → Sections Y (tensorPower Y M n)) :
      pullbackPowerSection g M n (∑ i, v i) = ∑ i, pullbackPowerSection g M n (v i) := by
    simp only [pullbackPowerSection, pullbackGlobalSection, map_sum]
  rw [hs]
  simp only [hp, hc, hs]
  have hprod (i : Fin h) (a : Cosets A i) :
      pullbackPowerSection g M n (tensorProductSection Y M n ⊤ (fun j => t (U.index i a j))) =
      scalar (PowerSeries k) (∏ j : Fin n,
        unarySeries k (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2) •
        tensorPowerSection (Disk k) ((Scheme.Modules.pullback g).obj M) n ⊤ e := by
    rw [pullbackPowerSection, pullback_tensorProduct_section]
    simp only [ht]
    change tensorProductSection (Disk k) ((Scheme.Modules.pullback g).obj M) n ⊤
      (fun j => scalar (PowerSeries k)
        (unarySeries k (commonN A) (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2) • e) = _
    rw [product_frame _ e he]
    simp only [scalar, map_prod]
  simp only [hprod, ← Finset.sum_smul, smul_smul]
  rw [hformal c]
  simp only [PowerSeries.smul_eq_C_mul, scalar, map_sum, map_mul, Finset.sum_smul]

#print axioms field_coset_section_expansion

end ArithmeticThetaArithmeticFieldR0231
