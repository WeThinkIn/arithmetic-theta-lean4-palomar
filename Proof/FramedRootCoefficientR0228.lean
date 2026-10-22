module

public import AmbientCompletedRootsDefinitionsR0227
public import ValuativeRootIntegralityR0223
public import AlgebraicBranchDefinitionsR0226

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaAmbientCompletedRootsR0227
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Sections powerIso powerComparison)
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaAlgebraicBranchesR0226
open ArithmeticThetaOpenHodgeR0180 (scalar)
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open ArithmeticThetaValuativeRootsR0223.ValuativeRootIntegralityR0223 (comp_power)

namespace FramedRootCoefficientR0228

/-- The two accepted recursive tensor isomorphisms agree, including degree zero. -/
lemma powerCongr_eq_powerIso (X : Scheme.{0}) {M N : X.Modules}
    (e : M ≅ N) (n : ℕ) : powerCongr X e n = powerIso e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sheafTensorCongr X (powerCongr X e n) e =
      sheafTensorCongr X (powerIso e n) e
    rw [ih]

lemma tensorComparison_eq_powerComparison {X Y : Scheme.{0}} (p : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (n : ℕ) :
    tensorComparison p M N e n = powerComparison p M e n := by
  unfold tensorComparison powerComparison
  rw [powerCongr_eq_powerIso]

/-- The concrete app formulation inherits arbitrary-module composition. -/
lemma comparison_comp {X Y Z : Scheme.{0}} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : X.Modules) (n : ℕ) (s : Sections (tensorPower X M n)) :
    (powerComparison q ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullbackComp q p).app M) n).hom.app ⊤
      (pullbackGlobalSection q _ (pullbackPowerSection p M n s)) =
      pullbackPowerSection (q ≫ p) M n s := by
  rw [← tensorComparison_eq_powerComparison, ← transport_as_app]
  exact comp_power p q M n s

lemma scalar_map (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E]
    (a : PowerSeries k) :
    (Spec.map (CommRingCat.ofHom (seriesMap k E))).appLE ⊤ ⊤ (by simp)
      (scalar (PowerSeries k) a) = scalar E (seriesMap k E a) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (seriesMap k E))) a).symm

end FramedRootCoefficientR0228

/-- The full coefficient in the given disk frame and its root equation over
any ambient field. The source module need not be a line bundle. -/
theorem framed_root_coefficient :
    ∀ (k : Type) [Field k] (Z : AlgebraicGeometry.Scheme.{0})
      (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z)
      (J : Z.Modules) (n : ℕ)
      (F : Sections (tensorPower Z J n))
      (h : Sections ((Scheme.Modules.pullback f).obj J)),
      IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ h →
      ∃! a : PowerSeries k,
        pullbackPowerSection f J n F = scalar (PowerSeries k) a •
          tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k)
            ((Scheme.Modules.pullback f).obj J) n ⊤ h ∧
        ∀ (E : Type) [Field E] [Algebra (LaurentSeries k) E] (r : E),
          Equation f J n F h r ↔ r ^ n = seriesMap k E a := by
  intro k _ Z f J n F h hh
  have hp := InitialHodgeSection.tensor_frame _ h hh n
  obtain ⟨C, hC⟩ := (hp ⊤ le_rfl).surjective (pullbackPowerSection f J n F)
  simp only [InitialHodgeSection.res_self] at hC
  let a : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom C
  have ha : scalar (PowerSeries k) a = C :=
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm_apply_apply C
  have he : pullbackPowerSection f J n F = scalar (PowerSeries k) a •
      tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k)
        ((Scheme.Modules.pullback f).obj J) n ⊤ h := by
    rw [ha]
    exact hC.symm
  refine ⟨a, ⟨he, ?_⟩, ?_⟩
  · intro E _ _ r
    let q := Spec.map (CommRingCat.ofHom (seriesMap k E))
    let e := (Scheme.Modules.pullbackComp q f).app J
    have hf : transportSection q _ _ e h = fieldFrame (E := E) f J h := by
      rw [transport_as_app]
      rfl
    have ht := congrArg (fun s =>
      (powerComparison q ((Scheme.Modules.pullback f).obj J) e n).hom.app ⊤
        (pullbackGlobalSection q _ s)) he
    rw [FramedRootCoefficientR0228.comparison_comp] at ht
    rw [← FramedRootCoefficientR0228.tensorComparison_eq_powerComparison,
      ← transport_as_app, transportSection_smul, transportSection_tensor] at ht
    rw [FramedRootCoefficientR0228.scalar_map, hf] at ht
    have hg : IsFrame _ ⊤ (fieldFrame (E := E) f J h) := by
      rw [← hf]
      exact transport_frame q _ _ e h hh
    have hinj := (InitialHodgeSection.tensor_frame _ _ hg n ⊤ le_rfl).injective
    constructor
    · intro hr
      have hs : scalar E (r ^ n) = scalar E (seriesMap k E a) := by
        apply hinj
        simp only [InitialHodgeSection.res_self]
        exact hr.symm.trans ht
      exact (Scheme.ΓSpecIso (CommRingCat.of E)).commRingCatIsoToRingEquiv.symm.injective hs
    · intro hr
      unfold Equation
      rw [hr]
      exact ht
  · intro b hb
    have hs : scalar (PowerSeries k) b = scalar (PowerSeries k) a := by
      apply (hp ⊤ le_rfl).injective
      simp only [InitialHodgeSection.res_self]
      exact hb.1.symm.trans he
    exact (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm.injective hs

#print axioms framed_root_coefficient
end ArithmeticThetaAmbientCompletedRootsR0227
