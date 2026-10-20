module

public import CompletedChartDefinitions
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

/-! Parameter cancellation for actual sections of a flat scheme and their
principal-adic completions. No finite-generation hypothesis is used. -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped Pointwise
universe u
noncomputable section
namespace ArithmeticThetaCompletedCharts

/-- Cancellation by a principal parameter passes to its adic completion. -/
lemma completion_parameter_injective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (t : R) (ht : Function.Injective (fun m : M => t • m)) :
    Function.Injective (fun z : AdicCompletion (Ideal.span {t}) M => t • z) := by
  suffices hz : ∀ z : AdicCompletion (Ideal.span {t}) M, t • z = 0 → z = 0 by
    intro x y h
    exact sub_eq_zero.mp (hz (x - y) (by simp [smul_sub, h]))
  intro z hz
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {t}) M z
  apply AdicCompletion.ext
  intro n
  have hn := congrArg (fun z : AdicCompletion (Ideal.span {t}) M => z.val (n + 1)) hz
  change Submodule.Quotient.mk (t • a (n + 1)) = (0 : M ⧸ ((Ideal.span {t}) ^ (n + 1) • ⊤ : Submodule R M)) at hn
  rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at hn
  obtain ⟨b, _, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hn
  have hab : a (n + 1) = t ^ n • b := ht (by simpa [pow_succ', mul_smul] using hb.symm)
  change Submodule.Quotient.mk (a n) = (0 : M ⧸ ((Ideal.span {t}) ^ n • ⊤ : Submodule R M))
  rw [← a.mk_eq_mk (Nat.le_succ n), hab, Submodule.Quotient.mk_eq_zero,
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)

/-- Affine sections are flat for the scalar action induced by the structural morphism. -/
lemma affine_sections_flat (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat R ((OModulePresheaf.unit f).obj U) := by
  have hf := f.flat_appLE (isAffineOpen_top (Spec (CommRingCat.of R))) hU (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  have he := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
  have h := (RingHom.Flat.comp_iff_of_bijective_right he).mpr hf
  exact h

lemma section_parameter_injective (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (t : R) (ht : IsRegular t) (U : X.Opens) :
    Function.Injective (fun z : (OModulePresheaf.unit f).obj U => t • z) := by
  intro a b hab
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  have := affine_sections_flat R X f V hV
  have hinj := Module.Flat.isSMulRegular_of_isRegular (M := (OModulePresheaf.unit f).obj V) ht
  refine ⟨V, hVU, hxV, hinj ?_⟩
  exact (show t • (OModulePresheaf.unit f).res hVU a = t • (OModulePresheaf.unit f).res hVU b from
    by simpa only [map_smul] using congrArg ((OModulePresheaf.unit f).res hVU) hab)

/-- Multiplication by the base parameter is injective on completed actual
sections of every open of a scheme flat over the power-series ring. -/
theorem completed_parameter_injective :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [AlgebraicGeometry.Flat f] (U : X.Opens),
      Function.Injective (fun z : ArithmeticThetaCompletedCharts.Completed
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) U =>
        (PowerSeries.X : PowerSeries k) • z) := by
  intro k _ X f _ U
  apply completion_parameter_injective
  exact section_parameter_injective (PowerSeries k) X f PowerSeries.X
    (IsRegular.of_ne_zero PowerSeries.X_ne_zero) U

end ArithmeticThetaCompletedCharts
