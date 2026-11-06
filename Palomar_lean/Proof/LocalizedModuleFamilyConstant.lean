module

public import ProperModelGlobalConstants
public import LocalizedCompletedAlgebraization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ArithmeticThetaCompletedCharts
universe u
noncomputable section
namespace ArithmeticThetaFormalConstants

/-- Flatness prevents parameter torsion even after completion, so passage to
localized completions loses no completed section. -/
private lemma chart_localization_injective (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) [Flat f] (U : X.Opens) :
    Function.Injective (toLocalized (PowerSeries k) X f PowerSeries.X U) := by
  intro x y h
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists
    (Submonoid.powers (PowerSeries.X : PowerSeries k))
    (toLocalized (PowerSeries k) X f PowerSeries.X U)).mp h
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 (PowerSeries.X : PowerSeries k)).mp s.2
  have hi : ∀ n : ℕ, Function.Injective
      (fun a : Completed (PowerSeries k) X f PowerSeries.X U =>
        (PowerSeries.X : PowerSeries k)^n • a) := by
    intro n
    induction n with
    | zero => intro a b hab; simpa only [pow_zero, one_smul] using hab
    | succ n ih =>
      intro a b hab
      apply ih
      apply completed_parameter_injective k X f U
      simpa only [pow_succ', mul_smul] using hab
  apply hi n
  simpa only [Submonoid.smul_def, ← hn] using hs

/-- Joint faithfulness of the actual localized completed restrictions of global
sections. Proper completed algebraization supplies the separatedness needed
here; no finite-generation assertion is made about affine section modules. -/
private lemma localized_global_injective (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) [Flat f] [IsProper f]
    (C : X.OrderedAffineCover) (a b : Sections (PowerSeries k) X f ⊤)
    (h : ∀ i : C.ι,
      toLocalized (PowerSeries k) X f PowerSeries.X (C.U i)
          (globalToCompleted (PowerSeries k) X f PowerSeries.X (C.U i) a) =
      toLocalized (PowerSeries k) X f PowerSeries.X (C.U i)
          (globalToCompleted (PowerSeries k) X f PowerSeries.X (C.U i) b)) : a = b := by
  have hz : Compatible (PowerSeries k) X f PowerSeries.X C (fun _ => 0) := by
    intro i j
    simp only [map_zero]
  obtain ⟨g, hg, hu⟩ := completed_affine_algebraization (PowerSeries k)
    (PowerSeries.X : PowerSeries k) X f C (fun _ => 0) hz
  have hzero : (0 : Sections (PowerSeries k) X f ⊤) = g :=
    hu 0 (by intro i; exact map_zero _)
  have hdiff : a - b = g := by
    apply hu
    intro i
    rw [map_sub, sub_eq_zero]
    exact chart_localization_injective k X f (C.U i) (h i)
  exact sub_eq_zero.mp (hdiff.trans hzero.symm)

private lemma structuralMap_smul (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) (q r : PowerSeries k) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    structuralMap (PowerSeries k) X f ⊤ (q * r) =
      q • (structuralMap (PowerSeries k) X f ⊤ r : Sections (PowerSeries k) X f ⊤) := by
  exact map_mul (structuralMap (PowerSeries k) X f ⊤) q r

set_option backward.isDefEq.respectTransparency false in
/-- A compatible family on the actual localized completed charts has a unique
Laurent scalar, independently of the common denominator chosen to describe it. -/
theorem localized_module_family_constant :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f]
      [AlgebraicGeometry.Smooth (ArithmeticThetaFormalConstants.genericStructure k X f)]
      [AlgebraicGeometry.GeometricallyConnected (ArithmeticThetaFormalConstants.genericStructure k X f)],
      ∀ (C : AlgebraicGeometry.Scheme.OrderedAffineCover X)
        (z : ArithmeticThetaCompletedCharts.LocalizedFamily
          (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C),
      ArithmeticThetaCompletedCharts.LocalizedCompatible
        (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C z →
      ∃! c : LaurentSeries k, ArithmeticThetaFormalConstants.IsLaurentConstant k X f C z c := by
  intro k _ X f _ _ _ _ C z hz
  let A := algebraMap (PowerSeries k) (LaurentSeries k)
  have hA : Function.Injective A := IsFractionRing.injective _ _
  have ht (n : ℕ) : A ((PowerSeries.X : PowerSeries k)^n) ≠ 0 := by
    exact fun h => (pow_ne_zero n PowerSeries.X_ne_zero) (hA (h.trans (map_zero A).symm))
  obtain ⟨n, a, ha⟩ := localized_completed_algebraization k X f C z hz
  obtain ⟨r, hr⟩ := (proper_model_global_constants k X f).surjective a
  let c : LaurentSeries k := A r / A ((PowerSeries.X : PowerSeries k)^n)
  have hc : A r = A ((PowerSeries.X : PowerSeries k)^n) * c := by
    exact (mul_div_cancel₀ (A r) (ht n)).symm
  refine ⟨c, ⟨n, r, hc, ?_⟩, ?_⟩
  · intro i
    rw [hr]
    exact ha i
  · intro d hd
    obtain ⟨m, s, hs, hsi⟩ := hd
    have hri (i : C.ι) :
        toLocalized (PowerSeries k) X f PowerSeries.X (C.U i)
          (globalToCompleted (PowerSeries k) X f PowerSeries.X (C.U i)
            (structuralMap (PowerSeries k) X f ⊤ r)) =
        (PowerSeries.X : PowerSeries k)^n • z i := by
      rw [hr]
      exact ha i
    have he : (PowerSeries.X : PowerSeries k)^n * s = PowerSeries.X^m * r := by
      apply (proper_model_global_constants k X f).injective
      apply localized_global_injective k X f C
      intro i
      rw [structuralMap_smul, structuralMap_smul, map_smul, map_smul,
        map_smul, map_smul, hsi i, hri i]
      simp only [smul_smul, mul_comm]
    have heA := congrArg A he
    rw [map_mul, map_mul] at heA
    change A (PowerSeries.X^n) * A s = A (PowerSeries.X^m) * A r at heA
    rw [hs, hc] at heA
    apply mul_left_cancel₀ (mul_ne_zero (ht n) (ht m))
    simpa only [← mul_assoc, mul_comm (A (PowerSeries.X^m)) (A (PowerSeries.X^n))] using heA

#print axioms localized_module_family_constant
end ArithmeticThetaFormalConstants
