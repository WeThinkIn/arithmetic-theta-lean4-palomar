import FormalConstantDefinitions
import Mathlib.RingTheory.AdicCompletion.Completeness

universe u₁ u₂

namespace ArithmeticThetaFormalConstants.Comparison
open AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem restrictScalars_map_pow_smul_top (n : ℕ) :
    (((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A) =
      (𝔭 ^ n • ⊤ : Submodule A B) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

noncomputable def levelRestrictScalarsEquiv (n : ℕ) :
    (B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) ≃ₗ[A]
      B ⧸ (𝔭 ^ n • ⊤ : Submodule A B) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top B 𝔭 n))

theorem levelRestrictScalarsEquiv_mk (n : ℕ) (b : B) :
    levelRestrictScalarsEquiv B 𝔭 n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b :=
  rfl

theorem transitionMap_levelRestrictScalarsEquiv {m n : ℕ} (hmn : m ≤ n)
    (y : B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :
    transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n y) =
      levelRestrictScalarsEquiv B 𝔭 m
        (transitionMap (𝔭.map (algebraMap A B)) B hmn y) :=
  Quotient.inductionOn' y fun _ => rfl

noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n), fun {m n} hmn => by
    show transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
      levelRestrictScalarsEquiv B 𝔭 m (x.val m)
    rw [← x.prop hmn]
    exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n), fun {m n} hmn => by
    show transitionMap (𝔭.map (algebraMap A B)) B hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
      (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
    rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
      ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
      LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) = of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end ArithmeticThetaFormalConstants.Comparison


namespace ArithmeticThetaFormalConstants.Comparison
open AdicCompletion

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]

/-- Change the ideal along its proved structural identification. -/
noncomputable def atIdeal (I : Ideal A) (J : Ideal B)
    (h : I.map (algebraMap A B) = J) :
    AdicCompletion J B ≃ₗ[A] AdicCompletion I B := by
  subst J
  exact restrictScalarsEquiv B I

theorem atIdeal_of (I : Ideal A) (J : Ideal B)
    (h : I.map (algebraMap A B) = J) (b : B) :
    atIdeal B I J h (of J B b) = of I B b := by
  subst J
  exact restrictScalarsEquiv_of B I b

/-- A linear map to a separated module is determined by original sections.
Only the ideal, not the original module, must be finitely generated. -/
theorem linearMap_ext_of {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (I : Ideal A) (hI : I.FG)
    [IsHausdorff I N] (p q : AdicCompletion I M →ₗ[A] N)
    (h : ∀ a, p (of I M a) = q (of I M a)) : p = q := by
  apply LinearMap.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule A M) (x.val n)
  have hx : x ≡ of I M a [SMOD (I ^ n • ⊤ : Submodule A (AdicCompletion I M))] := by
    rw [SModEq.sub_mem, pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    change x.val n - Submodule.mkQ _ a = 0
    exact sub_eq_zero.mpr ha.symm
  have hp := hx.map p
  have hq := hx.map q
  have ple : (I ^ n • (⊤ : Submodule A (AdicCompletion I M))).map p ≤ I ^ n • ⊤ := by
    rw [Submodule.map_smul'']
    exact smul_le_smul_left _ le_top
  have qle : (I ^ n • (⊤ : Submodule A (AdicCompletion I M))).map q ≤ I ^ n • ⊤ := by
    rw [Submodule.map_smul'']
    exact smul_le_smul_left _ le_top
  exact (hp.mono ple).trans ((h a) ▸ (hq.mono qle).symm)

end ArithmeticThetaFormalConstants.Comparison

open AlgebraicGeometry CategoryTheory
universe u
namespace ArithmeticThetaFormalConstants
noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R)

/-- The comparison uses exactly the section algebra induced by f. -/
def canonicalCompletionEquivalences : CompletionEquivalences R X f t := fun U => by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact Comparison.atIdeal Γ(X, U) (Ideal.span {t})
    (Ideal.span {structuralMap R X f U t}) (by simp [Ideal.map_span, structuralMap])

theorem canonicalCompletionEquivalences_matches :
    MatchesCompletion R X f t (canonicalCompletionEquivalences R X f t) := by
  intro U a
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact Comparison.atIdeal_of Γ(X, U) (Ideal.span {t})
    (Ideal.span {structuralMap R X f U t}) _ a

/-- The unique comparison family on all opens, with no finiteness assumption on sections. -/
theorem completed_ring_module_comparison :
    ∃! e : CompletionEquivalences R X f t, MatchesCompletion R X f t e := by
  refine ⟨canonicalCompletionEquivalences R X f t,
    canonicalCompletionEquivalences_matches R X f t, ?_⟩
  intro e he
  funext U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  let c := canonicalCompletionEquivalences R X f t U
  have hc := canonicalCompletionEquivalences_matches R X f t U
  have hcomp : (e U).toLinearMap.comp c.symm.toLinearMap = LinearMap.id := by
    apply Comparison.linearMap_ext_of (Ideal.span {t}) (Submodule.fg_span_singleton t)
    intro a
    change e U (c.symm (AdicCompletion.of (Ideal.span {t})
      (ArithmeticThetaCompletedCharts.Sections R X f U) a)) = _
    rw [← hc a, LinearEquiv.symm_apply_apply]
    exact (he U a).trans (hc a).symm
  apply LinearEquiv.ext
  intro x
  have hh := LinearMap.congr_fun hcomp (c x)
  simpa using hh

end
end ArithmeticThetaFormalConstants
