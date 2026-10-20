module

public import SchemeDoubledTorsionLiftR0259

@[expose] public section

/-! Midpoint-normalized symmetric lifts over arbitrary scheme bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeMidpointThetaLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open SchemeDoubledTorsionLift
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

variable {S : Scheme.{u}} (E : Family S)

lemma reflection_square (P : point E) : reflection E P ≫ reflection E P = 𝟙 E.curve := by
  let a := multiple E P 2
  let ca : SchemeHomOver E.p E.p :=
    ⟨E.p ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let i : SchemeHomOver E.p E.p := ⟨𝟙 E.curve, Category.id_comp _⟩
  let b := E.law.inv E.p (E.law.mul E.p i ca)
  have h₁ : reflection E P = b.val :=
    SchemeDoubledTorsionLift.point_inverse E E.p (E.law.mul E.p i ca)
  have h₂ : b.val ≫ translation E P = (E.law.mul E.p b ca).val :=
    SchemeDoubledTorsionLift.point_translation E E.p b P
  conv_lhs => lhs; rw [h₁]
  change b.val ≫ (translation E P ≫ inverse E) = _
  rw [← Category.assoc, h₂, SchemeDoubledTorsionLift.point_inverse]
  change (E.law.inv E.p
    (E.law.mul E.p (E.law.inv E.p (E.law.mul E.p i ca)) ca)).val = i.val
  congr 1
  letI := SchemeThetaInversion.pointGroup E E.p
  have hcomm (v w : SchemeHomOver E.p E.p) : v * w = w * v :=
    E.law.mul_comm E.p v w
  change ((i * ca)⁻¹ * ca)⁻¹ = i
  rw [mul_inv_rev, inv_inv, hcomm i ca, ← mul_assoc, inv_mul_cancel, one_mul]

lemma normalized_reflection (m : ℕ) (P : point E)
    (h : Nonempty (Lift E m (reflection E P))) :
    ∃! φ : Lift E m (reflection E P),
      (Scheme.Modules.pullback (negative E P)).mapIso φ =
        fixedComparison E m (negative E P) (reflection E P)
          (SchemeDoubledTorsionLift.reflection_fixed E P) := by
  obtain ⟨φ⟩ := h
  exact existsUnique_fibreIso E.p
    (SchemeThetaInversion.structure_surjective E) (negative E P)
    (E.law.inv (𝟙 _) P).property _ _
    ((SchemeThetaInversion.line_invertible E m).pullback _) _ φ

lemma normalized_square (m : ℕ) (P : point E) (φ : Lift E m (reflection E P))
    (hφ : (Scheme.Modules.pullback (negative E P)).mapIso φ =
      fixedComparison E m (negative E P) (reflection E P)
        (SchemeDoubledTorsionLift.reflection_fixed E P)) :
    (Scheme.Modules.pullback (reflection E P)).mapIso φ ≪≫ φ =
      squareComparison E m (reflection E P) (reflection_square E P) := by
  apply FixedPointPullback.square_of_rigidified (negative E P) (reflection E P)
    (SchemeDoubledTorsionLift.reflection_fixed E P) (reflection_square E P)
    (thetaLine E m) _ (Iso.refl _) φ
  · simpa only [Iso.trans_refl, fixedComparison] using hφ
  · intro ψ hψ
    exact aut_eq_refl E.p (SchemeThetaInversion.structure_surjective E)
      (negative E P) (E.law.inv (𝟙 _) P).property
      (SchemeThetaInversion.line_invertible E m) ψ
      (by simpa only [Iso.trans_refl] using hψ)

lemma midpoint_exists_unique (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E))
    (h : Nonempty (Lift E m (translation E P))) :
    ∃! α : Lift E m (translation E P),
      MidpointNormalized E m P ι α ∧ Symmetric E m P ι α := by
  obtain ⟨α₀⟩ := h
  obtain ⟨φ, hφ, hu⟩ := normalized_reflection E m P
    ⟨reflectionLift E m P ι α₀⟩
  let α : Lift E m (translation E P) :=
    ((Scheme.Modules.pullback (translation E P)).mapIso ι).symm ≪≫
      (Scheme.Modules.pullbackComp (translation E P) (inverse E)).app _ ≪≫ φ
  have hα : reflectionLift E m P ι α = φ := by
    apply Iso.ext
    simp [reflectionLift, compose, α]
  refine ⟨α, ⟨⟨SchemeDoubledTorsionLift.reflection_fixed E P, ?_⟩,
    ⟨reflection_square E P, ?_⟩⟩, ?_⟩
  · rw [hα]
    exact hφ
  · rw [hα]
    exact normalized_square E m P φ hφ
  · intro β hβ
    obtain ⟨_, hβ⟩ := hβ.1
    have he : reflectionLift E m P ι β = reflectionLift E m P ι α :=
      (hu _ hβ).trans hα.symm
    apply Iso.ext
    exact (cancel_epi (((Scheme.Modules.pullbackComp (translation E P) (inverse E)).app _).inv ≫
      ((Scheme.Modules.pullback (translation E P)).mapIso ι).hom)).mp
      (by simpa only [reflectionLift, compose, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        using congrArg Iso.hom he)

end SchemeMidpointThetaLift

theorem scheme_midpoint_theta_lift :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
    ∀ (m : ℕ), 0 < m → Even m → ∀ (P : point E),
      multiple E P (2*m) = E.law.one (CategoryTheory.CategoryStruct.id S) →
      ∀ (ι : Lift E m (inverse E)), NormalizedInversion E m ι →
      ∃! α : Lift E m (translation E P),
        MidpointNormalized E m P ι α ∧ Symmetric E m P ι α := by
  intro k _ _ S σ E m hm he P hP ι _
  exact SchemeMidpointThetaLift.midpoint_exists_unique E m P ι
    (scheme_doubled_torsion_lift k S σ E m hm he P hP)

#print axioms scheme_midpoint_theta_lift
end ArithmeticThetaSchemeThetaMarkingR0259
