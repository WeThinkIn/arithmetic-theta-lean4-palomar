module

public import AmbientCompletedRootsDefinitionsR0227

@[expose] public section

/-! Full prescribed values after the actual inclusion into the ambient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAmbientCompletedRootsR0227
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Base Sections)
open ArithmeticThetaConstantExtensionR0225 (Omega FieldStage)
open ArithmeticThetaAlgebraicBranchesR0226
open ArithmeticThetaValuativeRootsR0223
open ArithmeticThetaPullback
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185

namespace AmbientBranchValuesR0227

private lemma along_refl {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    (J : Z.Modules) :
    along p f (p ≫ f) rfl J = (Scheme.Modules.pullbackComp p f).app J := by
  apply Iso.ext
  simp [along, Scheme.Modules.pullbackCongr]

/-- Composition preserves the whole pulled-back frame through the given triangle. -/
lemma frame_transport {W X Y Z : Scheme.{0}}
    (q : W ⟶ X) (p : X ⟶ Y) (f : Y ⟶ Z) (d : W ⟶ Y)
    (hd : q ≫ p = d) (ht : q ≫ (p ≫ f) = d ≫ f)
    (J : Z.Modules) (h : Sections ((Scheme.Modules.pullback f).obj J)) :
    transportSection q _ _ (along q (p ≫ f) (d ≫ f) ht J)
      (((Scheme.Modules.pullbackComp p f).app J).hom.app ⊤
        (pullbackGlobalSection p _ h)) =
      ((Scheme.Modules.pullbackComp d f).app J).hom.app ⊤
        (pullbackGlobalSection d _ h) := by
  have hc := along_comp_section f p q (p ≫ f) d (d ≫ f)
    rfl hd rfl ht J h
  rw [along_refl, along_refl] at hc
  rw [transport_as_app] at hc
  rw [transport_as_app] at hc
  rw [transport_as_app] at hc
  rw [transport_as_app]
  exact hc

end AmbientBranchValuesR0227

/-- Pull back the same valuative branch and sections along the selected-field
inclusion. Every scalar becomes the originally prescribed ambient root. -/
theorem ambient_branch_values :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules) (n s : ℕ) (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space) (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)) (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E) (K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k), ∀ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by
  intro k _ _ X J n s F f h E _ _ r K0 M
  let i : Base E ⟶ Base M.field := Spec.map (CommRingCat.ofHom M.field.subtype)
  let q := i ≫ genericInclusion M.field M.branch.ring
  let p := Spec.map (CommRingCat.ofHom M.branch.inclusion)
  let d := Spec.map (CommRingCat.ofHom (seriesMap (Omega k) E))
  have hq : q = Spec.map (CommRingCat.ofHom
      (M.field.subtype.comp (algebraMap M.branch.ring M.field))) := by
    dsimp [q, i, genericInclusion]
    rw [← Spec.map_comp]
    rfl
  have hd : q ≫ p = d := by
    rw [hq]
    dsimp [p, d]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change (M.field.subtype.comp (algebraMap M.branch.ring M.field)).comp
      M.branch.inclusion = seriesMap (Omega k) E
    rw [RingHom.comp_assoc, M.branch.compatible]
    ext a
    exact M.field.val.commutes (algebraMap (PowerSeries (Omega k))
      (LaurentSeries (Omega k)) a)
  have hqr : q ≫ extendedDisk (Omega k) M.field M.branch.ring
      M.branch.inclusion f = fieldDisk (E := E) f := by
    change q ≫ (p ≫ f) = d ≫ f
    rw [← Category.assoc, hd]
  have he : M.ambientLift ≫ M.realization.cover.map = fieldDisk (E := E) f := by
    change (q ≫ M.realization.lift) ≫ M.realization.cover.map = _
    rw [Category.assoc, M.realization.lift_eq, hqr]
  refine ⟨?_, he, ?_⟩
  · have hi : Function.Surjective i := fun y =>
      ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ y⟩
    letI : IsDominant i := ⟨hi.denseRange⟩
    letI := M.realization.dominant
    change IsDominant ((i ≫ genericInclusion M.field M.branch.ring) ≫ M.realization.lift)
    rw [Category.assoc]
    infer_instance
  · intro j
    have hc := along_comp_section M.realization.cover.map M.realization.lift q
      (extendedDisk (Omega k) M.field M.branch.ring M.branch.inclusion f)
      M.ambientLift (fieldDisk (E := E) f) M.realization.lift_eq rfl he hqr J
      (M.realization.roots j)
    have hv : transportSection M.realization.lift _ _
        (along M.realization.lift M.realization.cover.map _ M.realization.lift_eq J)
        (M.realization.roots j) =
        scalar M.branch.ring (M.realization.coefficients j) •
          extendedFrame (Omega k) M.field M.branch.ring M.branch.inclusion f J h := by
      rw [transport_as_app]
      exact M.realization.values j
    rw [hv, transportSection_smul] at hc
    have hs : q.appLE ⊤ ⊤ (by simp) (scalar M.branch.ring (M.realization.coefficients j)) =
        scalar E (r j) := by
      rw [hq]
      rw [show (Spec.map (CommRingCat.ofHom
          (M.field.subtype.comp (algebraMap M.branch.ring M.field)))).appLE ⊤ ⊤ (by simp)
          (scalar M.branch.ring (M.realization.coefficients j)) =
          scalar E (M.field.subtype (algebraMap M.branch.ring M.field
            (M.realization.coefficients j))) from
        (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (M.field.subtype.comp (algebraMap M.branch.ring M.field))))
          (M.realization.coefficients j)).symm]
      rw [M.realization.coefficients_eq, M.prescribed_eq]
    have hf := AmbientBranchValuesR0227.frame_transport q p f d hd hqr J h
    change transportSection q _ _ (along q _ _ hqr J)
      (extendedFrame (Omega k) M.field M.branch.ring M.branch.inclusion f J h) =
        fieldFrame (E := E) f J h at hf
    rw [hs, hf, transport_as_app] at hc
    exact hc.symm

#print axioms ambient_branch_values
end ArithmeticThetaAmbientCompletedRootsR0227
