module

public import RamifiedRootsConstantExtensionR0225

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections)
open ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaValuativeRootsR0223 ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms

private theorem finite_model_framed_root_values
    {k : Type} [Field k] (s n : ℕ) (D : RootData k s n) (K : FieldStage k)
    (M : RootModel D K) (E : Type) [Field E] (A : ValuationSubring E)
    (f : ValuationPoint E A ⟶ D.base.space)
    (h : Sections ((Scheme.Modules.pullback f).obj D.line))
    (hh : IsFrame ((Scheme.Modules.pullback f).obj D.line) ⊤ h)
    (a : Fin s → A) (g : ValuationPoint E A ⟶ D.cover.space)
    (hg : g ≫ D.map = f) (hv : BranchValues D E A f h a g hg) :
    ModelBranchValues M E A f h a g := by
  refine ⟨?_, ?_⟩
  · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      (modelFrameComparison M f).symm h hh
  have hm : (g ≫ M.cover.projection) ≫ M.map = f ≫ M.base.projection := by
    rw [Category.assoc, M.comparison, ← Category.assoc, hg]
  refine ⟨hm, ?_⟩
  intro j
  have hd := ArithmeticThetaPrescribedRootModelsR0224.FiniteModelFramedRootValuesR0224.framed_diamond g M.cover.projection
    M.map D.map M.base.projection f M.comparison hg hm M.line M.lineComparison
  have hc := congrArg (fun e => e.hom.app ⊤
    (pullbackGlobalSection g _
      (pullbackGlobalSection M.cover.projection _ (M.roots j)))) hd
  change (along g D.map f hg D.line).hom.app ⊤
    (((Scheme.Modules.pullback g).map
      (coverLineComparison M.base M.cover D.map M.map M.comparison M.line
        M.lineComparison).hom).app ⊤
      (pullbackGlobalSection g _ (pullbackGlobalSection M.cover.projection _ (M.roots j)))) =
    (modelFrameComparison M f).hom.app ⊤
      ((along (g ≫ M.cover.projection) M.map (f ≫ M.base.projection) hm M.line).hom.app ⊤
        (((Scheme.Modules.pullbackComp g M.cover.projection).app
          ((Scheme.Modules.pullback M.map).obj M.line)).hom.app ⊤
          (pullbackGlobalSection g _
            (pullbackGlobalSection M.cover.projection _ (M.roots j))))) at hc
  rw [← pullbackGlobalSection_map, M.roots_comparison] at hc
  erw [pullbackComp_hom_unit g M.cover.projection _ ⊤ (M.roots j)] at hc
  apply (ConcreteCategory.bijective_of_isIso ((modelFrameComparison M f).hom.app ⊤)).injective
  erw [← hc, hv j]
  simp only [modelFrame, Scheme.Modules.Hom.app_smul]
  congr 1
  exact (ConcreteCategory.congr_hom
    (congrArg (fun k => k.app ⊤) (modelFrameComparison M f).inv_hom_id) h).symm


/-- Construct prescribed roots and their finite model over any characteristic-zero constant field. -/
theorem prescribed_roots_finite_constant_extension :
∀ (k : Type) [Field k] [CharZero k], ∀ (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (E : Type) [Field E] (A : ValuationSubring E) (f : Quiver.Hom (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A) X.space), AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaValuativeRootsR0223.genericInclusion E A) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (r : Fin s → E), (∀ j, ArithmeticThetaValuativeRootsR0223.FieldEquation E A f J n (F j) h (r j)) → ∀ (c : Quiver.Hom (ArithmeticThetaFiniteFieldModelsR0221.Base (ArithmeticThetaConstantExtensionR0225.Omega k)) (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A)), c (IsLocalRing.closedPoint (ArithmeticThetaConstantExtensionR0225.Omega k)) = IsLocalRing.closedPoint A → CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp c f) X.map = CategoryTheory.CategoryStruct.id _ → ∀ K0 : (ArithmeticThetaConstantExtensionR0225.FieldStage k), FiniteDimensional k K0 → ∃ T : ArithmeticThetaConstantExtensionR0225.RootRealization X J n s F E A f h r c, Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation (ArithmeticThetaConstantExtensionR0225.Omega k) X.space X.map) ∧ Nonempty (ArithmeticThetaPrescribedRootModelsR0224.ProjectivePresentation (ArithmeticThetaConstantExtensionR0225.Omega k) T.cover.space (CategoryTheory.CategoryStruct.comp T.cover.map X.map)) ∧ ArithmeticThetaConstantExtensionR0225.FiniteRealization T K0 := by
  intro k _ _ X J hJ n s hn F hF E _ A f hdom h hh r hr c _hc hcf K0 hK0
  classical
  letI := X.proper
  letI := X.smooth
  letI := X.geometricallyIntegral
  letI := GeometricallyIntegral.isIntegral_of_subsingleton X.map
  have hi (j : Fin s) := valuative_root_integrality E A X.space f J n hn
    (F j) h hh (r j) (hr j)
  choose a ha using fun j => (hi j).exists
  obtain ⟨R, g, hg, hgd, t, ht⟩ := valuative_simultaneous_sections
    (Omega k) X.space X.map J hJ n s hn F hF E A f hdom h hh a (fun j => (ha j).2)
  letI := R.integral
  letI := R.smooth
  have hgeom : GeometricallyIntegral (R.map ≫ X.map) :=
    geometricallyIntegral_of_isAlgClosed (R.map ≫ X.map)
  have hcentre : (c ≫ g) ≫ (R.map ≫ X.map) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc g, hg, ← Category.assoc]
    exact hcf
  let T : RootRealization X J n s F E A f h r c := {
    cover := R
    geometric := hgeom
    line := ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187.line_of_invertible J hJ
    powers_nonzero := hF
    coefficients := a
    coefficients_eq := fun j => (ha j).1
    lift := g
    lift_eq := hg
    dominant := hgd
    roots := t
    roots_nonzero := fun j => (ht j).1
    equation := fun j => (ht j).2.1
    values := fun j => (ht j).2.2
    centre_over := hcentre }
  obtain ⟨K, hK, h0K, ⟨M⟩⟩ :=
    ramified_roots_constant_extension k s n hn T.data K0 hK0
  refine ⟨T, ArithmeticThetaPrescribedRootModelsR0224.PrescribedProjectiveRootFiniteModelR0224.projective (Omega k) X,
    ArithmeticThetaPrescribedRootModelsR0224.PrescribedProjectiveRootFiniteModelR0224.projective (Omega k) T.data.cover,
    K, hK, h0K, M,
    ArithmeticThetaPrescribedRootModelsR0224.PrescribedProjectiveRootFiniteModelR0224.projective K M.base.curve,
    ArithmeticThetaPrescribedRootModelsR0224.PrescribedProjectiveRootFiniteModelR0224.projective K M.cover.curve, ?_⟩
  exact finite_model_framed_root_values s n T.data K M E A f h hh
    T.coefficients T.lift T.lift_eq T.values


#print axioms prescribed_roots_finite_constant_extension
end ArithmeticThetaConstantExtensionR0225
