import PrescribedRootModelsDefinitionsR0224

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaPrescribedRootModelsR0224
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRamifiedRootModelsR0222 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaValuativeRootsR0223 ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms

namespace FiniteModelFramedRootValuesR0224

/-- Pasting the model square with the prescribed third-scheme triangle, retaining
its specified line comparison. -/
lemma framed_diamond {V Y Y₀ X X₀ : Scheme}
    (g : V ⟶ Y) (p : Y ⟶ Y₀) (q : Y₀ ⟶ X₀)
    (r : Y ⟶ X) (t : X ⟶ X₀) (f : V ⟶ X)
    (hs : p ≫ q = r ≫ t) (hg : g ≫ r = f)
    (hm : (g ≫ p) ≫ q = f ≫ t)
    (J : X₀.Modules) {H : X.Modules}
    (e : (Scheme.Modules.pullback t).obj J ≅ H) :
    (Scheme.Modules.pullback g).mapIso
        (squareComparison p q r t hs J ≪≫ (Scheme.Modules.pullback r).mapIso e) ≪≫
      along g r f hg H =
    (Scheme.Modules.pullbackComp g p).app ((Scheme.Modules.pullback q).obj J) ≪≫
      along (g ≫ p) q (f ≫ t) hm J ≪≫
      ((Scheme.Modules.pullbackComp f t).app J).symm ≪≫
      (Scheme.Modules.pullback f).mapIso e := by
  have hd := triangle_diamond g p q r t (g ≫ p) f (f ≫ t)
    rfl hg hs hm rfl J
  have he := triangle_naturality g r f hg e
  have htri (A B C : Scheme) (a : A ⟶ B) (b : B ⟶ C) (L : C.Modules) :
      triangle a b (a ≫ b) rfl L = (Scheme.Modules.pullbackComp a b).app L := by
    apply Iso.ext
    simp [triangle, Scheme.Modules.pullbackCongr]
  rw [htri, htri] at hd
  have hd' := congrArg (fun i => i ≪≫ ((Scheme.Modules.pullbackComp f t).app J).symm) hd
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at hd'
  change _ ≪≫ triangle g r f hg H = _
  rw [Functor.mapIso_trans, Iso.trans_assoc, he, ← Iso.trans_assoc, hd']
  rfl

end FiniteModelFramedRootValuesR0224

/-- Every supplied finite model preserves the whole prescribed root values in
exactly the inverse image of the original valuation frame. -/
theorem finite_model_framed_root_values :
∀ (s n : ℕ) (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n) (K : ArithmeticThetaFiniteFieldModelsR0221.FieldStage) (M : ArithmeticThetaRamifiedRootModelsR0222.RootModel D K) (E : Type) [Field E] (A : ValuationSubring E) (f : Quiver.Hom (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A) D.base.space) (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj D.line)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj D.line) ⊤ h → ∀ (a : Fin s → A) (g : Quiver.Hom (ArithmeticThetaValuativeRootsR0223.ValuationPoint E A) D.cover.space) (hg : CategoryTheory.CategoryStruct.comp g D.map = f), ArithmeticThetaPrescribedRootModelsR0224.BranchValues D E A f h a g hg → ArithmeticThetaPrescribedRootModelsR0224.ModelBranchValues M E A f h a g := by
  intro s n D K M E _ A f h hh a g hg hv
  refine ⟨?_, ?_⟩
  · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      (modelFrameComparison M f).symm h hh
  have hm : (g ≫ M.cover.projection) ≫ M.map = f ≫ M.base.projection := by
    rw [Category.assoc, M.comparison, ← Category.assoc, hg]
  refine ⟨hm, ?_⟩
  intro j
  have hd := FiniteModelFramedRootValuesR0224.framed_diamond g M.cover.projection
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

#print axioms finite_model_framed_root_values
end ArithmeticThetaPrescribedRootModelsR0224
