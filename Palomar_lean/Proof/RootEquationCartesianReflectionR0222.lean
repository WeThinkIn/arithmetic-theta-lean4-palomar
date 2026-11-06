module

public import RamifiedRootModelsDefinitionsR0222

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRamifiedRootModelsR0222
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms
open ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
namespace RootEquationReflection

/-- Tensor pullback is natural in a specified line isomorphism. -/
theorem power_naturality {X Y : Scheme} (p : X ⟶ Y) {J H : Y.Modules}
    (hJ : IsLineBundle Y J) (e : J ≅ H) (n : ℕ) :
    (Scheme.Modules.pullback p).map (powerIso e n).hom ≫
      (pullback_tensorPower_iso X Y p H n).hom =
    (pullback_tensorPower_iso X Y p J n).hom ≫
      (powerIso ((Scheme.Modules.pullback p).mapIso e) n).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  choose U hx es using hJ
  refine hom_ext_frames (I := Y) (Y := Y) (J := tensorPower Y J n) U ?_
    (fun x => tensorPowerFrame Y J (U x)
      (localFrameOfIso Y J (U x) (Classical.choice (es x))) n) _ _ ?_
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  intro x
  let e0 := localFrameOfIso Y J (U x) (Classical.choice (es x))
  have he : (tensorPowerFrame Y J (U x) e0 n).equiv (U x) le_rfl 1 =
      tensorPowerSection Y J n (U x) (e0.equiv (U x) le_rfl 1) := by
    simpa only [one_pow] using (tensorPowerSection_frame Y J (U x) e0 n (U x) le_rfl 1).symm
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Scheme.Modules.pushforward_map_app]
  change (pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ U x)
    (((Scheme.Modules.pullback p).map (powerIso e n).hom).app _
      (pullbackLocalSection p (tensorPower Y J n) (U x)
        ((tensorPowerFrame Y J (U x) e0 n).equiv (U x) le_rfl 1))) =
    (powerIso ((Scheme.Modules.pullback p).mapIso e) n).hom.app (p ⁻¹ᵁ U x)
      ((pullback_tensorPower_iso X Y p J n).hom.app (p ⁻¹ᵁ U x)
        (pullbackLocalSection p (tensorPower Y J n) (U x)
          ((tensorPowerFrame Y J (U x) e0 n).equiv (U x) le_rfl 1)))
  rw [he, pullbackLocalSection_map, powerIso_section, pullback_tensorPower_local,
    pullback_tensorPower_local, powerIso_section]
  simp only [Functor.mapIso_hom]
  rw [pullbackLocalSection_map]

/-- Composition coherence as an equality of the actual isomorphisms. -/
theorem power_triangle_iso {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (t : X ⟶ Z) (h : p ≫ q = t) (J : Z.Modules)
    (hJ : IsLineBundle Z J) (n : ℕ) :
    (Scheme.Modules.pullback p).mapIso (pullback_tensorPower_iso Y Z q J n) ≪≫
      powerComparison p ((Scheme.Modules.pullback q).obj J) (triangle p q t h J) n =
    triangle p q t h (tensorPower Z J n) ≪≫ pullback_tensorPower_iso X Z t J n := by
  apply Iso.ext
  exact powerComparison_triangle p q t h J hJ n

/-- The two paths around the specified square give the same tensor comparison. -/
theorem power_square_iso {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T)
    (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t)
    (J : T.Modules) (hJ : IsLineBundle T J) (n : ℕ) :
    (Scheme.Modules.pullback p).mapIso (pullback_tensorPower_iso B T q J n) ≪≫
      powerComparison p ((Scheme.Modules.pullback q).obj J)
        (squareComparison p q r t h J) n =
    squareComparison p q r t h (tensorPower T J n) ≪≫
      (Scheme.Modules.pullback r).mapIso (pullback_tensorPower_iso C T t J n) ≪≫
      pullback_tensorPower_iso A C r ((Scheme.Modules.pullback t).obj J) n := by
  let b := (Scheme.Modules.pullbackComp r t).app J
  have ha := power_triangle_iso p q (r ≫ t) h J hJ n
  have hb' : (Scheme.Modules.pullback r).mapIso (pullback_tensorPower_iso C T t J n) ≪≫
      pullback_tensorPower_iso A C r ((Scheme.Modules.pullback t).obj J) n ≪≫
      powerIso b n =
    (Scheme.Modules.pullbackComp r t).app (tensorPower T J n) ≪≫
      pullback_tensorPower_iso A T (r ≫ t) J n := by
    apply Iso.ext
    exact powerComparison_comp r t J hJ n
  apply Iso.ext
  apply (cancel_mono (powerIso b n).hom).mp
  change ((Scheme.Modules.pullback p).mapIso (pullback_tensorPower_iso B T q J n) ≪≫
    powerComparison p ((Scheme.Modules.pullback q).obj J) (squareComparison p q r t h J) n ≪≫
    powerIso b n).hom =
    (squareComparison p q r t h (tensorPower T J n) ≪≫
      ((Scheme.Modules.pullback r).mapIso (pullback_tensorPower_iso C T t J n) ≪≫
      pullback_tensorPower_iso A C r ((Scheme.Modules.pullback t).obj J) n ≪≫ powerIso b n)).hom
  rw [hb']
  have hc : powerComparison p ((Scheme.Modules.pullback q).obj J)
      (squareComparison p q r t h J) n ≪≫ powerIso b n =
      powerComparison p ((Scheme.Modules.pullback q).obj J) (triangle p q (r ≫ t) h J) n := by
    rw [← powerComparison_trans]
    simp only [squareComparison, b, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [hc, ha]
  simp only [squareComparison, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The tensor square remains compatible with the prescribed final line isomorphism. -/
theorem power_square_line_iso {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T)
    (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t)
    (J : T.Modules) (hJ : IsLineBundle T J) {H : C.Modules}
    (e : (Scheme.Modules.pullback t).obj J ≅ H) (n : ℕ) :
    (Scheme.Modules.pullback p).mapIso (pullback_tensorPower_iso B T q J n) ≪≫
      powerComparison p ((Scheme.Modules.pullback q).obj J)
        (squareComparison p q r t h J ≪≫ (Scheme.Modules.pullback r).mapIso e) n =
    squareComparison p q r t h (tensorPower T J n) ≪≫
      (Scheme.Modules.pullback r).mapIso (powerComparison t J e n) ≪≫
      pullback_tensorPower_iso A C r H n := by
  have hn : (Scheme.Modules.pullback r).mapIso (powerIso e n) ≪≫
      pullback_tensorPower_iso A C r H n =
    pullback_tensorPower_iso A C r ((Scheme.Modules.pullback t).obj J) n ≪≫
      powerIso ((Scheme.Modules.pullback r).mapIso e) n := by
    apply Iso.ext
    exact power_naturality r (pullback_isLineBundle t J hJ) e n
  rw [powerComparison_trans, ← Iso.trans_assoc, power_square_iso p q r t h J hJ n]
  simp only [Iso.trans_assoc]
  rw [← hn]
  simp only [powerComparison, Functor.mapIso_trans, Iso.trans_assoc]

/-- Commuting squares identify the two successive global pullbacks. -/
theorem square_global {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T)
    (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t)
    (J : T.Modules) (s : Sections J) :
    (squareComparison p q r t h J).hom.app ⊤
      (pullbackGlobalSection p ((Scheme.Modules.pullback q).obj J)
        (pullbackGlobalSection q J s)) =
    pullbackGlobalSection r ((Scheme.Modules.pullback t).obj J)
      (pullbackGlobalSection t J s) := by
  have hc : ((Scheme.Modules.pullbackCongr h).app J).hom.app ⊤
      (pullbackGlobalSection (p ≫ q) J s) = pullbackGlobalSection (r ≫ t) J s := by
    simpa [pullbackSectionLE, pullbackGlobalSection, pullbackLocalSection]
      using pullbackCongr_sectionLE h J ⊤ ⊤ le_rfl s
  change ((Scheme.Modules.pullbackComp r t).app J).inv.app ⊤
    (((Scheme.Modules.pullbackCongr h).app J).hom.app ⊤
      (((Scheme.Modules.pullbackComp p q).app J).hom.app ⊤
        (pullbackGlobalSection p _ (pullbackGlobalSection q J s)))) = _
  erw [pullbackComp_hom_unit p q J ⊤ s]
  erw [hc]
  exact pullbackComp_inv_unit r t J ⊤ s

/-- Transport of the pulled power section through the specified square and line. -/
theorem pulled_power_square {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T)
    (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t)
    (J : T.Modules) (hJ : IsLineBundle T J) {H : C.Modules}
    (e : (Scheme.Modules.pullback t).obj J ≅ H) (n : ℕ)
    (F : Sections (tensorPower T J n)) :
    (powerComparison p ((Scheme.Modules.pullback q).obj J)
      (squareComparison p q r t h J ≪≫ (Scheme.Modules.pullback r).mapIso e) n).hom.app ⊤
      (pullbackGlobalSection p _ (pulledPower q J n F)) =
    pulledPower r H n ((powerComparison t J e n).hom.app ⊤
      (pullbackGlobalSection t _ F)) := by
  unfold pulledPower
  erw [pullbackGlobalSection_map, pullbackGlobalSection_map]
  have hh := ConcreteCategory.congr_hom (congrArg (fun k => k.app ⊤)
    (congrArg Iso.hom (power_square_line_iso p q r t h J hJ e n)))
    (pullbackGlobalSection p _ (pullbackGlobalSection q _ F))
  simp only [Iso.trans_hom, Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply] at hh
  exact hh.trans (congrArg (fun s => (pullback_tensorPower_iso A C r H n).hom.app ⊤
    (((Scheme.Modules.pullback r).map (powerComparison t J e n).hom).app ⊤ s))
    (square_global p q r t h (tensorPower T J n) F))

/-- Global sections of a model line are faithfully detected by its actual projection. -/
theorem model_sections_injective {X : Curve Omega} {K : FieldStage} (M : Model X K)
    (J : M.curve.space.Modules) (hJ : IsLineBundle M.curve.space J) :
    Function.Injective (pullbackGlobalSection M.projection J) := by
  intro a b hab
  choose U hx es using hJ
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨J.presheaf, J.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top)
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  intro x
  let e := localFrameOfIso M.curve.space J (U x) (Classical.choice (es x))
  let a' := (e.equiv (U x) le_rfl).symm (J.presheaf.map (homOfLE le_top).op a)
  let b' := (e.equiv (U x) le_rfl).symm (J.presheaf.map (homOfLE le_top).op b)
  have h : M.projection.app (U x) a' = M.projection.app (U x) b' := by
    apply ((pulledFrame M.projection e).equiv (M.projection ⁻¹ᵁ U x) le_rfl).injective
    rw [← pulledFrame_compatible M.projection e (U x) le_rfl a',
      ← pulledFrame_compatible M.projection e (U x) le_rfl b']
    simp only [a', b', LinearEquiv.apply_symm_apply]
    rw [pullbackLocalSection_restrict, pullbackLocalSection_restrict]
    exact congrArg (fun s => ((Scheme.Modules.pullback M.projection).obj J).presheaf.map
      (homOfLE (M.projection.preimage_mono (show U x ≤ ⊤ from le_top))).op s) hab
  have h' := model_projection_app_injective_all M (U x) h
  exact (e.equiv (U x) le_rfl).symm.injective h'

end RootEquationReflection

/-- Root equations are preserved and reflected through the actual constant-field models. -/
theorem root_equation_cartesian_reflection
    (X Y : Curve Omega) (K : FieldStage) (M : Model X K) (N : Model Y K)
    (f : Y.space ⟶ X.space) (g : N.curve.space ⟶ M.curve.space)
    (hc : N.projection ≫ g = f ≫ M.projection)
    (H0 : M.curve.space.Modules) (hH0 : IsLineBundle M.curve.space H0)
    (H : X.space.Modules) (e : (Scheme.Modules.pullback M.projection).obj H0 ≅ H)
    (n : ℕ) (F0 : Sections (tensorPower M.curve.space H0 n))
    (r0 : Sections ((Scheme.Modules.pullback g).obj H0)) :
    RootEquation g H0 n F0 r0 ↔
    RootEquation f H n
      ((powerComparison M.projection H0 e n).hom.app ⊤
        (pullbackGlobalSection M.projection (tensorPower M.curve.space H0 n) F0))
      ((coverLineComparison M N f g hc H0 e).hom.app ⊤
        (pullbackGlobalSection N.projection ((Scheme.Modules.pullback g).obj H0) r0)) := by
  let J := (Scheme.Modules.pullback g).obj H0
  let E := coverLineComparison M N f g hc H0 e
  let P := powerComparison N.projection J E n
  let transport (s : Sections (tensorPower N.curve.space J n)) :=
    P.hom.app ⊤ (pullbackGlobalSection N.projection _ s)
  have hi : Function.Injective transport :=
    (ConcreteCategory.bijective_of_isIso (P.hom.app ⊤)).injective.comp
      (RootEquationReflection.model_sections_injective N _
        (tensorPower_isLineBundle J (pullback_isLineBundle g H0 hH0) n))
  have hl : transport (tensorPowerSection N.curve.space J n ⊤ r0) =
      tensorPowerSection Y.space ((Scheme.Modules.pullback f).obj H) n ⊤
        (E.hom.app ⊤ (pullbackGlobalSection N.projection J r0)) :=
    powerComparison_local N.projection J E n ⊤ r0
  have hr : transport (pulledPower g H0 n F0) =
      pulledPower f H n ((powerComparison M.projection H0 e n).hom.app ⊤
        (pullbackGlobalSection M.projection _ F0)) :=
    RootEquationReflection.pulled_power_square N.projection g f M.projection hc H0 hH0 e n F0
  unfold RootEquation
  constructor
  · intro h
    exact hl.symm.trans ((congrArg transport h).trans hr)
  · intro h
    apply hi
    exact hl.trans (h.trans hr.symm)

end ArithmeticThetaRamifiedRootModelsR0222

#print axioms ArithmeticThetaRamifiedRootModelsR0222.root_equation_cartesian_reflection
