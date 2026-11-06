module

public import LineHomsConstantExtensionR0225

@[expose] public section

/-! Finite families of sections of model-line powers over arbitrary constant fields.
The general sheaf and tensor coherence theorems are reused from r0221. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections powerComparison)
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms (pullbackSectionLE)
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaSheafTensor ArithmeticThetaNormalizedSections
namespace PowerSections
variable {k : Type} [Field k] [CharZero k]

/-- The canonical refinement comparison preserves two successive global pullbacks. -/
theorem refinementComparison_global {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N)
    (J : M.curve.space.Modules) (s : Sections J) :
    (refinementComparison E J).hom.app ⊤
      (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj J)
        (pullbackGlobalSection E.map J s)) = pullbackGlobalSection M.projection J s := by
  simpa [pullbackSectionLE, pullbackGlobalSection, pullbackLocalSection]
    using LineHoms.refinementComparison_unit E J ⊤ s

/-- Finite families of sections of one model line descend via the frozen hom theorem. -/
theorem finite_line_sections (X : Curve (Omega k)) (K0 : (FieldStage k))
    (hK0 : FiniteDimensional k K0) (M : Model X K0)
    (H : M.curve.space.Modules) (hH : IsLineBundle M.curve.space H)
    (s : ℕ) (a : Fin s → Sections ((Scheme.Modules.pullback M.projection).obj H)) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ ∃ (N : Model X K) (E : Refinement M N)
      (a0 : Fin s → Sections ((Scheme.Modules.pullback E.map).obj H)),
      ∀ i, (refinementComparison E H).hom.app ⊤
        (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj H) (a0 i)) = a i := by
  let U : M.curve.space.Modules := SheafOfModules.unit M.curve.space.ringCatSheaf
  let b (i : Fin s) : (Scheme.Modules.pullback M.projection).obj U ⟶
      (Scheme.Modules.pullback M.projection).obj H :=
    (pullback_unit_iso X.space M.curve.space M.projection).hom ≫ sectionHom _ (a i)
  obtain ⟨K, hK, N, E, b0, hb, _, _⟩ := line_homs_constant_extension k X K0 hK0 M U H
    (unit_isLineBundle _) hH s b
  let one0 : Sections U := (1 : Γ(M.curve.space, ⊤))
  let t : Sections ((Scheme.Modules.pullback E.map).obj U) := pullbackGlobalSection E.map U one0
  refine ⟨K, hK, N, E, (fun i => (b0 i).app ⊤ t), ?_⟩
  intro i
  erw [pullbackGlobalSection_map]
  have hh := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤) (hb i))
    (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj U) t)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hh
  refine hh.trans ?_
  change (b i).app ⊤ ((refinementComparison E U).hom.app ⊤
    (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj U)
      (pullbackGlobalSection E.map U one0))) = _
  rw [refinementComparison_global]
  change (sectionHom _ (a i)).app ⊤
    ((pullback_unit_iso X.space M.curve.space M.projection).hom.app ⊤
      (pullbackGlobalSection M.projection U one0)) = _
  rw [show (pullback_unit_iso X.space M.curve.space M.projection).hom.app ⊤
      (pullbackGlobalSection M.projection U one0) = (1 : Γ(X.space, ⊤)) from
    pullback_unit_section X.space M.curve.space M.projection]
  exact sectionHom_one _ _


/-- The maps of spectra compose with the actual intermediate-field inclusions. -/
theorem extensionMap_trans {K K' K'' : (FieldStage k)} (h : K ≤ K') (h' : K' ≤ K'') :
    extensionMap h' ≫ extensionMap h = extensionMap (h.trans h') := by
  unfold extensionMap
  rw [← Spec.map_comp]
  rfl

/-- Successive enlargements give a refinement with its genuine pasted Cartesian square. -/
def composeRefinement {X : Curve (Omega k)} {K K' K'' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) : Refinement M P where
  inclusion := E.inclusion.trans F.inclusion
  map := F.map ≫ E.map
  cartesian := by
    simpa only [extensionMap_trans] using F.cartesian.paste_horiz E.cartesian
  comparison := by rw [← Category.assoc, F.comparison, E.comparison]

/-- The frozen comparisons are compatible with successive refinements. -/
theorem refinementComparison_comp {X : Curve (Omega k)} {K K' K'' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) (H : M.curve.space.Modules) :
    (Scheme.Modules.pullback P.projection).map ((Scheme.Modules.pullbackComp F.map E.map).app H).hom ≫
      (refinementComparison (composeRefinement E F) H).hom =
    (refinementComparison F ((Scheme.Modules.pullback E.map).obj H)).hom ≫
      (refinementComparison E H).hom := by
  exact pullback_triangle_comp P.projection F.map E.map N.projection M.projection
    F.comparison E.comparison (composeRefinement E F).comparison H

/-- A section already descended to a stage remains descended after any further refinement. -/
theorem refinementComparison_comp_section {X : Curve (Omega k)} {K K' K'' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) (H : M.curve.space.Modules)
    (s : Sections ((Scheme.Modules.pullback E.map).obj H)) :
    (refinementComparison (composeRefinement E F) H).hom.app ⊤
      (pullbackGlobalSection P.projection ((Scheme.Modules.pullback (composeRefinement E F).map).obj H)
        (((Scheme.Modules.pullbackComp F.map E.map).app H).hom.app ⊤
          (pullbackGlobalSection F.map ((Scheme.Modules.pullback E.map).obj H) s))) =
    (refinementComparison E H).hom.app ⊤
      (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj H) s) := by
  erw [pullbackGlobalSection_map]
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (refinementComparison_comp E F H))
    (pullbackGlobalSection P.projection
      ((Scheme.Modules.pullback F.map).obj ((Scheme.Modules.pullback E.map).obj H))
      (pullbackGlobalSection F.map ((Scheme.Modules.pullback E.map).obj H) s))
  refine h.trans ?_
  change (refinementComparison E H).hom.app ⊤
    ((refinementComparison F ((Scheme.Modules.pullback E.map).obj H)).hom.app ⊤
      (pullbackGlobalSection P.projection _ (pullbackGlobalSection F.map _ s))) = _
  rw [refinementComparison_global]

/-- The comparison equation on an arbitrary section at the twice-enlarged stage. -/
theorem refinementComparison_comp_image {X : Curve (Omega k)} {K K' K'' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) (H : M.curve.space.Modules)
    (t : Sections ((Scheme.Modules.pullback F.map).obj ((Scheme.Modules.pullback E.map).obj H))) :
    (refinementComparison (composeRefinement E F) H).hom.app ⊤
      (pullbackGlobalSection P.projection ((Scheme.Modules.pullback (composeRefinement E F).map).obj H)
        (((Scheme.Modules.pullbackComp F.map E.map).app H).hom.app ⊤ t)) =
    (refinementComparison E H).hom.app ⊤
      ((refinementComparison F ((Scheme.Modules.pullback E.map).obj H)).hom.app ⊤
        (pullbackGlobalSection P.projection _ t)) := by
  erw [pullbackGlobalSection_map]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (refinementComparison_comp E F H)) (pullbackGlobalSection P.projection _ t)

/-- A finite dependent family of sections of possibly different model lines descends together. -/
theorem finite_line_family (X : Curve (Omega k)) (s : ℕ) :
    ∀ (K0 : (FieldStage k)), FiniteDimensional k K0 → ∀ (M : Model X K0)
      (H : Fin s → M.curve.space.Modules),
      (∀ i, IsLineBundle M.curve.space (H i)) →
      ∀ (a : ∀ i, Sections ((Scheme.Modules.pullback M.projection).obj (H i))),
      ∃ K : (FieldStage k), FiniteDimensional k K ∧ ∃ (N : Model X K) (E : Refinement M N)
        (a0 : ∀ i, Sections ((Scheme.Modules.pullback E.map).obj (H i))),
        ∀ i, (refinementComparison E (H i)).hom.app ⊤
          (pullbackGlobalSection N.projection _ (a0 i)) = a i := by
  induction s with
  | zero =>
    intro K hK M H hH a
    exact ⟨K, hK, M, LineHoms.identityRefinement M, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  | succ s ih =>
    intro K hK M H hH a
    obtain ⟨K1, hK1, N, E, a0, ha0⟩ := ih K hK M (fun i => H i.succ)
      (fun i => hH i.succ) (fun i => a i.succ)
    let J := (Scheme.Modules.pullback E.map).obj (H 0)
    let b : Sections ((Scheme.Modules.pullback N.projection).obj J) :=
      (refinementComparison E (H 0)).inv.app ⊤ (a 0)
    obtain ⟨K2, hK2, P, F, b0, hb0⟩ := finite_line_sections X K1 hK1 N J
      (ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms.pullback_isLineBundle E.map (H 0) (hH 0)) 1 (fun _ => b)
    let c : ∀ i : Fin (s + 1), Sections ((Scheme.Modules.pullback (composeRefinement E F).map).obj (H i)) :=
      Fin.cases
        (((Scheme.Modules.pullbackComp F.map E.map).app (H 0)).hom.app ⊤ (b0 0))
        (fun i => ((Scheme.Modules.pullbackComp F.map E.map).app (H i.succ)).hom.app ⊤
          (pullbackGlobalSection F.map ((Scheme.Modules.pullback E.map).obj (H i.succ)) (a0 i)))
    refine ⟨K2, hK2, P, composeRefinement E F, c, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change (refinementComparison (composeRefinement E F) (H 0)).hom.app ⊤
        (pullbackGlobalSection P.projection _
          (((Scheme.Modules.pullbackComp F.map E.map).app (H 0)).hom.app ⊤ (b0 0))) = _
      rw [refinementComparison_comp_image]
      rw [hb0 0]
      exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
        (refinementComparison E (H 0)).inv_hom_id) (a 0)
    · exact (refinementComparison_comp_section E F (H i.succ) (a0 i)).trans (ha0 i)

/-- The exact tensor square required to use finite section descent on model powers. -/
theorem powerComparison_refinement {X : Curve (Omega k)} {K K' : (FieldStage k)}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) (J : M.curve.space.Modules)
    (hJ : IsLineBundle M.curve.space J) (n : ℕ) :
    (Scheme.Modules.pullback N.projection).map
        (pullback_tensorPower_iso N.curve.space M.curve.space E.map J n).hom ≫
      (powerComparison N.projection ((Scheme.Modules.pullback E.map).obj J)
        (refinementComparison E J) n).hom =
    (refinementComparison E (tensorPower M.curve.space J n)).hom ≫
      (pullback_tensorPower_iso X.space M.curve.space M.projection J n).hom := by
  exact powerComparison_triangle N.projection E.map M.projection E.comparison J hJ n

end PowerSections
open PowerSections

/-- Every finite family of genuine sections of model-line powers descends over one finite field. -/
theorem power_sections_constant_extension (k : Type) [Field k] [CharZero k] (X : Curve (Omega k)) (K0 : (FieldStage k))
    (hK0 : FiniteDimensional k K0) (M : Model X K0) (J : M.curve.space.Modules)
    (hJ : IsLineBundle M.curve.space J) (s : ℕ) (d : Fin s → ℕ)
    (a : ∀ i, Sections (tensorPower X.space ((Scheme.Modules.pullback M.projection).obj J) (d i))) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ ∃ (M1 : Model X K) (E : Refinement M M1)
      (a0 : ∀ i, Sections (tensorPower M1.curve.space ((Scheme.Modules.pullback E.map).obj J) (d i))),
      ∀ i, (powerComparison M1.projection ((Scheme.Modules.pullback E.map).obj J)
        (refinementComparison E J) (d i)).hom.app ⊤
        (pullbackGlobalSection M1.projection
          (tensorPower M1.curve.space ((Scheme.Modules.pullback E.map).obj J) (d i)) (a0 i)) = a i := by
  let H (i : Fin s) := tensorPower M.curve.space J (d i)
  let b (i : Fin s) : Sections ((Scheme.Modules.pullback M.projection).obj (H i)) :=
    (pullback_tensorPower_iso X.space M.curve.space M.projection J (d i)).inv.app ⊤ (a i)
  obtain ⟨K, hK, N, E, b0, hb0⟩ := finite_line_family X s K0 hK0 M H
    (fun i => tensorPower_isLineBundle J hJ (d i)) b
  let c (i : Fin s) : Sections (tensorPower N.curve.space ((Scheme.Modules.pullback E.map).obj J) (d i)) :=
    (pullback_tensorPower_iso N.curve.space M.curve.space E.map J (d i)).hom.app ⊤ (b0 i)
  refine ⟨K, hK, N, E, c, ?_⟩
  intro i
  change (powerComparison N.projection ((Scheme.Modules.pullback E.map).obj J)
    (refinementComparison E J) (d i)).hom.app ⊤
    (pullbackGlobalSection N.projection _
      ((pullback_tensorPower_iso N.curve.space M.curve.space E.map J (d i)).hom.app ⊤ (b0 i))) = _
  erw [pullbackGlobalSection_map]
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (powerComparison_refinement E J hJ (d i))) (pullbackGlobalSection N.projection _ (b0 i))
  refine h.trans ?_
  change (pullback_tensorPower_iso X.space M.curve.space M.projection J (d i)).hom.app ⊤
    ((refinementComparison E (H i)).hom.app ⊤ (pullbackGlobalSection N.projection _ (b0 i))) = _
  rw [hb0 i]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (pullback_tensorPower_iso X.space M.curve.space M.projection J (d i)).inv_hom_id) (a i)

end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.power_sections_constant_extension
