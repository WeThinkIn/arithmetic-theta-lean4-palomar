import FiniteLineHomsModelR0221

/-! Finite-stage descent of genuine sections, through morphisms from the unit sheaf. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaSheafTensor
open ArithmeticThetaNormalizedSections FiniteLineHoms

/-- A section on the top open gives its actual compatible restriction family. -/
def sectionFamily {Y : Scheme} (H : Y.Modules) (s : Sections H) : H.sections :=
  PresheafOfModules.sectionsMk
    (fun U => H.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (fun {U V} f => by
      change H.presheaf.map f (H.presheaf.map (homOfLE le_top).op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- Multiplication by the restrictions of a global section. -/
def sectionHom {Y : Scheme} (H : Y.Modules) (s : Sections H) :
    Scheme.Modules.Hom (SheafOfModules.unit Y.ringCatSheaf) H :=
  H.unitHomEquiv.symm (sectionFamily H s)

theorem sectionHom_apply {Y : Scheme} (H : Y.Modules) (s : Sections H)
    (U : Y.Opens) (r : Γ(Y, U)) :
    (sectionHom H s).app U r = r • H.presheaf.map (homOfLE le_top).op s := rfl

@[simp] theorem sectionHom_one {Y : Scheme} (H : Y.Modules) (s : Sections H) :
    (sectionHom H s).app ⊤ (1 : Γ(Y, ⊤)) = s := by
  rw [sectionHom_apply, one_smul]
  change H.presheaf.map (𝟙 (op ⊤)) s = s
  simp

/-- The structure sheaf is a line in the frozen local-triviality definition. -/
theorem unit_isLineBundle (Y : Scheme) :
    IsLineBundle Y (SheafOfModules.unit Y.ringCatSheaf) := by
  intro x
  exact ⟨⊤, Set.mem_univ x, ⟨localFrameIso Y _ ⊤ (unitFrame Y ⊤)⟩⟩

/-- Every tensor power is a line, including exponent zero. -/
theorem tensorPower_isLineBundle {Y : Scheme} (J : Y.Modules)
    (hJ : IsLineBundle Y J) (n : ℕ) : IsLineBundle Y (tensorPower Y J n) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hJ x
  exact ⟨U, hx, ⟨localFrameIso Y _ U
    (tensorPowerFrame Y J U (localFrameOfIso Y J U e) n)⟩⟩

/-- Naturality of the actual adjunction-unit map on global sections. -/
theorem pullbackGlobalSection_map {Y Z : Scheme} (p : Y ⟶ Z)
    {J H : Z.Modules} (f : J ⟶ H) (s : Sections J) :
    pullbackGlobalSection p H (f.app ⊤ s) =
      ((Scheme.Modules.pullback p).map f).app ⊤ (pullbackGlobalSection p J s) :=
  (pullbackLocalSection_map p f ⊤ s).symm

/-- The canonical refinement comparison preserves two successive global pullbacks. -/
theorem refinementComparison_global {X : Curve Omega} {K K' : FieldStage}
    {M : Model X K} {N : Model X K'} (E : Refinement M N)
    (J : M.curve.space.Modules) (s : Sections J) :
    (refinementComparison E J).hom.app ⊤
      (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj J)
        (pullbackGlobalSection E.map J s)) = pullbackGlobalSection M.projection J s := by
  simpa [pullbackSectionLE, pullbackGlobalSection, pullbackLocalSection]
    using refinementComparison_unit E J ⊤ s

/-- Finite families of sections of one model line descend via the frozen hom theorem. -/
theorem finite_line_sections (X : Curve Omega) (K0 : FieldStage)
    (hK0 : FiniteDimensional ℚ K0) (M : Model X K0)
    (H : M.curve.space.Modules) (hH : IsLineBundle M.curve.space H)
    (s : ℕ) (a : Fin s → Sections ((Scheme.Modules.pullback M.projection).obj H)) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (N : Model X K) (E : Refinement M N)
      (a0 : Fin s → Sections ((Scheme.Modules.pullback E.map).obj H)),
      ∀ i, (refinementComparison E H).hom.app ⊤
        (pullbackGlobalSection N.projection ((Scheme.Modules.pullback E.map).obj H) (a0 i)) = a i := by
  let U : M.curve.space.Modules := SheafOfModules.unit M.curve.space.ringCatSheaf
  let b (i : Fin s) : (Scheme.Modules.pullback M.projection).obj U ⟶
      (Scheme.Modules.pullback M.projection).obj H :=
    (pullback_unit_iso X.space M.curve.space M.projection).hom ≫ sectionHom _ (a i)
  obtain ⟨K, hK, N, E, b0, hb, _, _⟩ := finite_line_homs_model X K0 hK0 M U H
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
theorem extensionMap_trans {K K' K'' : FieldStage} (h : K ≤ K') (h' : K' ≤ K'') :
    extensionMap h' ≫ extensionMap h = extensionMap (h.trans h') := by
  unfold extensionMap
  rw [← Spec.map_comp]
  rfl

/-- Successive enlargements give a refinement with its genuine pasted Cartesian square. -/
def composeRefinement {X : Curve Omega} {K K' K'' : FieldStage}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) : Refinement M P where
  inclusion := E.inclusion.trans F.inclusion
  map := F.map ≫ E.map
  cartesian := by
    simpa only [extensionMap_trans] using F.cartesian.paste_horiz E.cartesian
  comparison := by rw [← Category.assoc, F.comparison, E.comparison]

/-- Associativity for the canonical scheme-module pullback comparisons. -/
theorem pullbackComp_assoc {W X Y Z : Scheme} (p : W ⟶ X) (q : X ⟶ Y) (r : Y ⟶ Z)
    (H : Z.Modules) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp q r).app H).hom ≫
      ((Scheme.Modules.pullbackComp p (q ≫ r)).app H).hom ≫
      ((Scheme.Modules.pullbackCongr (Category.assoc p q r).symm).app H).hom =
    ((Scheme.Modules.pullbackComp p q).app ((Scheme.Modules.pullback r).obj H)).hom ≫
      ((Scheme.Modules.pullbackComp (p ≫ q) r).app H).hom := by
  have h := congrArg (fun t => t.app H) (Scheme.Modules.pseudofunctor_associativity p q r)
  have hh := congrArg (fun t =>
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp q r).app H).hom ≫
      ((Scheme.Modules.pullbackComp p (q ≫ r)).app H).hom ≫ t) h
  simpa [Scheme.Modules.pullbackCongr, Category.assoc, ← Functor.map_comp] using hh.symm

/-- Associativity with both triangles explicitly retained. -/
theorem pullback_triangle_comp {W X Y Z : Scheme} (p : W ⟶ X) (q : X ⟶ Y) (r : Y ⟶ Z)
    (t : W ⟶ Y) (u : W ⟶ Z) (ht : p ≫ q = t) (hu : t ≫ r = u)
    (h : p ≫ (q ≫ r) = u) (H : Z.Modules) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp q r).app H).hom ≫
      ((Scheme.Modules.pullbackComp p (q ≫ r)).app H).hom ≫
      ((Scheme.Modules.pullbackCongr h).app H).hom =
    ((Scheme.Modules.pullbackComp p q).app ((Scheme.Modules.pullback r).obj H)).hom ≫
      ((Scheme.Modules.pullbackCongr ht).app ((Scheme.Modules.pullback r).obj H)).hom ≫
      ((Scheme.Modules.pullbackComp t r).app H).hom ≫
      ((Scheme.Modules.pullbackCongr hu).app H).hom := by
  subst t
  subst u
  simpa [Scheme.Modules.pullbackCongr] using pullbackComp_assoc p q r H

/-- The frozen comparisons are compatible with successive refinements. -/
theorem refinementComparison_comp {X : Curve Omega} {K K' K'' : FieldStage}
    {M : Model X K} {N : Model X K'} {P : Model X K''}
    (E : Refinement M N) (F : Refinement N P) (H : M.curve.space.Modules) :
    (Scheme.Modules.pullback P.projection).map ((Scheme.Modules.pullbackComp F.map E.map).app H).hom ≫
      (refinementComparison (composeRefinement E F) H).hom =
    (refinementComparison F ((Scheme.Modules.pullback E.map).obj H)).hom ≫
      (refinementComparison E H).hom := by
  exact pullback_triangle_comp P.projection F.map E.map N.projection M.projection
    F.comparison E.comparison (composeRefinement E F).comparison H

/-- A section already descended to a stage remains descended after any further refinement. -/
theorem refinementComparison_comp_section {X : Curve Omega} {K K' K'' : FieldStage}
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
theorem refinementComparison_comp_image {X : Curve Omega} {K K' K'' : FieldStage}
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
theorem finite_line_family (X : Curve Omega) (s : ℕ) :
    ∀ (K0 : FieldStage), FiniteDimensional ℚ K0 → ∀ (M : Model X K0)
      (H : Fin s → M.curve.space.Modules),
      (∀ i, IsLineBundle M.curve.space (H i)) →
      ∀ (a : ∀ i, Sections ((Scheme.Modules.pullback M.projection).obj (H i))),
      ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (N : Model X K) (E : Refinement M N)
        (a0 : ∀ i, Sections ((Scheme.Modules.pullback E.map).obj (H i))),
        ∀ i, (refinementComparison E (H i)).hom.app ⊤
          (pullbackGlobalSection N.projection _ (a0 i)) = a i := by
  induction s with
  | zero =>
    intro K hK M H hH a
    exact ⟨K, hK, M, identityRefinement M, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  | succ s ih =>
    intro K hK M H hH a
    obtain ⟨K1, hK1, N, E, a0, ha0⟩ := ih K hK M (fun i => H i.succ)
      (fun i => hH i.succ) (fun i => a i.succ)
    let J := (Scheme.Modules.pullback E.map).obj (H 0)
    let b : Sections ((Scheme.Modules.pullback N.projection).obj J) :=
      (refinementComparison E (H 0)).inv.app ⊤ (a 0)
    obtain ⟨K2, hK2, P, F, b0, hb0⟩ := finite_line_sections X K1 hK1 N J
      (pullback_isLineBundle E.map (H 0) (hH 0)) 1 (fun _ => b)
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

/-- The tensor comparison law on every open, needed for local-frame detection. -/
theorem pullback_sheafTensor_local (X Y : Scheme) (p : X ⟶ Y)
    (H K : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (pullback_sheafTensor_iso X Y p H K).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (sheafTensor Y H K) U (tensorSection Y H K U s t)) =
    tensorSection X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K)
      (p ⁻¹ᵁ U) (pullbackLocalSection p H U s) (pullbackLocalSection p K U t) := by
  change (sheafTensorCongr X
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm).hom.app (p ⁻¹ᵁ U)
    ((sheafificationTensorIso X ((presheafPullback X Y p).obj H.val)
      ((presheafPullback X Y p).obj K.val)).hom.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (presheafPullbackTensorMap X Y p H.val K.val)).val.app (op (p ⁻¹ᵁ U))
        (((SheafOfModules.sheafificationCompPullback p.toRingCatSheafHom).app
          (tensorPresheaf Y H K)).hom.val.app (op (p ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
            (sheafTensor Y H K)).app U
            (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              (tensorPresheaf Y H K)).app (op U) (s ⊗ₜ[Γ(Y, U)] t)))))) = _
  erw [sheafificationCompPullback_unit_apply X Y p (tensorPresheaf Y H K) U
    (s ⊗ₜ[Γ(Y, U)] t)]
  erw [sheafifyMap_unit_apply X (presheafPullbackTensorMap X Y p H.val K.val)
    (p ⁻¹ᵁ U)]
  erw [presheafPullbackTensorMap_unit_apply X Y p H.val K.val U s t]
  erw [sheafificationTensorIso_unit_apply X ((presheafPullback X Y p).obj H.val)
    ((presheafPullback X Y p).obj K.val) (p ⁻¹ᵁ U)]
  erw [sheafTensorCongr_section X
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm (p ⁻¹ᵁ U)]
  change tensorSection X _ _ (p ⁻¹ᵁ U)
    (((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).inv.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((presheafPullback X Y p).obj H.val)).app (op (p ⁻¹ᵁ U))
        (((presheafAdjunction X Y p).unit.app H.val).app (op U) s)))
    (((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).inv.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((presheafPullback X Y p).obj K.val)).app (op (p ⁻¹ᵁ U))
        (((presheafAdjunction X Y p).unit.app K.val).app (op U) t))) = _
  erw [pullbackIso_inv_unit_apply X Y p H U s, pullbackIso_inv_unit_apply X Y p K U t]
  rfl


/-- The power comparison on every local pure power. -/
theorem pullback_tensorPower_local {X Y : Scheme} (p : X ⟶ Y) (H : Y.Modules)
    (n : ℕ) (U : Y.Opens) (s : Γ(H, U)) :
    (pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower Y H n) U (tensorPowerSection Y H n U s)) =
    tensorPowerSection X ((Scheme.Modules.pullback p).obj H) n (p ⁻¹ᵁ U)
      (pullbackLocalSection p H U s) := by
  induction n with
  | zero =>
    simpa only [tensorPowerSection, tensorPower, pullback_tensorPower_iso, map_one]
      using pullback_unit_local p U 1
  | succ n ih =>
    change (sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)).hom.app
      (p ⁻¹ᵁ U) ((pullback_sheafTensor_iso X Y p (tensorPower Y H n) H).hom.app (p ⁻¹ᵁ U)
        (pullbackLocalSection p (sheafTensor Y (tensorPower Y H n) H) U
          (tensorSection Y (tensorPower Y H n) H U (tensorPowerSection Y H n U s) s))) = _
    rw [pullback_sheafTensor_local, sheafTensorCongr_section, ih]
    rfl

/-- A line comparison acts on powers of local sections by its underlying map. -/
theorem powerIso_section {X : Scheme} {H J : X.Modules} (e : H ≅ J)
    (n : ℕ) (U : X.Opens) (s : Γ(H, U)) :
    (powerIso e n).hom.app U (tensorPowerSection X H n U s) =
      tensorPowerSection X J n U (e.hom.app U s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sheafTensorCongr X (powerIso e n) e).hom.app U
      (tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s) = _
    rw [sheafTensorCongr_section, ih]
    rfl

/-- The prescribed composite power comparison preserves local pure powers. -/
theorem powerComparison_local {X Y : Scheme} (p : X ⟶ Y) (H : Y.Modules)
    {J : X.Modules} (e : (Scheme.Modules.pullback p).obj H ≅ J)
    (n : ℕ) (U : Y.Opens) (s : Γ(H, U)) :
    (powerComparison p H e n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower Y H n) U (tensorPowerSection Y H n U s)) =
    tensorPowerSection X J n (p ⁻¹ᵁ U) (e.hom.app (p ⁻¹ᵁ U) (pullbackLocalSection p H U s)) := by
  change (powerIso e n).hom.app (p ⁻¹ᵁ U)
    ((pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower Y H n) U (tensorPowerSection Y H n U s))) = _
  rw [pullback_tensorPower_local, powerIso_section]

/-- Maps from a line are detected on local frame generators, with arbitrary target sheaf. -/
theorem hom_ext_frames {Y : Scheme} {J H : Y.Modules} {I : Type*}
    (U : I → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame Y J (U i)) (f g : J ⟶ H)
    (h : ∀ i, f.app (U i) ((e i).equiv (U i) le_rfl 1) =
      g.app (U i) ((e i).equiv (U i) le_rfl 1)) : f = g := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro t
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
  · intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · intro i
    rw [hom_restrict, hom_restrict]
    obtain ⟨r, hr⟩ := ((e i).equiv (V ⊓ U i) inf_le_right).surjective
      (J.presheaf.map (homOfLE inf_le_left).op t)
    rw [← hr]
    have he : (e i).equiv (V ⊓ U i) inf_le_right r =
        r • (e i).equiv (V ⊓ U i) inf_le_right 1 := by
      simpa using ((e i).equiv (V ⊓ U i) inf_le_right).map_smul r (1 : Γ(Y, V ⊓ U i))
    rw [he, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
    congr 1
    have hh := congrArg (fun t => H.presheaf.map
      (homOfLE (inf_le_right : V ⊓ U i ≤ U i)).op t) (h i)
    simpa only [hom_restrict, (e i).naturality, map_one] using hh

/-- Tensor comparisons commute with a genuine two-step scheme pullback. -/
theorem powerComparison_comp {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (hJ : IsLineBundle Z J) (n : ℕ) :
    (Scheme.Modules.pullback p).map (pullback_tensorPower_iso Y Z q J n).hom ≫
      (powerComparison p ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullbackComp p q).app J) n).hom =
    ((Scheme.Modules.pullbackComp p q).app (tensorPower Z J n)).hom ≫
      (pullback_tensorPower_iso X Z (p ≫ q) J n).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  choose U hx e using hJ
  refine hom_ext_frames (I := Z) (Y := Z) (J := tensorPower Z J n) U ?_ (fun (x : Z) =>
    tensorPowerFrame Z J (U x) (localFrameOfIso Z J (U x) (Classical.choice (e x))) n) _ _ ?_
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  intro x
  let e0 := localFrameOfIso Z J (U x) (Classical.choice (e x))
  have he : (tensorPowerFrame Z J (U x) e0 n).equiv (U x) le_rfl 1 =
      tensorPowerSection Z J n (U x) (e0.equiv (U x) le_rfl 1) := by
    simpa only [one_pow] using (tensorPowerSection_frame Z J (U x) e0 n (U x) le_rfl 1).symm
  change _ = _
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Scheme.Modules.pushforward_map_app]
  change (powerComparison p ((Scheme.Modules.pullback q).obj J)
      ((Scheme.Modules.pullbackComp p q).app J) n).hom.app (p ⁻¹ᵁ (q ⁻¹ᵁ U x))
    (((Scheme.Modules.pullback p).map (pullback_tensorPower_iso Y Z q J n).hom).app _
      (pullbackLocalSection p ((Scheme.Modules.pullback q).obj (tensorPower Z J n)) (q ⁻¹ᵁ U x)
        (pullbackLocalSection q (tensorPower Z J n) (U x)
          ((tensorPowerFrame Z J (U x) e0 n).equiv (U x) le_rfl 1)))) =
    (pullback_tensorPower_iso X Z (p ≫ q) J n).hom.app _
      (((Scheme.Modules.pullbackComp p q).app (tensorPower Z J n)).hom.app _
        (pullbackLocalSection p _ (q ⁻¹ᵁ U x) (pullbackLocalSection q _ (U x)
          ((tensorPowerFrame Z J (U x) e0 n).equiv (U x) le_rfl 1))))
  rw [he, pullbackLocalSection_map, pullback_tensorPower_local, powerComparison_local]
  erw [pullbackComp_hom_unit p q J (U x),
    pullbackComp_hom_unit p q (tensorPower Z J n) (U x)]
  exact (pullback_tensorPower_local (p ≫ q) J n (U x) (e0.equiv (U x) le_rfl 1)).symm

/-- Composition compatibility retaining a specified equality of geometric maps. -/
theorem powerComparison_triangle {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (t : X ⟶ Z) (h : p ≫ q = t) (J : Z.Modules) (hJ : IsLineBundle Z J) (n : ℕ) :
    (Scheme.Modules.pullback p).map (pullback_tensorPower_iso Y Z q J n).hom ≫
      (powerComparison p ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullbackComp p q).app J ≪≫ (Scheme.Modules.pullbackCongr h).app J) n).hom =
    (((Scheme.Modules.pullbackComp p q).app (tensorPower Z J n)) ≪≫
      (Scheme.Modules.pullbackCongr h).app (tensorPower Z J n)).hom ≫
      (pullback_tensorPower_iso X Z t J n).hom := by
  subst t
  have he : (Scheme.Modules.pullbackCongr (rfl : p ≫ q = p ≫ q)).app J = Iso.refl _ := rfl
  rw [he, Iso.trans_refl]
  simpa [Scheme.Modules.pullbackCongr] using powerComparison_comp p q J hJ n

/-- The exact tensor square required to use finite section descent on model powers. -/
theorem powerComparison_refinement {X : Curve Omega} {K K' : FieldStage}
    {M : Model X K} {N : Model X K'} (E : Refinement M N) (J : M.curve.space.Modules)
    (hJ : IsLineBundle M.curve.space J) (n : ℕ) :
    (Scheme.Modules.pullback N.projection).map
        (pullback_tensorPower_iso N.curve.space M.curve.space E.map J n).hom ≫
      (powerComparison N.projection ((Scheme.Modules.pullback E.map).obj J)
        (refinementComparison E J) n).hom =
    (refinementComparison E (tensorPower M.curve.space J n)).hom ≫
      (pullback_tensorPower_iso X.space M.curve.space M.projection J n).hom := by
  exact powerComparison_triangle N.projection E.map M.projection E.comparison J hJ n

end ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.sectionHom_one
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.tensorPower_isLineBundle
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.refinementComparison_global

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.finite_line_sections

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.composeRefinement
#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.pullbackComp_assoc

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.refinementComparison_comp_section

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.finite_line_family

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.pullback_sheafTensor_local

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.powerComparison_comp

#print axioms ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections.powerComparison_refinement

namespace ArithmeticThetaFiniteFieldModelsR0221
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open FinitePowerSections

/-- Every finite family of genuine sections of model-line powers descends over one finite field. -/
theorem finite_power_sections_model (X : Curve Omega) (K0 : FieldStage)
    (hK0 : FiniteDimensional ℚ K0) (M : Model X K0) (J : M.curve.space.Modules)
    (hJ : IsLineBundle M.curve.space J) (s : ℕ) (d : Fin s → ℕ)
    (a : ∀ i, Sections (tensorPower X.space ((Scheme.Modules.pullback M.projection).obj J) (d i))) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (M1 : Model X K) (E : Refinement M M1)
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

end ArithmeticThetaFiniteFieldModelsR0221

#print axioms ArithmeticThetaFiniteFieldModelsR0221.finite_power_sections_model
