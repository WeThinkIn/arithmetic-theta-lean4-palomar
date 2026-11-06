import CanonicalCartierLineReductionR0133

/-! Descent of actual module-sheaf morphisms along open covers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

/-- Adjoint form of a local morphism to the structure sheaf. -/
def adjoint {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    M ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ q

/-- The adjoint of an iterated pullback is restriction of the adjoint's values. -/
lemma adjoint_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (q : (Scheme.Modules.pullback g).obj M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    adjoint (f ≫ g) ((Scheme.Modules.pullbackComp f g).inv.app M ≫ pulledInclusion f q) =
      adjoint g q ≫
        (Scheme.Modules.pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  unfold adjoint pulledInclusion
  rw [homEquiv_conjugate, Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv]
  change ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        ((Scheme.Modules.pullback f).map q ≫ unitPullback f)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (unitPullback f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    Equiv.apply_symm_apply _ _
  rw [hu, Category.assoc]

lemma adjoint_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (q : (Scheme.Modules.pullback g).obj M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (V : Z.Opens) (s : Γ(M, V)) :
    (adjoint (f ≫ g) ((Scheme.Modules.pullbackComp f g).inv.app M ≫ pulledInclusion f q)).app V s =
      f.app (g ⁻¹ᵁ V) ((adjoint g q).app V s) := by
  rw [adjoint_comp]
  rfl

lemma adjoint_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (q : (Scheme.Modules.pullback g).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    adjoint f ((Scheme.Modules.pullbackCongr h).hom.app M ≫ q) =
      adjoint g q ≫ (Scheme.Modules.pushforwardCongr h).inv.app (SheafOfModules.unit X.ringCatSheaf) := by
  subst h
  simp only [Scheme.Modules.pullbackCongr]
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change (adjoint f q).app W m =
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (eqToHom rfl).op ((adjoint f q).app W m)
  simp

/-- A commuting-square identity for local maps gives literal compatibility of their values. -/
lemma square_adjoint {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) (h : a ≫ f = g ≫ b) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (v : (Scheme.Modules.pullback b).obj M ⟶ (SheafOfModules.unit V.ringCatSheaf : V.Modules))
    (hq : (squareIso f a b g h M).hom ≫ pulledInclusion a q = pulledInclusion g v) :
    adjoint (a ≫ f) ((Scheme.Modules.pullbackComp a f).inv.app M ≫ pulledInclusion a q) =
      adjoint (a ≫ f) ((Scheme.Modules.pullbackCongr h).hom.app M ≫
        (Scheme.Modules.pullbackComp g b).inv.app M ≫ pulledInclusion g v) := by
  congr 1
  apply (cancel_epi ((Scheme.Modules.pullbackComp g b).hom.app M ≫
    (Scheme.Modules.pullbackCongr h.symm).hom.app M)).mp
  simpa [squareIso, Category.assoc, Scheme.Modules.pullbackCongr] using hq

/-- On an open contained in a chart, the chart's adjoint has a unique value downstairs. -/
def localValue {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (V : Y.Opens) (hV : V ≤ f.opensRange) : Γ(M, V) →+ Γ(Y, V) := by
  letI := f.isIso_app V hV
  exact (inv (f.app V)).hom.toAddMonoidHom.comp ((adjoint f q).app V).hom

lemma localValue_spec {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (V : Y.Opens) (hV : V ≤ f.opensRange) (m : Γ(M, V)) :
    f.app V (localValue f q V hV m) = (adjoint f q).app V m := by
  letI := f.isIso_app V hV
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (f.app V)) ((adjoint f q).app V m)

lemma localValue_smul {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (V : Y.Opens) (hV : V ≤ f.opensRange) (r : Γ(Y, V)) (m : Γ(M, V)) :
    localValue f q V hV (r • m) = r * localValue f q V hV m := by
  letI := f.isIso_app V hV
  apply (ConcreteCategory.bijective_of_isIso (f.app V)).1
  rw [map_mul, localValue_spec, localValue_spec]
  exact Scheme.Modules.Hom.app_smul (adjoint f q) r m

lemma localValue_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (V W : Y.Opens) (hWV : W ≤ V) (hV : V ≤ f.opensRange) (m : Γ(M, V)) :
    Y.presheaf.map (homOfLE hWV).op (localValue f q V hV m) =
      localValue f q W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op m) := by
  letI := f.isIso_app W (hWV.trans hV)
  apply (ConcreteCategory.bijective_of_isIso (f.app W)).1
  rw [localValue_spec]
  have hn := ConcreteCategory.congr_hom (f.naturality (homOfLE hWV).op)
    (localValue f q V hV m)
  change f.app W (Y.presheaf.map (homOfLE hWV).op (localValue f q V hV m)) =
    X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op
      (f.app V (localValue f q V hV m)) at hn
  rw [hn, localValue_spec]
  exact (ConcreteCategory.congr_hom ((adjoint f q).mapPresheaf.naturality (homOfLE hWV).op) m).symm

lemma localValue_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    {M : Z.Modules}
    (q : (Scheme.Modules.pullback g).obj M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (V : Z.Opens) (hV : V ≤ g.opensRange) (m : Γ(M, V)) :
    (f ≫ g).app V (localValue g q V hV m) =
      (adjoint (f ≫ g) ((Scheme.Modules.pullbackComp f g).inv.app M ≫ pulledInclusion f q)).app V m := by
  rw [adjoint_comp_apply]
  change f.app (g ⁻¹ᵁ V) (g.app V (localValue g q V hV m)) = _
  rw [localValue_spec]

lemma congr_app_adjoint {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (q : (Scheme.Modules.pullback g).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (V : Y.Opens) (m : Γ(M, V)) (z : Γ(Y, V))
    (hz : g.app V z = (adjoint g q).app V m) :
    f.app V z = (adjoint f ((Scheme.Modules.pullbackCongr h).hom.app M ≫ q)).app V m := by
  subst h
  simpa [Scheme.Modules.pullbackCongr] using hz

lemma localValue_square {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) [IsOpenImmersion f] [IsOpenImmersion b] [IsOpenImmersion a]
    (h : a ≫ f = g ≫ b) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (v : (Scheme.Modules.pullback b).obj M ⟶ (SheafOfModules.unit V.ringCatSheaf : V.Modules))
    (hq : (squareIso f a b g h M).hom ≫ pulledInclusion a q = pulledInclusion g v)
    (W : Y.Opens) (hf : W ≤ f.opensRange) (hb : W ≤ b.opensRange)
    (hW : W ≤ (a ≫ f).opensRange) (m : Γ(M, W)) :
    localValue f q W hf m = localValue b v W hb m := by
  letI := (a ≫ f).isIso_app W hW
  apply (ConcreteCategory.bijective_of_isIso ((a ≫ f).app W)).1
  rw [localValue_comp a f q]
  have he := square_adjoint f a b g h M q v hq
  rw [he]
  exact (congr_app_adjoint h _ W m (localValue b v W hb m)
    (localValue_comp g b v W hb m)).symm

/-- A natural linear map on a topological basis extends to a module-sheaf morphism. -/
lemma extend_linear_hom {X : Scheme.{u}} {M N : X.Modules} {ι : Type*}
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (β : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf)
    (hβ : ∀ (i : ι) (r : Γ(X, B i)) (m : Γ(M, B i)),
      β.app (Opposite.op i) (r • m) = (N.smul (U := B i) r).hom (β.app (Opposite.op i) m)) :
    ∃ φ : M ⟶ N, ∀ i, φ.app (B i) = β.app (Opposite.op i) := by
  let α := TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB β
  have hres (i : ι) (V : X.Opens) (hi : B i ≤ V) (m : Γ(M, V)) :
      N.presheaf.map (homOfLE hi).op (α.app (Opposite.op V) m) =
        β.app (Opposite.op i) (M.presheaf.map (homOfLE hi).op m) := by
    have hn := ConcreteCategory.congr_hom (α.naturality (homOfLE hi).op) m
    rw [TopCat.Sheaf.extend_hom_app] at hn
    exact hn.symm
  have hlin (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)) :
      α.app (Opposite.op V) (r • m) = r • α.app (Opposite.op V) m := by
    let W : {i : ι // B i ≤ V} → X.Opens := fun i => B i.val
    have hcover : V ≤ iSup W := by
      intro x hx
      obtain ⟨_, ⟨i, rfl⟩, hxi, hi⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      W V (fun i => homOfLE i.property) hcover
    intro i
    change N.presheaf.map (homOfLE i.property).op (α.app (Opposite.op V) (r • m)) =
      N.presheaf.map (homOfLE i.property).op (r • α.app (Opposite.op V) m)
    rw [hres, Scheme.Modules.map_smul N, hres, Scheme.Modules.map_smul M, hβ]
    rfl
  let φ : M ⟶ N := ⟨PresheafOfModules.homMk α (fun V r m => hlin V.unop r m)⟩
  refine ⟨φ, ?_⟩
  intro i
  exact TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB β i

/-- A global map has the expected adjoint restriction to a chart. -/
lemma adjoint_pulled {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (φ : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    adjoint f (pulledInclusion f φ) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  unfold adjoint pulledInclusion
  rw [Adjunction.homEquiv_naturality_left]
  congr 1
  exact Equiv.apply_symm_apply _ _

/-- It suffices to check the chart's values on opens contained in its image. -/
lemma pulled_eq_of_localValue {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (φ : M ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (h : ∀ (V : Y.Opens) (hV : V ≤ f.opensRange) (m : Γ(M, V)),
      φ.app V m = localValue f q V hV m) : pulledInclusion f φ = q := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  change adjoint f (pulledInclusion f φ) = adjoint f q
  rw [adjoint_pulled]
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  change f.app V (φ.app V m) = (adjoint f q).app V m
  let W := f.opensRange ⊓ V
  have hWV : W ≤ V := inf_le_right
  have hW : W ≤ f.opensRange := inf_le_left
  have hpre : f ⁻¹ᵁ W = f ⁻¹ᵁ V := by
    ext x
    simp [W]
  let e : f ⁻¹ᵁ W ≅ f ⁻¹ᵁ V := eqToIso hpre
  have he : ((Opens.map f.base).map (homOfLE hWV)) = e.hom := Subsingleton.elim _ _
  letI : IsIso ((Opens.map f.base).map (homOfLE hWV)).op := by rw [he]; infer_instance
  apply (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op)).1
  have hn := ConcreteCategory.congr_hom (f.naturality (homOfLE hWV).op) (φ.app V m)
  change f.app W (Y.presheaf.map (homOfLE hWV).op (φ.app V m)) =
    X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op (f.app V (φ.app V m)) at hn
  rw [← hn]
  have hφ := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hWV).op) m
  change φ.app W (M.presheaf.map (homOfLE hWV).op m) =
    Y.presheaf.map (homOfLE hWV).op (φ.app V m) at hφ
  rw [← hφ, h W hW, localValue_spec]
  exact ConcreteCategory.congr_hom ((adjoint f q).mapPresheaf.naturality (homOfLE hWV).op) m

/-- Compatible chart maps glue to an actual module-sheaf morphism. -/
lemma glue_local_maps {X : Scheme.{u}} {ι : Type*} (U : ι → Scheme.{u})
    (c : ∀ i, U i ⟶ X) (ho : ∀ i, IsOpenImmersion (c i))
    (hc : ∀ x : X, ∃ i z, c i z = x) (M : X.Modules)
    (q : ∀ i, (Scheme.Modules.pullback (c i)).obj M ⟶
      (SheafOfModules.unit (U i).ringCatSheaf : (U i).Modules))
    (h : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ (c i).opensRange) (hj : V ≤ (c j).opensRange)
      (m : Γ(M, V)),
      @localValue _ _ (c i) (ho i) M (q i) V hi m =
        @localValue _ _ (c j) (ho j) M (q j) V hj m) :
    ∃ φ : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      ∀ i, pulledInclusion (c i) φ = q i := by
  letI : ∀ i, IsOpenImmersion (c i) := ho
  let I := Σ i : ι, {V : X.Opens // V ≤ (c i).opensRange}
  let B : I → X.Opens := fun i => i.2.val
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨i, z, rfl⟩ := hc x
    refine ⟨(c i).opensRange ⊓ V, ⟨⟨i, ⟨_, inf_le_left⟩⟩, rfl⟩,
      ⟨?_, hx⟩, inf_le_right⟩
    exact ⟨z, rfl⟩
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let β : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun i => AddCommGrpCat.ofHom (localValue (c i.unop.1) (q i.unop.1)
        i.unop.2.val i.unop.2.property)
      naturality := by
        intro i j f
        ext m
        have hf : B j.unop ≤ B i.unop := ((inducedFunctor B).map f.unop).le
        change localValue (c j.unop.1) (q j.unop.1) (B j.unop) j.unop.2.property
            (M.presheaf.map (homOfLE hf).op m) =
          X.presheaf.map (homOfLE hf).op
            (localValue (c i.unop.1) (q i.unop.1) (B i.unop) i.unop.2.property m)
        rw [localValue_naturality]
        exact h j.unop.1 i.unop.1 _ _ _ _ }
  obtain ⟨φ, hφ⟩ := extend_linear_hom B hB β (by
    intro i r m
    exact localValue_smul (c i.1) (q i.1) i.2.val i.2.property r m)
  refine ⟨φ, ?_⟩
  intro i
  apply pulled_eq_of_localValue (c i) (q i) φ
  intro V hV m
  exact ConcreteCategory.congr_hom (hφ ⟨i, ⟨V, hV⟩⟩) m

/-- The range of the prescribed intersection map is the actual intersection of chart images. -/
lemma square_range {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y)
    (g : U ⟶ V) [IsOpenImmersion f] [IsOpenImmersion b] [IsOpenImmersion a]
    (h : IsPullback a g f b) : (a ≫ f).opensRange = f.opensRange ⊓ b.opensRange := by
  apply Opens.ext
  change Set.range (a ≫ f) = Set.range f ∩ Set.range b
  rw [← h.isoPullback_hom_fst, Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp]
  have he : Function.Surjective h.isoPullback.hom := by
    intro x
    refine ⟨h.isoPullback.inv x, ?_⟩
    have hx := congrArg (fun v : CategoryTheory.Limits.pullback f b ⟶ CategoryTheory.Limits.pullback f b => v x)
      h.isoPullback.inv_hom_id
    exact hx
  rw [Set.range_eq_univ.mpr he, Set.image_univ]
  exact IsOpenImmersion.range_pullback_to_base_of_left f b

lemma section_eq_of_empty {X : Scheme.{u}} (V : X.Opens) (hV : V = ⊥)
    (s t : Γ(X, V)) : s = t := by
  letI : Subsingleton Γ(X, V) := CommRingCat.subsingleton_of_isTerminal
    (X.sheaf.isTerminalOfEqEmpty hV)
  exact Subsingleton.elim _ _

end ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134
