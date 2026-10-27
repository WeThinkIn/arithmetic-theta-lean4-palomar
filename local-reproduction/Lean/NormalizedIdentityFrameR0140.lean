import GenericThetaEvaluationDefinitionsR0140

/-! Normalization of the actual identity pullback. All implementation helpers
are confined to this module's namespace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140
namespace NormalizedIdentityFrameR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (chartIso chartIso_inclusion compIso compIso_inclusion)
open ArithmeticThetaIdentitySectionsR0138
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation affine_pullback_inv)

section FrameFunctoriality
variable {W X Y Z : Scheme.{u}}

lemma pullFrame_post (f : X ⟶ Y) {L Q : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ L) (q : L ⟶ Q) :
    pullFrame f (α ≫ q) = pullFrame f α ≫ (Scheme.Modules.pullback f).map q := by
  simp only [pullFrame, Functor.map_comp, Category.assoc]

lemma pullFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z) {L : Z.Modules}
    (α : (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶ L) :
    pullFrame f (pullFrame g α) ≫ (Scheme.Modules.pullbackComp f g).hom.app L =
      pullFrame (f ≫ g) α := by
  letI := unitPullback_isIso f
  letI := unitPullback_isIso g
  letI := unitPullback_isIso (f ≫ g)
  apply (cancel_epi (unitPullback f)).mp
  simp only [pullFrame, Category.assoc, IsIso.hom_inv_id_assoc, Functor.map_comp]
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality α
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  apply (cancel_epi ((Scheme.Modules.pullback f).map (unitPullback g))).mp
  simp only [← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← unitPullback_comp_hom f g]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

lemma pullFrame_congr {f g : X ⟶ Y} (h : f = g) {L : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ L) :
    pullFrame f α ≫ (Scheme.Modules.pullbackCongr h).hom.app L = pullFrame g α := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

lemma pullFrame_compIso (f : X ⟶ Y) (g : Y ⟶ Z) (c : X ⟶ Z)
    (h : f ≫ g = c) {L : Z.Modules}
    (α : (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶ L) :
    pullFrame f (pullFrame g α) ≫ (compIso f g c h L).hom = pullFrame c α := by
  dsimp only [compIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, pullFrame_comp, pullFrame_congr]

lemma pullFrame_square (f : X ⟶ Y) (a : W ⟶ X) (b : Z ⟶ Y)
    (g : W ⟶ Z) (h : a ≫ f = g ≫ b) {L : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ L) :
    pullFrame g (pullFrame b α) ≫ (squareIso f a b g h L).hom =
      pullFrame a (pullFrame f α) := by
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← Category.assoc, pullFrame_comp, pullFrame_congr]
  rw [← pullFrame_comp a f α, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

lemma pullbackComp_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (L : Z.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app L) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app L =
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj L) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app L := by
  have H := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.comp_id] at H
  have HH := congrArg (fun q =>
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app L) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app L) ≫ q) H
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Category.id_comp, Category.comp_id,
    eqToHom_refl, Functor.comp_obj] at HH
  erw [CategoryTheory.Functor.map_id] at HH
  simpa only [Category.id_comp] using HH.symm

lemma compIso_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (h₁ : fg ≫ h = fgh) (h₂ : f ≫ gh = fgh) (L : Z.Modules) :
    (Scheme.Modules.pullback f).map (compIso g h gh hgh L).hom ≫
      (compIso f gh fgh h₂ L).hom =
    (compIso f g fg hfg ((Scheme.Modules.pullback h).obj L)).hom ≫
      (compIso fg h fgh h₁ L).hom := by
  subst fg
  subst gh
  subst fgh
  simpa only [compIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.comp_obj] using pullbackComp_assoc f g h L

lemma transportFrame_compatible {V : Scheme.{u}}
    (f : X ⟶ Y) (a : W ⟶ X) (b : Z ⟶ Y) (g : W ⟶ Z)
    (h : a ≫ f = g ≫ b) (c : X ⟶ V) (c' : Y ⟶ V) (hc : f ≫ c' = c)
    (q : W ⟶ V) (q' : Z ⟶ V) (hq : a ≫ c = q) (hq' : b ≫ c' = q')
    (hg : g ≫ q' = q) (L : V.Modules)
    (α : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ (Scheme.Modules.pullback c).obj L)
    (α' : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ (Scheme.Modules.pullback c').obj L)
    (hα : pullFrame f α' ≫ (compIso f c' c hc L).hom = α) :
    pullFrame g (pullFrame b α' ≫ (compIso b c' q' hq' L).hom) ≫
      (compIso g q' q hg L).hom =
    pullFrame a α ≫ (compIso a c q hq L).hom := by
  have ha : (g ≫ b) ≫ c' = q := by rw [Category.assoc, hq', hg]
  rw [← hα, pullFrame_post, pullFrame_post]
  simp only [Category.assoc]
  rw [compIso_assoc g b c' (g ≫ b) q' q rfl hq' ha hg L,
    compIso_assoc a f c' (g ≫ b) c q h hc ha hq L]
  rw [← Category.assoc, ← Category.assoc,
    pullFrame_compIso g b (g ≫ b) rfl α', pullFrame_compIso a f (g ≫ b) h α']

lemma uncurryFrame_compatible (f : W ⟶ X) (b : W ⟶ Y) (b' : X ⟶ Y)
    (hb : f ≫ b' = b) (s : Y ⟶ Z)
    (hbs : f ≫ (b' ≫ s) = b ≫ s) (L : Z.Modules)
    (α : (SheafOfModules.unit W.ringCatSheaf : W.Modules) ⟶
      (Scheme.Modules.pullback (b ≫ s)).obj L)
    (α' : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pullback (b' ≫ s)).obj L)
    (hα : pullFrame f α' ≫
      (compIso f (b' ≫ s) (b ≫ s) hbs L).hom = α) :
    pullFrame f (α' ≫ (Scheme.Modules.pullbackComp b' s).inv.app L) ≫
      (compIso f b' b hb ((Scheme.Modules.pullback s).obj L)).hom =
    α ≫ (Scheme.Modules.pullbackComp b s).inv.app L := by
  apply (cancel_mono ((Scheme.Modules.pullbackComp b s).hom.app L)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [pullFrame_post, Category.assoc]
  have h := compIso_assoc f b' s b (b' ≫ s) (b ≫ s) hb rfl rfl
    hbs L
  simp only [compIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at h
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp b' s).hom.app L) ≫
    (compIso f (b' ≫ s) (b ≫ s) hbs L).hom =
    (compIso f b' b hb ((Scheme.Modules.pullback s).obj L)).hom ≫
      (Scheme.Modules.pullbackComp b s).hom.app L at h
  rw [← h]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact hα

end FrameFunctoriality

variable (k : Type u) [Field k] [CharZero k]
/-- The specified base quotient inclusion, with its codomain written as the
same named base scheme used by the marked lift and identity pullback. -/
def baseRestriction (n : ℕ) : specR k n ⟶ baseScheme k := baseInclusion k n


variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The actual chart-zero marked point, over the nth quotient of the base. -/
def point (n : ℕ) : specR k n ⟶ specA k n :=
  Spec.map (CommRingCat.ofHom (markedPoint k n 1))

def chartFrame (h3 : 3 ≤ r) (d n : ℕ) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶
      (Scheme.Modules.pullback ((T.atlas n).chart (zeroIndex r hr))).obj
        (stageModule k (T.atlas n) d) :=
  fromSection _ (IdentityStageSectionRealizationR0138.localGenerator
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (zeroIndex r hr))

instance chartFrame_isIso (h3 : 3 ≤ r) (d n : ℕ) :
    IsIso (chartFrame k (T := T) h3 d n) :=
  IdentityStageSectionRealizationR0138.localGenerator_frame
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (zeroIndex r hr)

/-- The actual commuting square identifies reduction of the identity pullback
with the pullback to the finite-stage marked point. -/
def identityStageIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    (Scheme.Modules.pullback (baseRestriction k n)).obj
      ((Scheme.Modules.pullback s).obj (powerModule k M s d)) ≅
    (Scheme.Modules.pullback (point k n)).obj
      ((Scheme.Modules.pullback ((T.atlas n).chart (zeroIndex r hr))).obj
        (stageModule k (T.atlas n) d)) :=
  squareIso (M.inclusion n)
      (markedSection k r n hr (T.atlas n) (zeroIndex r hr) 1) s
      (baseRestriction k n) (hs.2 n).symm (powerModule k M s d) ≪≫
    (Scheme.Modules.pullback
      (markedSection k r n hr (T.atlas n) (zeroIndex r hr) 1)).mapIso
        (stageIso k h3 M hM s hs d n) ≪≫
    ((Scheme.Modules.pullbackComp (point k n)
      ((T.atlas n).chart (zeroIndex r hr))).app (stageModule k (T.atlas n) d)).symm

lemma identityStageIso_evaluation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (φ : Dual k M s d) :
    (identityStageIso k h3 M hM s hs d n).hom ≫
      pulledInclusion (point k n)
        (pulledInclusion ((T.atlas n).chart (zeroIndex r hr))
          (reduceDual k h3 M hM s hs d n φ)) =
      pulledInclusion (baseRestriction k n) (pulledInclusion s φ) := by
  dsimp only [identityStageIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Iso.app_inv, Category.assoc]
  rw [pulledInclusion_comp_inv (point k n) ((T.atlas n).chart (zeroIndex r hr))
    (reduceDual k h3 M hM s hs d n φ)]
  change _ ≫ (Scheme.Modules.pullback
    (markedSection k r n hr (T.atlas n) (zeroIndex r hr) 1)).map
      (stageIso k h3 M hM s hs d n).hom ≫
    pulledInclusion (markedSection k r n hr (T.atlas n) (zeroIndex r hr) 1)
      (reduceDual k h3 M hM s hs d n φ) = _
  rw [pulledInclusion, ← Category.assoc ((Scheme.Modules.pullback _).map _),
    ← Functor.map_comp]
  simp only [reduceDual, Iso.hom_inv_id_assoc]
  exact squareIso_inclusion _ _ _ _ _ _ φ

/-- A frame on the actual reduction of the identity pullback, with no degree
restriction. Its inverse will be algebraized over the complete base. -/
def finiteFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules) ⟶
      (Scheme.Modules.pullback (baseRestriction k n)).obj
        ((Scheme.Modules.pullback s).obj (powerModule k M s d)) :=
  pullFrame (point k n) (chartFrame k (T := T) h3 d n) ≫
    (identityStageIso k h3 M hM s hs d n).inv

instance finiteFrame_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) : IsIso (finiteFrame k h3 M hM s hs d n) := by
  letI := pullFrame_isIso (point k n) (chartFrame k (T := T) h3 d n)
  unfold finiteFrame
  infer_instance

lemma finiteFrame_evaluation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (φ : Dual k M s d) :
    finiteFrame k h3 M hM s hs d n ≫
      pulledInclusion (baseRestriction k n) (pulledInclusion s φ) =
    fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv
        (markedPoint k n 1
          (((AlgebraizedThetaSaturationR0138.algebraicFormal k h3 M hM s hs d φ).val n).val
            (zeroIndex r hr)))) := by
  rw [← identityStageIso_evaluation k h3 M hM s hs d n φ]
  simp only [finiteFrame, Category.assoc, Iso.inv_hom_id_assoc]
  have h := pullFrame_evaluation (point k n) (chartFrame k (T := T) h3 d n)
    (pulledInclusion ((T.atlas n).chart (zeroIndex r hr))
      (reduceDual k h3 M hM s hs d n φ)) _
    (IdentityStageSectionRealizationR0138.frame_evaluation k r n hr h3
      (T.overlap_spec n) (T.atlas n) d (reduceDual k h3 M hM s hs d n φ) (zeroIndex r hr))
  rw [h]
  congr 1
  apply (Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.injective
  dsimp only [point]
  erw [affine_pullback_inv]
  exact ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

/-- Every formal numerator has a well-defined full-series identity value.
This uses all thicknesses, rather than a finite jet or a field structure on the
power-series ring. -/
lemma formalValue_exists (d : ℕ) (v : FormalNumerators k (T := T) d) :
    ∃! a : PowerSeries k, ∀ n,
      trunc (PowerSeries k) PowerSeries.X n a =
        markedPoint k n 1 ((v.val n).val (zeroIndex r hr)) := by
  apply ArithmeticThetaPositiveLineR0134.CompatibleFormalSectionBasisR0134.powerSeries_limit
  intro n N h
  have hh := RingHom.congr_fun (CompatibleMarkingsR0131.point_reduction k n N h 1)
    ((v.val N).val (zeroIndex r hr))
  dsimp only [RingHom.comp_apply] at hh
  rw [v.property n N h] at hh
  exact hh.symm

/-- Reduction is forced by the actual local equation: no choices of local
frames can alter its transport between stages. -/
def chartTransitionIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    (Scheme.Modules.pullback (chartReduction k n N h)).obj
      ((Scheme.Modules.pullback ((T.atlas N).chart (zeroIndex r hr))).obj
        (stageModule k (T.atlas N) d)) ≅
    (Scheme.Modules.pullback ((T.atlas n).chart (zeroIndex r hr))).obj
      (stageModule k (T.atlas n) d) :=
  squareIso (T.transition n N h) ((T.atlas n).chart (zeroIndex r hr))
    ((T.atlas N).chart (zeroIndex r hr)) (chartReduction k n N h)
    ((T.transition_spec n N h).2 (zeroIndex r hr)) (stageModule k (T.atlas N) d) ≪≫
    (Scheme.Modules.pullback ((T.atlas n).chart (zeroIndex r hr))).mapIso
      (finiteIso k h3 M hM s hs d n N h)

lemma chartFrame_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    pullFrame (chartReduction k n N h) (chartFrame k (T := T) h3 d N) ≫
      (chartTransitionIso k h3 M hM s hs d n N h).hom =
    chartFrame k (T := T) h3 d n := by
  let cn := (T.atlas n).chart (zeroIndex r hr)
  let cN := (T.atlas N).chart (zeroIndex r hr)
  let jn := pulledInclusion cn (idealInclusion ((stageIdeal k (T.atlas n))^d))
  let jN := pulledInclusion cN (idealInclusion ((stageIdeal k (T.atlas N))^d))
  letI : IsOpenImmersion cn := (T.atlas n).chart_open _
  letI : Mono jn := (pullback_open_realization cn _ _ _ (ideal_realization _)).1
  apply (cancel_mono jn).mp
  have hj : (chartTransitionIso k h3 M hM s hs d n N h).hom ≫ jn =
      pulledInclusion (chartReduction k n N h) jN :=
    square_comparison _ _ _ _ _ _ _ _ _ _
      (finiteIso_inclusion k h3 M hM s hs d n N h)
  rw [Category.assoc, hj]
  have hN := IdentityStageSectionRealizationR0138.frame_inclusion
    k r N hr h3 (T.overlap_spec N) (T.atlas N) d (zeroIndex r hr)
  have hn := IdentityStageSectionRealizationR0138.frame_inclusion
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (zeroIndex r hr)
  change chartFrame k (T := T) h3 d n ≫ jn = _ at hn
  change chartFrame k (T := T) h3 d N ≫ jN = _ at hN
  rw [hn, pullFrame_evaluation (chartReduction k n N h) _ _ _ hN]
  congr 1
  unfold IdentityStageSectionRealizationR0138.localEquation
  rw [ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.chartReduction_value,
    map_pow, reduce_equation]

def algebraicChart (M : Model k T) (n : ℕ) : specA k n ⟶ M.X :=
  (T.atlas n).chart (zeroIndex r hr) ≫ M.inclusion n

lemma algebraicChart_reduction (M : Model k T) (hM : IsModel k T M)
    (n N : ℕ) (h : n ≤ N) :
    chartReduction k n N h ≫ algebraicChart k M N = algebraicChart k M n := by
  rw [algebraicChart, ← Category.assoc, ← (T.transition_spec n N h).2,
    Category.assoc, hM.2.2.2 n N h]
  rfl

def algebraicChartFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶
      (Scheme.Modules.pullback (algebraicChart k M n)).obj (powerModule k M s d) :=
  chartFrame k (T := T) h3 d n ≫
    (chartIso ((T.atlas n).chart (zeroIndex r hr)) (M.inclusion n) _ _
      (stageIso k h3 M hM s hs d n)).inv

instance algebraicChartFrame_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) : IsIso (algebraicChartFrame k h3 M hM s hs d n) := by
  unfold algebraicChartFrame
  infer_instance

lemma algebraicChartFrame_eval (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (φ : Dual k M s d) :
    algebraicChartFrame k h3 M hM s hs d n ≫
      pulledInclusion (algebraicChart k M n) φ =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (((AlgebraizedThetaSaturationR0138.algebraicFormal k h3 M hM s hs d φ).val n).val
          (zeroIndex r hr))) := by
  have he := chartIso_inclusion ((T.atlas n).chart (zeroIndex r hr)) (M.inclusion n)
    (powerModule k M s d) (stageModule k (T.atlas n) d) (stageIso k h3 M hM s hs d n)
    φ (reduceDual k h3 M hM s hs d n φ) (by simp only [reduceDual, Iso.hom_inv_id_assoc])
  change _ = pulledInclusion (algebraicChart k M n) φ at he
  rw [← he]
  simp only [algebraicChartFrame, Category.assoc, Iso.inv_hom_id_assoc]
  exact IdentityStageSectionRealizationR0138.frame_evaluation
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d _ (zeroIndex r hr)

lemma algebraicChartFrame_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    algebraicChartFrame k h3 M hM s hs d n ≫
      pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^d)) =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      (IdentityStageSectionRealizationR0138.localEquation k r n d (zeroIndex r hr)) := by
  have he := chartIso_inclusion ((T.atlas n).chart (zeroIndex r hr)) (M.inclusion n)
    (powerModule k M s d) (stageModule k (T.atlas n) d) (stageIso k h3 M hM s hs d n)
    (idealInclusion (s.ker^d)) (idealInclusion ((stageIdeal k (T.atlas n))^d))
    (stageIso_inclusion k h3 M hM s hs d n)
  change _ = pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^d)) at he
  rw [← he]
  simp only [algebraicChartFrame, Category.assoc, Iso.inv_hom_id_assoc]
  exact IdentityStageSectionRealizationR0138.frame_inclusion
    k r n hr h3 (T.overlap_spec n) (T.atlas n) d (zeroIndex r hr)

lemma algebraicChart_mono (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) : Mono (pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^d))) := by
  have he := chartIso_inclusion ((T.atlas n).chart (zeroIndex r hr)) (M.inclusion n)
    (powerModule k M s d) (stageModule k (T.atlas n) d) (stageIso k h3 M hM s hs d n)
    (idealInclusion (s.ker^d)) (idealInclusion ((stageIdeal k (T.atlas n))^d))
    (stageIso_inclusion k h3 M hM s hs d n)
  change _ = pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^d)) at he
  rw [← he]
  letI : IsOpenImmersion ((T.atlas n).chart (zeroIndex r hr)) := (T.atlas n).chart_open _
  letI := (pullback_open_realization ((T.atlas n).chart (zeroIndex r hr))
    ((stageIdeal k (T.atlas n))^d) _ _ (ideal_realization _)).1
  infer_instance

lemma algebraicChartFrame_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    pullFrame (chartReduction k n N h) (algebraicChartFrame k h3 M hM s hs d N) ≫
      (compIso (chartReduction k n N h) (algebraicChart k M N) (algebraicChart k M n)
        (algebraicChart_reduction k M hM n N h) (powerModule k M s d)).hom =
      algebraicChartFrame k h3 M hM s hs d n := by
  let jn := pulledInclusion (algebraicChart k M n) (idealInclusion (s.ker^d))
  letI : Mono jn := algebraicChart_mono k h3 M hM s hs d n
  apply (cancel_mono jn).mp
  rw [Category.assoc]
  change _ ≫ ((compIso _ _ _ _ _).hom ≫ pulledInclusion _ _) = _
  rw [compIso_inclusion, algebraicChartFrame_inclusion k h3 M hM s hs d n,
    pullFrame_evaluation _ _ _ _ (algebraicChartFrame_inclusion k h3 M hM s hs d N)]
  congr 1
  unfold IdentityStageSectionRealizationR0138.localEquation
  rw [ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.chartReduction_value,
    map_pow, reduce_equation]

lemma point_chart (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (n : ℕ) :
    point k n ≫ algebraicChart k M n = baseRestriction k n ≫ s := by
  exact (hs.2 n).symm

lemma baseInclusion_reduction (n N : ℕ) (h : n ≤ N) :
    baseReduction k n N h ≫ baseRestriction k N = baseRestriction k n := by
  dsimp only [baseRestriction, baseReduction, baseInclusion]
  rw [← Spec.map_comp]
  rfl

lemma point_reduction (n N : ℕ) (h : n ≤ N) :
    point k n ≫ chartReduction k n N h = baseReduction k n N h ≫ point k N := by
  dsimp only [point, chartReduction, baseReduction]
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (CompatibleMarkingsR0131.point_reduction k n N h 1)

def pointStageFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules) ⟶
      (Scheme.Modules.pullback (baseRestriction k n ≫ s)).obj (powerModule k M s d) :=
  pullFrame (point k n) (algebraicChartFrame k h3 M hM s hs d n) ≫
    (compIso (point k n) (algebraicChart k M n) (baseRestriction k n ≫ s)
      (point_chart k M s hs n) (powerModule k M s d)).hom

lemma pointStageFrame_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    pullFrame (baseReduction k n N h) (pointStageFrame k h3 M hM s hs d N) ≫
      (compIso (baseReduction k n N h) (baseRestriction k N ≫ s) (baseRestriction k n ≫ s)
        (by rw [← Category.assoc, baseInclusion_reduction]) (powerModule k M s d)).hom =
    pointStageFrame k h3 M hM s hs d n :=
  transportFrame_compatible (chartReduction k n N h) (point k n) (point k N)
    (baseReduction k n N h) (point_reduction k n N h)
    (algebraicChart k M n) (algebraicChart k M N) (algebraicChart_reduction k M hM n N h)
    (baseRestriction k n ≫ s) (baseRestriction k N ≫ s)
    (point_chart k M s hs n) (point_chart k M s hs N)
    (by rw [← Category.assoc, baseInclusion_reduction]) (powerModule k M s d)
    (algebraicChartFrame k h3 M hM s hs d n) (algebraicChartFrame k h3 M hM s hs d N)
    (algebraicChartFrame_transition k h3 M hM s hs d n N h)

def completedStageFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules) ⟶
      (Scheme.Modules.pullback (baseRestriction k n)).obj
        ((Scheme.Modules.pullback s).obj (powerModule k M s d)) :=
  pointStageFrame k h3 M hM s hs d n ≫
    (Scheme.Modules.pullbackComp (baseRestriction k n) s).inv.app (powerModule k M s d)

instance completedStageFrame_isIso (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) : IsIso (completedStageFrame k h3 M hM s hs d n) := by
  letI := pullFrame_isIso (point k n) (algebraicChartFrame k h3 M hM s hs d n)
  unfold completedStageFrame pointStageFrame
  infer_instance

set_option maxHeartbeats 800000 in
lemma completedStageFrame_transition (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    pullFrame (baseReduction k n N h) (completedStageFrame k h3 M hM s hs d N) ≫
      (compIso (baseReduction k n N h) (baseRestriction k N) (baseRestriction k n)
        (baseInclusion_reduction k n N h)
        ((Scheme.Modules.pullback s).obj (powerModule k M s d))).hom =
    completedStageFrame k h3 M hM s hs d n := by
  have hn : completedStageFrame k h3 M hM s hs d n =
      pointStageFrame k h3 M hM s hs d n ≫
        (Scheme.Modules.pullbackComp (baseRestriction k n) s).inv.app (powerModule k M s d) := rfl
  have hN : completedStageFrame k h3 M hM s hs d N =
      pointStageFrame k h3 M hM s hs d N ≫
        (Scheme.Modules.pullbackComp (baseRestriction k N) s).inv.app (powerModule k M s d) := rfl
  rw [hn, hN]
  exact uncurryFrame_compatible (W := specR k n) (X := specR k N)
    (Y := baseScheme k) (Z := M.X)
    (baseReduction k n N h) (baseRestriction k n) (baseRestriction k N)
    (baseInclusion_reduction k n N h) s
    (by rw [← Category.assoc, baseInclusion_reduction]) (powerModule k M s d)
    (pointStageFrame k h3 M hM s hs d n) (pointStageFrame k h3 M hM s hs d N)
    (pointStageFrame_transition k h3 M hM s hs d n N h)

lemma frameValue_morphism (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (e : IdentityFrame k M s d) (φ : Dual k M s d) :
    e.inv ≫ pulledInclusion s φ =
      fromSection (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules)
        ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv
          (frameValue k M s d e φ)) := by
  apply unit_hom_ext
  simp only [frameValue, map_one]
  rw [fromSection_apply]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
    one_smul]
  exact ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm_apply_apply _).symm

/-- Matching the constructed finite frames suffices for the frozen universal
normalization predicate; the remaining existence step must establish this
matching, not assume it as part of the target theorem. -/
lemma normalized_of_reductions (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (e : IdentityFrame k M s d)
    (he : ∀ n, pullFrame (baseRestriction k n) e.inv = finiteFrame k h3 M hM s hs d n) :
    NormalizedFrame k h3 M hM s hs d e := by
  intro φ n
  have hp := pullFrame_evaluation (baseRestriction k n) e.inv (pulledInclusion s φ) _
    (frameValue_morphism k M s d e φ)
  rw [he n, finiteFrame_evaluation k h3 M hM s hs d n φ] at hp
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun q => Scheme.Modules.Hom.app q ⊤) hp) (1 : Γ(specR k n, ⊤))
  simp only [fromSection_apply, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, one_smul] at hh
  have hv := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of (R k n))).hom x) hh
  dsimp only [baseRestriction, baseInclusion] at hv
  erw [affine_pullback_inv] at hv
  exact hv.symm.trans
    ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.apply_symm_apply _)

end NormalizedIdentityFrameR0140
end ArithmeticThetaGenericEvaluationR0140

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (compIso compIso_unit compIso_inclusion)
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation affine_pullback_inv)
open ArithmeticThetaIdentitySectionsR0138 AlgebraizedThetaSectionsR0138
open ArithmeticThetaPolygonCohomologyR0131

lemma pullFrame_inverse_pair {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Y.Modules}
    (α : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ F)
    (β : F ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (h : α ≫ β = 𝟙 _) : pullFrame f α ≫ pulledInclusion f β = 𝟙 _ := by
  letI := unitPullback_isIso f
  simp only [pullFrame, pulledInclusion, Category.assoc, ← Functor.map_comp_assoc,
    h, CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]

lemma inverseFrame_compatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Y.Modules} {G : X.Modules} (e : (Scheme.Modules.pullback f).obj F ≅ G)
    (α : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ G)
    (β : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ F)
    [IsIso α] [IsIso β] (h : pullFrame f β ≫ e.hom = α) :
    e.hom ≫ inv α = pulledInclusion f (inv β) := by
  letI := pullFrame_isIso f β
  apply (cancel_epi (pullFrame f β)).mp
  rw [← Category.assoc, h, IsIso.hom_inv_id,
    pullFrame_inverse_pair f β (inv β) (IsIso.hom_inv_id β)]

variable (k : Type u) [Field k] [CharZero k]

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma completedStageFrame_evaluation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) (φ : Dual k M s d) :
    completedStageFrame k h3 M hM s hs d n ≫
      pulledInclusion (baseRestriction k n) (pulledInclusion s φ) =
    fromSection (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules)
      ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv
        (markedPoint k n 1
          (((AlgebraizedThetaSaturationR0138.algebraicFormal k h3 M hM s hs d φ).val n).val
            (zeroIndex r hr)))) := by
  simp only [completedStageFrame, Category.assoc]
  rw [pulledInclusion_comp_inv (baseRestriction k n) s φ]
  simp only [pointStageFrame, Category.assoc]
  rw [compIso_inclusion, pullFrame_evaluation _ _ _ _
    (algebraicChartFrame_eval k h3 M hM s hs d n φ)]
  congr 1
  apply (Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.injective
  dsimp only [point]
  erw [affine_pullback_inv]
  exact ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

lemma normalized_completed_reductions (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (e : IdentityFrame k M s d)
    (he : ∀ n, pullFrame (baseRestriction k n) e.inv = completedStageFrame k h3 M hM s hs d n) :
    NormalizedFrame k h3 M hM s hs d e := by
  intro φ n
  have hp := pullFrame_evaluation (baseRestriction k n) e.inv (pulledInclusion s φ) _
    (frameValue_morphism k M s d e φ)
  rw [he n, completedStageFrame_evaluation k h3 M hM s hs d n φ] at hp
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun q => Scheme.Modules.Hom.app q ⊤) hp) (1 : Γ(specR k n, ⊤))
  simp only [fromSection_apply, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, one_smul] at hh
  have hv := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of (R k n))).hom x) hh
  dsimp only [baseRestriction, baseInclusion] at hv
  erw [affine_pullback_inv] at hv
  exact hv.symm.trans
    ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.apply_symm_apply _)

end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

lemma compIso_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : X ⟶ Z) (h : f ≫ g = c) {F G : Z.Modules} (q : F ⟶ G) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map q) ≫
      (compIso f g c h G).hom =
    (compIso f g c h F).hom ≫ (Scheme.Modules.pullback c).map q := by
  subst c
  simpa only [compIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.comp_map] using
    (Scheme.Modules.pullbackComp f g).hom.naturality q

variable (k : Type u) [Field k] [CharZero k]

lemma base_reduction (n N : ℕ) (h : n ≤ N) :
    baseReduction k n N h ≫ baseRestriction k N = baseRestriction k n := by
  dsimp only [baseRestriction, baseReduction, baseInclusion]
  rw [← Spec.map_comp]
  rfl

def baseComp (F : (baseScheme k).Modules) (n : ℕ) :=
  compIso (baseReduction k n (n+1) (Nat.le_succ n)) (baseRestriction k (n+1))
    (baseRestriction k n) (base_reduction k n (n+1) (Nat.le_succ n)) F


def baseAffineIso : baseScheme k ≅ Spec (CommRingCat.of (PowerSeries k)) := eqToIso rfl

def quotientAffineIso (n : ℕ) : specR k n ≅
    Spec (CommRingCat.of ((PowerSeries k) ⧸ (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k))^(n+1))) :=
  eqToIso rfl

lemma base_square (n : ℕ) :
    IsPullback (baseRestriction k n) (quotientAffineIso k n).hom (baseAffineIso k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k)
        ((PowerSeries k) ⧸ (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k))^(n+1))))) := by
  apply IsPullback.of_vert_isIso
  constructor
  simp only [baseAffineIso, quotientAffineIso, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  rfl


end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion

/- The following proof terms specialize the accepted completion theorem in
small steps. Inferred intermediate types avoid expanding the concrete scheme
pullbacks repeatedly during kernel conversion. -/
set_option linter.defProp false

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.BaseCompletion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
variable (k : Type u) [Field k] [CharZero k]
private def overCompleteBase := pullback_completion (R := PowerSeries k) (X := baseScheme k)
  (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k))
private def overIdentity := overCompleteBase k (baseAffineIso k).hom
private def onQuotientSchemes := overIdentity k (specR k)
private def withInclusions (c : ∀ n, specR k n ⟶ baseScheme k) := onQuotientSchemes k c
private def onBaseRestrictions := withInclusions k (baseRestriction k)
private def withAffineComparisons := onBaseRestrictions k (fun n => (quotientAffineIso k n).hom)
private def withBaseSquares := withAffineComparisons k (base_square k)
private def withTransitions (t : ∀ n, specR k n ⟶ specR k (n+1)) := withBaseSquares k t
def baseStep (n : ℕ) : specR k n ⟶ specR k (n+1) := baseReduction k n (n+1) (Nat.le_succ n)
private def onBaseSteps := withTransitions k (baseStep k)
lemma baseStep_spec (n : ℕ) : baseStep k n ≫ baseRestriction k (n+1) = baseRestriction k n := base_reduction k n (n+1) (Nat.le_succ n)
private def compatibleMorphisms := onBaseSteps k (baseStep_spec k)
end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.BaseCompletion

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

variable (k : Type u) [Field k] [CharZero k]

set_option maxHeartbeats 800000 in
lemma base_completion (F G : (baseScheme k).Modules)
    (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (q : ∀ n, (Scheme.Modules.pullback (baseRestriction k n)).obj F ⟶
      (Scheme.Modules.pullback (baseRestriction k n)).obj G)
    (hq : ∀ n, q n = (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) F).inv ≫
      (Scheme.Modules.pullback (BaseCompletion.baseStep k n)).map (q (n+1)) ≫
      (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) G).hom) :
    ∃! φ : F ⟶ G, ∀ n, (Scheme.Modules.pullback (baseRestriction k n)).map φ = q n := by
  exact BaseCompletion.compatibleMorphisms k F G hF hG q hq

end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133

variable (k : Type u) [Field k] [CharZero k]

lemma base_hom_ext (F G : (baseScheme k).Modules)
    (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (φ ψ : F ⟶ G)
    (h : ∀ n, (Scheme.Modules.pullback (baseRestriction k n)).map φ =
      (Scheme.Modules.pullback (baseRestriction k n)).map ψ) : φ = ψ := by
  obtain ⟨χ, hχ, hu⟩ := base_completion k F G hF hG
    (fun n => (Scheme.Modules.pullback (baseRestriction k n)).map φ) (fun n => by
      have hn := compIso_naturality (BaseCompletion.baseStep k n)
        (baseRestriction k (n+1)) (baseRestriction k n)
        (BaseCompletion.baseStep_spec k n) φ
      change _ ≫ (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) G).hom = (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) F).hom ≫ _ at hn
      rw [hn, Iso.inv_hom_id_assoc])
  exact (hu φ (fun _ => rfl)).trans (hu ψ (fun n => (h n).symm)).symm

lemma base_isIso_of_pullbacks (F G : (baseScheme k).Modules)
    (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (φ : F ⟶ G) (hφ : ∀ n, IsIso ((Scheme.Modules.pullback (baseRestriction k n)).map φ)) :
    IsIso φ := by
  letI := hφ
  obtain ⟨ψ, hψ, _⟩ := base_completion k G F hG hF
    (fun n => inv ((Scheme.Modules.pullback (baseRestriction k n)).map φ)) (fun n => by
      apply (cancel_epi ((Scheme.Modules.pullback (baseRestriction k n)).map φ)).mp
      simp only [IsIso.hom_inv_id]
      have hn := compIso_naturality (BaseCompletion.baseStep k n)
        (baseRestriction k (n+1)) (baseRestriction k n)
        (BaseCompletion.baseStep_spec k n) φ
      change _ ≫ (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) G).hom = (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) F).hom ≫ _ at hn
      have hn' : (Scheme.Modules.pullback (baseRestriction k n)).map φ ≫
          (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) G).inv =
        (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) F).inv ≫
          (Scheme.Modules.pullback (BaseCompletion.baseStep k n)).map
            ((Scheme.Modules.pullback (baseRestriction k (n+1))).map φ) := by
        apply (cancel_epi (compIso (BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n) (BaseCompletion.baseStep_spec k n) F).hom).mp
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        rw [← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc ((Scheme.Modules.pullback (baseRestriction k n)).map φ), hn']
      simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id])
  have h₁ : φ ≫ ψ = 𝟙 F := base_hom_ext k F F hF hF _ _ (by
    intro n
    rw [Functor.map_comp, hψ n, IsIso.hom_inv_id, CategoryTheory.Functor.map_id])
  have h₂ : ψ ≫ φ = 𝟙 G := base_hom_ext k G G hG hG _ _ (by
    intro n
    rw [Functor.map_comp, hψ n, IsIso.inv_hom_id, CategoryTheory.Functor.map_id])
  exact ⟨⟨ψ, h₁, h₂⟩⟩

end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.DualConstruction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
variable (k : Type u) [Field k] [CharZero k]
private def overCompleteBase := pullback_dual_completion (R := PowerSeries k) (X := baseScheme k)
  (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k))
private def overIdentity := overCompleteBase k (baseAffineIso k).hom
private def onQuotientSchemes := overIdentity k (specR k)
private def withInclusions (c : ∀ n, specR k n ⟶ baseScheme k) := onQuotientSchemes k c
private def onBaseRestrictions := withInclusions k (baseRestriction k)
private def withAffineComparisons := onBaseRestrictions k (fun n => (quotientAffineIso k n).hom)
private def withBaseSquares := withAffineComparisons k (base_square k)
private def withTransitions (t : ∀ n, specR k n ⟶ specR k (n+1)) := withBaseSquares k t
private def onBaseSteps := withTransitions k (BaseCompletion.baseStep k)
private def compatibleMorphisms := onBaseSteps k (BaseCompletion.baseStep_spec k)
end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.Completion.DualConstruction

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (compIso compIso_unit compIso_inclusion)
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation affine_pullback_inv)
open ArithmeticThetaIdentitySectionsR0138 AlgebraizedThetaSectionsR0138
open ArithmeticThetaPolygonCohomologyR0131

variable (k : Type u) [Field k] [CharZero k]

lemma base_dual_completion (F : (baseScheme k).Modules) (hF : Scheme.Modules.IsInvertible F)
    (q : ∀ n, (Scheme.Modules.pullback (baseRestriction k n)).obj F ⟶
      (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules))
    (hq : ∀ n, (compIso (Completion.BaseCompletion.baseStep k n)
      (baseRestriction k (n+1)) (baseRestriction k n)
      (Completion.BaseCompletion.baseStep_spec k n) F).hom ≫ q n =
        pulledInclusion (Completion.BaseCompletion.baseStep k n) (q (n+1))) :
    ∃ φ : F ⟶ (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules),
      ∀ n, pulledInclusion (baseRestriction k n) φ = q n := by
  exact (Completion.DualConstruction.compatibleMorphisms k F hF q hq).exists

end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140

namespace ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (compIso compIso_unit compIso_inclusion)
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation affine_pullback_inv)
open ArithmeticThetaIdentitySectionsR0138 AlgebraizedThetaSectionsR0138
open ArithmeticThetaPolygonCohomologyR0131

variable (k : Type u) [Field k] [CharZero k]

lemma exists_frame_reductions (F : (baseScheme k).Modules) (hF : Scheme.Modules.IsInvertible F)
    (α : ∀ n, (SheafOfModules.unit (specR k n).ringCatSheaf : (specR k n).Modules) ⟶
      (Scheme.Modules.pullback (baseRestriction k n)).obj F)
    (hα : ∀ n, IsIso (α n))
    (hc : ∀ n, pullFrame (Completion.BaseCompletion.baseStep k n) (α (n+1)) ≫
      (compIso (Completion.BaseCompletion.baseStep k n) (baseRestriction k (n+1))
        (baseRestriction k n) (Completion.BaseCompletion.baseStep_spec k n) F).hom = α n) :
    ∃ e : F ≅ (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules),
      ∀ n, pullFrame (baseRestriction k n) e.inv = α n := by
  letI := hα
  obtain ⟨q, hq⟩ := base_dual_completion k F hF (fun n => inv (α n))
    (fun n => inverseFrame_compatible _ _ _ _ (hc n))
  have hqi (n : ℕ) : IsIso ((Scheme.Modules.pullback (baseRestriction k n)).map q) := by
    letI := unitPullback_isIso (baseRestriction k n)
    have he : (Scheme.Modules.pullback (baseRestriction k n)).map q =
        inv (α n) ≫ inv (unitPullback (baseRestriction k n)) := by
      rw [← hq n]
      simp only [pulledInclusion, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  letI := Completion.base_isIso_of_pullbacks k F _ hF
    (Scheme.Modules.isInvertible_unit (baseScheme k)) q hqi
  refine ⟨asIso q, fun n => ?_⟩
  apply (cancel_mono (inv (α n))).mp
  rw [← hq n]
  change pullFrame (baseRestriction k n) (asIso q).inv ≫
    pulledInclusion (baseRestriction k n) (asIso q).hom = α n ≫ pulledInclusion (baseRestriction k n) q
  rw [pullFrame_inverse_pair _ _ _ (asIso q).inv_hom_id, hq n, IsIso.hom_inv_id]

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma completedStageFrame_step (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n : ℕ) :
    pullFrame (Completion.BaseCompletion.baseStep k n) (completedStageFrame k h3 M hM s hs d (n+1)) ≫
      (compIso (Completion.BaseCompletion.baseStep k n) (baseRestriction k (n+1)) (baseRestriction k n)
        (Completion.BaseCompletion.baseStep_spec k n)
        ((Scheme.Modules.pullback s).obj (powerModule k M s d))).hom =
    completedStageFrame k h3 M hM s hs d n := by
  have he : compIso (Completion.BaseCompletion.baseStep k n) (baseRestriction k (n+1))
      (baseRestriction k n) (Completion.BaseCompletion.baseStep_spec k n)
      ((Scheme.Modules.pullback s).obj (powerModule k M s d)) =
      compIso (baseReduction k n (n+1) (Nat.le_succ n)) (baseRestriction k (n+1))
      (baseRestriction k n) (baseInclusion_reduction k n (n+1) (Nat.le_succ n))
      ((Scheme.Modules.pullback s).obj (powerModule k M s d)) := rfl
  have hf : pullFrame (Completion.BaseCompletion.baseStep k n)
      (completedStageFrame k h3 M hM s hs d (n+1)) =
      pullFrame (baseReduction k n (n+1) (Nat.le_succ n))
      (completedStageFrame k h3 M hM s hs d (n+1)) := rfl
  rw [he, hf]
  exact completedStageFrame_transition k h3 M hM s hs d n (n+1) (Nat.le_succ n)

end ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140

namespace ArithmeticThetaGenericEvaluationR0140
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138
open NormalizedIdentityFrameR0140

theorem normalized_identity_frame :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (d : ℕ), ∃ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s d, ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k h3 M hM s hs d e := by
  intro k _ _ r hr h3 T M hM s hs d
  obtain ⟨e, he⟩ := exists_frame_reductions k
    ((Scheme.Modules.pullback s).obj (powerModule k M s d))
    ((power_invertible k h3 M hM s hs d).isInvertible_module.pullback s)
    (completedStageFrame k h3 M hM s hs d)
    (fun n => completedStageFrame_isIso k h3 M hM s hs d n)
    (completedStageFrame_step k h3 M hM s hs d)
  exact ⟨e, normalized_completed_reductions k h3 M hM s hs d e he⟩

end ArithmeticThetaGenericEvaluationR0140

#print axioms ArithmeticThetaGenericEvaluationR0140.normalized_identity_frame
