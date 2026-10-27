import PointedCurveConstantExtensionR0225
import FiniteMapConstantExtensionR0225
import LineConstantExtensionR0225
import PowerSectionsConstantExtensionR0225

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base Sections powerIso powerComparison)
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
  (powerComparison_local pullbackGlobalSection_map tensorPower_isLineBundle)
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms (pullback_isLineBundle pulledFrame pulledFrame_compatible pullbackLocalSection_restrict)
open ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
  (squareComparison triangle square_paste powerComparison_trans)
open ArithmeticThetaRamifiedRootModelsR0222 (RootEquation pulledPower)
open FiniteMapExtension
open PowerSections (finite_line_sections powerComparison_refinement refinementComparison_global)
namespace RamifiedRoots
variable {k : Type} [Field k] [CharZero k]

/-- A descended line, retaining its actual scalar-extension comparison. -/
structure LineModel (X : Curve (Omega k)) (J : X.space.Modules) (K : (FieldStage k)) where
  model : Model X K
  line : model.curve.space.Modules
  isLine : IsLineBundle model.curve.space line
  comparison : (Scheme.Modules.pullback model.projection).obj line ≅ J

def LineModel.refine {X : Curve (Omega k)} {J : X.space.Modules} {K L : (FieldStage k)}
    (A : LineModel X J K) {N : Model X L} (E : Refinement A.model N) : LineModel X J L where
  model := N
  line := (Scheme.Modules.pullback E.map).obj A.line
  isLine := pullback_isLineBundle E.map A.line A.isLine
  comparison := refinementComparison E A.line ≪≫ A.comparison

/-- A rational marked point is retained under every Cartesian refinement. -/
def refinePoint {X : Curve (Omega k)} {K L : (FieldStage k)} {M : Model X K} {N : Model X L}
    (E : Refinement M N) (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _) :
    Base L ⟶ N.curve.space :=
  E.cartesian.lift (extensionMap E.inclusion ≫ x) (𝟙 _) (by simp [Category.assoc, hx])

@[simp] theorem refinePoint_over {X : Curve (Omega k)} {K L : (FieldStage k)}
    {M : Model X K} {N : Model X L} (E : Refinement M N)
    (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _) :
    refinePoint E x hx ≫ N.curve.map = 𝟙 _ := E.cartesian.lift_snd _ _ _

theorem refinePoint_comparison {X : Curve (Omega k)} {K L : (FieldStage k)}
    {M : Model X K} {N : Model X L} (E : Refinement M N)
    (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _)
    (z : Base (Omega k) ⟶ X.space) (hz : z ≫ X.map = 𝟙 _)
    (hc : constantMap K ≫ x = z ≫ M.projection) :
    constantMap L ≫ refinePoint E x hx = z ≫ N.projection := by
  apply E.cartesian.hom_ext
  · simp only [Category.assoc, refinePoint, IsPullback.lift_fst]
    rw [← Category.assoc, constantMap_extensionMap, hc, E.comparison]
  · simp only [Category.assoc, refinePoint_over, Category.comp_id]
    rw [N.cartesian.w, ← Category.assoc, hz, Category.id_comp]

/-- Pointed line models exist over a finite extension of any prescribed stage. -/
theorem pointed_line_model (X : Curve (Omega k)) (J : X.space.Modules)
    (hJ : IsLineBundle X.space J) (z : Base (Omega k) ⟶ X.space)
    (hz : z ≫ X.map = 𝟙 _) (K0 : (FieldStage k)) (hK0 : FiniteDimensional k K0) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧
      ∃ (A : LineModel X J K) (x : Base K ⟶ A.model.curve.space),
        x ≫ A.model.curve.map = 𝟙 _ ∧ constantMap K ≫ x = z ≫ A.model.projection := by
  obtain ⟨K, hK, hle, M, x, hx⟩ :=
    pointed_curve_constant_extension k X K0 hK0 1 (fun _ => z) (fun _ => hz)
  obtain ⟨L, hL, N, E, J0, hJ0, ⟨e⟩⟩ := line_constant_extension k X K hK M J hJ
  refine ⟨L, hL, hle.trans E.inclusion, ⟨N, J0, hJ0, e⟩,
    refinePoint E (x 0) (hx 0).1, refinePoint_over E (x 0) (hx 0).1, ?_⟩
  exact refinePoint_comparison E (x 0) (hx 0).1 z hz (hx 0).2

/-- Refinement coherence with the actual comparison to the prescribed line. -/
theorem line_power_refinement {X : Curve (Omega k)} {J : X.space.Modules} {K L : (FieldStage k)}
    (A : LineModel X J K) {N : Model X L} (E : Refinement A.model N) (n : ℕ) :
    (Scheme.Modules.pullback N.projection).map
        (pullback_tensorPower_iso N.curve.space A.model.curve.space E.map A.line n).hom ≫
      (powerComparison N.projection (A.refine E).line (A.refine E).comparison n).hom =
    (refinementComparison E (tensorPower A.model.curve.space A.line n)).hom ≫
      (powerComparison A.model.projection A.line A.comparison n).hom := by
  dsimp only [LineModel.refine]
  rw [powerComparison_trans]
  simp only [Iso.trans_hom]
  rw [← Category.assoc, powerComparison_refinement E A.line A.isLine n]
  simp only [powerComparison, Iso.trans_hom, Category.assoc]

/-- Pulling a model power section further retains its original comparison. -/
theorem line_power_section_refinement {X : Curve (Omega k)} {J : X.space.Modules}
    {K L : (FieldStage k)} (A : LineModel X J K) {N : Model X L}
    (E : Refinement A.model N) (n : ℕ) (a : Sections (tensorPower A.model.curve.space A.line n)) :
    (powerComparison N.projection (A.refine E).line (A.refine E).comparison n).hom.app ⊤
      (pullbackGlobalSection N.projection _ (pullbackPowerSection E.map A.line n a)) =
    (powerComparison A.model.projection A.line A.comparison n).hom.app ⊤
      (pullbackGlobalSection A.model.projection _ a) := by
  unfold pullbackPowerSection
  erw [pullbackGlobalSection_map]
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (line_power_refinement A E n))
    (pullbackGlobalSection N.projection _ (pullbackGlobalSection E.map _ a))
  refine h.trans ?_
  change (powerComparison A.model.projection A.line A.comparison n).hom.app ⊤
    ((refinementComparison E (tensorPower A.model.curve.space A.line n)).hom.app ⊤
      (pullbackGlobalSection N.projection _ (pullbackGlobalSection E.map _ a))) = _
  rw [refinementComparison_global]

/-- Global sections of a model line are faithfully detected by its actual projection. -/
theorem model_sections_injective {X : Curve (Omega k)} {K : (FieldStage k)} (M : Model X K)
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
  have h' := LineHoms.model_projection_app_injective_all M (U x) h
  exact (e.equiv (U x) le_rfl).symm.injective h'



/-- Root equations are preserved and reflected through the actual constant-field models. -/
theorem root_equation_cartesian_reflection
    (X Y : Curve (Omega k)) (K : (FieldStage k)) (M : Model X K) (N : Model Y K)
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
      (model_sections_injective N _
        (tensorPower_isLineBundle J (pullback_isLineBundle g H0 hH0) n))
  have hl : transport (tensorPowerSection N.curve.space J n ⊤ r0) =
      tensorPowerSection Y.space ((Scheme.Modules.pullback f).obj H) n ⊤
        (E.hom.app ⊤ (pullbackGlobalSection N.projection J r0)) :=
    powerComparison_local N.projection J E n ⊤ r0
  have hr : transport (pulledPower g H0 n F0) =
      pulledPower f H n ((powerComparison M.projection H0 e n).hom.app ⊤
        (pullbackGlobalSection M.projection _ F0)) :=
    ArithmeticThetaRamifiedRootModelsR0222.RootEquationReflection.pulled_power_square N.projection g f M.projection hc H0 hH0 e n F0
  unfold RootEquation
  constructor
  · intro h
    exact hl.symm.trans ((congrArg transport h).trans hr)
  · intro h
    apply hi
    exact hl.trans (h.trans hr.symm)

/-- The actual section comparison carries the zero section to zero. -/
theorem sectionComparison_zero {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    {H : X.Modules} (e : (Scheme.Modules.pullback p).obj J ≅ H) :
    e.hom.app ⊤ (pullbackGlobalSection p J 0) = 0 := by
  have h : pullbackGlobalSection p J 0 = 0 :=
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app J).app ⊤).hom.map_zero
  rw [h]
  exact (e.hom.app ⊤).hom.map_zero

/-- A model of the base line together with the specified power sections. -/
structure Powers {s n : ℕ} (D : RootData k s n)
    (K : (FieldStage k)) where
  base : LineModel D.base D.line K
  sections : Fin s → Sections (tensorPower base.model.curve.space base.line n)
  comparison : ∀ i, (powerComparison base.model.projection base.line base.comparison n).hom.app ⊤
    (pullbackGlobalSection base.model.projection _ (sections i)) = D.powers i

def Powers.refine {s n : ℕ} {D : RootData k s n}
    {K L : (FieldStage k)} (A : Powers D K) {N : Model D.base L}
    (E : Refinement A.base.model N) : Powers D L where
  base := A.base.refine E
  sections := fun i => pullbackPowerSection E.map A.base.line n (A.sections i)
  comparison := fun i => (line_power_section_refinement A.base E n (A.sections i)).trans
    (A.comparison i)

theorem powers_exists {s n : ℕ} (D : RootData k s n)
    (K0 : (FieldStage k)) (hK0 : FiniteDimensional k K0) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧ Nonempty (Powers D K) := by
  have hz : (D.cusp ≫ D.map) ≫ D.base.map = 𝟙 _ := by
    rw [Category.assoc, D.over_eq, D.cusp_over]
  obtain ⟨K, hK, hle, A, _, _⟩ := pointed_line_model D.base D.line D.isLine
    (D.cusp ≫ D.map) hz K0 hK0
  let a (i : Fin s) := (powerIso A.comparison n).inv.app ⊤ (D.powers i)
  obtain ⟨L, hL, N, E, a0, ha0⟩ := power_sections_constant_extension k D.base K hK A.model
    A.line A.isLine s (fun _ => n) a
  refine ⟨L, hL, hle.trans E.inclusion, ⟨⟨A.refine E, a0, ?_⟩⟩⟩
  intro i
  change (powerComparison N.projection ((Scheme.Modules.pullback E.map).obj A.line)
    (refinementComparison E A.line ≪≫ A.comparison) n).hom.app ⊤ _ = _
  rw [powerComparison_trans]
  change (powerIso A.comparison n).hom.app ⊤
    ((powerComparison N.projection _ (refinementComparison E A.line) n).hom.app ⊤ _) = _
  dsimp only [LineModel.refine]
  rw [ha0 i]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (powerIso A.comparison n).inv_hom_id) (D.powers i)

/-- Pointed geometry with powers, before descent of the regular roots. -/
structure Geometry {s n : ℕ} (D : RootData k s n)
    (K : (FieldStage k)) where
  powers : Powers D K
  cover : Model D.cover K
  map : cover.curve.space ⟶ powers.base.model.curve.space
  over_eq : map ≫ powers.base.model.curve.map = cover.curve.map
  comparison : cover.projection ≫ map = D.map ≫ powers.base.model.projection
  cusp : Base K ⟶ cover.curve.space
  cusp_over : cusp ≫ cover.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.projection

theorem geometry_exists {s n : ℕ} (D : RootData k s n)
    (K0 : (FieldStage k)) (hK0 : FiniteDimensional k K0) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧ Nonempty (Geometry D K) := by
  obtain ⟨K1, hK1, h01, ⟨A⟩⟩ := powers_exists D K0 hK0
  obtain ⟨K2, hK2, h12, B, x, hx⟩ := pointed_curve_constant_extension k D.cover K1 hK1 1
    (fun _ => D.cusp) (fun _ => D.cusp_over)
  let A2 := A.refine (extendRefinement A.base.model h12)
  obtain ⟨K3, hK3, Y, X, EY, EX, f, hf, hcart, _, _, _⟩ :=
    finite_map_constant_extension k D.cover D.base K2 hK2 B A2.base.model
      D.map D.over_eq D.finite D.surjective
  refine ⟨K3, hK3, h01.trans (h12.trans EY.inclusion), ⟨{
    powers := A2.refine EX
    cover := Y
    map := f
    over_eq := hf
    comparison := hcart.w
    cusp := refinePoint EY (x 0) (hx 0).1
    cusp_over := refinePoint_over EY (x 0) (hx 0).1
    cusp_comparison := refinePoint_comparison EY (x 0) (hx 0).1
      D.cusp D.cusp_over (hx 0).2 }⟩⟩

/-- Enlarge both schemes along a refinement of the cover. -/
def Geometry.refine {s n : ℕ} {D : RootData k s n}
    {K L : (FieldStage k)} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover N) : Geometry D L where
  powers := G.powers.refine (extendRefinement G.powers.base.model E.inclusion)
  cover := N
  map := pullback.lift (E.map ≫ G.map) N.curve.map (by
    rw [Category.assoc, G.over_eq]; exact E.cartesian.w)
  over_eq := pullback.lift_snd _ _ _
  comparison := by
    apply pullback.hom_ext
    · change N.projection ≫ _ ≫ pullback.fst _ _ =
        D.map ≫ extendProjection G.powers.base.model E.inclusion ≫ pullback.fst _ _
      rw [pullback.lift_fst, extendProjection, pullback.lift_fst, ← Category.assoc, E.comparison]
      exact G.comparison
    · change N.projection ≫ _ ≫ pullback.snd _ _ =
        D.map ≫ extendProjection G.powers.base.model E.inclusion ≫ pullback.snd _ _
      rw [pullback.lift_snd, extendProjection, pullback.lift_snd, N.cartesian.w, ← Category.assoc, D.over_eq]
  cusp := refinePoint E G.cusp G.cusp_over
  cusp_over := refinePoint_over E G.cusp G.cusp_over
  cusp_comparison := refinePoint_comparison E G.cusp G.cusp_over D.cusp D.cusp_over G.cusp_comparison

theorem Geometry.refine_map {s n : ℕ} {D : RootData k s n}
    {K L : (FieldStage k)} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover N) :
    E.map ≫ G.map = (G.refine E).map ≫
      (extendRefinement G.powers.base.model E.inclusion).map :=
  (pullback.lift_fst _ _ _).symm

/-- The actual line on the refined cover, identified by the commuting square. -/
def Geometry.targetRefinement {s n : ℕ} {D : RootData k s n}
    {K L : (FieldStage k)} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover N) :
    (Scheme.Modules.pullback E.map).obj ((Scheme.Modules.pullback G.map).obj G.powers.base.line) ≅
      (Scheme.Modules.pullback (G.refine E).map).obj (G.refine E).powers.base.line :=
  squareComparison E.map G.map (G.refine E).map
    (extendRefinement G.powers.base.model E.inclusion).map (G.refine_map E) G.powers.base.line

def Geometry.lineComparison {s n : ℕ} {D : RootData k s n}
    {K : (FieldStage k)} (G : Geometry D K) :=
  coverLineComparison G.powers.base.model G.cover D.map G.map G.comparison
    G.powers.base.line G.powers.base.comparison

/-- Pasting the refinement square preserves the specified comparison to the original cover line. -/
theorem Geometry.targetRefinement_comparison {s n : ℕ}
    {D : RootData k s n} {K L : (FieldStage k)}
    (G : Geometry D K) {N : Model D.cover L} (E : Refinement G.cover N) :
    (Scheme.Modules.pullback N.projection).mapIso (G.targetRefinement E) ≪≫
      (G.refine E).lineComparison =
    refinementComparison E ((Scheme.Modules.pullback G.map).obj G.powers.base.line) ≪≫
      G.lineComparison := by
  let B := extendRefinement G.powers.base.model E.inclusion
  have h := square_paste G.cover.projection N.projection E.map G.map (G.refine E).map
    B.map D.map G.powers.base.model.projection (extendModel G.powers.base.model E.inclusion).projection
    E.comparison B.comparison (G.refine_map E) G.comparison (G.refine E).comparison G.powers.base.line
  have hh := congrArg (fun e => e ≪≫ (Scheme.Modules.pullback D.map).mapIso G.powers.base.comparison) h
  simpa only [Geometry.targetRefinement, Geometry.lineComparison, coverLineComparison,
    squareComparison, triangle, refinementComparison, Geometry.refine, Powers.refine,
    LineModel.refine, Functor.mapIso_trans, Iso.trans_assoc] using hh

/-- Descend all specified roots as sections, with their exact final comparison. -/
theorem Geometry.roots_exist {s n : ℕ} {D : RootData k s n}
    {K : (FieldStage k)} (G : Geometry D K) (hK : FiniteDimensional k K) :
    ∃ L : (FieldStage k), FiniteDimensional k L ∧ ∃ (N : Model D.cover L)
      (E : Refinement G.cover N)
      (r : Fin s → Sections ((Scheme.Modules.pullback (G.refine E).map).obj
        (G.refine E).powers.base.line)),
      ∀ i, (G.refine E).lineComparison.hom.app ⊤
        (pullbackGlobalSection N.projection _ (r i)) = D.roots i := by
  let H := (Scheme.Modules.pullback G.map).obj G.powers.base.line
  let a (i : Fin s) := G.lineComparison.inv.app ⊤ (D.roots i)
  obtain ⟨L, hL, N, E, a0, ha0⟩ := finite_line_sections D.cover K hK G.cover H
    (pullback_isLineBundle G.map G.powers.base.line G.powers.base.isLine) s a
  refine ⟨L, hL, N, E, (fun i => (G.targetRefinement E).hom.app ⊤ (a0 i)), ?_⟩
  intro i
  erw [pullbackGlobalSection_map]
  have hh := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (congrArg Iso.hom (G.targetRefinement_comparison E)))
    (pullbackGlobalSection N.projection _ (a0 i))
  refine hh.trans ?_
  change G.lineComparison.hom.app ⊤
    ((refinementComparison E H).hom.app ⊤ (pullbackGlobalSection N.projection _ (a0 i))) = _
  rw [ha0 i]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    G.lineComparison.inv_hom_id) (D.roots i)

end RamifiedRoots
open RamifiedRoots
variable {k : Type} [Field k] [CharZero k]

/-- Simultaneous descent of all finite algebraic data of the specified ramified root family. -/
theorem ramified_roots_constant_extension (k : Type) [Field k] [CharZero k] (s n : ℕ) (_hn : 0 < n)
    (D : RootData k s n)
    (K0 : (FieldStage k)) (hK0 : FiniteDimensional k K0) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧
      Nonempty (RootModel D K) := by
  obtain ⟨K1, hK1, h01, ⟨G⟩⟩ := RamifiedRoots.geometry_exists D K0 hK0
  obtain ⟨K2, hK2, N, E, r, hr⟩ := G.roots_exist hK1
  let G2 := G.refine E
  have hc := cartesian_of_comparison G2.cover G2.powers.base.model D.map D.over_eq
    G2.map G2.over_eq G2.comparison
  let := D.finite
  let := D.surjective
  obtain ⟨hf, hs, hd⟩ := FiniteMapExtension.properties_of_cartesian
    G2.cover G2.powers.base.model D.map G2.map G2.over_eq hc
  refine ⟨K2, hK2, h01.trans E.inclusion, ⟨{
    base := G2.powers.base.model
    cover := G2.cover
    map := G2.map
    over_eq := G2.over_eq
    comparison := G2.comparison
    cartesian := hc
    finite := hf
    surjective := hs
    degree_comparison := hd
    degree := ?_
    cusp := G2.cusp
    cusp_over := G2.cusp_over
    cusp_comparison := G2.cusp_comparison
    line := G2.powers.base.line
    isLine := G2.powers.base.isLine
    lineComparison := G2.powers.base.comparison
    powers := G2.powers.sections
    powers_nonzero := ?_
    powers_comparison := G2.powers.comparison
    roots := r
    roots_comparison := hr
    equation := ?_ }⟩⟩
  · intro x
    have := (projection_fpqc G2.powers.base.model).1
    obtain ⟨y, rfl⟩ := G2.powers.base.model.projection.surjective x
    rw [hd y]
    exact D.degree y
  · intro i hi
    apply D.powers_nonzero i
    rw [← G2.powers.comparison i, hi]
    exact RamifiedRoots.sectionComparison_zero G2.powers.base.model.projection
      (tensorPower G2.powers.base.model.curve.space G2.powers.base.line n)
      (powerComparison G2.powers.base.model.projection G2.powers.base.line
        G2.powers.base.comparison n)
  · intro i
    apply (root_equation_cartesian_reflection D.base D.cover K2 G2.powers.base.model
      G2.cover D.map G2.map G2.comparison G2.powers.base.line G2.powers.base.isLine
      D.line G2.powers.base.comparison n (G2.powers.sections i) (r i)).mpr
    rw [G2.powers.comparison i]
    change RootEquation D.map D.line n (D.powers i)
      ((G.refine E).lineComparison.hom.app ⊤ (pullbackGlobalSection N.projection _ (r i)))
    rw [hr i]
    exact D.equation i

end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.ramified_roots_constant_extension
