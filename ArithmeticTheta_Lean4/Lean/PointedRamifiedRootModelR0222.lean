import RamifiedFiniteMapModelR0222
import RootEquationCartesianReflectionR0222

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRamifiedRootModelsR0222
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteEtaleMap
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
namespace PointedRamifiedRoot

/-- The actual section comparison carries the zero section to zero. -/
theorem sectionComparison_zero {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules)
    {H : X.Modules} (e : (Scheme.Modules.pullback p).obj J ≅ H) :
    e.hom.app ⊤ (pullbackGlobalSection p J 0) = 0 := by
  have h : pullbackGlobalSection p J 0 = 0 :=
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app J).app ⊤).hom.map_zero
  rw [h]
  exact (e.hom.app ⊤).hom.map_zero

/-- A model of the base line together with the specified power sections. -/
structure Powers {s n : ℕ} (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
    (K : FieldStage) where
  base : LineModel D.base D.line K
  sections : Fin s → Sections (tensorPower base.model.curve.space base.line n)
  comparison : ∀ i, (powerComparison base.model.projection base.line base.comparison n).hom.app ⊤
    (pullbackGlobalSection base.model.projection _ (sections i)) = D.powers i

def Powers.refine {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K L : FieldStage} (A : Powers D K) {N : Model D.base L}
    (E : Refinement A.base.model N) : Powers D L where
  base := A.base.refine E
  sections := fun i => pullbackPowerSection E.map A.base.line n (A.sections i)
  comparison := fun i => (line_power_section_refinement A.base E n (A.sections i)).trans
    (A.comparison i)

theorem powers_exists {s n : ℕ} (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
    (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧ Nonempty (Powers D K) := by
  have hz : (D.cusp ≫ D.map) ≫ D.base.map = 𝟙 _ := by
    rw [Category.assoc, D.over_eq, D.cusp_over]
  obtain ⟨K, hK, hle, A, _, _⟩ := pointed_line_model D.base D.line D.isLine
    (D.cusp ≫ D.map) hz K0 hK0
  let a (i : Fin s) := (powerIso A.comparison n).inv.app ⊤ (D.powers i)
  obtain ⟨L, hL, N, E, a0, ha0⟩ := finite_power_sections_model D.base K hK A.model
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
structure Geometry {s n : ℕ} (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
    (K : FieldStage) where
  powers : Powers D K
  cover : Model D.cover K
  map : cover.curve.space ⟶ powers.base.model.curve.space
  over_eq : map ≫ powers.base.model.curve.map = cover.curve.map
  comparison : cover.projection ≫ map = D.map ≫ powers.base.model.projection
  cusp : Base K ⟶ cover.curve.space
  cusp_over : cusp ≫ cover.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.projection

theorem geometry_exists {s n : ℕ} (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
    (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧ Nonempty (Geometry D K) := by
  obtain ⟨K1, hK1, h01, ⟨A⟩⟩ := powers_exists D K0 hK0
  obtain ⟨K2, hK2, h12, B, x, hx⟩ := pointed_curve_finite_model D.cover K1 hK1 1
    (fun _ => D.cusp) (fun _ => D.cusp_over)
  let A2 := A.refine (extendRefinement A.base.model h12)
  obtain ⟨K3, hK3, Y, X, EY, EX, f, hf, hcart, _, _, _⟩ :=
    ramified_finite_map_model D.cover D.base K2 hK2 B A2.base.model
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
def Geometry.refine {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K L : FieldStage} (G : Geometry D K) {N : Model D.cover L}
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
      rw [pullback.lift_fst, extendProjection_fst, ← Category.assoc, E.comparison]
      exact G.comparison
    · change N.projection ≫ _ ≫ pullback.snd _ _ =
        D.map ≫ extendProjection G.powers.base.model E.inclusion ≫ pullback.snd _ _
      rw [pullback.lift_snd, extendProjection_snd, N.cartesian.w, ← Category.assoc, D.over_eq]
  cusp := refinePoint E G.cusp G.cusp_over
  cusp_over := refinePoint_over E G.cusp G.cusp_over
  cusp_comparison := refinePoint_comparison E G.cusp G.cusp_over D.cusp D.cusp_over G.cusp_comparison

theorem Geometry.refine_map {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K L : FieldStage} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover N) :
    E.map ≫ G.map = (G.refine E).map ≫
      (extendRefinement G.powers.base.model E.inclusion).map :=
  (pullback.lift_fst _ _ _).symm

/-- The actual line on the refined cover, identified by the commuting square. -/
def Geometry.targetRefinement {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K L : FieldStage} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover N) :
    (Scheme.Modules.pullback E.map).obj ((Scheme.Modules.pullback G.map).obj G.powers.base.line) ≅
      (Scheme.Modules.pullback (G.refine E).map).obj (G.refine E).powers.base.line :=
  squareComparison E.map G.map (G.refine E).map
    (extendRefinement G.powers.base.model E.inclusion).map (G.refine_map E) G.powers.base.line

def Geometry.lineComparison {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K : FieldStage} (G : Geometry D K) :=
  coverLineComparison G.powers.base.model G.cover D.map G.map G.comparison
    G.powers.base.line G.powers.base.comparison

/-- Pasting the refinement square preserves the specified comparison to the original cover line. -/
theorem Geometry.targetRefinement_comparison {s n : ℕ}
    {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n} {K L : FieldStage}
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
theorem Geometry.roots_exist {s n : ℕ} {D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n}
    {K : FieldStage} (G : Geometry D K) (hK : FiniteDimensional ℚ K) :
    ∃ L : FieldStage, FiniteDimensional ℚ L ∧ ∃ (N : Model D.cover L)
      (E : Refinement G.cover N)
      (r : Fin s → Sections ((Scheme.Modules.pullback (G.refine E).map).obj
        (G.refine E).powers.base.line)),
      ∀ i, (G.refine E).lineComparison.hom.app ⊤
        (pullbackGlobalSection N.projection _ (r i)) = D.roots i := by
  let H := (Scheme.Modules.pullback G.map).obj G.powers.base.line
  let a (i : Fin s) := G.lineComparison.inv.app ⊤ (D.roots i)
  obtain ⟨L, hL, N, E, a0, ha0⟩ := finite_line_sections D.cover K hK G.cover H
    (FiniteLineHoms.pullback_isLineBundle G.map G.powers.base.line G.powers.base.isLine) s a
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

end PointedRamifiedRoot

/-- Simultaneous descent of all finite algebraic data of the specified ramified root family. -/
theorem pointed_ramified_root_model (s n : ℕ) (_hn : 0 < n)
    (D : ArithmeticThetaRamifiedRootModelsR0222.RootData s n)
    (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧
      Nonempty (ArithmeticThetaRamifiedRootModelsR0222.RootModel D K) := by
  obtain ⟨K1, hK1, h01, ⟨G⟩⟩ := PointedRamifiedRoot.geometry_exists D K0 hK0
  obtain ⟨K2, hK2, N, E, r, hr⟩ := G.roots_exist hK1
  let G2 := G.refine E
  have hc := cartesian_of_comparison G2.cover G2.powers.base.model D.map D.over_eq
    G2.map G2.over_eq G2.comparison
  let := D.finite
  let := D.surjective
  obtain ⟨hf, hs, hd⟩ := RamifiedFiniteMap.properties_of_cartesian
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
    exact PointedRamifiedRoot.sectionComparison_zero G2.powers.base.model.projection
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

end ArithmeticThetaRamifiedRootModelsR0222

#print axioms ArithmeticThetaRamifiedRootModelsR0222.pointed_ramified_root_model
