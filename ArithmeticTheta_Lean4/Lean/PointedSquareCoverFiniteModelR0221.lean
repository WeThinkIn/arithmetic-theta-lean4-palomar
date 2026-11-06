import PointedCurveFiniteModelR0221
import FiniteEtaleMapFiniteModelR0221
import LineFiniteModelR0221
import FinitePowerSectionsModelR0221

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open FiniteEtaleMap FinitePowerSections

/-- A descended line, retaining its actual scalar-extension comparison. -/
structure LineModel (X : Curve Omega) (J : X.space.Modules) (K : FieldStage) where
  model : Model X K
  line : model.curve.space.Modules
  isLine : IsLineBundle model.curve.space line
  comparison : (Scheme.Modules.pullback model.projection).obj line ≅ J

def LineModel.refine {X : Curve Omega} {J : X.space.Modules} {K L : FieldStage}
    (A : LineModel X J K) {N : Model X L} (E : Refinement A.model N) : LineModel X J L where
  model := N
  line := (Scheme.Modules.pullback E.map).obj A.line
  isLine := FiniteLineHoms.pullback_isLineBundle E.map A.line A.isLine
  comparison := refinementComparison E A.line ≪≫ A.comparison

/-- A rational marked point is retained under every Cartesian refinement. -/
def refinePoint {X : Curve Omega} {K L : FieldStage} {M : Model X K} {N : Model X L}
    (E : Refinement M N) (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _) :
    Base L ⟶ N.curve.space :=
  E.cartesian.lift (extensionMap E.inclusion ≫ x) (𝟙 _) (by simp [Category.assoc, hx])

@[simp] theorem refinePoint_over {X : Curve Omega} {K L : FieldStage}
    {M : Model X K} {N : Model X L} (E : Refinement M N)
    (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _) :
    refinePoint E x hx ≫ N.curve.map = 𝟙 _ := E.cartesian.lift_snd _ _ _

theorem refinePoint_comparison {X : Curve Omega} {K L : FieldStage}
    {M : Model X K} {N : Model X L} (E : Refinement M N)
    (x : Base K ⟶ M.curve.space) (hx : x ≫ M.curve.map = 𝟙 _)
    (z : Base Omega ⟶ X.space) (hz : z ≫ X.map = 𝟙 _)
    (hc : constantMap K ≫ x = z ≫ M.projection) :
    constantMap L ≫ refinePoint E x hx = z ≫ N.projection := by
  apply E.cartesian.hom_ext
  · simp only [Category.assoc, refinePoint, IsPullback.lift_fst]
    rw [← Category.assoc, constantMap_extensionMap, hc, E.comparison]
  · simp only [Category.assoc, refinePoint_over, Category.comp_id]
    rw [N.cartesian.w, ← Category.assoc, hz, Category.id_comp]

/-- Pointed line models exist over a finite extension of any prescribed stage. -/
theorem pointed_line_model (X : Curve Omega) (J : X.space.Modules)
    (hJ : IsLineBundle X.space J) (z : Base Omega ⟶ X.space)
    (hz : z ≫ X.map = 𝟙 _) (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧
      ∃ (A : LineModel X J K) (x : Base K ⟶ A.model.curve.space),
        x ≫ A.model.curve.map = 𝟙 _ ∧ constantMap K ≫ x = z ≫ A.model.projection := by
  obtain ⟨K, hK, hle, M, x, hx⟩ :=
    pointed_curve_finite_model X K0 hK0 1 (fun _ => z) (fun _ => hz)
  obtain ⟨L, hL, N, E, J0, hJ0, ⟨e⟩⟩ := line_finite_model X K hK M J hJ
  refine ⟨L, hL, hle.trans E.inclusion, ⟨N, J0, hJ0, e⟩,
    refinePoint E (x 0) (hx 0).1, refinePoint_over E (x 0) (hx 0).1, ?_⟩
  exact refinePoint_comparison E (x 0) (hx 0).1 z hz (hx 0).2

/-- Geometric and line data of the cover, before imposing its square and sections. -/
structure Geometry {s n b : ℕ} (D : RootData s n b) (K : FieldStage) where
  base : LineModel D.base D.weight K
  cover : LineModel D.cover D.half K
  map : cover.model.curve.space ⟶ base.model.curve.space
  over_eq : map ≫ base.model.curve.map = cover.model.curve.map
  comparison : cover.model.projection ≫ map = D.map ≫ base.model.projection
  cusp : Base K ⟶ cover.model.curve.space
  cusp_over : cusp ≫ cover.model.curve.map = 𝟙 _
  cusp_comparison : constantMap K ≫ cusp = D.cusp ≫ cover.model.projection

/-- Both lines and the marked cover are constructed over a common finite stage. -/
theorem geometry_exists {s n b : ℕ} (D : RootData s n b)
    (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧ Nonempty (Geometry D K) := by
  have hz : (D.cusp ≫ D.map) ≫ D.base.map = 𝟙 _ := by
    rw [Category.assoc, D.over_eq, D.cusp_over]
  obtain ⟨K1, hK1, h01, A, _, _⟩ := pointed_line_model D.base D.weight D.weight_line
    (D.cusp ≫ D.map) hz K0 hK0
  obtain ⟨K2, hK2, h12, B, x, hx, hxc⟩ := pointed_line_model D.cover D.half D.half_line
    D.cusp D.cusp_over K1 hK1
  let A2 := A.refine (extendRefinement A.model h12)
  obtain ⟨K3, hK3, Y, X, EY, EX, f, hf, hcart, _, _, _, _⟩ :=
    finite_etale_map_finite_model D.cover D.base K2 hK2 B.model A2.model
      D.map D.over_eq D.finite D.etale D.surjective
  refine ⟨K3, hK3, h01.trans (h12.trans EY.inclusion), ⟨{
    base := A2.refine EX
    cover := B.refine EY
    map := f
    over_eq := hf
    comparison := hcart.w
    cusp := refinePoint EY x hx
    cusp_over := refinePoint_over EY x hx
    cusp_comparison := refinePoint_comparison EY x hx D.cusp D.cusp_over hxc }⟩⟩

/-- Refining the cover induces an actual compatible extension of its base. -/
def Geometry.refine {s n b : ℕ} {D : RootData s n b} {K L : FieldStage}
    (G : Geometry D K) {N : Model D.cover L} (E : Refinement G.cover.model N) :
    Geometry D L where
  base := G.base.refine (extendRefinement G.base.model E.inclusion)
  cover := G.cover.refine E
  map := pullback.lift (E.map ≫ G.map) N.curve.map (by
    rw [Category.assoc, G.over_eq]; exact E.cartesian.w)
  over_eq := pullback.lift_snd _ _ _
  comparison := by
    apply pullback.hom_ext
    · change N.projection ≫ _ ≫ pullback.fst _ _ =
        D.map ≫ extendProjection G.base.model E.inclusion ≫ pullback.fst _ _
      rw [pullback.lift_fst, extendProjection_fst, ← Category.assoc, E.comparison]
      exact G.comparison
    · change N.projection ≫ _ ≫ pullback.snd _ _ =
        D.map ≫ extendProjection G.base.model E.inclusion ≫ pullback.snd _ _
      rw [pullback.lift_snd, extendProjection_snd, N.cartesian.w, ← Category.assoc, D.over_eq]
  cusp := refinePoint E G.cusp G.cusp_over
  cusp_over := refinePoint_over E G.cusp G.cusp_over
  cusp_comparison := refinePoint_comparison E G.cusp G.cusp_over
    D.cusp D.cusp_over G.cusp_comparison

/-- Functoriality of the recursively induced power isomorphism. -/
theorem powerIso_trans {X : Scheme} {H J Q : X.Modules} (e : H ≅ J) (f : J ≅ Q)
    (n : ℕ) : powerIso (e ≪≫ f) n = powerIso e n ≪≫ powerIso f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [powerIso]
    rw [ih]
    apply Iso.ext
    simp [sheafTensorCongr, Functor.map_comp, ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]

/-- A final line comparison composes with the canonical power comparison. -/
theorem powerComparison_trans {X Y : Scheme} (p : X ⟶ Y) (H : Y.Modules)
    {J Q : X.Modules} (e : (Scheme.Modules.pullback p).obj H ≅ J) (f : J ≅ Q) (n : ℕ) :
    powerComparison p H (e ≪≫ f) n = powerComparison p H e n ≪≫ powerIso f n := by
  simp only [powerComparison, powerIso_trans, Iso.trans_assoc]

/-- Refinement coherence with the actual comparison to the prescribed line. -/
theorem line_power_refinement {X : Curve Omega} {J : X.space.Modules} {K L : FieldStage}
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
theorem line_power_section_refinement {X : Curve Omega} {J : X.space.Modules}
    {K L : FieldStage} (A : LineModel X J K) {N : Model X L}
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

/-- The finite section provider applies to any chosen comparison with the original half-line. -/
theorem line_sections_exist {s n b : ℕ} (D : RootData s n b) {K : FieldStage}
    (hK : FiniteDimensional ℚ K) (A : LineModel D.cover D.half K) :
    ∃ L : FieldStage, FiniteDimensional ℚ L ∧ ∃ (N : Model D.cover L)
      (E : Refinement A.model N) (a : Fin s → Sections (tensorPower N.curve.space (A.refine E).line n)),
      ∀ i, (powerComparison N.projection (A.refine E).line (A.refine E).comparison n).hom.app ⊤
        (pullbackGlobalSection N.projection _ (a i)) = D.sections i := by
  let a (i : Fin s) := (powerIso A.comparison n).inv.app ⊤ (D.sections i)
  obtain ⟨L, hL, N, E, a0, ha0⟩ := finite_power_sections_model D.cover K hK A.model A.line
    A.isLine s (fun _ => n) a
  refine ⟨L, hL, N, E, a0, ?_⟩
  intro i
  change (powerComparison N.projection ((Scheme.Modules.pullback E.map).obj A.line)
    (refinementComparison E A.line ≪≫ A.comparison) n).hom.app ⊤ _ = _
  rw [powerComparison_trans]
  change (powerIso A.comparison n).hom.app ⊤
    ((powerComparison N.projection _ (refinementComparison E A.line) n).hom.app ⊤ _) = _
  dsimp only [LineModel.refine]
  rw [ha0 i]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (powerIso A.comparison n).inv_hom_id) (D.sections i)

/-- The prescribed cover degree bounds hold at all points of every geometric model. -/
theorem Geometry.properties {s n b : ℕ} {D : RootData s n b} {K : FieldStage}
    (G : Geometry D K) :
    IsPullback G.cover.model.projection D.map G.map G.base.model.projection ∧
    IsFinite G.map ∧ Etale G.map ∧ Surjective G.map ∧
      ∀ x : G.base.model.curve.space, 0 < G.map.finrank x ∧ G.map.finrank x ≤ b := by
  have hc := cartesian_of_comparison G.cover.model G.base.model D.map D.over_eq
    G.map G.over_eq G.comparison
  let := D.etale
  let := D.surjective
  obtain ⟨hf, he, hs, hd⟩ := properties_of_cartesian G.cover.model G.base.model D.map G.map G.over_eq hc
  refine ⟨hc, hf, he, hs, ?_⟩
  intro x
  have := (projection_fpqc G.base.model).1
  obtain ⟨y, rfl⟩ := G.base.model.projection.surjective x
  rw [hd y]
  exact D.degree y

/-- The canonical comparison for a specified commuting triangle. -/
def triangle {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z) (t : X ⟶ Z)
    (h : p ≫ q = t) (H : Z.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj H) ≅
      (Scheme.Modules.pullback t).obj H :=
  (Scheme.Modules.pullbackComp p q).app H ≪≫ (Scheme.Modules.pullbackCongr h).app H

/-- Pasting two triangles uses the accepted pullback associativity law. -/
theorem triangle_assoc {W X Y Z : Scheme} (p : W ⟶ X) (q : X ⟶ Y) (r : Y ⟶ Z)
    (t : W ⟶ Y) (u : W ⟶ Z) (ht : p ≫ q = t) (hu : t ≫ r = u)
    (h : p ≫ (q ≫ r) = u) (H : Z.Modules) :
    (Scheme.Modules.pullback p).mapIso ((Scheme.Modules.pullbackComp q r).app H) ≪≫
      triangle p (q ≫ r) u h H =
    triangle p q t ht ((Scheme.Modules.pullback r).obj H) ≪≫ triangle t r u hu H := by
  apply Iso.ext
  exact pullback_triangle_comp p q r t u ht hu h H

/-- Equality transport in the second leg is compatible with the triangle comparison. -/
theorem triangle_change {X Y Z : Scheme} (p : X ⟶ Y) (q q' : Y ⟶ Z)
    (u : X ⟶ Z) (hq : q = q') (h : p ≫ q = u) (h' : p ≫ q' = u) (H : Z.Modules) :
    (Scheme.Modules.pullback p).mapIso ((Scheme.Modules.pullbackCongr hq).app H) ≪≫
      triangle p q' u h' H = triangle p q u h H := by
  subst q'
  apply Iso.ext
  simp [Scheme.Modules.pullbackCongr]

/-- Naturality of the triangle comparison in its actual sheaf. -/
theorem triangle_naturality {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (u : X ⟶ Z) (h : p ≫ q = u) {H J : Z.Modules} (e : H ≅ J) :
    (Scheme.Modules.pullback p).mapIso ((Scheme.Modules.pullback q).mapIso e) ≪≫
      triangle p q u h J = triangle p q u h H ≪≫ (Scheme.Modules.pullback u).mapIso e := by
  apply Iso.ext
  exact ((Scheme.Modules.pullbackComp p q) ≪≫ Scheme.Modules.pullbackCongr h).hom.naturality e.hom

/-- The pullback comparison around a square. -/
def squareComparison {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ T)
    (r : A ⟶ C) (t : C ⟶ T) (h : p ≫ q = r ≫ t) (H : T.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj H) ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback t).obj H) :=
  triangle p q (r ≫ t) h H ≪≫ ((Scheme.Modules.pullbackComp r t).app H).symm

/-- Pasting a change of the middle factor into a two-step pullback path. -/
theorem triangle_diamond {A B C D E : Scheme}
    (p : A ⟶ B) (q : B ⟶ C) (r : C ⟶ E) (f : B ⟶ D) (g : D ⟶ E)
    (v : A ⟶ C) (t : A ⟶ D) (u : A ⟶ E)
    (hv : p ≫ q = v) (ht : p ≫ f = t) (he : q ≫ r = f ≫ g)
    (hu : v ≫ r = u) (hu' : t ≫ g = u) (H : E.Modules) :
    (Scheme.Modules.pullback p).mapIso (squareComparison q r f g he H) ≪≫
      triangle p f t ht ((Scheme.Modules.pullback g).obj H) ≪≫ triangle t g u hu' H =
    triangle p q v hv ((Scheme.Modules.pullback r).obj H) ≪≫ triangle v r u hu H := by
  have h₁ : p ≫ (q ≫ r) = u := by rw [← Category.assoc, hv, hu]
  have h₂ : p ≫ (f ≫ g) = u := by rw [← Category.assoc, ht, hu']
  rw [← triangle_assoc p f g t u ht hu' h₂ H]
  simp only [squareComparison, triangle, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hc := triangle_change p (q ≫ r) (f ≫ g) u he h₁ h₂ H
  have ha := triangle_assoc p q r v u hv hu h₁ H
  simpa only [triangle, Iso.trans_assoc] using
    (congrArg (fun e => (Scheme.Modules.pullback p).mapIso
      ((Scheme.Modules.pullbackComp q r).app H) ≪≫ e) hc).trans ha

/-- A triangle whiskered on the left, in the exact presentations of its maps. -/
theorem triangle_whisker {A B C T : Scheme} (p : A ⟶ B) (q : B ⟶ C)
    (r : C ⟶ T) (t : B ⟶ T) (ht : q ≫ r = t)
    (h : (p ≫ q) ≫ r = p ≫ t) (H : T.Modules) :
    ((Scheme.Modules.pullbackComp p q).app ((Scheme.Modules.pullback r).obj H)).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (triangle q r t ht H) =
    triangle (p ≫ q) r (p ≫ t) h H ≪≫ ((Scheme.Modules.pullbackComp p t).app H).symm := by
  have h' : p ≫ (q ≫ r) = p ≫ t := by rw [ht]
  have ha := triangle_assoc p q r (p ≫ q) (p ≫ t) rfl h h' H
  have hc := triangle_change p (q ≫ r) t (p ≫ t) ht h' rfl H
  have hcr : triangle p q (p ≫ q) rfl ((Scheme.Modules.pullback r).obj H) =
      (Scheme.Modules.pullbackComp p q).app ((Scheme.Modules.pullback r).obj H) := by
    apply Iso.ext; simp [triangle, Scheme.Modules.pullbackCongr]
  have htr : triangle p t (p ≫ t) rfl H = (Scheme.Modules.pullbackComp p t).app H := by
    apply Iso.ext; simp [triangle, Scheme.Modules.pullbackCongr]
  rw [hcr, ← hc, htr] at ha
  have hh := congrArg (fun e =>
    ((Scheme.Modules.pullbackComp p q).app ((Scheme.Modules.pullback r).obj H)).symm ≪≫
      e ≪≫ ((Scheme.Modules.pullbackComp p t).app H).symm) ha
  simpa only [triangle, Functor.mapIso_trans, Iso.trans_assoc,
    Iso.self_symm_id, Iso.symm_self_id_assoc, Iso.trans_refl] using hh

/-- Canonical square comparisons commute with refinement of both projections. -/
theorem square_paste {A B B' C T T' : Scheme}
    (p : A ⟶ B) (p' : A ⟶ B') (e : B' ⟶ B)
    (f : B ⟶ T) (f' : B' ⟶ T') (d : T' ⟶ T)
    (r : A ⟶ C) (q : C ⟶ T) (q' : C ⟶ T')
    (hp : p' ≫ e = p) (hq : q' ≫ d = q)
    (hf : e ≫ f = f' ≫ d) (h : p ≫ f = r ≫ q) (h' : p' ≫ f' = r ≫ q')
    (H : T.Modules) :
    (Scheme.Modules.pullback p').mapIso (squareComparison e f f' d hf H) ≪≫
      squareComparison p' f' r q' h' ((Scheme.Modules.pullback d).obj H) ≪≫
      (Scheme.Modules.pullback r).mapIso (triangle q' d q hq H) =
    triangle p' e p hp ((Scheme.Modules.pullback f).obj H) ≪≫
      squareComparison p f r q h H := by
  have hu : (r ≫ q') ≫ d = r ≫ q := by rw [Category.assoc, hq]
  have hd := triangle_diamond p' e f f' d p (r ≫ q') (r ≫ q) hp h' hf h hu H
  have hw := triangle_whisker r q' d q hq hu H
  dsimp only [squareComparison]
  rw [Iso.trans_assoc, hw]
  simpa only [squareComparison, Iso.trans_assoc] using
    congrArg (fun e => e ≪≫ ((Scheme.Modules.pullbackComp r q).app H).symm) hd

/-- The refinement's map commutes with the old cover map. -/
theorem Geometry.refine_map {s n b : ℕ} {D : RootData s n b} {K L : FieldStage}
    (G : Geometry D K) {N : Model D.cover L} (E : Refinement G.cover.model N) :
    E.map ≫ G.map = (G.refine E).map ≫ (extendRefinement G.base.model E.inclusion).map :=
  (pullback.lift_fst _ _ _).symm

/-- Actual identification of the two presentations of the refined target line. -/
def Geometry.targetRefinement {s n b : ℕ} {D : RootData s n b} {K L : FieldStage}
    (G : Geometry D K) {N : Model D.cover L} (E : Refinement G.cover.model N) :
    (Scheme.Modules.pullback E.map).obj ((Scheme.Modules.pullback G.map).obj G.base.line) ≅
      (Scheme.Modules.pullback (G.refine E).map).obj (G.refine E).base.line :=
  squareComparison E.map G.map (G.refine E).map
    (extendRefinement G.base.model E.inclusion).map (G.refine_map E) G.base.line

/-- Exact target comparison retained when the cover and base are refined together. -/
theorem Geometry.targetRefinement_comparison {s n b : ℕ} {D : RootData s n b}
    {K L : FieldStage} (G : Geometry D K) {N : Model D.cover L}
    (E : Refinement G.cover.model N) :
    (Scheme.Modules.pullback N.projection).mapIso (G.targetRefinement E) ≪≫
      squareTargetComparison D (G.refine E).base.model (G.refine E).cover.model
        (G.refine E).map (G.refine E).comparison (G.refine E).base.line
        (G.refine E).base.comparison =
    refinementComparison E ((Scheme.Modules.pullback G.map).obj G.base.line) ≪≫
      squareTargetComparison D G.base.model G.cover.model G.map G.comparison
        G.base.line G.base.comparison := by
  let B := extendRefinement G.base.model E.inclusion
  have h := square_paste G.cover.model.projection N.projection E.map G.map (G.refine E).map
    B.map D.map G.base.model.projection (extendModel G.base.model E.inclusion).projection
    E.comparison B.comparison (G.refine_map E) G.comparison (G.refine E).comparison G.base.line
  have hh := congrArg (fun e => e ≪≫ (Scheme.Modules.pullback D.map).mapIso G.base.comparison) h
  simpa only [Geometry.targetRefinement, squareComparison, triangle, squareTargetComparison,
    refinementComparison, Geometry.refine, LineModel.refine, Functor.mapIso_trans, Iso.trans_assoc]
    using hh

/-- Descend the specified square isomorphism with its exact canonical comparison. -/
theorem Geometry.square_exists {s n b : ℕ} {D : RootData s n b} {K : FieldStage}
    (G : Geometry D K) (hK : FiniteDimensional ℚ K) :
    ∃ L : FieldStage, FiniteDimensional ℚ L ∧ ∃ (N : Model D.cover L)
      (E : Refinement G.cover.model N)
      (sq : tensorPower N.curve.space (G.refine E).cover.line 2 ≅
        (Scheme.Modules.pullback (G.refine E).map).obj (G.refine E).base.line),
      (Scheme.Modules.pullback N.projection).mapIso sq ≪≫
        squareTargetComparison D (G.refine E).base.model (G.refine E).cover.model
          (G.refine E).map (G.refine E).comparison (G.refine E).base.line
          (G.refine E).base.comparison =
      powerComparison N.projection (G.refine E).cover.line (G.refine E).cover.comparison 2 ≪≫
        D.square := by
  let J := tensorPower G.cover.model.curve.space G.cover.line 2
  let H := (Scheme.Modules.pullback G.map).obj G.base.line
  let S := powerComparison G.cover.model.projection G.cover.line G.cover.comparison 2
  let T := squareTargetComparison D G.base.model G.cover.model G.map G.comparison
    G.base.line G.base.comparison
  let a : (Scheme.Modules.pullback G.cover.model.projection).obj J ≅
      (Scheme.Modules.pullback G.cover.model.projection).obj H := S ≪≫ D.square ≪≫ T.symm
  obtain ⟨L, hL, N, E, a0, ha0, hi, _⟩ := finite_line_homs_model D.cover K hK G.cover.model
    J H (tensorPower_isLineBundle G.cover.line G.cover.isLine 2)
    (FiniteLineHoms.pullback_isLineBundle G.map G.base.line G.base.isLine) 1 (fun _ => a.hom)
  have : IsIso (a0 0) := (hi 0).mpr (by infer_instance)
  let P := pullback_tensorPower_iso N.curve.space G.cover.model.curve.space E.map G.cover.line 2
  let sq := P.symm ≪≫ asIso (a0 0) ≪≫ G.targetRefinement E
  refine ⟨L, hL, N, E, sq, ?_⟩
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullback N.projection).map P.hom)).mp
  have ht := congrArg Iso.hom (G.targetRefinement_comparison E)
  dsimp only [Iso.trans_hom, Functor.mapIso_hom] at ht
  have hs := line_power_refinement G.cover E 2
  change (Scheme.Modules.pullback N.projection).map P.hom ≫
      ((Scheme.Modules.pullback N.projection).map sq.hom ≫ _) =
    (Scheme.Modules.pullback N.projection).map P.hom ≫
      ((powerComparison N.projection (G.cover.refine E).line
        (G.cover.refine E).comparison 2).hom ≫ D.square.hom)
  dsimp only [sq, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, P.hom_inv_id]
  erw [(Scheme.Modules.pullback N.projection).map_id, Category.id_comp]
  erw [ht, ← Category.assoc, ha0 0, Category.assoc]
  dsimp only [a, Iso.trans_hom, Iso.symm_hom]
  change (refinementComparison E J).hom ≫ S.hom ≫ D.square.hom ≫ T.inv ≫ T.hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using (congrArg (fun f => f ≫ D.square.hom) hs).symm

end ArithmeticThetaFiniteFieldModelsR0221.PointedSquareCover


namespace ArithmeticThetaFiniteFieldModelsR0221
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open PointedSquareCover

/-- Simultaneous finite number-field descent of the same pointed square-root cover,
its two actual lines, specified square isomorphism, and finite section family. -/
theorem pointed_square_cover_finite_model (s n b : ℕ) (D : RootData s n b)
    (K0 : FieldStage) (hK0 : FiniteDimensional ℚ K0) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧ Nonempty (RootModel D K) := by
  obtain ⟨K1, hK1, h01, ⟨G⟩⟩ := geometry_exists D K0 hK0
  obtain ⟨K2, hK2, N, E, a, ha⟩ := line_sections_exist D hK1 G.cover
  let G2 := G.refine E
  obtain ⟨K3, hK3, P, F, sq, hsq⟩ := G2.square_exists hK2
  let G3 := G2.refine F
  obtain ⟨hc, hf, he, hs, hd⟩ := G3.properties
  refine ⟨K3, hK3, h01.trans (E.inclusion.trans F.inclusion), ⟨{
    base := G3.base.model
    cover := G3.cover.model
    map := G3.map
    over_eq := G3.over_eq
    comparison := G3.comparison
    cartesian := hc
    finite := hf
    etale := he
    surjective := hs
    degree := hd
    cusp := G3.cusp
    cusp_over := G3.cusp_over
    cusp_comparison := G3.cusp_comparison
    weight := G3.base.line
    weight_line := G3.base.isLine
    weightComparison := G3.base.comparison
    half := G3.cover.line
    half_line := G3.cover.isLine
    halfComparison := G3.cover.comparison
    square := sq
    square_comparison := hsq
    sections := fun i => pullbackPowerSection F.map G2.cover.line n (a i)
    sections_comparison := ?_ }⟩⟩
  intro i
  exact (line_power_section_refinement G2.cover F n (a i)).trans (ha i)

end ArithmeticThetaFiniteFieldModelsR0221

#print axioms ArithmeticThetaFiniteFieldModelsR0221.pointed_square_cover_finite_model
