import RootAlgebraBaseChange
import NormalizedPowerCoefficients
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Global root charts

Construction of the root scheme from affine trivializations of the actual line
bundle. The transition maps use the actual frame coefficients and the quotient
root in `unitRootAlgebra`.
-/

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower
open ArithmeticThetaNormalizedSections ArithmeticThetaGeometricPrerequisites
open ArithmeticThetaRootTorsor

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaGlobalization

/-- Restrict an actual natural frame to a smaller open. -/
def restrictFrame {X : Scheme.{u}} {H : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (V : X.Opens) (hVU : V ≤ U) : LocalFrame X H V where
  equiv W hWV := e.equiv W (hWV.trans hVU)
  naturality W Z hZW hWV a := e.naturality W Z hZW (hWV.trans hVU) a

/-- Coordinates commute with restriction on the actual sheaf. -/
lemma frame_coordinate_restrict {X : Scheme.{u}} {H : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U)
    (s : Γ(H, V)) :
    (e.equiv W (hWV.trans hVU)).symm (H.presheaf.map (homOfLE hWV).op s) =
      X.presheaf.map (homOfLE hWV).op ((e.equiv V hVU).symm s) := by
  apply (e.equiv W (hWV.trans hVU)).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [← e.naturality V W hWV hVU, LinearEquiv.apply_symm_apply]

/-- Changing a genuine local basis preserves invertibility of a coefficient. -/
lemma isUnit_coordinate_change {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (e f : R ≃ₗ[R] M) (s : M) (hs : IsUnit (f.symm s)) : IsUnit (e.symm s) := by
  have h : e.symm s = (transitionUnit e f : R) * f.symm s := by
    apply e.injective
    simpa only [LinearEquiv.apply_symm_apply, transitionUnit] using
      transition_apply e f (f.symm s)
  rw [h]
  exact (transitionUnit e f).isUnit.mul hs

/-- An affine chart with an actual frame and an invertible coefficient of `d`. -/
structure RootChart (X : Scheme.{u}) (H : X.Modules) (N : ℕ)
    (d : Γ(tensorPower X H N, ⊤)) where
  opens : X.Opens
  affine : IsAffineOpen opens
  nonempty : Nonempty opens
  frame : LocalFrame X H opens
  coefficient_isUnit : IsUnit (sectionCoordinate X (tensorPower X H N) opens
    (tensorPowerFrame X H opens frame N) d)

/-- Good root charts form a basis, including when the base scheme is empty. -/
lemma exists_rootChart {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    {x : X} {W : X.Opens} (hxW : x ∈ W) :
    ∃ C : RootChart X H N d, x ∈ C.opens ∧ C.opens ≤ W := by
  obtain ⟨U, hxU, ⟨E⟩⟩ := hH x
  let e := localFrameOfIso X H U E
  obtain ⟨V, hxV, f, hf⟩ := hd x
  obtain ⟨Z, hZ, hxZ, hZsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (U ⊓ V) ⊓ W from ⟨⟨hxU, hxV⟩, hxW⟩)
  have hZU : Z ≤ U := le_trans hZsub (inf_le_left.trans inf_le_left)
  have hZV : Z ≤ V := le_trans hZsub (inf_le_left.trans inf_le_right)
  let eZ := restrictFrame e Z hZU
  refine ⟨⟨Z, hZ, ⟨⟨x, hxZ⟩⟩, eZ, ?_⟩, hxZ, le_trans hZsub inf_le_right⟩
  apply isUnit_coordinate_change _ (f.equiv Z hZV)
  have hres := hf.map (X.presheaf.map (homOfLE hZV).op).hom
  rw [← frame_coordinate_restrict f V Z hZV le_rfl] at hres
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using hres

namespace RootChart

variable {X : Scheme.{u}} {H : X.Modules} {N : ℕ}
  {d : Γ(tensorPower X H N, ⊤)}

instance (C : RootChart X H N d) : Nonempty C.opens := C.nonempty

/-- The unit defining the chart polynomial is the coefficient of the given section. -/
def coefficient (C : RootChart X H N d) : Γ(X, C.opens)ˣ :=
  C.coefficient_isUnit.unit

@[simp] lemma coefficient_val (C : RootChart X H N d) :
    (C.coefficient : Γ(X, C.opens)) = sectionCoordinate X (tensorPower X H N) C.opens
      (tensorPowerFrame X H C.opens C.frame N) d :=
  C.coefficient_isUnit.unit_spec

instance : Preorder (RootChart X H N d) := Preorder.lift RootChart.opens

/-- The actual coefficient relating two frames on a contained chart. -/
def transition (C D : RootChart X H N d) (hCD : C ≤ D) : Γ(X, C.opens)ˣ :=
  transitionUnit (D.frame.equiv C.opens hCD) (C.frame.equiv C.opens le_rfl)

/-- The defining coefficients transform by the Nth power of the frame transition. -/
lemma coefficient_transition (C D : RootChart X H N d) (hCD : C ≤ D) :
    X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op (D.coefficient : Γ(X, D.opens)) =
      (C.transition D hCD : Γ(X, C.opens)) ^ N * (C.coefficient : Γ(X, C.opens)) := by
  rw [coefficient_val, coefficient_val]
  unfold sectionCoordinate
  rw [← frame_coordinate_restrict]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  let e := (tensorPowerFrame X H D.opens D.frame N).equiv C.opens hCD
  let f := (tensorPowerFrame X H C.opens C.frame N).equiv C.opens le_rfl
  have h := transition_apply e f
    (f.symm ((tensorPower X H N).presheaf.map (homOfLE le_top).op d))
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.apply_symm_apply] at h
  have ht : ArithmeticThetaLineRoot.transition e f =
      (C.transition D hCD : Γ(X, C.opens)) ^ N :=
    congrArg (fun z : Γ(X, C.opens)ˣ => (z : Γ(X, C.opens)))
      (tensorPowerFrame_transition X H D.opens C.opens D.frame C.frame N C.opens hCD le_rfl)
  rw [ht] at h
  exact h

end RootChart

/-- The universal algebra homomorphism of a root chart. -/
def rootAlgebraLift {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (N : ℕ) (a : Rˣ) (f : R →+* S) (b : S) (hb : b ^ N = f a) :
    unitRootAlgebra R N a →+* S :=
  AdjoinRoot.lift f b (by simpa using sub_eq_zero.mpr hb)

@[simp] lemma rootAlgebraLift_root {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] (N : ℕ) (a : Rˣ) (f : R →+* S)
    (b : S) (hb : b ^ N = f a) :
    rootAlgebraLift N a f b hb (rootElement R N a) = b :=
  AdjoinRoot.lift_root _

@[simp] lemma rootAlgebraLift_algebraMap {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] (N : ℕ) (a : Rˣ) (f : R →+* S)
    (b : S) (hb : b ^ N = f a) (r : R) :
    rootAlgebraLift N a f b hb (algebraMap R (unitRootAlgebra R N a) r) = f r :=
  AdjoinRoot.lift_of _

/-- A ring map out of a chart is uniquely determined by coefficients and the root. -/
lemma rootAlgebra_hom_ext {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (N : ℕ) (a : Rˣ) {f g : unitRootAlgebra R N a →+* S}
    (hcoeff : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hroot : f (rootElement R N a) = g (rootElement R N a)) : f = g := by
  apply AdjoinRoot.ringHom_ext (RingHom.ext hcoeff) hroot

/-- Universal property with literal coefficient ring map; no chosen scalar structure. -/
lemma rootAlgebra_existsUnique_lift {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] (N : ℕ) (a : Rˣ) (f : R →+* S)
    (b : S) (hb : b ^ N = f a) :
    ∃! F : unitRootAlgebra R N a →+* S,
      (∀ r, F (algebraMap R _ r) = f r) ∧ F (rootElement R N a) = b := by
  refine ⟨rootAlgebraLift N a f b hb, ⟨?_, rootAlgebraLift_root ..⟩, ?_⟩
  · exact rootAlgebraLift_algebraMap N a f b hb
  · intro F hF
    apply rootAlgebra_hom_ext N a
    · intro r
      rw [hF.1, rootAlgebraLift_algebraMap]
    · rw [hF.2, rootAlgebraLift_root]

/-- The quotient root is invertible for positive exponent, even over a zero ring. -/
lemma rootElement_isUnit {R : Type u} [CommRing R] (N : ℕ) (hN : 0 < N) (a : Rˣ) :
    IsUnit (rootElement R N a) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt hN)).mp
  rw [show rootElement R N a ^ N = algebraMap R _ (a : R) from unitRoot_pow R N a]
  exact a.isUnit.map (algebraMap R _)

/-- Base change followed by the actual unit frame transition. -/
lemma root_algebra_base_change_transition (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (N : ℕ) (a : Rˣ) (b c : Sˣ)
    (h : Units.map ((algebraMap R S).toMonoidHom) a = c ^ N * b) :
    ∃ e : TensorProduct R S (unitRootAlgebra R N a) ≃ₐ[S] unitRootAlgebra S N b,
      e (TensorProduct.tmul R (1 : S) (rootElement R N a)) =
        algebraMap S (unitRootAlgebra S N b) c * rootElement S N b := by
  obtain ⟨e, he⟩ := root_algebra_base_change R S N a
  obtain ⟨f, hf⟩ := unit_root_frame_transition S N _ b c h
  refine ⟨e.trans f, ?_⟩
  change f (e _) = _
  rw [he]
  exact hf

namespace RootChart

variable {X : Scheme.{u}} {H : X.Modules} {N : ℕ}
  {d : Γ(tensorPower X H N, ⊤)}

/-- The ring of the root chart is the supplied `AdjoinRoot` algebra. -/
abbrev Algebra (C : RootChart X H N d) := unitRootAlgebra Γ(X, C.opens) N C.coefficient

/-- Restriction with the actual change-of-frame multiplier. -/
def algebraMap (C D : RootChart X H N d) (hCD : C ≤ D) : D.Algebra →+* C.Algebra :=
  rootAlgebraLift N D.coefficient
    ((_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra).comp
      (X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op).hom)
    (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra (C.transition D hCD) *
      rootElement Γ(X, C.opens) N C.coefficient) (by
    rw [mul_pow, show rootElement Γ(X, C.opens) N C.coefficient ^ N =
      _root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra (C.coefficient : Γ(X, C.opens)) from
      unitRoot_pow .., ← map_pow, ← map_mul]
    exact congrArg (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra)
      (coefficient_transition C D hCD).symm)

@[simp] lemma algebraMap_root (C D : RootChart X H N d) (hCD : C ≤ D) :
    C.algebraMap D hCD (rootElement Γ(X, D.opens) N D.coefficient) =
      _root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra (C.transition D hCD) *
        rootElement Γ(X, C.opens) N C.coefficient := rootAlgebraLift_root ..

@[simp] lemma algebraMap_coeff (C D : RootChart X H N d) (hCD : C ≤ D)
    (a : Γ(X, D.opens)) :
    C.algebraMap D hCD (_root_.Algebra.algebraMap Γ(X, D.opens) D.Algebra a) =
      _root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra
        (X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op a) := rootAlgebraLift_algebraMap ..

@[simp] lemma transition_self (C : RootChart X H N d) : C.transition C le_rfl = 1 := by
  apply Units.ext
  exact ArithmeticThetaLineRoot.transition_self _

lemma transition_comp (C D E : RootChart X H N d) (hCD : C ≤ D) (hDE : D ≤ E) :
    (C.transition E (hCD.trans hDE) : Γ(X, C.opens)) =
      X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op (D.transition E hDE : Γ(X, D.opens)) * (C.transition D hCD : Γ(X, C.opens)) := by
  change ArithmeticThetaLineRoot.transition _ _ =
    X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op (ArithmeticThetaLineRoot.transition _ _) *
      ArithmeticThetaLineRoot.transition _ _
  rw [ArithmeticThetaLineRoot.transition_restrict E.frame D.frame hDE le_rfl hCD]
  exact ArithmeticThetaLineRoot.transition_cocycle _ _ _

@[simp] lemma algebraMap_self (C : RootChart X H N d) :
    C.algebraMap C le_rfl = RingHom.id _ := by
  apply rootAlgebra_hom_ext N C.coefficient
  · intro r
    rw [algebraMap_coeff]
    simp
  · simp

lemma algebraMap_comp (C D E : RootChart X H N d) (hCD : C ≤ D) (hDE : D ≤ E) :
    (C.algebraMap D hCD).comp (D.algebraMap E hDE) =
      C.algebraMap E (hCD.trans hDE) := by
  apply rootAlgebra_hom_ext N E.coefficient
  · intro r
    simp only [RingHom.comp_apply, algebraMap_coeff]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · simp only [RingHom.comp_apply, algebraMap_root, map_mul, algebraMap_coeff]
    rw [transition_comp C D E hCD hDE, map_mul, mul_assoc]

/-- Chart restriction is scalar extension, with its prescribed frame multiplier. -/
lemma algebraMap_isPushout (C D : RootChart X H N d) (hCD : C ≤ D) :
    IsPushout (X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op)
      (CommRingCat.ofHom (_root_.Algebra.algebraMap Γ(X, D.opens) D.Algebra))
      (CommRingCat.ofHom (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra))
      (CommRingCat.ofHom (C.algebraMap D hCD)) := by
  let f := (X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op).hom
  let : _root_.Algebra Γ(X, D.opens) Γ(X, C.opens) := f.toAlgebra
  have hc : Units.map ((_root_.Algebra.algebraMap Γ(X, D.opens) Γ(X, C.opens)).toMonoidHom)
      D.coefficient = C.transition D hCD ^ N * C.coefficient := by
    apply Units.ext
    exact coefficient_transition C D hCD
  obtain ⟨e, he⟩ := root_algebra_base_change_transition Γ(X, D.opens) Γ(X, C.opens)
    N D.coefficient C.coefficient (C.transition D hCD) hc
  apply (CommRingCat.isPushout_tensorProduct Γ(X, D.opens) Γ(X, C.opens) D.Algebra).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
  · rfl
  · rfl
  · ext r
    exact e.commutes r
  · apply CommRingCat.hom_ext
    apply rootAlgebra_hom_ext N D.coefficient
    · intro r
      change e (TensorProduct.tmul Γ(X, D.opens) 1
          (_root_.Algebra.algebraMap Γ(X, D.opens) D.Algebra r)) =
        C.algebraMap D hCD (_root_.Algebra.algebraMap Γ(X, D.opens) D.Algebra r)
      rw [algebraMap_coeff]
      have h : TensorProduct.tmul Γ(X, D.opens) (1 : Γ(X, C.opens))
          (_root_.Algebra.algebraMap Γ(X, D.opens) D.Algebra r) =
          _root_.Algebra.algebraMap Γ(X, C.opens)
            (TensorProduct Γ(X, D.opens) Γ(X, C.opens) D.Algebra) (f r) := by
        exact (_root_.Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
      rw [h, e.commutes]
    · change e (TensorProduct.tmul Γ(X, D.opens) 1
          (rootElement Γ(X, D.opens) N D.coefficient)) =
        C.algebraMap D hCD (rootElement Γ(X, D.opens) N D.coefficient)
      rw [algebraMap_root]
      exact he

end RootChart

/-- Affine trivializations on which the prescribed power section has unit coefficient. -/
def rootChartCover {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) : X.OpenCover where
  I₀ := RootChart X H N d
  X C := Spec Γ(X, C.opens)
  f C := C.affine.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨C, hxC, _⟩ := exists_rootChart hH hd (show x ∈ (⊤ : X.Opens) from trivial)
    refine ⟨C, ?_⟩
    change x ∈ Set.range C.affine.fromSpec
    rw [C.affine.range_fromSpec]
    exact hxC

instance rootChartCover_preorder {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) :
    Preorder (rootChartCover hH hd).I₀ := inferInstanceAs (Preorder (RootChart X H N d))

instance rootChartCover_locallyDirected {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) :
    (rootChartCover hH hd).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange (by
    intro C D
    simp only [rootChartCover, IsAffineOpen.opensRange_fromSpec]
    rfl) (by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hxW
    obtain ⟨C, hxC, hCW⟩ := exists_rootChart hH hd hxW
    refine ⟨C.opens, ⟨C, ?_⟩, hxC, hCW⟩
    exact C.affine.opensRange_fromSpec)

/-- The cover transition is the Spec of the restriction map on the base scheme. -/
lemma rootChartCover_trans {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    (rootChartCover hH hd).trans (homOfLE hCD) =
      Spec.map (X.presheaf.map (homOfLE (show C.opens ≤ D.opens from hCD)).op) := by
  rw [← cancel_mono ((rootChartCover hH hd).f D), Scheme.Cover.trans_map]
  exact (D.affine.map_fromSpec C.affine _).symm

/-- The affine root schemes and their contravariant ring maps. -/
def rootSchemeFunctor {X : Scheme.{u}} {H : X.Modules} {N : ℕ}
    {d : Γ(tensorPower X H N, ⊤)} : RootChart X H N d ⥤ Scheme.{u} where
  obj C := Spec (CommRingCat.of C.Algebra)
  map {C D} hCD := Spec.map (CommRingCat.ofHom (C.algebraMap D (leOfHom hCD)))
  map_id C := by rw [RootChart.algebraMap_self]; exact Spec.map_id _
  map_comp {C D E} hCD hDE := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RootChart.algebraMap_comp C D E (leOfHom hCD) (leOfHom hDE)).symm

/-- Root-chart structure morphisms form an equifibered diagram over the base cover. -/
def rootGluingData {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) :
    Scheme.Cover.RelativeGluingData (rootChartCover hH hd) where
  functor := rootSchemeFunctor
  natTrans :=
    { app C := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra))
      naturality {C D} hCD := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (rootChartCover hH hd).trans hCD
        rw [show hCD = homOfLE (leOfHom hCD) from Subsingleton.elim _ _, rootChartCover_trans]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext r
        exact C.algebraMap_coeff D (leOfHom hCD) r }
  equifibered {C D} hCD := by
    change IsPullback (Spec.map _) (Spec.map _) (Spec.map _)
      ((rootChartCover hH hd).trans hCD)
    rw [show hCD = homOfLE (leOfHom hCD) from Subsingleton.elim _ _, rootChartCover_trans]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _
      (C.algebraMap_isPushout D (leOfHom hCD))).flip

/-- The scheme obtained by gluing the actual unit-root affine charts. -/
abbrev globalRootScheme {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) : Scheme.{u} :=
  (rootGluingData hH hd).glued

/-- The structural morphism of the glued root scheme. -/
abbrev globalRootMap {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) : globalRootScheme hH hd ⟶ X :=
  (rootGluingData hH hd).toBase

/-- Properties local on the target descend from the constructed affine root charts. -/
lemma globalRootMap_property {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ C : RootChart X H N d,
      P (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra)))) :
    P (globalRootMap hH hd) := by
  apply IsZariskiLocalAtTarget.of_openCover (rootChartCover hH hd)
  intro C
  let h := ((rootGluingData hH hd).isPullback_natTrans_ι_toBase C).flip
  change P (CategoryTheory.Limits.pullback.snd (globalRootMap hH hd) _)
  rw [← h.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hP C

/-- Finiteness, etaleness and the rank of each actual chart morphism. -/
lemma rootChart_properties {X : Scheme.{u}} {H : X.Modules} {N : ℕ}
    {d : Γ(tensorPower X H N, ⊤)} (hN : 0 < N) (hNu : IsUnit (N : Γ(X, ⊤)))
    (C : RootChart X H N d) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra))) ∧
    Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra))) ∧
    ∀ x : Spec Γ(X, C.opens),
      Scheme.Hom.finrank (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, C.opens) C.Algebra))) x = N := by
  have hNuC : IsUnit (N : Γ(X, C.opens)) := by
    simpa only [map_natCast] using
      hNu.map (X.presheaf.map (homOfLE (show C.opens ≤ ⊤ from le_top)).op).hom
  obtain ⟨hf, hfin, hr, he⟩ := unit_root_algebra_finite_etale Γ(X, C.opens) N hN hNuC C.coefficient
  let := hf
  let := hfin
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hfin
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he
  · intro x
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    exact hr

/-- The glued root cover is finite and etale when the positive exponent is invertible. -/
lemma globalRootMap_finite_etale {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (hN : 0 < N) (hNu : IsUnit (N : Γ(X, ⊤))) :
    IsFinite (globalRootMap hH hd) ∧ Etale (globalRootMap hH hd) := by
  constructor
  · exact globalRootMap_property hH hd _ (fun C => (rootChart_properties hN hNu C).1)
  · exact globalRootMap_property hH hd _ (fun C => (rootChart_properties hN hNu C).2.1)

/-- The rank is the prescribed exponent at every point, including disconnected bases. -/
lemma globalRootMap_finrank {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (hN : 0 < N) (hNu : IsUnit (N : Γ(X, ⊤))) (x : X) :
    Scheme.Hom.finrank (globalRootMap hH hd) x = N := by
  obtain ⟨hfin, he⟩ := globalRootMap_finite_etale hH hd hN hNu
  let := hfin
  let := he
  obtain ⟨C, y, hy⟩ := (rootChartCover hH hd).exists_eq x
  rw [← hy]
  have hr := Scheme.Hom.finrank_of_isPullback _ _ _ _
    ((rootGluingData hH hd).isPullback_natTrans_ι_toBase C).flip y
  exact hr.symm.trans ((rootChart_properties hN hNu C).2.2 y)

/-- A positive-rank finite etale root cover is surjective. -/
lemma globalRootMap_surjective {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (hN : 0 < N) (hNu : IsUnit (N : Γ(X, ⊤))) :
    Surjective (globalRootMap hH hd) := by
  obtain ⟨hfin, he⟩ := globalRootMap_finite_etale hH hd hN hNu
  let := hfin
  let := he
  apply (Scheme.Hom.one_le_finrank_iff_surjective _).mp
  intro x
  rw [globalRootMap_finrank hH hd hN hNu x]
  exact hN

/-- The affine chart immersion into the glued scheme. -/
abbrev rootChartInclusion {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    Spec (CommRingCat.of C.Algebra) ⟶ globalRootScheme hH hd :=
  CategoryTheory.Limits.colimit.ι (rootGluingData hH hd).functor C

lemma rootChartInclusion_range {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    (rootChartInclusion hH hd C).opensRange = globalRootMap hH hd ⁻¹ᵁ C.opens := by
  simpa only [rootChartCover, IsAffineOpen.opensRange_fromSpec] using
    ((rootGluingData hH hd).toBase_preimage_eq_opensRange_ι C).symm

lemma rootChartInclusion_preimage {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    (⊤ : (Spec (CommRingCat.of C.Algebra)).Opens) ≤
      rootChartInclusion hH hd C ⁻¹ᵁ (globalRootMap hH hd ⁻¹ᵁ C.opens) := by
  rw [← rootChartInclusion_range hH hd C, Scheme.Hom.preimage_opensRange]

/-- Evaluation on the actual affine chart, with the canonical Gamma-Spec comparison. -/
def rootChartEvaluation {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    Γ(globalRootScheme hH hd, globalRootMap hH hd ⁻¹ᵁ C.opens) ⟶ CommRingCat.of C.Algebra :=
  (rootChartInclusion hH hd C).appLE _ ⊤ (rootChartInclusion_preimage hH hd C) ≫
    (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).hom

instance rootChartEvaluation_isIso {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    IsIso (rootChartEvaluation hH hd C) := by
  have := (rootChartInclusion hH hd C).isIso_app
    (globalRootMap hH hd ⁻¹ᵁ C.opens) (rootChartInclusion_range hH hd C).ge
  have hm : (homOfLE (rootChartInclusion_preimage hH hd C)).op =
      (eqToHom (top_le_iff.mp (rootChartInclusion_preimage hH hd C)).symm).op :=
    Subsingleton.elim _ _
  unfold rootChartEvaluation Scheme.Hom.appLE
  rw [hm]
  infer_instance

/-- The universal quotient root regarded as a function on the inverse-image open. -/
def tautologicalCoefficient {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    Γ(globalRootScheme hH hd, globalRootMap hH hd ⁻¹ᵁ C.opens) :=
  inv (rootChartEvaluation hH hd C) (rootElement Γ(X, C.opens) N C.coefficient)

@[simp] lemma tautologicalCoefficient_evaluation {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    rootChartEvaluation hH hd C (tautologicalCoefficient hH hd C) =
      rootElement Γ(X, C.opens) N C.coefficient := by
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (rootChartEvaluation hH hd C)) _

lemma tautologicalCoefficient_isUnit {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (hN : 0 < N)
    (C : RootChart X H N d) : IsUnit (tautologicalCoefficient hH hd C) :=
  (rootElement_isUnit N hN C.coefficient).map (inv (rootChartEvaluation hH hd C)).hom

open P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux
  (appLE_congr_hom appLE_top_top)

@[reassoc] lemma rootChartInclusion_transition {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    Spec.map (CommRingCat.ofHom (C.algebraMap D hCD)) ≫ rootChartInclusion hH hd D =
      rootChartInclusion hH hd C :=
  CategoryTheory.Limits.colimit.w (rootGluingData hH hd).functor (homOfLE hCD)

lemma rootChartEvaluation_naturality {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    (globalRootScheme hH hd).presheaf.map
        (homOfLE ((globalRootMap hH hd).preimage_mono hCD)).op ≫ rootChartEvaluation hH hd C =
      rootChartEvaluation hH hd D ≫ CommRingCat.ofHom (C.algebraMap D hCD) := by
  unfold rootChartEvaluation
  have hle : (⊤ : (Spec (CommRingCat.of C.Algebra)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (C.algebraMap D hCD)) ≫ rootChartInclusion hH hd D) ⁻¹ᵁ
        (globalRootMap hH hd ⁻¹ᵁ D.opens) := by
    rw [Scheme.Hom.comp_preimage,
      top_le_iff.mp (rootChartInclusion_preimage hH hd D)]
    exact le_rfl
  rw [Scheme.Hom.map_appLE_assoc,
    appLE_congr_hom (rootChartInclusion_transition hH hd C D hCD).symm _ ⊤ _ hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ (rootChartInclusion_preimage hH hd D) le_rfl,
    Category.assoc, appLE_top_top, Scheme.ΓSpecIso_naturality, Category.assoc]

lemma rootChartInclusion_toBase {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    rootChartInclusion hH hd C ≫ globalRootMap hH hd =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra)) ≫ C.affine.fromSpec :=
  (rootGluingData hH hd).ι_toBase C

lemma rootChartEvaluation_base {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    (globalRootMap hH hd).app C.opens ≫ rootChartEvaluation hH hd C =
      CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra) := by
  have h1 : (⊤ : (Spec Γ(X, C.opens)).Opens) ≤ C.affine.fromSpec ⁻¹ᵁ C.opens := by
    rw [C.affine.fromSpec_preimage_self]
  have h2 : (⊤ : (Spec (CommRingCat.of C.Algebra)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra)) ≫
        C.affine.fromSpec) ⁻¹ᵁ C.opens := by
    rw [Scheme.Hom.comp_preimage, C.affine.fromSpec_preimage_self]
    exact le_rfl
  have h4 : C.affine.fromSpec.appLE C.opens ⊤ h1 = (Scheme.ΓSpecIso Γ(X, C.opens)).inv := by
    rw [Scheme.Hom.appLE, C.affine.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have hm : (eqToHom C.affine.fromSpec_preimage_self).op ≫ (homOfLE h1).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hm, CategoryTheory.Functor.map_id, Category.comp_id]
  unfold rootChartEvaluation
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc,
    appLE_congr_hom (rootChartInclusion_toBase hH hd C) C.opens ⊤ _ h2]
  trans (C.affine.fromSpec.appLE C.opens ⊤ h1 ≫
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra))).appLE ⊤ ⊤ le_rfl) ≫ (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).hom
  · rw [Scheme.Hom.appLE_comp_appLE]
  rw [h4, Category.assoc, appLE_top_top, Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc _ _

/-- The quotient root equation holds as an equality of functions on the chart preimage. -/
lemma tautologicalCoefficient_pow {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    tautologicalCoefficient hH hd C ^ N =
      (globalRootMap hH hd).app C.opens (C.coefficient : Γ(X, C.opens)) := by
  apply (ConcreteCategory.bijective_of_isIso (rootChartEvaluation hH hd C)).injective
  rw [map_pow, tautologicalCoefficient_evaluation]
  rw [← CommRingCat.comp_apply, rootChartEvaluation_base]
  exact unitRoot_pow ..

/-- The local universal roots transform by the actual frame multiplier. -/
lemma tautologicalCoefficient_transition {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    (globalRootScheme hH hd).presheaf.map
        (homOfLE ((globalRootMap hH hd).preimage_mono hCD)).op
        (tautologicalCoefficient hH hd D) =
      (globalRootMap hH hd).app C.opens (C.transition D hCD : Γ(X, C.opens)) *
        tautologicalCoefficient hH hd C := by
  apply (ConcreteCategory.bijective_of_isIso (rootChartEvaluation hH hd C)).injective
  rw [← CommRingCat.comp_apply, rootChartEvaluation_naturality, CommRingCat.comp_apply,
    tautologicalCoefficient_evaluation, map_mul,
    ← CommRingCat.comp_apply, rootChartEvaluation_base, tautologicalCoefficient_evaluation]
  exact C.algebraMap_root D hCD

namespace RootChart

variable {X Y : Scheme.{u}} {H : X.Modules} {N : ℕ}
  {d : Γ(tensorPower X H N, ⊤)}

/-- The actual pullback frame, chosen from the proved compatible-frame construction. -/
def pulledFrame (f : Y ⟶ X) (C : RootChart X H N d) :
    LocalFrame Y ((Scheme.Modules.pullback f).obj H) (f ⁻¹ᵁ C.opens) :=
  (exists_pullbackFrame Y X f H C.opens C.frame).choose

lemma pulledFrame_compatible (f : Y ⟶ X) (C : RootChart X H N d) :
    FramePullbackCompatible f H C.opens C.frame (C.pulledFrame f) :=
  (exists_pullbackFrame Y X f H C.opens C.frame).choose_spec

/-- The transition unit of pulled frames is the image of the original transition. -/
lemma pulledFrame_transition (f : Y ⟶ X) (C D : RootChart X H N d) (hCD : C ≤ D) :
    ArithmeticThetaLineRoot.transition
        ((D.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) (f.preimage_mono hCD))
        ((C.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) le_rfl) =
      f.app C.opens (C.transition D hCD : Γ(X, C.opens)) := by
  apply ((D.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) (f.preimage_mono hCD)).injective
  simp only [ArithmeticThetaLineRoot.transition, LinearEquiv.apply_symm_apply]
  rw [← D.pulledFrame_compatible f C.opens hCD]
  have he : D.frame.equiv C.opens hCD (C.transition D hCD : Γ(X, C.opens)) =
      C.frame.equiv C.opens le_rfl 1 := by
    exact LinearEquiv.apply_symm_apply _ _
  rw [he, C.pulledFrame_compatible f C.opens le_rfl, map_one (f.app C.opens).hom]

lemma pulledFrame_transition_apply (f : Y ⟶ X) (C D : RootChart X H N d)
    (hCD : C ≤ D) (b : Γ(Y, f ⁻¹ᵁ C.opens)) :
    (D.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) (f.preimage_mono hCD)
        (f.app C.opens (C.transition D hCD : Γ(X, C.opens)) * b) =
      (C.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) le_rfl b := by
  rw [← pulledFrame_transition f C D hCD]
  exact (ArithmeticThetaLineRoot.transition_apply _ _ b).symm

end RootChart

lemma rootChart_preimages_cover {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) :
    (⊤ : Y.Opens) ≤ ⨆ C : RootChart X H N d, f ⁻¹ᵁ C.opens := by
  intro y _
  obtain ⟨C, hy, _⟩ := exists_rootChart hH hd (show f y ∈ (⊤ : X.Opens) from trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨C, hy⟩

/-- Compatibility on contained root charts implies compatibility on every overlap. -/
lemma rootChart_sections_compatible {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) (M : Y.Modules)
    (s : ∀ C : RootChart X H N d, Γ(M, f ⁻¹ᵁ C.opens))
    (hs : ∀ (C D : RootChart X H N d) (hCD : C ≤ D),
      M.presheaf.map (homOfLE (f.preimage_mono hCD)).op (s D) = s C) :
    TopCat.Presheaf.IsCompatible M.presheaf (fun C : RootChart X H N d => f ⁻¹ᵁ C.opens) s := by
  intro C D
  let J := {E : RootChart X H N d // E ≤ C ∧ E ≤ D}
  let U : J → Y.Opens := fun E => f ⁻¹ᵁ E.val.opens
  have hU : f ⁻¹ᵁ C.opens ⊓ f ⁻¹ᵁ D.opens ≤ iSup U := by
    intro y hy
    obtain ⟨E, hyE, hECD⟩ := exists_rootChart hH hd
      (show f y ∈ C.opens ⊓ D.opens from hy)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨E, hECD.trans inf_le_left, hECD.trans inf_le_right⟩, hyE⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ U
    (f ⁻¹ᵁ C.opens ⊓ f ⁻¹ᵁ D.opens)
    (fun E => homOfLE (le_inf (f.preimage_mono E.property.1) (f.preimage_mono E.property.2))) hU
  intro E
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (hs E.val C E.property.1).trans (hs E.val D E.property.2).symm

/-- A compatible family on the inverse images of all root charts glues uniquely. -/
lemma rootChart_sections_glue {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) (M : Y.Modules)
    (s : ∀ C : RootChart X H N d, Γ(M, f ⁻¹ᵁ C.opens))
    (hs : ∀ (C D : RootChart X H N d) (hCD : C ≤ D),
      M.presheaf.map (homOfLE (f.preimage_mono hCD)).op (s D) = s C) :
    ∃! v : Γ(M, ⊤), ∀ C : RootChart X H N d,
      M.presheaf.map (homOfLE le_top).op v = s C :=
  TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ _ ⊤ (fun _ => homOfLE le_top)
    (rootChart_preimages_cover hH hd f) s (rootChart_sections_compatible hH hd f M s hs)

/-- The local tautological section in the actual pulled-back frame. -/
def tautologicalLocalSection {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    Γ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H, globalRootMap hH hd ⁻¹ᵁ C.opens) :=
  (C.pulledFrame (globalRootMap hH hd)).equiv _ le_rfl (tautologicalCoefficient hH hd C)

lemma tautologicalLocalSection_restrict {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H).presheaf.map
      (homOfLE ((globalRootMap hH hd).preimage_mono hCD)).op (tautologicalLocalSection hH hd D) =
      tautologicalLocalSection hH hd C := by
  unfold tautologicalLocalSection
  rw [(D.pulledFrame (globalRootMap hH hd)).naturality, tautologicalCoefficient_transition]
  exact C.pulledFrame_transition_apply (globalRootMap hH hd) D hCD _

/-- The generating tautological root in the genuine pullback line bundle. -/
def tautologicalSection {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) :
    Γ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H, ⊤) :=
  (rootChart_sections_glue hH hd (globalRootMap hH hd) _
    (tautologicalLocalSection hH hd) (tautologicalLocalSection_restrict hH hd)).choose

lemma tautologicalSection_restrict {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (C : RootChart X H N d) :
    ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H).presheaf.map (homOfLE le_top).op
      (tautologicalSection hH hd) = tautologicalLocalSection hH hd C :=
  (rootChart_sections_glue hH hd (globalRootMap hH hd) _
    (tautologicalLocalSection hH hd) (tautologicalLocalSection_restrict hH hd)).choose_spec.1 C

/-- The tautological section generates the pullback line everywhere. -/
lemma tautologicalSection_generating {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (hN : 0 < N) :
    IsGeneratingSection (globalRootScheme hH hd)
      ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H) (tautologicalSection hH hd) := by
  intro y
  obtain ⟨C, hyC, _⟩ := exists_rootChart hH hd
    (show globalRootMap hH hd y ∈ (⊤ : X.Opens) from trivial)
  refine ⟨globalRootMap hH hd ⁻¹ᵁ C.opens, hyC, C.pulledFrame (globalRootMap hH hd), ?_⟩
  rw [tautologicalSection_restrict]
  change IsUnit (((C.pulledFrame (globalRootMap hH hd)).equiv _ le_rfl).symm
    (((C.pulledFrame (globalRootMap hH hd)).equiv _ le_rfl) (tautologicalCoefficient hH hd C)))
  rw [LinearEquiv.symm_apply_apply]
  exact tautologicalCoefficient_isUnit hH hd hN C

/-- The actual tensor power of the tautological section is the canonical pullback of `d`. -/
lemma tautologicalSection_pow {X : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) :
    tensorPowerSection (globalRootScheme hH hd)
      ((Scheme.Modules.pullback (globalRootMap hH hd)).obj H) N ⊤ (tautologicalSection hH hd) =
      pullbackPowerSection (globalRootMap hH hd) H N d := by
  let T := globalRootScheme hH hd
  let p := globalRootMap hH hd
  let M := (Scheme.Modules.pullback p).obj H
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨(tensorPower T M N).presheaf, (tensorPower T M N).isSheaf⟩
    (fun C : RootChart X H N d => p ⁻¹ᵁ C.opens) ⊤ (fun _ => homOfLE le_top)
    (rootChart_preimages_cover hH hd p)
  intro C
  rw [tensorPowerSection_restrict, tautologicalSection_restrict]
  change tensorPowerSection T M N (p ⁻¹ᵁ C.opens)
      ((C.pulledFrame p).equiv _ le_rfl (tautologicalCoefficient hH hd C)) = _
  rw [tensorPowerSection_frame, tautologicalCoefficient_pow]
  apply ((tensorPowerFrame T M _ (C.pulledFrame p) N).equiv _ le_rfl).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (pullbackPowerSection_coordinate T X p H C.opens C.frame (C.pulledFrame p)
    (C.pulledFrame_compatible p) N d).symm

/-- Pullback composition carries the iterated adjunction unit to the composite unit. -/
lemma pullbackComp_localSection {S T X : Scheme.{u}} (g : S ⟶ T) (p : T ⟶ X)
    (H : X.Modules) (U : X.Opens) (s : Γ(H, U)) :
    ((Scheme.Modules.pullbackComp g p).hom.app H).app (g ⁻¹ᵁ (p ⁻¹ᵁ U))
      (pullbackLocalSection g ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
        (pullbackLocalSection p H U s)) =
      pullbackLocalSection (g ≫ p) H U s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ p))
    (Scheme.Modules.pullbackComp g p).inv H
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hs := ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k U) h) s
  change pullbackLocalSection g ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
      (pullbackLocalSection p H U s) =
    ((Scheme.Modules.pullbackComp g p).inv.app H).app (g ⁻¹ᵁ (p ⁻¹ᵁ U))
      (pullbackLocalSection (g ≫ p) H U s) at hs
  rw [hs]
  exact ConcreteCategory.congr_hom (congrArg
    (fun k => Scheme.Modules.Hom.app k (g ⁻¹ᵁ (p ⁻¹ᵁ U)))
    ((Scheme.Modules.pullbackComp g p).app H).inv_hom_id) _

/-- The canonical global pullback restricts to the local adjunction-unit pullback. -/
lemma pullbackGlobalSection_restrict {Y X : Scheme.{u}} (f : Y ⟶ X)
    (H : X.Modules) (U : X.Opens) (s : Γ(H, ⊤)) :
    ((Scheme.Modules.pullback f).obj H).presheaf.map (homOfLE le_top).op
      (ArithmeticThetaPullback.pullbackGlobalSection f H s) =
    pullbackLocalSection f H U (H.presheaf.map (homOfLE le_top).op s) := by
  exact (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).val
    (homOfLE (show U ≤ ⊤ from le_top)).op s).symm

namespace RootChart

variable {X Y : Scheme.{u}} {H : X.Modules} {N : ℕ}
  {d : Γ(tensorPower X H N, ⊤)}

/-- The coefficient of an actual section in the pulled chart frame. -/
def sectionCoefficient (f : Y ⟶ X) (C : RootChart X H N d)
    (w : Γ((Scheme.Modules.pullback f).obj H, ⊤)) : Γ(Y, f ⁻¹ᵁ C.opens) :=
  sectionCoordinate Y ((Scheme.Modules.pullback f).obj H) (f ⁻¹ᵁ C.opens)
    (C.pulledFrame f) w

lemma sectionCoefficient_transition (f : Y ⟶ X) (C D : RootChart X H N d) (hCD : C ≤ D)
    (w : Γ((Scheme.Modules.pullback f).obj H, ⊤)) :
    Y.presheaf.map (homOfLE (f.preimage_mono hCD)).op (D.sectionCoefficient f w) =
      f.app C.opens (C.transition D hCD : Γ(X, C.opens)) * C.sectionCoefficient f w := by
  unfold sectionCoefficient sectionCoordinate
  rw [← frame_coordinate_restrict (D.pulledFrame f)]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  apply ((D.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) (f.preimage_mono hCD)).injective
  rw [LinearEquiv.apply_symm_apply, pulledFrame_transition_apply,
    LinearEquiv.apply_symm_apply]

/-- A root section satisfies the literal chart polynomial over the specific base map. -/
lemma rootSection_coefficient_pow (f : Y ⟶ X) (C : RootChart X H N d)
    (w : RootSections H N d f) :
    C.sectionCoefficient f w.val ^ N = f.app C.opens (C.coefficient : Γ(X, C.opens)) := by
  have hw := congrArg
    (sectionCoordinate Y (tensorPower Y ((Scheme.Modules.pullback f).obj H) N)
      (f ⁻¹ᵁ C.opens)
      (tensorPowerFrame Y ((Scheme.Modules.pullback f).obj H) (f ⁻¹ᵁ C.opens)
        (C.pulledFrame f) N)) w.property
  rw [pullbackPowerSection_coordinate Y X f H C.opens C.frame (C.pulledFrame f)
    (C.pulledFrame_compatible f)] at hw
  rw [coefficient_val]
  refine Eq.trans ?_ hw
  unfold sectionCoordinate
  rw [tensorPowerSection_restrict]
  have he : ((Scheme.Modules.pullback f).obj H).presheaf.map (homOfLE le_top).op w.val =
      (C.pulledFrame f).equiv (f ⁻¹ᵁ C.opens) le_rfl (C.sectionCoefficient f w.val) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  rw [he, tensorPowerSection_frame, LinearEquiv.symm_apply_apply]

end RootChart

namespace RootChart

variable {X Y : Scheme.{u}} {H : X.Modules} {N : ℕ}
  {d : Γ(tensorPower X H N, ⊤)}

/-- The ring map classified by the root coefficient on a test scheme. -/
def sectionLift (f : Y ⟶ X) (w : RootSections H N d f) (C : RootChart X H N d) :
    C.Algebra →+* Γ(Y, f ⁻¹ᵁ C.opens) :=
  rootAlgebraLift N C.coefficient (f.app C.opens).hom
    (C.sectionCoefficient f w.val) (C.rootSection_coefficient_pow f w)

@[simp] lemma sectionLift_root (f : Y ⟶ X) (w : RootSections H N d f)
    (C : RootChart X H N d) :
    C.sectionLift f w (rootElement Γ(X, C.opens) N C.coefficient) =
      C.sectionCoefficient f w.val := rootAlgebraLift_root ..

@[simp] lemma sectionLift_coeff (f : Y ⟶ X) (w : RootSections H N d f)
    (C : RootChart X H N d) (a : Γ(X, C.opens)) :
    C.sectionLift f w (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra a) =
      f.app C.opens a := rootAlgebraLift_algebraMap ..

lemma sectionLift_transition (f : Y ⟶ X) (w : RootSections H N d f)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    (Y.presheaf.map (homOfLE (f.preimage_mono hCD)).op).hom.comp (D.sectionLift f w) =
      (C.sectionLift f w).comp (C.algebraMap D hCD) := by
  apply rootAlgebra_hom_ext N D.coefficient
  · intro a
    simp only [RingHom.comp_apply, sectionLift_coeff, algebraMap_coeff]
    exact (ConcreteCategory.congr_hom (f.naturality
      (homOfLE (show C.opens ≤ D.opens from hCD)).op) a).symm
  · simp only [RingHom.comp_apply, sectionLift_root, algebraMap_root, map_mul, sectionLift_coeff]
    exact sectionCoefficient_transition f C D hCD w.val

/-- The map from the inverse-image open to the affine root chart. -/
def sectionMorphism (f : Y ⟶ X) (w : RootSections H N d f) (C : RootChart X H N d) :
    (f ⁻¹ᵁ C.opens).toScheme ⟶ Spec (CommRingCat.of C.Algebra) :=
  (f ⁻¹ᵁ C.opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (C.sectionLift f w))

lemma sectionMorphism_transition (f : Y ⟶ X) (w : RootSections H N d f)
    (C D : RootChart X H N d) (hCD : C ≤ D) :
    Y.homOfLE (f.preimage_mono hCD) ≫ D.sectionMorphism f w =
      C.sectionMorphism f w ≫ Spec.map (CommRingCat.ofHom (C.algebraMap D hCD)) := by
  unfold sectionMorphism
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map, Category.assoc,
    ← Spec.map_comp, Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  exact CommRingCat.hom_ext (sectionLift_transition f w C D hCD)

lemma sectionMorphism_toBase (f : Y ⟶ X) (w : RootSections H N d f)
    (C : RootChart X H N d) :
    C.sectionMorphism f w ≫
      Spec.map (CommRingCat.ofHom (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra)) ≫
        C.affine.fromSpec = (f ⁻¹ᵁ C.opens).ι ≫ f := by
  have hc : CommRingCat.ofHom (_root_.Algebra.algebraMap Γ(X, C.opens) C.Algebra) ≫
      CommRingCat.ofHom (C.sectionLift f w) = f.app C.opens := by
    ext a
    exact sectionLift_coeff f w C a
  unfold sectionMorphism
  rw [Category.assoc, ← Spec.map_comp_assoc, hc, Scheme.Opens.toSpecΓ_naturality_assoc,
    C.affine.toSpecΓ_fromSpec]
  exact morphismRestrict_ι f C.opens

end RootChart

/-- The inverse images of root charts form a directed cover of any test scheme. -/
abbrev rootPreimageCover {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) : Y.OpenCover where
  I₀ := RootChart X H N d
  X C := (f ⁻¹ᵁ C.opens).toScheme
  f C := (f ⁻¹ᵁ C.opens).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, inferInstance⟩
    obtain ⟨C, hyC, _⟩ := exists_rootChart hH hd (show f y ∈ (⊤ : X.Opens) from trivial)
    exact ⟨C, ⟨y, hyC⟩, rfl⟩

instance rootPreimageCover_preorder {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) :
    Preorder (rootPreimageCover hH hd f).I₀ := inferInstanceAs (Preorder (RootChart X H N d))

instance rootPreimageCover_locallyDirected {X Y : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : Y ⟶ X) :
    (rootPreimageCover hH hd f).LocallyDirected where
  trans {C D} hCD := Y.homOfLE (f.preimage_mono (leOfHom hCD))
  trans_id C := by simp
  trans_comp hCD hDE := by simp
  w hCD := by simp [rootPreimageCover]
  directed {C D} z := by
    let y := (CategoryTheory.Limits.pullback.fst ((f ⁻¹ᵁ C.opens).ι) ((f ⁻¹ᵁ D.opens).ι)) z
    let y' := (CategoryTheory.Limits.pullback.snd ((f ⁻¹ᵁ C.opens).ι) ((f ⁻¹ᵁ D.opens).ι)) z
    have heq : y.val = y'.val := congrArg (fun k : _ ⟶ Y => k z)
      (CategoryTheory.Limits.pullback.condition (f := (f ⁻¹ᵁ C.opens).ι) (g := (f ⁻¹ᵁ D.opens).ι))
    obtain ⟨E, hyE, hECD⟩ := exists_rootChart hH hd
      (show f y.val ∈ C.opens ⊓ D.opens from ⟨y.property, heq ▸ y'.property⟩)
    refine ⟨E, homOfLE (show E ≤ C from hECD.trans inf_le_left),
      homOfLE (show E ≤ D from hECD.trans inf_le_right), ⟨y.val, hyE⟩, ?_⟩
    apply (CategoryTheory.Limits.pullback.fst ((f ⁻¹ᵁ C.opens).ι) ((f ⁻¹ᵁ D.opens).ι)).injective
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Limits.pullback.lift_fst]
    exact Subtype.ext (Y.homOfLE_apply _ _)
  property_trans hCD := inferInstance

/-- The morphism to the glued cover classified by an actual root on a test scheme. -/
def rootSectionMorphism {X S : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : S ⟶ X)
    (w : RootSections H N d f) : S ⟶ globalRootScheme hH hd :=
  (rootPreimageCover hH hd f).glueMorphismsOfLocallyDirected
    (fun C => C.sectionMorphism f w ≫ rootChartInclusion hH hd C) (by
      intro C D hCD
      change S.homOfLE (f.preimage_mono (leOfHom hCD)) ≫ D.sectionMorphism f w ≫
        rootChartInclusion hH hd D = _
      rw [← Category.assoc, RootChart.sectionMorphism_transition f w C D (leOfHom hCD), Category.assoc,
        rootChartInclusion_transition hH hd C D (leOfHom hCD)])

lemma rootSectionMorphism_chart {X S : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : S ⟶ X)
    (w : RootSections H N d f) (C : RootChart X H N d) :
    (f ⁻¹ᵁ C.opens).ι ≫ rootSectionMorphism hH hd f w =
      C.sectionMorphism f w ≫ rootChartInclusion hH hd C :=
  by
    unfold rootSectionMorphism
    apply (rootPreimageCover hH hd f).map_glueMorphismsOfLocallyDirected
    intro D E hDE
    change S.homOfLE (f.preimage_mono (leOfHom hDE)) ≫ E.sectionMorphism f w ≫
      rootChartInclusion hH hd E = _
    rw [← Category.assoc, RootChart.sectionMorphism_transition f w D E (leOfHom hDE),
      Category.assoc, rootChartInclusion_transition hH hd D E (leOfHom hDE)]

lemma rootSectionMorphism_over {X S : Scheme.{u}} {H : X.Modules}
    (hH : IsLineBundle X H) {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (hd : IsGeneratingSection X (tensorPower X H N) d) (f : S ⟶ X)
    (w : RootSections H N d f) :
    rootSectionMorphism hH hd f w ≫ globalRootMap hH hd = f := by
  apply (rootPreimageCover hH hd f).hom_ext
  intro C
  change (f ⁻¹ᵁ C.opens).ι ≫ rootSectionMorphism hH hd f w ≫ globalRootMap hH hd = _
  rw [← Category.assoc, rootSectionMorphism_chart, Category.assoc, rootChartInclusion_toBase]
  exact C.sectionMorphism_toBase f w

/-- Scalar multiplication under the actual local section pullback. -/
lemma pullbackLocalSection_smul {Y X : Scheme.{u}} (f : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (a : Γ(X, U)) (s : Γ(H, U)) :
    pullbackLocalSection f H U (a • s) = f.app U a • pullbackLocalSection f H U s := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app_smul a s

/-- Canonical composition preserves the chosen pulled basis and hence every coefficient. -/
lemma pullbackComp_frame {S T X : Scheme.{u}} (g : S ⟶ T) (p : T ⟶ X)
    {H : X.Modules} {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (C : RootChart X H N d) (a : Γ(T, p ⁻¹ᵁ C.opens)) :
    ((Scheme.Modules.pullbackComp g p).hom.app H).app (g ⁻¹ᵁ (p ⁻¹ᵁ C.opens))
      (pullbackLocalSection g ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ C.opens)
        ((C.pulledFrame p).equiv _ le_rfl a)) =
      (C.pulledFrame (g ≫ p)).equiv _ le_rfl (g.app (p ⁻¹ᵁ C.opens) a) := by
  have hb : (C.pulledFrame p).equiv _ le_rfl a =
      a • pullbackLocalSection p H C.opens (C.frame.equiv C.opens le_rfl 1) := by
    rw [C.pulledFrame_compatible p C.opens le_rfl, map_one (p.app C.opens).hom]
    simpa only [smul_eq_mul, mul_one] using ((C.pulledFrame p).equiv _ le_rfl).map_smul a 1
  rw [hb, pullbackLocalSection_smul]
  rw [Scheme.Modules.Hom.app_smul, pullbackComp_localSection,
    C.pulledFrame_compatible (g ≫ p) C.opens le_rfl, map_one ((g ≫ p).app C.opens).hom]
  simpa only [smul_eq_mul, mul_one] using
    (((C.pulledFrame (g ≫ p)).equiv _ le_rfl).map_smul (g.app (p ⁻¹ᵁ C.opens) a) 1).symm

/-- Local coefficients of the exact canonical iterated pullback in the contract. -/
lemma pullbackSectionOver_comp_coefficient {S T X : Scheme.{u}} (g : S ⟶ T) (p : T ⟶ X)
    {H : X.Modules} {N : ℕ} {d : Γ(tensorPower X H N, ⊤)} (C : RootChart X H N d)
    (v : Γ((Scheme.Modules.pullback p).obj H, ⊤)) :
    C.sectionCoefficient (g ≫ p) (pullbackSectionOver p (g ≫ p) H ⟨g, rfl⟩ v) =
      g.app (p ⁻¹ᵁ C.opens) (C.sectionCoefficient p v) := by
  let A := (Scheme.Modules.pullback p).obj H
  let e := (Scheme.Modules.pullbackComp g p).app H
  have hn := PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (show (g ≫ p) ⁻¹ᵁ C.opens ≤ ⊤ from le_top)).op
    (ArithmeticThetaPullback.pullbackGlobalSection g A v)
  change e.hom.app _
      (((Scheme.Modules.pullback g).obj A).presheaf.map (homOfLE le_top).op
        (ArithmeticThetaPullback.pullbackGlobalSection g A v)) =
    ((Scheme.Modules.pullback (g ≫ p)).obj H).presheaf.map (homOfLE le_top).op
      (e.hom.app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection g A v)) at hn
  erw [pullbackGlobalSection_restrict g A (p ⁻¹ᵁ C.opens) v] at hn
  have hv : A.presheaf.map (homOfLE le_top).op v =
      (C.pulledFrame p).equiv _ le_rfl (C.sectionCoefficient p v) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  rw [hv] at hn
  unfold RootChart.sectionCoefficient sectionCoordinate pullbackSectionOver
  change ((C.pulledFrame (g ≫ p)).equiv _ le_rfl).symm
    (((Scheme.Modules.pullback (g ≫ p)).obj H).presheaf.map (homOfLE le_top).op
      (e.hom.app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection g A v))) = _
  rw [← hn]
  erw [pullbackComp_frame g p C (C.sectionCoefficient p v), LinearEquiv.symm_apply_apply]
  rfl

/-- The open inequality induced by a triangle over the base. -/
lemma rootOver_preimage {X S T : Scheme.{u}} (p : T ⟶ X) (f : S ⟶ X)
    (g : {g : S ⟶ T // g ≫ p = f}) (U : X.Opens) :
    f ⁻¹ᵁ U ≤ g.val ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, g.property]

lemma pullbackSectionOver_coefficient {S T X : Scheme.{u}} (p : T ⟶ X) (f : S ⟶ X)
    {H : X.Modules} {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
    (g : {g : S ⟶ T // g ≫ p = f}) (C : RootChart X H N d)
    (v : Γ((Scheme.Modules.pullback p).obj H, ⊤)) :
    C.sectionCoefficient f (pullbackSectionOver p f H g v) =
      g.val.appLE (p ⁻¹ᵁ C.opens) (f ⁻¹ᵁ C.opens) (rootOver_preimage p f g C.opens)
        (C.sectionCoefficient p v) := by
  rcases g with ⟨g, hg⟩
  subst f
  erw [Scheme.Hom.appLE_eq_app]
  exact pullbackSectionOver_comp_coefficient g p C v

section Universal

variable {X S : Scheme.{u}} {H : X.Modules} (hH : IsLineBundle X H)
  {N : ℕ} {d : Γ(tensorPower X H N, ⊤)}
  (hd : IsGeneratingSection X (tensorPower X H N) d) (f : S ⟶ X)

/-- Restriction of a morphism over the base to the corresponding chart opens. -/
def rootOverRestriction (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    Γ(globalRootScheme hH hd, globalRootMap hH hd ⁻¹ᵁ C.opens) ⟶ Γ(S, f ⁻¹ᵁ C.opens) :=
  g.val.appLE _ _ (rootOver_preimage (globalRootMap hH hd) f g C.opens)

lemma rootOverRestriction_base
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    (globalRootMap hH hd).app C.opens ≫ rootOverRestriction hH hd f g C = f.app C.opens := by
  unfold rootOverRestriction
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact (appLE_congr_hom g.property C.opens (f ⁻¹ᵁ C.opens) _ le_rfl).trans
    (Scheme.Hom.appLE_eq_app f)

/-- The ring map into local test-scheme functions associated to a morphism over the base. -/
def rootOverRingMap
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) : CommRingCat.of C.Algebra ⟶ Γ(S, f ⁻¹ᵁ C.opens) :=
  inv (rootChartEvaluation hH hd C) ≫ rootOverRestriction hH hd f g C

lemma rootOverRingMap_coeff
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    CommRingCat.ofHom (algebraMap Γ(X, C.opens) C.Algebra) ≫ rootOverRingMap hH hd f g C =
      f.app C.opens := by
  unfold rootOverRingMap
  rw [← rootChartEvaluation_base hH hd C, Category.assoc, IsIso.hom_inv_id_assoc,
    rootOverRestriction_base]

lemma tautologicalSection_coefficient (C : RootChart X H N d) :
    C.sectionCoefficient (globalRootMap hH hd) (tautologicalSection hH hd) =
      tautologicalCoefficient hH hd C := by
  unfold RootChart.sectionCoefficient sectionCoordinate
  rw [tautologicalSection_restrict]
  exact LinearEquiv.symm_apply_apply _ _

lemma rootOverRingMap_root
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    rootOverRingMap hH hd f g C (rootElement Γ(X, C.opens) N C.coefficient) =
      C.sectionCoefficient f
        (pullbackSectionOver (globalRootMap hH hd) f H g (tautologicalSection hH hd)) := by
  rw [pullbackSectionOver_coefficient, tautologicalSection_coefficient]
  rfl

/-- The local factor of any over-base map through the corresponding affine chart. -/
def rootOverChartMorphism
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) : (f ⁻¹ᵁ C.opens).toScheme ⟶ Spec (CommRingCat.of C.Algebra) :=
  IsOpenImmersion.lift (rootChartInclusion hH hd C) ((f ⁻¹ᵁ C.opens).ι ≫ g.val) (by
    change Set.range ((f ⁻¹ᵁ C.opens).ι ≫ g.val) ⊆
      (rootChartInclusion hH hd C).opensRange
    rw [rootChartInclusion_range]
    rintro _ ⟨y, rfl⟩
    change globalRootMap hH hd (g.val y.val) ∈ C.opens
    rw [← Scheme.Hom.comp_apply, g.property]
    exact y.property)

@[reassoc] lemma rootOverChartMorphism_fac
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    rootOverChartMorphism hH hd f g C ≫ rootChartInclusion hH hd C =
      (f ⁻¹ᵁ C.opens).ι ≫ g.val := IsOpenImmersion.lift_fac ..

lemma rootOverChartMorphism_normalized
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (C : RootChart X H N d) :
    (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).inv ≫
        (rootOverChartMorphism hH hd f g C).appTop =
      rootOverRingMap hH hd f g C ≫ (f ⁻¹ᵁ C.opens).topIso.inv := by
  rw [← cancel_epi (rootChartEvaluation hH hd C)]
  unfold rootOverRingMap
  rw [Category.assoc, ← Category.assoc (rootChartEvaluation hH hd C)
    (inv (rootChartEvaluation hH hd C)), IsIso.hom_inv_id, Category.id_comp]
  unfold rootChartEvaluation
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hi : (⊤ : (f ⁻¹ᵁ C.opens).toScheme.Opens) ≤
      (f ⁻¹ᵁ C.opens).ι ⁻¹ᵁ (f ⁻¹ᵁ C.opens) := by simp
  have hiapp : (f ⁻¹ᵁ C.opens).ι.appLE (f ⁻¹ᵁ C.opens) ⊤ hi =
      (f ⁻¹ᵁ C.opens).topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [← hiapp]
  change (rootChartInclusion hH hd C).appLE _ ⊤ _ ≫
      (rootOverChartMorphism hH hd f g C).appTop =
    g.val.appLE _ _ _ ≫ (f ⁻¹ᵁ C.opens).ι.appLE _ ⊤ _
  rw [← appLE_top_top (rootOverChartMorphism hH hd f g C) le_rfl,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom (rootOverChartMorphism_fac hH hd f g C) _ _ _ _

/-- The affine chart ring maps determine a morphism to the glued scheme. -/
lemma rootOverRingMap_injective
    (g k : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (h : ∀ C : RootChart X H N d, rootOverRingMap hH hd f g C = rootOverRingMap hH hd f k C) :
    g = k := by
  apply Subtype.ext
  apply (rootPreimageCover hH hd f).hom_ext
  intro C
  change (f ⁻¹ᵁ C.opens).ι ≫ g.val = (f ⁻¹ᵁ C.opens).ι ≫ k.val
  rw [← rootOverChartMorphism_fac hH hd f g C, ← rootOverChartMorphism_fac hH hd f k C]
  congr 1
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).inv ≫
      (rootOverChartMorphism hH hd f g C).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).inv ≫
      (rootOverChartMorphism hH hd f k C).appTop
  rw [rootOverChartMorphism_normalized, rootOverChartMorphism_normalized, h C]

lemma sectionMorphism_normalized (w : RootSections H N d f) (C : RootChart X H N d) :
    (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).inv ≫ (C.sectionMorphism f w).appTop =
      CommRingCat.ofHom (C.sectionLift f w) ≫ (f ⁻¹ᵁ C.opens).topIso.inv := by
  unfold RootChart.sectionMorphism
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc]

/-- The morphism constructed from a root has exactly the classifying chart ring maps. -/
lemma rootSectionMorphism_ringMap (w : RootSections H N d f) (C : RootChart X H N d) :
    rootOverRingMap hH hd f
      ⟨rootSectionMorphism hH hd f w, rootSectionMorphism_over hH hd f w⟩ C =
      CommRingCat.ofHom (C.sectionLift f w) := by
  let g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f} :=
    ⟨rootSectionMorphism hH hd f w, rootSectionMorphism_over hH hd f w⟩
  have hgC : rootOverChartMorphism hH hd f g C = C.sectionMorphism f w := by
    rw [← cancel_mono (rootChartInclusion hH hd C), rootOverChartMorphism_fac]
    exact rootSectionMorphism_chart hH hd f w C
  rw [← cancel_mono (f ⁻¹ᵁ C.opens).topIso.inv]
  exact (rootOverChartMorphism_normalized hH hd f g C).symm.trans
    ((congrArg (fun k : (f ⁻¹ᵁ C.opens).toScheme ⟶ Spec (CommRingCat.of C.Algebra) =>
      (Scheme.ΓSpecIso (CommRingCat.of C.Algebra)).inv ≫ k.appTop) hgC).trans
        (sectionMorphism_normalized f w C))

/-- Pulling back the tautological section along its classifying morphism recovers the root. -/
lemma rootSectionMorphism_section (w : RootSections H N d f) :
    pullbackSectionOver (globalRootMap hH hd) f H
      ⟨rootSectionMorphism hH hd f w, rootSectionMorphism_over hH hd f w⟩
      (tautologicalSection hH hd) = w.val := by
  let M := (Scheme.Modules.pullback f).obj H
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun C : RootChart X H N d => f ⁻¹ᵁ C.opens) ⊤ (fun _ => homOfLE le_top)
    (rootChart_preimages_cover hH hd f)
  intro C
  apply ((C.pulledFrame f).equiv _ le_rfl).symm.injective
  change C.sectionCoefficient f _ = C.sectionCoefficient f w.val
  rw [← rootOverRingMap_root hH hd f, rootSectionMorphism_ringMap]
  exact C.sectionLift_root f w

/-- Uniqueness follows from the coefficient-ring map and the image of the quotient root. -/
lemma rootSectionMorphism_unique (w : RootSections H N d f)
    (g : {g : S ⟶ globalRootScheme hH hd // g ≫ globalRootMap hH hd = f})
    (hg : pullbackSectionOver (globalRootMap hH hd) f H g (tautologicalSection hH hd) = w.val) :
    g = ⟨rootSectionMorphism hH hd f w, rootSectionMorphism_over hH hd f w⟩ := by
  apply rootOverRingMap_injective hH hd f
  intro C
  rw [rootSectionMorphism_ringMap]
  apply CommRingCat.hom_ext
  apply rootAlgebra_hom_ext N C.coefficient
  · intro a
    exact (ConcreteCategory.congr_hom (rootOverRingMap_coeff hH hd f g C) a).trans
      (C.sectionLift_coeff f w a).symm
  · change rootOverRingMap hH hd f g C (rootElement Γ(X, C.opens) N C.coefficient) = _
    rw [rootOverRingMap_root, hg]
    exact (C.sectionLift_root f w).symm

end Universal


/-- The representable root functor with its finite etale cover and genuine tautological section. -/
theorem global_root_torsor :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (H : X.Modules),
    ArithmeticThetaNormalizedSections.IsLineBundle X H → ∀ (N : ℕ),
    0 < N → IsUnit (N : X.presheaf.obj (Opposite.op ⊤)) →
    ∀ d : (ArithmeticThetaTensorPower.tensorPower X H N).presheaf.obj (Opposite.op ⊤),
    ArithmeticThetaRootTorsor.IsGeneratingSection X
      (ArithmeticThetaTensorPower.tensorPower X H N) d →
    ∃ (T : AlgebraicGeometry.Scheme.{u}) (p : Quiver.Hom T X)
      (v : ((AlgebraicGeometry.Scheme.Modules.pullback p).obj H).presheaf.obj (Opposite.op ⊤)),
      AlgebraicGeometry.IsFinite p ∧ AlgebraicGeometry.Etale p ∧
      AlgebraicGeometry.Surjective p ∧
      (∀ x : X, AlgebraicGeometry.Scheme.Hom.finrank p x = N) ∧
      ArithmeticThetaRootTorsor.IsGeneratingSection T
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj H) v ∧
      ArithmeticThetaTensorPower.tensorPowerSection T
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj H) N ⊤ v =
        ArithmeticThetaNormalizedSections.pullbackPowerSection p H N d ∧
      ∀ (S : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom S X)
        (w : ArithmeticThetaRootTorsor.RootSections H N d f),
        ∃! g : {g : Quiver.Hom S T // CategoryTheory.CategoryStruct.comp g p = f},
          ArithmeticThetaRootTorsor.pullbackSectionOver p f H g v = w.val := by
  intro X H hH N hN hNu d hd
  obtain ⟨hfin, het⟩ := globalRootMap_finite_etale hH hd hN hNu
  refine ⟨globalRootScheme hH hd, globalRootMap hH hd, tautologicalSection hH hd,
    hfin, het, globalRootMap_surjective hH hd hN hNu,
    globalRootMap_finrank hH hd hN hNu, tautologicalSection_generating hH hd hN,
    tautologicalSection_pow hH hd, ?_⟩
  intro S f w
  exact ⟨⟨rootSectionMorphism hH hd f w, rootSectionMorphism_over hH hd f w⟩,
    rootSectionMorphism_section hH hd f w,
    fun g hg => rootSectionMorphism_unique hH hd f w g hg⟩

end ArithmeticThetaGlobalization
