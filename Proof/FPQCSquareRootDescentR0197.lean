module

public import FPQCRootMorphismsR0197
public import AffineSquareRootEffectivityR0197
public import OpenSquareRootEffectivityR0197
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe v
namespace ArithmeticThetaRootDescentR0197
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
namespace FPQCSquareRootDescentR0197

/-- Invertible modules as an actual full sub-pseudofunctor of modules. -/
def invertibleProperty : moduleFunctor.ObjectProperty where
  prop _X := Scheme.Modules.IsInvertible

instance : invertibleProperty.IsClosedUnderMapObj where
  map_obj hM f := hM.pullback f.as.unop

abbrev lineFunctor := invertibleProperty.fullsubcategory

section FullSubcategory
universe u₀ v₀ u₁ v₁
variable {C : Type u₀} [Category.{v₀} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
  (P : F.ObjectProperty) [P.IsClosedUnderMapObj]

def forgetData {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) : P.fullsubcategory.DescentData f ⥤ F.DescentData f where
  obj D :=
    { obj := fun i => (D.obj i).obj
      hom := fun {_} p {_ _} a b ha hb => (D.hom p a b ha hb).hom
      pullHom_hom := fun {_ _} g p p' hp {_ _} a b ha hb ga gb hga hgb =>
        congrArg (fun z => z.hom) (D.pullHom_hom g p p' hp a b ha hb ga gb hga hgb)
      hom_self := fun {_} p {_} a ha => congrArg (fun z => z.hom) (D.hom_self p a ha)
      hom_comp := fun {_} p {_ _ _} a b c ha hb hc => congrArg (fun z => z.hom) (D.hom_comp p a b c ha hb hc) }
  map φ :=
    { hom := fun i => (φ.hom i).hom
      comm := fun {_} p {_ _} a b ha hb => congrArg (fun z => z.hom) (φ.comm p a b ha hb) }

def liftData {B : C} {ι : Type v} {V : ι → C}
    {f : ∀ i, V i ⟶ B} (D : F.DescentData f)
    (hD : ∀ i, P.prop (.mk (Opposite.op (V i))) (D.obj i)) : P.fullsubcategory.DescentData f where
  obj i := ⟨D.obj i, hD i⟩
  hom _ p _ _ a b ha hb := ObjectProperty.homMk (D.hom p a b ha hb)
  pullHom_hom _ _ g p p' hp _ _ a b ha hb ga gb hga hgb := by
    apply ObjectProperty.hom_ext
    exact D.pullHom_hom g p p' hp a b ha hb ga gb hga hgb
  hom_self _ p _ a ha := by
    apply ObjectProperty.hom_ext
    exact D.hom_self p a ha
  hom_comp _ p _ _ _ a b c ha hb hc := by
    apply ObjectProperty.hom_ext
    exact D.hom_comp p a b c ha hb hc

def liftHom {B : C} {ι : Type v} {V : ι → C}
    {f : ∀ i, V i ⟶ B} {D E : P.fullsubcategory.DescentData f}
    (φ : (forgetData P f).obj D ⟶ (forgetData P f).obj E) : D ⟶ E where
  hom i := ObjectProperty.homMk (φ.hom i)
  comm _ p _ _ a b ha hb := by
    apply ObjectProperty.hom_ext
    exact φ.comm p a b ha hb

def forgetFullyFaithful {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) : (forgetData P f).FullyFaithful where
  preimage := liftHom P
  map_preimage := by intros; rfl
  preimage_map := by intros; rfl

lemma forget_toDescent_obj {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) (M : P.fullsubcategory.obj (.mk (Opposite.op B))) :
    (forgetData P f).obj ((P.fullsubcategory.toDescentData f).obj M) =
      (F.toDescentData f).obj M.obj := rfl

lemma subcategory_morphisms_bijective {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) (M N : P.fullsubcategory.obj (.mk (Opposite.op B)))
    (h : Function.Bijective ((F.toDescentData f).map : (M.obj ⟶ N.obj) → _)) :
    Function.Bijective ((P.fullsubcategory.toDescentData f).map : (M ⟶ N) → _) := by
  constructor
  · intro a b hab
    apply ObjectProperty.hom_ext
    apply h.1
    exact congrArg ((forgetData P f).map) hab
  · intro t
    obtain ⟨a, ha⟩ := h.2 ((forgetData P f).map t)
    refine ⟨ObjectProperty.homMk a, ?_⟩
    apply (forgetFullyFaithful P f).map_injective
    exact ha

lemma lift_effective {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) (D : P.fullsubcategory.DescentData f)
    (M : F.obj (.mk (Opposite.op B))) (hM : P.prop _ M)
    (e : (F.toDescentData f).obj M ≅ (forgetData P f).obj D) :
    Nonempty ((P.fullsubcategory.toDescentData f).obj ⟨M, hM⟩ ≅ D) :=
  ⟨(forgetFullyFaithful P f).preimageIso e⟩

lemma forget_effective {B : C} {ι : Type v} {V : ι → C}
    (f : ∀ i, V i ⟶ B) (D : F.DescentData f) (hD : ∀ i, P.prop _ (D.obj i))
    (M : P.fullsubcategory.obj (.mk (Opposite.op B)))
    (e : (P.fullsubcategory.toDescentData f).obj M ≅ liftData P D hD) :
    Nonempty ((F.toDescentData f).obj M.obj ≅ D) :=
  ⟨(forgetData P f).mapIso e⟩

end FullSubcategory

section Refinement
universe u₀ v₀ u₁ v₁
variable {C : Type u₀} [Category.{v₀} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
  {J : GrothendieckTopology C} [F.IsPrestack J]

lemma effective_of_refinement {B Y A : C} (q : Y ⟶ B) (r : A ⟶ Y)
    (hr : Sieve.ofArrows (fun _ : Unit => A) (fun _ => r ≫ q) ∈ J B)
    (D : F.DescentData (fun _ : Unit => q))
    (M : F.obj (.mk (Opposite.op B)))
    (e : (F.toDescentData (fun _ : Unit => r ≫ q)).obj M ≅
      (Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit => q)
        (p := 𝟙 B) (f' := fun _ : Unit => r ≫ q) (α := fun _ => ())
        (p' := fun _ => r) (fun _ => by simp)).obj D) :
    Nonempty ((F.toDescentData (fun _ : Unit => q)).obj M ≅ D) := by
  let H := Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit => q)
    (p := 𝟙 B) (f' := fun _ : Unit => r ≫ q) (α := fun _ => ())
    (p' := fun _ => r) (fun _ => by simp)
  let ff : H.FullyFaithful := Pseudofunctor.DescentData.fullyFaithfulPullFunctor F
    (fun _ : Unit => (rfl : r ≫ q = r ≫ q)) hr
  let c : F.toDescentData (fun _ : Unit => q) ⋙ H ≅
      F.toDescentData (fun _ : Unit => r ≫ q) :=
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F _ ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _
  exact ⟨ff.preimageIso (c.app M ≪≫ e)⟩

end Refinement

lemma line_morphisms_bijective {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (M N : lineFunctor.obj (.mk (Opposite.op B))) :
    Function.Bijective ((lineFunctor.toDescentData (fun _ : Unit => q)).map :
      (M ⟶ N) → _) :=
  subcategory_morphisms_bijective invertibleProperty (fun _ : Unit => q) M N
    (FPQCRootMorphismsR0197.morphisms_bijective q M.obj N.obj M.property N.property)

/-- An auxiliary singleton-cover topology; no stack effectivity is assumed. -/
def qcTopology : GrothendieckTopology Scheme.{0} where
  sieves B := {R | ∃ (Y : Scheme.{0}) (q : Y ⟶ B),
    QuasiCompact q ∧ Flat q ∧ Surjective q ∧ R q}
  top_mem' B := ⟨B, 𝟙 B, inferInstance, inferInstance, inferInstance, trivial⟩
  pullback_stable' := by
    rintro B Z R z ⟨Y, q, hq, hf, hs, hR⟩
    letI := hq
    letI := hf
    letI := hs
    refine ⟨pullback q z, pullback.snd q z, inferInstance, inferInstance, inferInstance, ?_⟩
    change R (pullback.snd q z ≫ z)
    rw [← pullback.condition]
    exact R.downward_closed hR _
  transitive' := by
    rintro B S ⟨Y, q, hq, hf, hs, hS⟩ R hR
    obtain ⟨Z, r, hr, hrf, hrs, h⟩ := hR hS
    letI := hq
    letI := hf
    letI := hs
    letI := hr
    letI := hrf
    letI := hrs
    exact ⟨Z, r ≫ q, inferInstance, inferInstance, inferInstance, h⟩

lemma line_isPrestackFor_singleton {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q] :
    lineFunctor.IsPrestackFor (Presieve.ofArrows (fun _ : Unit => Y) (fun _ => q)) := by
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective]
  exact line_morphisms_bijective q

instance line_prestack : lineFunctor.IsPrestack qcTopology := by
  apply Pseudofunctor.IsPrestack.of_isPrestackFor
  rintro B R ⟨Y, q, hq, hf, hs, hR⟩
  letI := hq
  letI := hf
  letI := hs
  rw [Pseudofunctor.isPrestackFor_iff_isSheafFor]
  intro M N
  let S := Sieve.ofArrows (fun _ : Unit => Y) (fun _ => q)
  apply Presieve.isSheafFor_subsieve (lineFunctor.presheafHom M N)
    (S := (Sieve.overEquiv (Over.mk (𝟙 B))).symm S)
  · apply (Sieve.overEquiv (Over.mk (𝟙 B))).symm.monotone
    dsimp [S]
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact hR
  · intro Z z
    rw [← Sieve.overEquiv_symm_pullback]
    have he : Sieve.ofArrows (fun _ : Unit => pullback q z.left)
        (fun _ => pullback.snd q z.left) = S.pullback z.left :=
      Sieve.ofArrows_eq_pullback_of_isPullback (fun _ : Unit => q)
        (fun _ => (IsPullback.of_hasPullback q z.left).flip)
    rw [← he]
    exact (Pseudofunctor.isPrestackFor_iff_isSheafFor' _ _).1
      ((Pseudofunctor.IsPrestackFor_generate_iff _ _).2
        (line_isPrestackFor_singleton (pullback.snd q z.left))) M N Z.hom


/-- A finite affine refinement of an fpqc map with affine target. -/
lemma exists_affine_refinement {B Y : Scheme.{0}} [IsAffine B] (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q] :
    ∃ (A : Scheme.{0}) (r : A ⟶ Y), IsAffine A ∧ Flat (r ≫ q) ∧ Surjective (r ≫ q) := by
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  let U : Y.OpenCover := Y.affineCover.finiteSubcover
  haveI : Finite U.I₀ := by dsimp [U]; infer_instance
  haveI : ∀ i, IsAffine (U.X i) := by intro i; dsimp [U]; infer_instance
  let r : (∐ U.X) ⟶ Y := Sigma.desc U.f
  haveI : Flat r := IsZariskiLocalAtSource.sigmaDesc (fun i => inferInstance)
  haveI : Surjective r := by dsimp [r]; infer_instance
  exact ⟨∐ U.X, r, inferInstance, inferInstance, inferInstance⟩

/-- Invertible-module effectivity on an affine base, without assuming that the
original covering morphism is affine. -/
lemma module_effective_affine_base {B Y : Scheme.{0}} [IsAffine B] (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (D : moduleFunctor.DescentData (fun _ : Unit => q))
    (hD : ∀ i, Scheme.Modules.IsInvertible (D.obj i)) :
    ∃ L : B.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((descent (fun _ : Unit => q)).obj L ≅ D) := by
  obtain ⟨A, r, hA, hrF, hrS⟩ := exists_affine_refinement q
  letI := hA
  letI := hrF
  letI := hrS
  let DL := liftData invertibleProperty D hD
  let H := Pseudofunctor.DescentData.pullFunctor lineFunctor (f := fun _ : Unit => q)
    (p := 𝟙 B) (f' := fun _ : Unit => r ≫ q) (α := fun _ => ())
    (p' := fun _ => r) (fun _ => by simp)
  let E := H.obj DL
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
      (r ≫ q) ((forgetData invertibleProperty (fun _ : Unit => r ≫ q)).obj E)
      (fun i => (E.obj i).property)
  obtain ⟨eL⟩ := lift_effective invertibleProperty (fun _ : Unit => r ≫ q) E L hL e
  have hcover : Sieve.ofArrows (fun _ : Unit => A) (fun _ => r ≫ q) ∈ qcTopology B :=
    ⟨A, r ≫ q, inferInstance, inferInstance, inferInstance, Sieve.ofArrows_mk _ _ ()⟩
  obtain ⟨eD⟩ := effective_of_refinement lineFunctor q r hcover DL ⟨L, hL⟩ eL
  exact ⟨L, hL, forget_effective invertibleProperty (fun _ : Unit => q) D hD ⟨L, hL⟩ eD⟩

open P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective.AlgebraicGeometry.Scheme.Modules.InvDescAssembly

/-- Full invertible-module effectivity for every quasicompact flat surjection.
The accepted local-effectivity assembly theorem retains the original all-test datum. -/
lemma module_effective {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (D : moduleFunctor.DescentData (fun _ : Unit => q))
    (hD : ∀ i, Scheme.Modules.IsInvertible (D.obj i)) :
    ∃ L : B.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((descent (fun _ : Unit => q)).obj L ≅ D) := by
  obtain ⟨L, hL, e⟩ :=
    Pseudofunctor.DescentData.exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
      (C := Scheme.{0}) moduleFunctor
      (fun _ M => Scheme.Modules.IsInvertible M)
      (fun _ _ g M hM => hM.pullback g)
      (fun _ _ _ ⟨i⟩ hM => isInvertible_of_iso i hM)
      q (U := fun U : B.affineOpens => ((U : B.Opens) : Scheme.{0})) (fun U => (U : B.Opens).ι)
      (Scheme.Modules.isStackFor_openCover B (affineOpensCover B))
      (fun Z z => (Scheme.Modules.isStackFor_openCover Z
        ((affineOpensCover B).pullback₁ z)).isPrestackFor)
      (fun Z z M N hM hN => FPQCRootMorphismsR0197.morphisms_bijective
        (pullback.snd q z) M N hM hN)
      D
      (fun U => by
        letI : IsAffine ((U : B.Opens) : Scheme.{0}) := U.2
        exact module_effective_affine_base (pullback.snd q (U : B.Opens).ι) _
          (fun i => (hD i).pullback _))
  exact ⟨L, isInvertible_of_forall_affineOpens L hL, e⟩

/-- The specified square descends on the same effective invertible module and
with the same full descent isomorphism. -/
lemma square_effective {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (W : B.Modules) (hW : Scheme.Modules.IsInvertible W)
    (D : RootDatum W (fun _ : Unit => q)) (hD : CompatibleSquares D) : Effective D := by
  obtain ⟨L, hL, ⟨e⟩⟩ := module_effective q D.data D.invertible
  have hP := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorPower_invertible L hL 2
  let E := OpenSquareRootEffectivityR0197.squareDescentIso D e hL hD
  have ff := FPQCRootMorphismsR0197.morphisms_bijective q
  obtain ⟨s, hs⟩ := (ff (tensorPower B L 2) W hP hW).2 E.hom
  obtain ⟨t, ht⟩ := (ff W (tensorPower B L 2) hW hP).2 E.inv
  have hst : s ≫ t = 𝟙 _ := by
    apply (ff (tensorPower B L 2) (tensorPower B L 2) hP hP).1
    rw [Functor.map_comp, hs, ht, E.hom_inv_id]
    exact ((descent (fun _ : Unit => q)).map_id _).symm
  have hts : t ≫ s = 𝟙 _ := by
    apply (ff W W hW hW).1
    rw [Functor.map_comp, ht, hs, E.inv_hom_id]
    exact ((descent (fun _ : Unit => q)).map_id _).symm
  let J : SquareLine B W := ⟨L, hL, ⟨s, t, hst, hts⟩⟩
  refine ⟨J, e, ?_⟩
  intro i
  have hi := congrArg (fun z => z.hom i) hs
  change (Scheme.Modules.pullback q).map s =
    (pullback_tensorPower_iso Y B q L 2).hom ≫ tensorPowerMap (e.hom.hom i) 2 ≫
      (D.square i).hom at hi
  change tensorPowerMap (e.hom.hom i) 2 ≫ (D.square i).hom =
    (pullback_tensorPower_iso Y B q L 2).inv ≫ (Scheme.Modules.pullback q).map s
  rw [hi]
  simp [Category.assoc]

end FPQCSquareRootDescentR0197
/-- Effective fpqc descent for the actual specified square-root moduli problem. -/
theorem fpqc_square_root_descent
    (B Y : Scheme.{0}) (q : Y ⟶ B)
    (hq : QuasiCompact q) (hf : Flat q) (hs : Surjective q)
    (W : B.Modules) (hW : Scheme.Modules.IsInvertible W) :
    RootDescent W (fun _ : Unit => q) := by
  letI := hq
  letI := hf
  letI := hs
  exact ⟨FPQCSquareRootDescentR0197.square_effective q W hW,
    (fpqc_root_morphisms B Y q hq hf hs W hW).2⟩

#print axioms fpqc_square_root_descent
end ArithmeticThetaRootDescentR0197
