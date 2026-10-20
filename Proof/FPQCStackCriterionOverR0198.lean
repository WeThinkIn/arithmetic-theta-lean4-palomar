module

public import RootStackDefinitionsR0198

@[expose] public section

/-! Categorical descent on the standard fpqc slice site. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaRootStackR0198
namespace FPQCStackCriterionOver
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

variable {B : Scheme.{0}}
  (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0, 1})

/-- The singleton hypothesis retains categorical effectivity, including arrows. -/
lemma singleton_isStackFor (hF : SingletonDescent F)
    {T V : Over B} (q : V ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    F.IsStackFor (Presieve.singleton q) := by
  rw [← Presieve.ofArrows_of_unique (fun _ : Unit => q), F.isStackFor_ofArrows_iff]
  exact hF T V q hq hf hs

/-- Open descent is precisely the standard categorical stack condition on the
Zariski topology of the slice, without a finiteness restriction on covers. -/
lemma zariski_isStack (hF : OpenDescent F) :
    F.IsStack (Scheme.zariskiTopology.over B) := by
  rw [Scheme.zariskiTopology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply Pseudofunctor.IsStack.of_precoverage
  intro T R hR
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Scheme.ofArrows_mem_precoverage_iff] at hR
  rw [F.isStackFor_ofArrows_iff]
  exact hF T ι V f hR.2 hR.1

omit F in
/-- Transitivity can be checked on the arrows of a generating family. -/
lemma covering_of_pullback_family {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {T : C} {ι : Type*} {V : ι → C}
    (f : ∀ i, V i ⟶ T) (R : Sieve T)
    (hf : Sieve.ofArrows V f ∈ J T)
    (hR : ∀ i, R.pullback (f i) ∈ J (V i)) : R ∈ J T := by
  apply J.transitive hf R
  rintro Y g ⟨Z, a, _, ⟨i⟩, rfl⟩
  simpa only [Sieve.pullback_comp] using J.pullback_stable a (hR i)

omit F in
/-- Lift an open covering of the underlying scheme to a covering on the slice. -/
lemma open_cover_mem (J : GrothendieckTopology (Over B))
    (hZ : Scheme.zariskiTopology.over B ≤ J) (T : Over B)
    (U : T.left.OpenCover) :
    Sieve.ofArrows (fun i => Over.mk (U.f i ≫ T.hom))
      (fun i => Over.homMk (U.f i) : ∀ i, Over.mk (U.f i ≫ T.hom) ⟶ T) ∈ J T := by
  apply hZ
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact U.mem_grothendieckTopology

omit F in
lemma overEquiv_mem_iff {T V : Over B} (R : Sieve T) (f : V ⟶ T) :
    Sieve.overEquiv T R f.left ↔ R f := by
  simpa only [OrderIso.symm_apply_apply] using
    (Sieve.overEquiv_symm_iff (Sieve.overEquiv T R) (f := f)).symm

omit F in
/-- A finite affine flat cover is generated topologically by a faithfully flat
quasicompact singleton followed by the open cover of its disjoint union. -/
lemma finite_affine_cover_mem (J : GrothendieckTopology (Over B))
    (hZ : Scheme.zariskiTopology.over B ≤ J)
    (hQ : ∀ {T V : Over B} (q : V ⟶ T),
      QuasiCompact q.left → Flat q.left → Surjective q.left →
      Sieve.generate (Presieve.singleton q) ∈ J T)
    (T : Over B) [IsAffine T.left] (U : Scheme.AffineCover (@Flat) T.left)
    [Finite U.I₀] (R : Sieve T)
    (hR : ∀ i, R (Over.homMk (U.f i) : Over.mk (U.f i ≫ T.hom) ⟶ T)) :
    R ∈ J T := by
  let : Finite U.cover.I₀ := ‹Finite U.I₀›
  let q : Over.mk (Sigma.desc U.f ≫ T.hom) ⟶ T := Over.homMk (Sigma.desc U.f)
  have hqf : Flat q.left := IsZariskiLocalAtSource.sigmaDesc U.cover.map_prop
  have hqs : Surjective q.left := by
    change Surjective (Sigma.desc U.f)
    exact ⟨fun x => by
      obtain ⟨i, y, rfl⟩ := U.cover.exists_eq x
      refine ⟨Sigma.ι U.cover.X i y, ?_⟩
      change (Sigma.ι U.cover.X i ≫ Sigma.desc U.cover.f) y = _
      simp⟩
  have hqc : QuasiCompact q.left := by
    change QuasiCompact (Sigma.desc U.f)
    infer_instance
  have hq := hQ q hqc hqf hqs
  apply covering_of_pullback_family J (fun _ : Unit => q) R
    (by simpa only [Sieve.ofArrows, Presieve.ofArrows_of_unique] using hq)
  intro i
  apply J.superset_covering _ (open_cover_mem J hZ _ (sigmaOpenCover U.cover.X))
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  change R _
  rw [← overEquiv_mem_iff]
  have h := (Sieve.overEquiv_iff R (U.f j)).2 (hR j)
  change Sieve.overEquiv T R (Sigma.ι U.cover.X j ≫ Sigma.desc U.cover.f)
  simpa using h

omit F in
/-- Any fpqc covering family of an affine scheme admits the finite affine
refinement required by the preceding lemma. -/
lemma affine_fpqc_cover_mem (J : GrothendieckTopology (Over B))
    (hZ : Scheme.zariskiTopology.over B ≤ J)
    (hQ : ∀ {T V : Over B} (q : V ⟶ T),
      QuasiCompact q.left → Flat q.left → Surjective q.left →
      Sieve.generate (Presieve.singleton q) ∈ J T)
    (T : Over B) [IsAffine T.left] (U : Scheme.Cover Scheme.fpqcPrecoverage T.left)
    (R : Sieve T)
    (hR : ∀ i, R (Over.homMk (U.f i) : Over.mk (U.f i ≫ T.hom) ⟶ T)) :
    R ∈ J T := by
  obtain ⟨V, e, hfin, _⟩ := QuasiCompactCover.exists_hom U.forgetQc
  let := hfin
  apply finite_affine_cover_mem J hZ hQ T V R
  intro i
  rw [← overEquiv_mem_iff]
  have h := (Sieve.overEquiv T R).downward_closed
    ((Sieve.overEquiv_iff R (U.f (e.s₀ i))).2 (hR (e.s₀ i))) (e.h₀ i)
  change Sieve.overEquiv T R (V.cover.f i)
  simpa only [e.w₀ i] using h

omit F in
/-- The affine reduction uses the actual pullbacks of an arbitrary fpqc family. -/
lemma fpqc_cover_mem (J : GrothendieckTopology (Over B))
    (hZ : Scheme.zariskiTopology.over B ≤ J)
    (hQ : ∀ {T V : Over B} (q : V ⟶ T),
      QuasiCompact q.left → Flat q.left → Surjective q.left →
      Sieve.generate (Presieve.singleton q) ∈ J T)
    (T : Over B) (U : Scheme.Cover Scheme.fpqcPrecoverage T.left)
    (R : Sieve T)
    (hR : ∀ i, R (Over.homMk (U.f i) : Over.mk (U.f i ≫ T.hom) ⟶ T)) :
    R ∈ J T := by
  apply covering_of_pullback_family J
    (fun j => (Over.homMk (T.left.affineCover.f j) :
      Over.mk (T.left.affineCover.f j ≫ T.hom) ⟶ T)) R
    (open_cover_mem J hZ T T.left.affineCover)
  intro j
  have : IsAffine (Over.mk (T.left.affineCover.f j ≫ T.hom)).left := by
    change IsAffine (T.left.affineCover.X j)
    infer_instance
  apply affine_fpqc_cover_mem J hZ hQ _ (U.pullback₂ (T.left.affineCover.f j))
  intro i
  change R _
  rw [← overEquiv_mem_iff]
  change Sieve.overEquiv T R
    (pullback.snd (U.f i) (T.left.affineCover.f j) ≫ T.left.affineCover.f j)
  rw [← pullback.condition]
  exact (Sieve.overEquiv T R).downward_closed
    ((Sieve.overEquiv_iff R (U.f i)).2 (hR i)) _

omit F in
/-- Open covers and quasicompact faithfully flat singletons generate the
standard big fpqc topology on the slice. This is a topology comparison only;
categorical effectivity must also be propagated through these refinements. -/
lemma fpqc_le_of_open_singleton (J : GrothendieckTopology (Over B))
    (hZ : Scheme.zariskiTopology.over B ≤ J)
    (hQ : ∀ {T V : Over B} (q : V ⟶ T),
      QuasiCompact q.left → Flat q.left → Surjective q.left →
      Sieve.generate (Presieve.singleton q) ∈ J T) :
    Scheme.fpqcTopology.over B ≤ J := by
  rw [Scheme.fpqcTopology, over_toGrothendieck_eq_toGrothendieck_comap_forget,
    Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro T R hR
  rw [Precoverage.mem_comap_iff] at hR
  obtain ⟨U, hU⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  apply fpqc_cover_mem J hZ hQ T U
  intro i
  rw [← overEquiv_mem_iff]
  have hi : R.map (Over.forget B) (U.f i) := by
    rw [hU]
    exact Presieve.ofArrows.mk i
  rw [Sieve.overEquiv_generate]
  exact Sieve.le_generate _ _ _ ((R.map_le_functorPushforward (Over.forget B)) _ _ hi)

/-- Universal descent of morphisms defines a Grothendieck topology. -/
def prestackTopology : GrothendieckTopology (Over B) where
  sieves T := {R | ∀ (V : Over B) (f : V ⟶ T), F.IsPrestackFor (R.pullback f).arrows}
  top_mem' T V f := by
    rw [Sieve.pullback_top, F.isPrestackFor_iff_isSheafFor]
    intro M N
    simpa using Presieve.isSheafFor_top (F.presheafHom M N)
  pullback_stable' T V R f hR W g := by
    simpa only [← Sieve.pullback_comp] using hR W (g ≫ f)
  transitive' T R hR S hS V f := by
    rw [F.isPrestackFor_iff_isSheafFor]
    intro M N
    apply Presieve.isSheafFor_trans (F.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 V))).symm (R.pullback f))
    · exact (F.isPrestackFor_iff_isSheafFor _).mp (hR V f) M N
    · intro W g hg
      rw [← Sieve.overEquiv_symm_pullback, ← Sieve.pullback_comp]
      exact ((F.isPrestackFor_iff_isSheafFor' _).mp
        (hR W.left (g.left ≫ f)) M N W.hom).isSeparatedFor
    · intro W g hg
      rw [← Sieve.overEquiv_symm_pullback, ← Sieve.pullback_comp]
      have h := hS hg W.left (𝟙 W.left)
      change F.IsPrestackFor ((S.pullback (g.left ≫ f)).pullback (𝟙 W.left)).arrows at h
      rw [Sieve.pullback_id] at h
      exact (F.isPrestackFor_iff_isSheafFor' _).mp h M N W.hom

instance isPrestack_prestackTopology : F.IsPrestack (prestackTopology F) := by
  apply Pseudofunctor.IsPrestack.of_isPrestackFor
  intro T R hR
  simpa only [Sieve.pullback_id] using hR T (𝟙 T)

/-- Every topology for which the pseudofunctor is a prestack is contained in
its universal morphism-descent topology. -/
lemma le_prestackTopology (J : GrothendieckTopology (Over B)) [F.IsPrestack J] :
    J ≤ prestackTopology F := by
  intro T R hR V f
  exact F.isPrestackFor' _ (J.pullback_stable f hR)

lemma singleton_mem_prestackTopology (hF : SingletonDescent F)
    {T V : Over B} (q : V ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    Sieve.generate (Presieve.singleton q) ∈ prestackTopology F T := by
  intro W f
  rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
    F.IsPrestackFor_generate_iff]
  have H := (Over.forget B).map_isPullback (IsPullback.of_hasPullback q f)
  apply (singleton_isStackFor F hF (pullback.snd q f) ?_ ?_ ?_).isPrestackFor
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) H hq
  · exact MorphismProperty.of_isPullback (P := @Flat) H hf
  · exact MorphismProperty.of_isPullback (P := @Surjective) H hs

/-- The two categorical descent hypotheses imply descent of all morphisms for
the standard fpqc topology. Effectivity is not assumed in this conclusion. -/
lemma fpqc_isPrestack (hO : OpenDescent F) (hQ : SingletonDescent F) :
    F.IsPrestack (rootTopology B) := by
  let := zariski_isStack F hO
  have hle := fpqc_le_of_open_singleton (prestackTopology F)
    (le_prestackTopology F (Scheme.zariskiTopology.over B))
    (fun q hq hf hs => singleton_mem_prestackTopology F hQ q hq hf hs)
  apply Pseudofunctor.IsPrestack.of_isPrestackFor
  intro T R hR
  exact F.isPrestackFor' R (hle _ hR)

namespace SieveDescent
open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

/-- The family of all arrows in a sieve, as used by Mathlib's stack predicate. -/
abbrev family {T : Over B} (R : Sieve T) :=
  fun r : R.arrows.category => r.obj.hom

variable {T V : Over B} (R : Sieve T) (q : V ⟶ T)
  {ι : Type 1} {X : ι → Over B} (f : ∀ i, X i ⟶ V)
  (hf : ∀ i, R (f i ≫ q))

abbrev index (i : ι) : R.arrows.category := ⟨Over.mk (f i ≫ q), hf i⟩

/-- Restrict sieve descent data along a scheme map and a family over its source.
The objects are the actual components of the original descent datum. -/
def restrictObj (D : F.DescentData (family R)) : F.DescentData f where
  obj i := D.obj (index R q f hf i)
  hom Y p i j a b ha hb := D.hom (p ≫ q)
    (i₁ := index R q f hf i) (i₂ := index R q f hf j) a b
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) ha)
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) hb)
  pullHom_hom Y' Y g p p' hp i j a b ha hb a' b' ha' hb' := by
    apply D.pullHom_hom g (p ≫ q) (p' ≫ q)
      (i₁ := index R q f hf i) (i₂ := index R q f hf j)
    · simpa only [Category.assoc] using congrArg (fun k => k ≫ q) hp
    · simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) ha
    · simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) hb
    · exact ha'
    · exact hb'
  hom_self Y p i a ha := D.hom_self _ (i := index R q f hf i) _
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) ha)
  hom_comp Y p i j k a b c ha hb hc := D.hom_comp _
    (i₁ := index R q f hf i) (i₂ := index R q f hf j)
    (i₃ := index R q f hf k) a b c
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) ha)
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) hb)
    (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) hc)

/-- Functorial restriction preserves all morphisms of descent data. -/
def restrict : F.DescentData (family R) ⥤ F.DescentData f where
  obj := restrictObj F R q f hf
  map φ :=
    { hom i := φ.hom (index R q f hf i)
      comm Y p i j a b ha hb := φ.comm (p ≫ q)
        (i₁ := index R q f hf i) (i₂ := index R q f hf j) a b
        (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) ha)
        (by simpa only [family, index, Over.mk_hom, Category.assoc] using congrArg (fun k => k ≫ q) hb) }

/-- The direct restriction agrees with Mathlib's canonical pullback of descent
data, through the identity comparison of the same pseudofunctor. -/
def pullRestrictIso :
    DescentData.pullFunctor F (p := q)
      (f := family R) (f' := f)
      (α := fun i => ⟨Over.mk (f i ≫ q), hf i⟩)
      (p' := fun i => 𝟙 (X i)) (by intro i; simp [family]) ≅
    restrict F R q f hf :=
  NatIso.ofComponents (fun D => DescentData.isoMk
    (fun i => (Cat.Hom.toNatIso (F.mapId _)).app _)
    (by
      intro Y p i j a b ha hb
      dsimp [restrict, restrictObj]
      rw [DescentData.pullFunctorObjHom_eq_assoc _ _ (a ≫ f i) a b (p ≫ q) a b
        rfl (hb.trans ha.symm) (by rw [ha]) (by simp) (by simp)]
      simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))
    (by intro D D' φ; ext i; exact (Cat.Hom.toNatIso (F.mapId _)).hom.naturality _)

/-- Restriction of a globally induced descent datum is induced by the actual
pseudofunctor pullback along `q`, with its canonical composition comparison. -/
def toDescentRestrictIso :
    F.toDescentData (family R) ⋙ restrict F R q f hf ≅
      (F.map q.op.toLoc).toFunctor ⋙ F.toDescentData f :=
  Functor.isoWhiskerLeft _ (pullRestrictIso F R q f hf).symm ≪≫
    DescentData.toDescentDataCompPullFunctorIso F
      (p := q) (f := family R) (f' := f)
      (α := fun i => index R q f hf i) (p' := fun i => 𝟙 (X i))
      (by intro i; simp [family, index])

/-- Restricting along an arrow already in the sieve is effective, with the
corresponding component as its explicitly specified effective object. -/
def restrictMemberIso (hq : R q) (D : F.DescentData (family R)) :
    (F.toDescentData f).obj (D.obj ⟨Over.mk q, hq⟩) ≅ (restrict F R q f hf).obj D := by
  let w : ∀ i, f i ≫ family R ⟨Over.mk q, hq⟩ = f i ≫ q := fun _ => rfl
  let w' : ∀ i, (𝟙 (X i)) ≫ family R (index R q f hf i) = f i ≫ q := by
    intro i; simp [family, index]
  refine ?_ ≪≫ (DescentData.pullFunctorIso F w w').app D ≪≫
    (pullRestrictIso F R q f hf).app D
  refine DescentData.isoMk (fun i => Iso.refl _) ?_
  intro Y p i j a b ha hb
  dsimp
  rw [DescentData.pullFunctorObjHom_eq _ _ (a ≫ f i) a b (p ≫ q) p p
    rfl (hb.trans ha.symm) (by rw [ha]) ha hb]
  rw [D.hom_self (p ≫ q) (i := ⟨Over.mk q, hq⟩) p rfl]
  simp

/-- Composition of direct sieve restrictions. The comparison transports the
actual composite arrow, rather than replacing the pullback map. -/
def restrictCompIso {W : Over B} (a : W ⟶ V) (s : W ⟶ T) (ha : a ≫ q = s)
    {κ : Type 1} {Z : κ → Over B} (g : ∀ i, Z i ⟶ W)
    (hg : ∀ i, R (g i ≫ s)) :
    restrict F R q (family (R.pullback q)) (fun r => r.property) ⋙
      restrict F (R.pullback q) a g (fun i => by
        change R ((g i ≫ a) ≫ q)
        simpa only [Category.assoc, ha] using hg i) ≅
    restrict F R s g hg := by
  subst s
  apply eqToIso
  unfold restrict Functor.comp
  congr 1

/-- Direct restriction along the identity recovers the original descent datum. -/
def restrictIdIso :
    restrict F R (𝟙 T) (family R) (fun r => by simpa using r.property) ≅
      𝟭 (F.DescentData (family R)) :=
  (pullRestrictIso F R (𝟙 T) (family R) (fun r => by simpa using r.property)).symm ≪≫
    DescentData.pullFunctorIso F _ (p := 𝟙 T) (α := id) (p'' := fun _ => 𝟙 _)
      (by intro r; simp) ≪≫ DescentData.pullFunctorIdIso F T

lemma toDescentRestrictIso_hom_hom (M : F.obj (.mk (.op T))) (i : ι) :
    ((toDescentRestrictIso F R q f hf).hom.app M).hom i =
      (F.mapComp q.op.toLoc (f i).op.toLoc).hom.toNatTrans.app M := by
  dsimp [toDescentRestrictIso, pullRestrictIso,
    DescentData.toDescentDataCompPullFunctorIso]
  rw [F.isoMapOfCommSq_eq _ _ rfl]
  simp [family, index, mapComp'_comp_id_inv_app_assoc, mapComp'_eq_mapComp]

lemma toDescentRestrictIso_inv_hom (M : F.obj (.mk (.op T))) (i : ι) :
    ((toDescentRestrictIso F R q f hf).inv.app M).hom i =
      (F.mapComp q.op.toLoc (f i).op.toLoc).inv.toNatTrans.app M := by
  have h := congrArg (fun φ => φ.hom i) ((toDescentRestrictIso F R q f hf).app M).inv_hom_id
  change ((toDescentRestrictIso F R q f hf).inv.app M).hom i ≫
    ((toDescentRestrictIso F R q f hf).hom.app M).hom i = 𝟙 _ at h
  rw [toDescentRestrictIso_hom_hom] at h
  rw [← cancel_mono ((F.mapComp q.op.toLoc (f i).op.toLoc).hom.toNatTrans.app M)]
  simpa using h

/-- An effective object together with an isomorphism to the specified
restricted descent datum. This records actual effectivity data. -/
structure Lift (D : F.DescentData (family R)) where
  obj : F.obj (.mk (.op V))
  trivialization : (F.toDescentData (family (R.pullback q))).obj obj ≅
    (restrict F R q (family (R.pullback q)) (fun r => r.property)).obj D

namespace Lift
variable {F R q} {D : F.DescentData (family R)}

/-- Pull an effective object and its specified trivialization along a map. -/
def pull (L : Lift F R q D) {W : Over B} (a : W ⟶ V) (s : W ⟶ T)
    (ha : a ≫ q = s) : Lift F R s D where
  obj := (F.map a.op.toLoc).toFunctor.obj L.obj
  trivialization :=
    (toDescentRestrictIso F (R.pullback q) a (family (R.pullback s))
      (fun r => by
        change R ((r.obj.hom ≫ a) ≫ q)
        simpa only [Sieve.pullback_apply, Category.assoc, ha] using r.property)).symm.app L.obj ≪≫
    (restrict F (R.pullback q) a (family (R.pullback s))
      (fun r => by
        change R ((r.obj.hom ≫ a) ≫ q)
        simpa only [Sieve.pullback_apply, Category.assoc, ha] using r.property)).mapIso L.trivialization ≪≫
    (restrictCompIso F R q a s ha (family (R.pullback s)) (fun r => r.property)).app D

abbrev pullIndex {W : Over B} (a : W ⟶ V)
    (r : (R.pullback (a ≫ q)).arrows.category) : (R.pullback q).arrows.category :=
  ⟨Over.mk (r.obj.hom ≫ a), by
    change R ((r.obj.hom ≫ a) ≫ q)
    simpa only [Sieve.pullback_apply, Category.assoc] using r.property⟩

lemma pull_trivialization_hom (L : Lift F R q D) {W : Over B} (a : W ⟶ V)
    (r : (R.pullback (a ≫ q)).arrows.category) :
    ((L.pull a (a ≫ q) rfl).trivialization.hom).hom r =
      (F.mapComp a.op.toLoc r.obj.hom.op.toLoc).inv.toNatTrans.app L.obj ≫
        L.trivialization.hom.hom (pullIndex a r) := by
  dsimp only [pull, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, DescentData.comp_hom]
  rw [toDescentRestrictIso_inv_hom]
  simp [restrictCompIso, restrict, restrictObj, pullIndex, index, family]

/-- A component of a sieve datum is its effective object over that member. -/
def member (hq : R q) (D : F.DescentData (family R)) : Lift F R q D where
  obj := D.obj ⟨Over.mk q, hq⟩
  trivialization := restrictMemberIso F R q (family (R.pullback q)) (fun r => r.property) hq D

lemma member_trivialization_hom (hq : R q) (D : F.DescentData (family R))
    (r : (R.pullback q).arrows.category) :
    (member hq D).trivialization.hom.hom r =
      D.hom (r.obj.hom ≫ q) (i₁ := ⟨Over.mk q, hq⟩)
        (i₂ := index R q (family (R.pullback q)) (fun r => r.property) r)
        r.obj.hom (𝟙 _) rfl (by simp [family, index]) ≫
      (F.mapId _).hom.toNatTrans.app
        (D.obj (index R q (family (R.pullback q)) (fun r => r.property) r)) := by
  simp [member, restrictMemberIso, pullRestrictIso, DescentData.pullFunctorIso, family, index]

lemma member_pull_trivialization_hom (hq : R q) (D : F.DescentData (family R))
    {W : Over B} (a : W ⟶ V) (s : W ⟶ T) (ha : a ≫ q = s)
    (r : (R.pullback s).arrows.category) :
    ((member hq D).pull a s ha).trivialization.hom.hom r =
      (F.mapComp a.op.toLoc r.obj.hom.op.toLoc).inv.toNatTrans.app
        (D.obj ⟨Over.mk q, hq⟩) ≫
      D.hom (r.obj.hom ≫ s) (i₁ := ⟨Over.mk q, hq⟩)
        (i₂ := index R s (family (R.pullback s)) (fun r => r.property) r)
        (r.obj.hom ≫ a) (𝟙 _) (by simp [family, Category.assoc, ha])
        (by simp [family, index]) ≫
      (F.mapId _).hom.toNatTrans.app
        (D.obj (index R s (family (R.pullback s)) (fun r => r.property) r)) := by
  subst s
  rw [pull_trivialization_hom, member_trivialization_hom]
  dsimp only [member]
  congr 3

variable (J : GrothendieckTopology (Over B)) [F.IsPrestack J] (hR : R ∈ J T)

/-- Full faithfulness gives the unique comparison between two effective
objects inducing the same restricted datum. -/
def compare (L K : Lift F R q D) : L.obj ≅ K.obj :=
  (F.fullyFaithfulToDescentData (family (R.pullback q))
    (by simpa [family, Sieve.ofArrows_category'] using J.pullback_stable q hR)).preimageIso
      (L.trivialization ≪≫ K.trivialization.symm)

@[reassoc]
lemma map_compare_hom (L K : Lift F R q D) :
    (F.toDescentData (family (R.pullback q))).map (compare J hR L K).hom =
      L.trivialization.hom ≫ K.trivialization.inv := by
  apply Functor.FullyFaithful.map_preimage

@[simp]
lemma compare_self (L : Lift F R q D) : (compare J hR L L).hom = 𝟙 L.obj := by
  apply (F.fullyFaithfulToDescentData (family (R.pullback q))
    (by simpa [family, Sieve.ofArrows_category'] using J.pullback_stable q hR)).map_injective
  simp [map_compare_hom]

@[reassoc]
lemma compare_comp (L K N : Lift F R q D) :
    (compare J hR L K).hom ≫ (compare J hR K N).hom = (compare J hR L N).hom := by
  apply (F.fullyFaithfulToDescentData (family (R.pullback q))
    (by simpa [family, Sieve.ofArrows_category'] using J.pullback_stable q hR)).map_injective
  simp [map_compare_hom]

lemma eq_compare (L K : Lift F R q D) (φ : L.obj ⟶ K.obj)
    (hφ : (F.toDescentData (family (R.pullback q))).map φ ≫ K.trivialization.hom =
      L.trivialization.hom) : φ = (compare J hR L K).hom := by
  apply (F.fullyFaithfulToDescentData (family (R.pullback q))
    (by simpa [family, Sieve.ofArrows_category'] using J.pullback_stable q hR)).map_injective
  rw [map_compare_hom, ← cancel_mono K.trivialization.hom]
  simpa using hφ

/-- The unique comparison of effective objects is preserved by actual pullback. -/
lemma compare_pull (L K : Lift F R q D) {W : Over B} (a : W ⟶ V)
    (s : W ⟶ T) (ha : a ≫ q = s) :
    (F.map a.op.toLoc).toFunctor.map (compare J hR L K).hom =
      (compare J hR (L.pull a s ha) (K.pull a s ha)).hom := by
  apply eq_compare (F := F) J hR (L.pull a s ha) (K.pull a s ha)
  let G := restrict F (R.pullback q) a (family (R.pullback s))
    (fun r => by
      change R ((r.obj.hom ≫ a) ≫ q)
      simpa only [Sieve.pullback_apply, Category.assoc, ha] using r.property)
  let e := toDescentRestrictIso F (R.pullback q) a (family (R.pullback s))
    (fun r => by
      change R ((r.obj.hom ≫ a) ≫ q)
      simpa only [Sieve.pullback_apply, Category.assoc, ha] using r.property)
  let c := restrictCompIso F R q a s ha (family (R.pullback s)) (fun r => r.property)
  change (F.toDescentData (family (R.pullback s))).map
      ((F.map a.op.toLoc).toFunctor.map (compare J hR L K).hom) ≫
        (e.inv.app K.obj ≫ G.map K.trivialization.hom ≫ c.hom.app D) =
    e.inv.app L.obj ≫ G.map L.trivialization.hom ≫ c.hom.app D
  have hn := e.inv.naturality (compare J hR L K).hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [map_compare_hom]
  change (e.inv.app L.obj ≫ G.map (L.trivialization.hom ≫ K.trivialization.inv)) ≫
    G.map K.trivialization.hom ≫ c.hom.app D = _
  rw [Category.assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The comparison between repeated and composite pullback is the original
pseudofunctor composition isomorphism. -/
lemma compare_pull_comp (L : Lift F R q D) {W U : Over B}
    (a : W ⟶ V) (g : U ⟶ W) :
    (compare J hR ((L.pull a (a ≫ q) rfl).pull g (g ≫ (a ≫ q)) rfl)
      (L.pull (g ≫ a) (g ≫ (a ≫ q)) (Category.assoc _ _ _))).hom =
    (F.mapComp a.op.toLoc g.op.toLoc).inv.toNatTrans.app L.obj := by
  symm
  apply eq_compare (F := F) J hR
    ((L.pull a (a ≫ q) rfl).pull g (g ≫ (a ≫ q)) rfl)
    (L.pull (g ≫ a) (g ≫ (a ≫ q)) (Category.assoc _ _ _))
  ext r
  dsimp only [DescentData.comp_hom, toDescentData_map_hom]
  change (F.map r.obj.hom.op.toLoc).toFunctor.map
      ((F.mapComp a.op.toLoc g.op.toLoc).inv.toNatTrans.app L.obj) ≫
        (L.pull (g ≫ a) ((g ≫ a) ≫ q) rfl).trivialization.hom.hom r = _
  rw [pull_trivialization_hom L (g ≫ a) r,
    pull_trivialization_hom (L.pull a (a ≫ q) rfl) g r,
    pull_trivialization_hom L a (pullIndex g r)]
  dsimp only [pull]
  have hc := F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
    a.op.toLoc g.op.toLoc r.obj.hom.op.toLoc (g ≫ a).op.toLoc
    (r.obj.hom ≫ g).op.toLoc (r.obj.hom ≫ g ≫ a).op.toLoc rfl rfl rfl L.obj
  simp [mapComp'] at hc
  have ht := congrArg (fun k => k ≫ L.trivialization.hom.hom (pullIndex (g ≫ a) r)) hc
  convert ht using 1 <;> simp [pullIndex, restrict, restrictObj, index, family, Category.assoc]
  all_goals congr 3

lemma compare_pull_comp' (L : Lift F R q D) {W U : Over B}
    (a : W ⟶ V) (s : W ⟶ T) (ha : a ≫ q = s)
    (g : U ⟶ W) (t : U ⟶ T) (hg : g ≫ s = t)
    (ga : U ⟶ V) (hga : g ≫ a = ga) :
    (compare J hR ((L.pull a s ha).pull g t hg)
      (L.pull ga t (by rw [← hga, Category.assoc, ha, hg]))).hom =
    (F.mapComp' a.op.toLoc g.op.toLoc ga.op.toLoc (by rw [← hga]; rfl)).inv.toNatTrans.app L.obj := by
  subst s t ga
  simpa [mapComp'] using compare_pull_comp J hR L a g

lemma compare_pull_comp_hom' (L : Lift F R q D) {W U : Over B}
    (a : W ⟶ V) (s : W ⟶ T) (ha : a ≫ q = s)
    (g : U ⟶ W) (t : U ⟶ T) (hg : g ≫ s = t)
    (ga : U ⟶ V) (hga : g ≫ a = ga) :
    (compare J hR (L.pull ga t (by rw [← hga, Category.assoc, ha, hg]))
      ((L.pull a s ha).pull g t hg)).hom =
    (F.mapComp' a.op.toLoc g.op.toLoc ga.op.toLoc (by rw [← hga]; rfl)).hom.toNatTrans.app L.obj := by
  rw [← cancel_mono (compare J hR ((L.pull a s ha).pull g t hg)
    (L.pull ga t (by rw [← hga, Category.assoc, ha, hg]))).hom]
  rw [compare_comp, compare_self, compare_pull_comp' J hR L a s ha g t hg ga hga]
  simp [pull]

/-- Transition isomorphisms between effective lifts obey pullback naturality. -/
lemma pullHom_compare {V' W U : Over B} {q' : V' ⟶ T}
    (L : Lift F R q D) (K : Lift F R q' D)
    (a : W ⟶ V) (b : W ⟶ V') (s : W ⟶ T)
    (ha : a ≫ q = s) (hb : b ≫ q' = s)
    (g : U ⟶ W) (t : U ⟶ T) (hg : g ≫ s = t)
    (ga : U ⟶ V) (gb : U ⟶ V') (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    pullHom (compare J hR (L.pull a s ha) (K.pull b s hb)).hom g ga gb hga hgb =
      (compare J hR (L.pull ga t (by rw [← hga, Category.assoc, ha, hg]))
        (K.pull gb t (by rw [← hgb, Category.assoc, hb, hg]))).hom := by
  dsimp only [pullHom]
  rw [compare_pull (J := J) hR (L.pull a s ha) (K.pull b s hb) g t hg]
  rw [← compare_pull_comp' J hR K b s hb g t hg gb hgb,
    ← compare_pull_comp_hom' J hR L a s ha g t hg ga hga]
  rw [compare_comp, compare_comp]

/-- The comparisons of canonical member lifts are exactly the transitions of
the original descent datum. -/
lemma compare_member_pull {V' W : Over B} {q' : V' ⟶ T}
    (hq : R q) (hq' : R q') (D : F.DescentData (family R))
    (a : W ⟶ V) (b : W ⟶ V') (s : W ⟶ T)
    (ha : a ≫ q = s) (hb : b ≫ q' = s) :
    (compare J hR ((member hq D).pull a s ha) ((member hq' D).pull b s hb)).hom =
      D.hom s (i₁ := ⟨Over.mk q, hq⟩) (i₂ := ⟨Over.mk q', hq'⟩) a b ha hb := by
  symm
  apply eq_compare (F := F) J hR ((member hq D).pull a s ha) ((member hq' D).pull b s hb)
  ext r
  dsimp only [DescentData.comp_hom, toDescentData_map_hom]
  rw [member_pull_trivialization_hom, member_pull_trivialization_hom]
  rw [map_eq_pullHom (D.hom s (i₁ := ⟨Over.mk q, hq⟩)
    (i₂ := ⟨Over.mk q', hq'⟩) a b ha hb) r.obj.hom (r.obj.hom ≫ a) (r.obj.hom ≫ b) rfl rfl]
  rw [D.pullHom_hom r.obj.hom s (r.obj.hom ≫ s) rfl
    (i₁ := ⟨Over.mk q, hq⟩) (i₂ := ⟨Over.mk q', hq'⟩)
    a b ha hb (r.obj.hom ≫ a) (r.obj.hom ≫ b) rfl rfl]
  simp [mapComp', Category.assoc]

end Lift

/-- Effective local objects acquire genuine categorical descent data from the
unique comparisons supplied by the prestack property. -/
def liftDescentData (J : GrothendieckTopology (Over B)) [F.IsPrestack J]
    (hR : R ∈ J T) {ι : Type 1} {X : ι → Over B} (f : ∀ i, X i ⟶ T)
    (D : F.DescentData (family R)) (L : ∀ i, Lift F R (f i) D) : F.DescentData f where
  obj i := (L i).obj
  hom _Y p i j a b ha hb := (Lift.compare J hR ((L i).pull a p ha) ((L j).pull b p hb)).hom
  pullHom_hom _Y' _Y g p p' hp i j a b ha hb a' b' ha' hb' :=
    Lift.pullHom_compare J hR (L i) (L j) a b p ha hb g p' hp a' b' ha' hb'
  hom_self _Y p i a ha := Lift.compare_self J hR ((L i).pull a p ha)
  hom_comp _Y p i j k a b c ha hb hc :=
    Lift.compare_comp J hR ((L i).pull a p ha) ((L j).pull b p hb) ((L k).pull c p hc)

/-- The descent data from any two systems of lifts are canonically isomorphic. -/
def liftDescentDataIso (J : GrothendieckTopology (Over B)) [F.IsPrestack J]
    (hR : R ∈ J T) {ι : Type 1} {X : ι → Over B} (f : ∀ i, X i ⟶ T)
    (D : F.DescentData (family R)) (L K : ∀ i, Lift F R (f i) D) :
    liftDescentData F R J hR f D L ≅ liftDescentData F R J hR f D K :=
  DescentData.isoMk (fun i => Lift.compare J hR (L i) (K i)) (by
    intro Y p i j a b ha hb
    dsimp only [liftDescentData]
    rw [Lift.compare_pull J hR (L i) (K i) a p ha,
      Lift.compare_pull J hR (L j) (K j) b p hb,
      Lift.compare_comp, Lift.compare_comp])

/-- Choosing the original components recovers the original descent datum. -/
def memberDescentDataIso (J : GrothendieckTopology (Over B)) [F.IsPrestack J]
    (hR : R ∈ J T) (D : F.DescentData (family R)) :
    liftDescentData F R J hR (family R) D (fun i => Lift.member i.property D) ≅ D :=
  DescentData.isoMk (fun i => Iso.refl _) (by
    intro Y p i j a b ha hb
    dsimp only [liftDescentData, Iso.refl_hom]
    simp only [Lift.member, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact (Lift.compare_member_pull J hR i.property j.property D a b p ha hb).symm)

/-- Component isomorphism of an isomorphism of descent data. -/
def componentIso {ι : Type 1} {X : ι → Over B} {f : ∀ i, X i ⟶ T}
    {D E : F.DescentData f} (e : D ≅ E) (i : ι) : D.obj i ≅ E.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by rw [← DescentData.comp_hom, e.hom_inv_id, DescentData.id_hom]
  inv_hom_id := by rw [← DescentData.comp_hom, e.inv_hom_id, DescentData.id_hom]

/-- The sieve of maps over which a fixed datum has an effective object. -/
def effectiveSieve (D : F.DescentData (family R)) : Sieve T where
  arrows _ q := Nonempty (Lift F R q D)
  downward_closed := by
    intro V W q hq a
    exact ⟨hq.some.pull a (a ≫ q) rfl⟩

lemma le_effectiveSieve (D : F.DescentData (family R)) : R ≤ effectiveSieve F R D := by
  intro V q hq
  exact ⟨Lift.member hq D⟩

/-- Local categorical effectivity descends along any covering sieve for which
the pseudofunctor already has effective descent. -/
lemma isStackFor_of_local (J : GrothendieckTopology (Over B)) [F.IsPrestack J]
    (hR : R ∈ J T) (S : Sieve T) (hS : S ∈ J T)
    (hStack : F.IsStackFor S.arrows)
    (hlocal : ∀ ⦃V : Over B⦄ (q : V ⟶ T), S q → F.IsStackFor (R.pullback q).arrows) :
    F.IsStackFor R.arrows := by
  rw [F.isStackFor_iff]
  have hff := F.fullyFaithfulToDescentData (J := J) (family R)
    (by simpa [family, Sieve.ofArrows_category'] using hR)
  have := hff.full
  have := hff.faithful
  have ess : (F.toDescentData (family R)).EssSurj := by
    constructor
    intro D
    let E := effectiveSieve F R D
    have hSE : S ≤ E := by
      intro V q hq
      have := (hlocal q hq).essSurj
      exact ⟨⟨(F.toDescentData (family (R.pullback q))).objPreimage
        ((restrict F R q (family (R.pullback q)) (fun r => r.property)).obj D),
        (F.toDescentData (family (R.pullback q))).objObjPreimageIso _⟩⟩
    have hEstack := hStack.of_le' F hS hSE
    have := hEstack.essSurj
    let L : ∀ i : E.arrows.category, Lift F R (family E i) D := fun i => i.property.some
    let A := liftDescentData F R J hR (family E) D L
    let M := (F.toDescentData (family E)).objPreimage A
    let e : (F.toDescentData (family E)).obj M ≅ A :=
      (F.toDescentData (family E)).objObjPreimageIso A
    let inc : R.arrows.category → E.arrows.category := fun i =>
      ⟨i.obj, le_effectiveSieve F R D _ i.property⟩
    let e' : (F.toDescentData (family R)).obj M ≅
        liftDescentData F R J hR (family R) D (fun i => L (inc i)) :=
      DescentData.isoMk (fun i => componentIso F e (inc i)) (by
        intro Y p i j a b ha hb
        exact e.hom.comm p (i₁ := inc i) (i₂ := inc j) a b ha hb)
    exact ⟨M, ⟨e' ≪≫ liftDescentDataIso F R J hR (family R) D
      (fun i => L (inc i)) (fun i => Lift.member i.property D) ≪≫
        memberDescentDataIso F R J hR D⟩⟩
  exact { }

end SieveDescent

/-- Fpqc covering sieves with universally effective categorical descent form
a Grothendieck topology. -/
def stackTopology (hO : OpenDescent F) [F.IsPrestack (rootTopology B)] :
    GrothendieckTopology (Over B) where
  sieves T := {R | R ∈ rootTopology B T ∧
    ∀ (V : Over B) (f : V ⟶ T), F.IsStackFor (R.pullback f).arrows}
  top_mem' T := by
    refine ⟨(rootTopology B).top_mem T, ?_⟩
    intro V f
    rw [Sieve.pullback_top]
    let := zariski_isStack F hO
    exact F.isStackFor' _ ((Scheme.zariskiTopology.over B).top_mem V)
  pullback_stable' T V R f hR := by
    refine ⟨(rootTopology B).pullback_stable f hR.1, ?_⟩
    intro W g
    simpa only [← Sieve.pullback_comp] using hR.2 W (g ≫ f)
  transitive' T R hR S hS := by
    have hSJ : S ∈ rootTopology B T :=
      (rootTopology B).transitive hR.1 S (fun V q hq => (hS hq).1)
    refine ⟨hSJ, ?_⟩
    intro V f
    apply SieveDescent.isStackFor_of_local F (S.pullback f) (rootTopology B)
      ((rootTopology B).pullback_stable f hSJ) (R.pullback f)
      ((rootTopology B).pullback_stable f hR.1) (hR.2 V f)
    intro W q hq
    have h := (hS hq).2 W (𝟙 W)
    simpa only [Sieve.pullback_id, ← Sieve.pullback_comp, Category.id_comp] using h

lemma zariski_le_stackTopology (hO : OpenDescent F) [F.IsPrestack (rootTopology B)] :
    Scheme.zariskiTopology.over B ≤ stackTopology F hO := by
  let := zariski_isStack F hO
  intro T R hR
  refine ⟨?_, fun V f => F.isStackFor' _ ((Scheme.zariskiTopology.over B).pullback_stable f hR)⟩
  exact Scheme.zariskiTopology_le_fpqcTopology _ hR

lemma singleton_mem_stackTopology (hO : OpenDescent F) (hQ : SingletonDescent F)
    [F.IsPrestack (rootTopology B)] {T V : Over B} (q : V ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    Sieve.generate (Presieve.singleton q) ∈ stackTopology F hO T := by
  refine ⟨?_, ?_⟩
  · change Sieve.overEquiv T (Sieve.generate (Presieve.singleton q)) ∈ Scheme.fpqcTopology T.left
    rw [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve, Presieve.map_singleton]
    letI := hq
    letI := hf
    letI := hs
    exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fpqcPrecoverage
  · intro W f
    rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
      F.IsStackFor_generate_iff]
    have H := (Over.forget B).map_isPullback (IsPullback.of_hasPullback q f)
    apply singleton_isStackFor F hQ (pullback.snd q f)
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) H hq
    · exact MorphismProperty.of_isPullback (P := @Flat) H hf
    · exact MorphismProperty.of_isPullback (P := @Surjective) H hs

end FPQCStackCriterionOver

open CategoryTheory

/-- Categorical descent for arbitrary open covers and faithfully flat
quasi-compact singletons implies the stack condition for the standard big
fpqc topology on schemes over the given base. -/
theorem fpqc_stack_criterion_over (B : AlgebraicGeometry.Scheme.{0})
    (F : CategoryTheory.Pseudofunctor
      (CategoryTheory.LocallyDiscrete (CategoryTheory.Over B)ᵒᵖ) CategoryTheory.Cat.{0, 1})
    (hO : OpenDescent F) (hQ : SingletonDescent F) : F.IsStack (rootTopology B) := by
  let := FPQCStackCriterionOver.fpqc_isPrestack F hO hQ
  have hle := FPQCStackCriterionOver.fpqc_le_of_open_singleton
    (FPQCStackCriterionOver.stackTopology F hO)
    (FPQCStackCriterionOver.zariski_le_stackTopology F hO)
    (fun q hq hf hs => FPQCStackCriterionOver.singleton_mem_stackTopology F hO hQ q hq hf hs)
  apply CategoryTheory.Pseudofunctor.IsStack.of_isStackFor
  intro T R hR
  simpa only [CategoryTheory.Sieve.pullback_id] using (hle _ hR).2 T (𝟙 T)

end ArithmeticThetaRootStackR0198

#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.fpqc_le_of_open_singleton
#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.fpqc_isPrestack
#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.SieveDescent.pullRestrictIso
#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.SieveDescent.toDescentRestrictIso
#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.SieveDescent.restrictMemberIso

#print axioms ArithmeticThetaRootStackR0198.FPQCStackCriterionOver.SieveDescent.isStackFor_of_local
#print axioms ArithmeticThetaRootStackR0198.fpqc_stack_criterion_over
