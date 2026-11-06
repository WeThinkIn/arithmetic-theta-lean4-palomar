module

public import EvenMarkingTorsorDefinitionsR0216
public import Mathlib.AlgebraicGeometry.RelativeGluing

@[expose] public section

/-! Transport of actual markings for the general-scheme representing cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216
namespace SchemeFourCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

variable {S : Scheme.{u}} (E : Family S)

/-- Markings on a test scheme, expressed by their actual maps to the original family. -/
structure Marking {T : Scheme.{u}} (t : T ⟶ S) where
  x : SchemeHomOver t E.p
  y : SchemeHomOver t E.p
  killed_x : multiple E t 4 x = E.law.one t
  killed_y : multiple E t 4 y = E.law.one t
  avoids : ∀ i j : Fin 4, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (E.law.mul t (multiple E t i.val x)
      (multiple E t j.val y)).val) (Set.range E.zero)

lemma one_val {T : Scheme.{u}} (t : T ⟶ S) :
    (E.law.one t).val = t ≫ E.zero := by
  exact (congrArg Subtype.val
    (SchemeLocal.one_natural E.law (𝟙 S) t t (by simp))).symm

lemma multiple_natural {T U : Scheme.{u}} (t : T ⟶ S) (s : U ⟶ S)
    (a : U ⟶ T) (ha : a ≫ t = s) (n : ℕ) (x : SchemeHomOver t E.p) :
    GoodReductionJacobian.schemeHomOverComp a ha (multiple E t n x) =
      multiple E s n (GoodReductionJacobian.schemeHomOverComp a ha x) := by
  induction n with
  | zero => exact SchemeLocal.one_natural E.law t s a ha
  | succ n ih =>
    change GoodReductionJacobian.schemeHomOverComp a ha
      (E.law.mul t (multiple E t n x) x) = _
    rw [E.law.mul_natural, ih]
    rfl

def Marking.pull {T U : Scheme.{u}} {t : T ⟶ S} (M : Marking E t)
    (a : U ⟶ T) : Marking E (a ≫ t) where
  x := GoodReductionJacobian.schemeHomOverComp a rfl M.x
  y := GoodReductionJacobian.schemeHomOverComp a rfl M.y
  killed_x := by
    rw [← multiple_natural, M.killed_x]
    exact SchemeLocal.one_natural E.law t (a ≫ t) a rfl
  killed_y := by
    rw [← multiple_natural, M.killed_y]
    exact SchemeLocal.one_natural E.law t (a ≫ t) a rfl
  avoids := by
    intro i j hij
    have h := congrArg Subtype.val
      (E.law.mul_natural t (a ≫ t) a rfl
        (multiple E t i.val M.x) (multiple E t j.val M.y))
    rw [multiple_natural, multiple_natural] at h
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    rw [← h] at hz
    exact Set.disjoint_left.mp (M.avoids i j hij) (Set.mem_range_self (a z)) hz

lemma Marking.ext {T : Scheme.{u}} {t : T ⟶ S} {M N : Marking E t}
    (hx : M.x = N.x) (hy : M.y = N.y) : M = N := by
  cases M; cases N; cases hx; cases hy; rfl

def Marking.cast {T : Scheme.{u}} {t t' : T ⟶ S} (h : t = t')
    (M : Marking E t) : Marking E t' := h ▸ M

@[simp] lemma Marking.cast_x {T : Scheme.{u}} {t t' : T ⟶ S} (h : t = t')
    (M : Marking E t) : (M.cast E h).x.val = M.x.val := by subst t'; rfl

@[simp] lemma Marking.cast_y {T : Scheme.{u}} {t t' : T ⟶ S} (h : t = t')
    (M : Marking E t) : (M.cast E h).y.val = M.y.val := by subst t'; rfl

@[simp] lemma Marking.pull_x {T U : Scheme.{u}} {t : T ⟶ S} (M : Marking E t)
    (a : U ⟶ T) : (M.pull E a).x.val = a ≫ M.x.val := rfl

@[simp] lemma Marking.pull_y {T U : Scheme.{u}} {t : T ⟶ S} (M : Marking E t)
    (a : U ⟶ T) : (M.pull E a).y.val = a ≫ M.y.val := rfl

/-- The identity-base interface changes no section or equation. -/
def Marking.toFullLevel (M : Marking E (𝟙 S)) : FullLevel E 4 where
  x := M.x
  y := M.y
  killed_x := M.killed_x
  killed_y := M.killed_y
  avoids := M.avoids

def ofFullLevel (M : FullLevel E 4) : Marking E (𝟙 S) where
  x := M.x
  y := M.y
  killed_x := M.killed_x
  killed_y := M.killed_y
  avoids := M.avoids

section CartesianLift
variable {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)

def liftPoint (x : SchemeHomOver b E.p) : SchemeHomOver (𝟙 T) F.p :=
  ⟨hc.1.lift x.val (𝟙 T) (by simpa using x.property), hc.1.lift_snd _ _ _⟩

lemma liftPoint_comp (x : SchemeHomOver b E.p) :
    (liftPoint E F b f hc x).val ≫ f = x.val := hc.1.lift_fst _ _ _

include hc in
lemma mul_comp (x y : SchemeHomOver (𝟙 T) F.p)
    (x' y' : SchemeHomOver b E.p)
    (hx : x.val ≫ f = x'.val) (hy : y.val ≫ f = y'.val) :
    (F.law.mul (𝟙 T) x y).val ≫ f = (E.law.mul b x' y').val := by
  let xx : SchemeHomOver ((𝟙 T) ≫ b) E.p := ⟨x'.val, by simpa using x'.property⟩
  let yy : SchemeHomOver ((𝟙 T) ≫ b) E.p := ⟨y'.val, by simpa using y'.property⟩
  exact (hc.2.2 T (𝟙 T) x y xx yy hx.symm hy.symm).symm.trans
    (SchemeLocal.mul_val_congr E.law (Category.id_comp b) xx yy x' y' rfl rfl)

include hc in
lemma multiple_comp (x : SchemeHomOver (𝟙 T) F.p)
    (x' : SchemeHomOver b E.p) (hx : x.val ≫ f = x'.val) (n : ℕ) :
    (multiple F (𝟙 T) n x).val ≫ f = (multiple E b n x').val := by
  induction n with
  | zero => exact hc.2.1.trans (one_val E b).symm
  | succ n ih => exact mul_comp E F b f hc _ _ _ _ ih hx

/-- Lift a marking into any actual Cartesian group-family square. -/
def liftMarking (M : Marking E b) : FullLevel F 4 where
  x := liftPoint E F b f hc M.x
  y := liftPoint E F b f hc M.y
  killed_x := by
    apply CartesianFullMarking.section_ext E F b f hc.1
    rw [multiple_comp E F b f hc _ M.x (liftPoint_comp E F b f hc M.x),
      M.killed_x, one_val]
    exact hc.2.1.symm
  killed_y := by
    apply CartesianFullMarking.section_ext E F b f hc.1
    rw [multiple_comp E F b f hc _ M.y (liftPoint_comp E F b f hc M.y),
      M.killed_y, one_val]
    exact hc.2.1.symm
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨t, ht⟩
    have h := mul_comp E F b f hc _ _ _ _
      (multiple_comp E F b f hc _ M.x (liftPoint_comp E F b f hc M.x) i.val)
      (multiple_comp E F b f hc _ M.y (liftPoint_comp E F b f hc M.y) j.val)
    apply Set.disjoint_left.mp (M.avoids i j hij) (Set.mem_range_self z)
    refine ⟨b t, ?_⟩
    have hh := congrArg (fun x => f x) ht
    change (F.zero ≫ f) t = _ at hh
    rw [hc.2.1] at hh
    exact hh.trans (congrArg (fun g : T ⟶ E.curve => g z) h)

end CartesianLift

section CartesianPush
variable {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)

include hc in
lemma zero_cartesian : IsPullback F.zero b f E.zero := by
  have hF : F.zero ≫ F.p = 𝟙 T := (F.law.one (𝟙 T)).property
  have hE : E.zero ≫ E.p = 𝟙 S := (E.law.one (𝟙 S)).property
  have h : IsPullback (F.zero ≫ F.p) b b (E.zero ≫ E.p) := by
    rw [hF, hE]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact h.of_right hc.2.1 hc.1.flip

include hc in
lemma zero_preimage (x : F.curve) (hx : f x ∈ Set.range E.zero) :
    x ∈ Set.range F.zero := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
    (zero_cartesian E F b f hc) x s hs.symm
  exact ⟨t, ht⟩

def pushPoint (x : SchemeHomOver (𝟙 T) F.p) : SchemeHomOver b E.p :=
  ⟨x.val ≫ f, by rw [Category.assoc, hc.1.w, ← Category.assoc, x.property]; simp⟩

/-- Push a marking through the Cartesian comparison, preserving the actual identity locus. -/
def pushMarking (N : FullLevel F 4) : Marking E b where
  x := pushPoint E F b f hc N.x
  y := pushPoint E F b f hc N.y
  killed_x := by
    apply Subtype.ext
    rw [← multiple_comp E F b f hc N.x _ rfl, N.killed_x, one_val E b]
    exact hc.2.1
  killed_y := by
    apply Subtype.ext
    rw [← multiple_comp E F b f hc N.y _ rfl, N.killed_y, one_val E b]
    exact hc.2.1
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    have hh := mul_comp E F b f hc _ _ _ _
      (multiple_comp E F b f hc N.x (pushPoint E F b f hc N.x) rfl i.val)
      (multiple_comp E F b f hc N.y (pushPoint E F b f hc N.y) rfl j.val)
    rw [← hh] at hz
    exact Set.disjoint_left.mp (N.avoids i j hij) (Set.mem_range_self z)
      (zero_preimage E F b f hc _ hz)

lemma push_lift (M : Marking E b) :
    pushMarking E F b f hc (liftMarking E F b f hc M) = M := by
  apply Marking.ext
  · exact Subtype.ext (liftPoint_comp E F b f hc M.x)
  · exact Subtype.ext (liftPoint_comp E F b f hc M.y)

lemma lift_push (N : FullLevel F 4) :
    liftMarking E F b f hc (pushMarking E F b f hc N) = N := by
  apply CartesianFullMarking.fullLevel_ext
  · apply CartesianFullMarking.section_ext E F b f hc.1
    exact liftPoint_comp E F b f hc _
  · apply CartesianFullMarking.section_ext E F b f hc.1
    exact liftPoint_comp E F b f hc _

/-- Markings on all test schemes coincide with full markings on any Cartesian family. -/
def markingEquiv : Marking E b ≃ FullLevel F 4 where
  toFun := liftMarking E F b f hc
  invFun := pushMarking E F b f hc
  left_inv := push_lift E F b f hc
  right_inv := lift_push E F b f hc

end CartesianPush

section Composition
variable {T U : Scheme.{u}} (F : Family T) (G : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hF : Cartesian E F b f)
    (c : U ⟶ T) (g : G.curve ⟶ F.curve) (hG : Cartesian F G c g)

include hF hG in
lemma cartesian_comp : Cartesian E G (c ≫ b) (g ≫ f) := by
  refine ⟨hG.1.paste_horiz hF.1, ?_, ?_⟩
  · rw [← Category.assoc, hG.2.1, Category.assoc, hF.2.1, Category.assoc]
  · intro V t x y x' y' hx hy
    let xx : SchemeHomOver (t ≫ c) F.p :=
      ⟨x.val ≫ g, by rw [Category.assoc, hG.1.w, ← Category.assoc, x.property]⟩
    let yy : SchemeHomOver (t ≫ c) F.p :=
      ⟨y.val ≫ g, by rw [Category.assoc, hG.1.w, ← Category.assoc, y.property]⟩
    let xx' : SchemeHomOver ((t ≫ c) ≫ b) E.p :=
      ⟨x'.val, by simpa only [Category.assoc] using x'.property⟩
    let yy' : SchemeHomOver ((t ≫ c) ≫ b) E.p :=
      ⟨y'.val, by simpa only [Category.assoc] using y'.property⟩
    have H := hF.2.2 V (t ≫ c) xx yy xx' yy'
      (by simpa only [xx, xx', Category.assoc] using hx)
      (by simpa only [yy, yy', Category.assoc] using hy)
    have K := hG.2.2 V t x y xx yy rfl rfl
    calc
      (E.law.mul _ x' y').val = (E.law.mul _ xx' yy').val :=
        SchemeLocal.mul_val_congr E.law (Category.assoc t c b).symm _ _ _ _ rfl rfl
      _ = (F.law.mul _ xx yy).val ≫ f := H
      _ = (G.law.mul _ x y).val ≫ (g ≫ f) := by rw [K, Category.assoc]

end Composition

section RelativeTransport
variable {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)

/-- Cartesian comparison on arbitrary test schemes, not just on global sections. -/
def relativeMarkingEquiv {T : Scheme.{u}} (t : T ⟶ B) :
    Marking E (t ≫ b) ≃ Marking F t :=
  let G := SchemeFamilyBaseChange.baseChangeFamily F t
  let g := pullback.fst F.p t
  let hG : Cartesian F G t g :=
    ⟨IsPullback.of_hasPullback F.p t,
      SchemeFamilyBaseChange.baseChangeLaw_zero F t,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative F t⟩
  (markingEquiv E G (t ≫ b) (g ≫ f) (cartesian_comp E F G b f hc t g hG)).trans
    (markingEquiv F G t g hG).symm

lemma relativeMarkingEquiv_x {T : Scheme.{u}} (t : T ⟶ B) (M : Marking E (t ≫ b)) :
    (relativeMarkingEquiv E F b f hc t M).x.val ≫ f = M.x.val := by
  change (_ ≫ pullback.fst F.p t) ≫ f = _
  rw [Category.assoc]
  exact liftPoint_comp E _ _ _
    (cartesian_comp E F _ b f hc t _
      ⟨IsPullback.of_hasPullback F.p t,
        SchemeFamilyBaseChange.baseChangeLaw_zero F t,
        SchemeFamilyBaseChange.baseChangeFamily_multiplicative F t⟩) _

lemma relativeMarkingEquiv_y {T : Scheme.{u}} (t : T ⟶ B) (M : Marking E (t ≫ b)) :
    (relativeMarkingEquiv E F b f hc t M).y.val ≫ f = M.y.val := by
  change (_ ≫ pullback.fst F.p t) ≫ f = _
  rw [Category.assoc]
  exact liftPoint_comp E _ _ _
    (cartesian_comp E F _ b f hc t _
      ⟨IsPullback.of_hasPullback F.p t,
        SchemeFamilyBaseChange.baseChangeLaw_zero F t,
        SchemeFamilyBaseChange.baseChangeFamily_multiplicative F t⟩) _

end RelativeTransport

section Affine
variable {k : Type u} [Field k] {σ : S ⟶ Base k}
  (P : LocalPresentation k S σ E)
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- Exact affine interface conversion, valid on every test scheme. -/
def affineMarkingEquiv {T : Scheme.{u}} (t : T ⟶ Base P.ring) :
    Marking (SchemeLocalClassifier.family P) t ≃
      ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law 4 t where
  toFun M := {
    x := M.x, y := M.y
    killed_x := by rw [← SchemeLocalClassifier.multiple_eq]; exact M.killed_x
    killed_y := by rw [← SchemeLocalClassifier.multiple_eq]; exact M.killed_y
    avoids := by
      intro i j hij
      have h := M.avoids i j hij
      rw [SchemeLocalClassifier.multiple_eq, SchemeLocalClassifier.multiple_eq,
        SchemeLocalClassifier.family_zero] at h
      exact h }
  invFun M := {
    x := M.x, y := M.y
    killed_x := by rw [SchemeLocalClassifier.multiple_eq]; exact M.killed_x
    killed_y := by rw [SchemeLocalClassifier.multiple_eq]; exact M.killed_y
    avoids := by
      intro i j hij
      rw [SchemeLocalClassifier.multiple_eq, SchemeLocalClassifier.multiple_eq,
        SchemeLocalClassifier.family_zero]
      exact M.avoids i j hij }
  left_inv M := Marking.ext _ rfl rfl
  right_inv M := ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175.marking_ext
    _ _ rfl rfl

end Affine

/-- A universal pair of actual sections; existence is not assumed. -/
structure PointCover where
  space : Scheme.{u}
  projection : space ⟶ S
  marking : Marking E projection

def PointRepresents (D : PointCover E) : Prop :=
  ∀ (T : Scheme.{u}) (b : T ⟶ S) (M : Marking E b),
    ∃! q : SchemeHomOver b D.projection,
      q.val ≫ D.marking.x.val = M.x.val ∧ q.val ≫ D.marking.y.val = M.y.val

section AffineRepresentation
variable {k : Type u} [Field k] {σ : S ⟶ Base k}
  (P : LocalPresentation k S σ E)
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- Reuse the accepted affine representing scheme, retaining both universal maps. -/
def affinePointCover : PointCover (SchemeLocalClassifier.family P) :=
  let D := ArithmeticThetaFullLevelCoverR0175.Representability.level
    P.ring P.equation P.law P.originLaw 4
  { space := D.space, projection := D.projection
    marking := (affineMarkingEquiv E P D.projection).symm D.level }

lemma affinePointCover_represents :
    PointRepresents (SchemeLocalClassifier.family P) (affinePointCover E P) := by
  intro T t M
  exact ArithmeticThetaFullLevelCoverR0175.Representability.represents
    P.ring P.equation P.law P.originLaw 4 T t (affineMarkingEquiv E P t M)

end AffineRepresentation

/-- The universal family is the actual pullback, with its lifted universal marking. -/
def PointCover.toCover (D : PointCover E) : Cover E :=
  let F := SchemeFamilyBaseChange.baseChangeFamily E D.projection
  let hc : Cartesian E F D.projection (pullback.fst E.p D.projection) :=
    ⟨IsPullback.of_hasPullback E.p D.projection,
      SchemeFamilyBaseChange.baseChangeLaw_zero E D.projection,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative E D.projection⟩
  { space := D.space, projection := D.projection, family := F
    comparison := pullback.fst E.p D.projection, cartesian := hc
    marking := liftMarking E F D.projection (pullback.fst E.p D.projection) hc D.marking }

section RepresentationBridge
variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

include k σ in
lemma marked_factor {B T : Scheme.{u}} (G : Family B) (F : Family T)
    (c : B ⟶ S) (g : G.curve ⟶ E.curve) (hG : Cartesian E G c g)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hF : Cartesian E F b f)
    (q : T ⟶ B) (hq : q ≫ c = b) (M : FullLevel G 4) (N : FullLevel F 4)
    (hx : N.x.val ≫ f = q ≫ M.x.val ≫ g)
    (hy : N.y.val ≫ f = q ≫ M.y.val ≫ g) :
    ∃ h : F.curve ⟶ G.curve, MarkedCartesian G F M N q h ∧ h ≫ g = f := by
  let h := hG.1.lift f (F.p ≫ q) (by rw [Category.assoc, hq]; exact hF.1.w)
  have hg : h ≫ g = f := hG.1.lift_fst _ _ _
  have hp : h ≫ G.p = F.p ≫ q := hG.1.lift_snd _ _ _
  have hpb : IsPullback h F.p G.p q := by
    apply IsPullback.of_right (h₁₂ := g) (h₂₂ := c) _ hp hG.1
    rw [hg, hq]
    exact hF.1
  have hz : F.zero ≫ h = q ≫ G.zero := by
    apply hG.1.hom_ext
    · rw [Category.assoc, hg, hF.2.1, Category.assoc, hG.2.1,
        ← Category.assoc, hq]
    · rw [Category.assoc, hp, ← Category.assoc, Family.zero, Family.zero,
        (F.law.one (𝟙 T)).property, Category.id_comp,
        Category.assoc, (G.law.one (𝟙 B)).property, Category.comp_id]
  refine ⟨h, ⟨hpb, hz,
    pointed_cartesian_group_law k B T (c ≫ σ) G F q h hpb hz, ?_, ?_⟩, hg⟩
  · apply hG.1.hom_ext
    · simpa only [Category.assoc, hg] using hx
    · rw [Category.assoc, hp, ← Category.assoc, N.x.property, Category.id_comp,
        Category.assoc, M.x.property, Category.comp_id]
  · apply hG.1.hom_ext
    · simpa only [Category.assoc, hg] using hy
    · rw [Category.assoc, hp, ← Category.assoc, N.y.property, Category.id_comp,
        Category.assoc, M.y.property, Category.comp_id]

include k σ in
lemma PointCover.toCover_represents (D : PointCover E) (hD : PointRepresents E D) :
    Represents E (D.toCover E) := by
  intro T F N b f hc
  let A := pushMarking E F b f hc N
  obtain ⟨q, hq, huniq⟩ := hD T b A
  have hx : (D.toCover E).marking.x.val ≫ (D.toCover E).comparison = D.marking.x.val :=
    liftPoint_comp E _ _ _ (D.toCover E).cartesian _
  have hy : (D.toCover E).marking.y.val ≫ (D.toCover E).comparison = D.marking.y.val :=
    liftPoint_comp E _ _ _ (D.toCover E).cartesian _
  refine ⟨q, ?_, ?_⟩
  · apply marked_factor E k σ _ F _ _ (D.toCover E).cartesian b f hc q.val q.property
    · rw [hx]; exact hq.1.symm
    · rw [hy]; exact hq.2.symm
  · intro q' hq'
    obtain ⟨h, hh, hf⟩ := hq'
    apply huniq q'
    constructor
    · rw [← hx, ← Category.assoc, ← hh.2.2.2.1, Category.assoc, hf]
      rfl
    · rw [← hy, ← Category.assoc, ← hh.2.2.2.2, Category.assoc, hf]
      rfl

end RepresentationBridge

/-- A local representing candidate with its marking in the original family. -/
structure LocalPointCover {B : Scheme.{u}} (b : B ⟶ S) where
  space : Scheme.{u}
  projection : space ⟶ B
  marking : Marking E (projection ≫ b)

def LocalPointRepresents {B : Scheme.{u}} {b : B ⟶ S} (D : LocalPointCover E b) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ B) (M : Marking E (t ≫ b)),
    ∃! q : SchemeHomOver t D.projection,
      q.val ≫ D.marking.x.val = M.x.val ∧ q.val ≫ D.marking.y.val = M.y.val

section Classifier
variable {B : Scheme.{u}} {b : B ⟶ S} (D : LocalPointCover E b)
    (hD : LocalPointRepresents E D)

def LocalPointCover.classify {T : Scheme.{u}} (t : T ⟶ B) (M : Marking E (t ≫ b)) :
    SchemeHomOver t D.projection := Classical.choose (hD T t M)

lemma LocalPointCover.classify_x {T : Scheme.{u}} (t : T ⟶ B) (M : Marking E (t ≫ b)) :
    (D.classify E hD t M).val ≫ D.marking.x.val = M.x.val :=
  (Classical.choose_spec (hD T t M)).1.1

lemma LocalPointCover.classify_y {T : Scheme.{u}} (t : T ⟶ B) (M : Marking E (t ≫ b)) :
    (D.classify E hD t M).val ≫ D.marking.y.val = M.y.val :=
  (Classical.choose_spec (hD T t M)).1.2

include hD in
lemma LocalPointCover.hom_ext {T : Scheme.{u}} (q r : T ⟶ D.space)
    (hp : q ≫ D.projection = r ≫ D.projection)
    (hx : q ≫ D.marking.x.val = r ≫ D.marking.x.val)
    (hy : q ≫ D.marking.y.val = r ≫ D.marking.y.val) : q = r := by
  let M := (D.marking.pull E r).cast E (Category.assoc r D.projection b).symm
  obtain ⟨v, _, hu⟩ := hD T (r ≫ D.projection) M
  have hq : (⟨q, hp⟩ : SchemeHomOver (r ≫ D.projection) D.projection) = v := by
    apply hu
    simpa only [M, Marking.cast_x, Marking.cast_y, Marking.pull_x, Marking.pull_y] using And.intro hx hy
  have hr : (⟨r, rfl⟩ : SchemeHomOver (r ≫ D.projection) D.projection) = v := by
    apply hu
    simp only [M, Marking.cast_x, Marking.cast_y, Marking.pull_x, Marking.pull_y, and_self]
  exact congrArg Subtype.val (hq.trans hr.symm)

end Classifier

section Transition
variable {B C : Scheme.{u}} {b : B ⟶ S} {c : C ⟶ S}
  (D : LocalPointCover E b) (H : LocalPointCover E c) (hH : LocalPointRepresents E H)
  (a : B ⟶ C) (ha : a ≫ c = b)

/-- The unique transition preserves both actual marking sections. -/
def LocalPointCover.map : D.space ⟶ H.space :=
  (H.classify E hH (D.projection ≫ a)
    (D.marking.cast E (by rw [Category.assoc, ha]))).val

lemma LocalPointCover.map_projection :
    D.map E H hH a ha ≫ H.projection = D.projection ≫ a :=
  (H.classify E hH (D.projection ≫ a) _).property

lemma LocalPointCover.map_x : D.map E H hH a ha ≫ H.marking.x.val = D.marking.x.val := by
  exact (H.classify_x E hH _ _).trans (Marking.cast_x E _ _)

lemma LocalPointCover.map_y : D.map E H hH a ha ≫ H.marking.y.val = D.marking.y.val := by
  exact (H.classify_y E hH _ _).trans (Marking.cast_y E _ _)

end Transition

lemma LocalPointCover.map_id {B : Scheme.{u}} {b : B ⟶ S}
    (D : LocalPointCover E b) (hD : LocalPointRepresents E D) :
    D.map E D hD (𝟙 B) (Category.id_comp b) = 𝟙 D.space := by
  apply D.hom_ext E hD
  · rw [LocalPointCover.map_projection, Category.comp_id, Category.id_comp]
  · rw [LocalPointCover.map_x, Category.id_comp]
  · rw [LocalPointCover.map_y, Category.id_comp]

lemma LocalPointCover.map_comp {B C V : Scheme.{u}} {b : B ⟶ S} {c : C ⟶ S} {v : V ⟶ S}
    (D : LocalPointCover E b) (H : LocalPointCover E c) (K : LocalPointCover E v)
    (hH : LocalPointRepresents E H) (hK : LocalPointRepresents E K)
    (a : B ⟶ C) (ha : a ≫ c = b) (a' : C ⟶ V) (ha' : a' ≫ v = c) :
    D.map E K hK (a ≫ a') (by rw [Category.assoc, ha', ha]) =
      D.map E H hH a ha ≫ H.map E K hK a' ha' := by
  apply K.hom_ext E hK
  · simp only [Category.assoc, LocalPointCover.map_projection]
    rw [← Category.assoc (D.map E H hH a ha) H.projection a',
      LocalPointCover.map_projection, Category.assoc]
  · simp only [Category.assoc, LocalPointCover.map_x]
  · simp only [Category.assoc, LocalPointCover.map_y]

lemma LocalPointCover.map_isPullback {B C : Scheme.{u}} {b : B ⟶ S} {c : C ⟶ S}
    (D : LocalPointCover E b) (H : LocalPointCover E c)
    (hD : LocalPointRepresents E D) (hH : LocalPointRepresents E H)
    (a : B ⟶ C) (ha : a ≫ c = b) :
    IsPullback (D.map E H hH a ha) D.projection H.projection a := by
  let M (s : PullbackCone H.projection a) : Marking E (s.snd ≫ b) :=
    (H.marking.pull E s.fst).cast E
      (by rw [← Category.assoc, s.condition, Category.assoc, ha])
  let l (s : PullbackCone H.projection a) := D.classify E hD s.snd (M s)
  have lx (s : PullbackCone H.projection a) :
      (l s).val ≫ D.marking.x.val = s.fst ≫ H.marking.x.val := by
    simpa only [l, M, Marking.cast_x, Marking.pull_x] using D.classify_x E hD s.snd (M s)
  have ly (s : PullbackCone H.projection a) :
      (l s).val ≫ D.marking.y.val = s.fst ≫ H.marking.y.val := by
    simpa only [l, M, Marking.cast_y, Marking.pull_y] using D.classify_y E hD s.snd (M s)
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk (D.map_projection E H hH a ha)
    (fun s => (l s).val) (fun s => ?_) (fun s => (l s).property) (fun s m hm hp => ?_))
  · apply H.hom_ext E hH
    · rw [Category.assoc, LocalPointCover.map_projection, ← Category.assoc,
        (l s).property, s.condition]
    · rw [Category.assoc, LocalPointCover.map_x, lx]
    · rw [Category.assoc, LocalPointCover.map_y, ly]
  · apply D.hom_ext E hD
    · exact hp.trans (l s).property.symm
    · rw [lx, ← LocalPointCover.map_x E D H hH a ha, ← Category.assoc, hm]
    · rw [ly, ← LocalPointCover.map_y E D H hH a ha, ← Category.assoc, hm]

section LocalRepresentation
variable {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f) (D : PointCover F)

def localPointCover : LocalPointCover E b where
  space := D.space
  projection := D.projection
  marking := (relativeMarkingEquiv E F b f hc D.projection).symm D.marking

lemma localPointCover_x :
    D.marking.x.val ≫ f = (localPointCover E F b f hc D).marking.x.val := by
  have h := relativeMarkingEquiv_x E F b f hc D.projection
    ((relativeMarkingEquiv E F b f hc D.projection).symm D.marking)
  simpa only [localPointCover, Equiv.apply_symm_apply] using h

lemma localPointCover_y :
    D.marking.y.val ≫ f = (localPointCover E F b f hc D).marking.y.val := by
  have h := relativeMarkingEquiv_y E F b f hc D.projection
    ((relativeMarkingEquiv E F b f hc D.projection).symm D.marking)
  simpa only [localPointCover, Equiv.apply_symm_apply] using h

lemma localPointCover_represents (hD : PointRepresents F D) :
    LocalPointRepresents E (localPointCover E F b f hc D) := by
  intro T t M
  let N := relativeMarkingEquiv E F b f hc t M
  obtain ⟨q, hq, hu⟩ := hD T t N
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · rw [← localPointCover_x, ← Category.assoc, hq.1]
    exact relativeMarkingEquiv_x E F b f hc t M
  · rw [← localPointCover_y, ← Category.assoc, hq.2]
    exact relativeMarkingEquiv_y E F b f hc t M
  · intro q' hq'
    apply hu q'
    constructor
    · apply hc.1.hom_ext
      · rw [Category.assoc, localPointCover_x E F b f hc D, hq'.1]
        exact (relativeMarkingEquiv_x E F b f hc t M).symm
      · rw [Category.assoc, D.marking.x.property]
        exact q'.property.trans N.x.property.symm
    · apply hc.1.hom_ext
      · rw [Category.assoc, localPointCover_y E F b f hc D, hq'.2]
        exact (relativeMarkingEquiv_y E F b f hc t M).symm
      · rw [Category.assoc, D.marking.y.property]
        exact q'.property.trans N.y.property.symm

end LocalRepresentation

section LocalExistence
variable {k : Type u} [Field k] [CharZero k] {σ : S ⟶ Base k}
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

/-- Local existence, with all test markings expressed in the original scheme family. -/
lemma exists_local_point_cover (s : S) :
    ∃ (P : LocalPresentation k S σ E) (D : LocalPointCover E P.base),
      s ∈ Set.range P.base ∧ LocalPointRepresents E D := by
  obtain ⟨P, hP⟩ := scheme_local_weierstrass k S σ E s
  have hc : Cartesian E (SchemeLocalClassifier.family P) P.base P.comparison :=
    ⟨P.cartesian, by rw [SchemeLocalClassifier.family_zero]; exact P.zero_eq, P.mul_eq⟩
  exact ⟨P, localPointCover E (SchemeLocalClassifier.family P) P.base P.comparison hc
    (affinePointCover E P), hP,
    localPointCover_represents E _ _ _ hc _ (affinePointCover_represents E P)⟩

end LocalExistence

section Restriction
variable {B C : Scheme.{u}} {b : B ⟶ S} (D : LocalPointCover E b) (a : C ⟶ B)

/-- Restrict the representing candidate by an actual scheme pullback. -/
def LocalPointCover.baseChange : LocalPointCover E (a ≫ b) where
  space := pullback D.projection a
  projection := pullback.snd D.projection a
  marking := ((D.marking.pull E (pullback.fst D.projection a)).cast E
    (by rw [← Category.assoc, pullback.condition, Category.assoc]))

@[simp] lemma LocalPointCover.baseChange_x :
    (D.baseChange E a).marking.x.val = pullback.fst D.projection a ≫ D.marking.x.val := by
  dsimp only [LocalPointCover.baseChange]
  rw [Marking.cast_x, Marking.pull_x]

@[simp] lemma LocalPointCover.baseChange_y :
    (D.baseChange E a).marking.y.val = pullback.fst D.projection a ≫ D.marking.y.val := by
  dsimp only [LocalPointCover.baseChange]
  rw [Marking.cast_y, Marking.pull_y]

lemma LocalPointCover.baseChange_represents (hD : LocalPointRepresents E D) :
    LocalPointRepresents E (D.baseChange E a) := by
  intro T t M
  let N := M.cast E (Category.assoc t a b).symm
  obtain ⟨q, hq, hu⟩ := hD T (t ≫ a) N
  let r : SchemeHomOver t (D.baseChange E a).projection :=
    ⟨pullback.lift q.val t q.property, pullback.lift_snd _ _ _⟩
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · rw [LocalPointCover.baseChange_x]
    change pullback.lift _ _ _ ≫ _ ≫ _ = _
    rw [pullback.lift_fst_assoc, hq.1]
    exact Marking.cast_x E _ _
  · rw [LocalPointCover.baseChange_y]
    change pullback.lift _ _ _ ≫ _ ≫ _ = _
    rw [pullback.lift_fst_assoc, hq.2]
    exact Marking.cast_y E _ _
  · intro r' hr'
    have he : r'.val ≫ pullback.fst D.projection a = q.val := by
      have hp : (r'.val ≫ pullback.fst D.projection a) ≫ D.projection = t ≫ a := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (r'.val ≫ (D.baseChange E a).projection) ≫ a = t ≫ a
        rw [r'.property]
      apply congrArg Subtype.val (hu ⟨r'.val ≫ pullback.fst D.projection a, hp⟩ ?_)
      constructor
      · simpa only [LocalPointCover.baseChange_x, Category.assoc, N, Marking.cast_x] using hr'.1
      · simpa only [LocalPointCover.baseChange_y, Category.assoc, N, Marking.cast_y] using hr'.2
    apply Subtype.ext
    apply pullback.hom_ext
    · exact he.trans (pullback.lift_fst q.val t q.property).symm
    · exact r'.property.trans (pullback.lift_snd q.val t q.property).symm

end Restriction

def LocalPointCover.cast {B : Scheme.{u}} {b b' : B ⟶ S} (h : b = b')
    (D : LocalPointCover E b) : LocalPointCover E b' := h ▸ D

lemma LocalPointCover.cast_represents {B : Scheme.{u}} {b b' : B ⟶ S} (h : b = b')
    (D : LocalPointCover E b) (hD : LocalPointRepresents E D) :
    LocalPointRepresents E (D.cast E h) := by subst b'; exact hD

/-- Open subsets on which the marking functor is already represented. -/
def GoodOpen (U : S.Opens) : Prop :=
  ∃ D : LocalPointCover E U.ι, LocalPointRepresents E D

lemma goodOpen_mono {U V : S.Opens} (h : V ≤ U) (hU : GoodOpen E U) : GoodOpen E V := by
  obtain ⟨D, hD⟩ := hU
  let D' := D.baseChange E (S.homOfLE h)
  have e : S.homOfLE h ≫ U.ι = V.ι := Scheme.homOfLE_ι S h
  exact ⟨D'.cast E e,
    LocalPointCover.cast_represents E e D' (D.baseChange_represents E _ hD)⟩

section GoodCover
variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

include k σ in
lemma exists_goodOpen (s : S) : ∃ U : S.Opens, GoodOpen E U ∧ s ∈ U := by
  obtain ⟨P, D, hs, hD⟩ := exists_local_point_cover E (σ := σ) s
  letI := P.openImmersion
  let a := P.base.isoOpensRange.inv
  have e : a ≫ P.base = P.base.opensRange.ι := Scheme.Hom.isoOpensRange_inv_comp P.base
  refine ⟨P.base.opensRange, ?_, hs⟩
  exact ⟨(D.baseChange E a).cast E e,
    LocalPointCover.cast_represents E e _ (D.baseChange_represents E a hD)⟩

include k σ in
lemma goodOpen_basis : TopologicalSpace.Opens.IsBasis {U : S.Opens | GoodOpen E U} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U s hs
  obtain ⟨V, hV, hv⟩ := exists_goodOpen E k σ s
  exact ⟨U ⊓ V, goodOpen_mono E inf_le_right hV, ⟨hs, hv⟩, inf_le_left⟩

def goodCover : S.OpenCover where
  I₀ := {U : S.Opens // GoodOpen E U}
  X U := U.val.toScheme
  f U := U.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun s => ?_, fun U => inferInstance⟩
    obtain ⟨U, hU, hs⟩ := exists_goodOpen E k σ s
    exact ⟨⟨U, hU⟩, ⟨⟨s, hs⟩, rfl⟩⟩

instance goodCover_preorder : Preorder (goodCover E k σ).I₀ :=
  inferInstanceAs (Preorder {U : S.Opens // GoodOpen E U})

instance goodCover_locallyDirected : (goodCover E k σ).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
    (by intros; change _ ↔ _; simp only [goodCover, Scheme.Opens.opensRange_ι]; rfl)
    (by
      convert goodOpen_basis E k σ using 1
      ext U
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨V, hV⟩
        have h : V.val = U := by simpa [goodCover] using hV
        exact h ▸ V.property
      · intro hU
        exact ⟨⟨U, hU⟩, by simp [goodCover]⟩)

end GoodCover

section Gluing
variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

def provider (i : (goodCover E k σ).I₀) : LocalPointCover E ((goodCover E k σ).f i) :=
  Classical.choose i.property

lemma provider_represents (i : (goodCover E k σ).I₀) :
    LocalPointRepresents E (provider E k σ i) := Classical.choose_spec i.property

def coverFunctor : (goodCover E k σ).I₀ ⥤ Scheme.{u} where
  obj i := (provider E k σ i).space
  map {i j} h := (provider E k σ i).map E (provider E k σ j)
    (provider_represents E k σ j) ((goodCover E k σ).trans h) ((goodCover E k σ).trans_map h)
  map_id i := by
    simpa only [Scheme.Cover.trans_id] using
      (provider E k σ i).map_id E (provider_represents E k σ i)
  map_comp {i j l} h h' := by
    simpa only [Scheme.Cover.trans_comp] using
      (provider E k σ i).map_comp E (provider E k σ j) (provider E k σ l)
        (provider_represents E k σ j) (provider_represents E k σ l)
        ((goodCover E k σ).trans h) ((goodCover E k σ).trans_map h)
        ((goodCover E k σ).trans h') ((goodCover E k σ).trans_map h')

def gluingData : Scheme.Cover.RelativeGluingData (goodCover E k σ) where
  functor := coverFunctor E k σ
  natTrans := {
    app i := (provider E k σ i).projection
    naturality {i j} h := (provider E k σ i).map_projection E (provider E k σ j)
      (provider_represents E k σ j) ((goodCover E k σ).trans h)
        ((goodCover E k σ).trans_map h) }
  equifibered {i j} h := (provider E k σ i).map_isPullback E (provider E k σ j)
    (provider_represents E k σ i) (provider_represents E k σ j)
    ((goodCover E k σ).trans h) ((goodCover E k σ).trans_map h)

def gluedX : (gluingData E k σ).glued ⟶ E.curve :=
  colimit.desc (gluingData E k σ).functor {
    pt := E.curve
    ι := {
      app i := (provider E k σ i).marking.x.val
      naturality {i j} h := by
        change _ = _ ≫ 𝟙 E.curve
        rw [Category.comp_id]
        exact
          (provider E k σ i).map_x E (provider E k σ j) (provider_represents E k σ j) ((goodCover E k σ).trans h)
            ((goodCover E k σ).trans_map h) } }

def gluedY : (gluingData E k σ).glued ⟶ E.curve :=
  colimit.desc (gluingData E k σ).functor {
    pt := E.curve
    ι := {
      app i := (provider E k σ i).marking.y.val
      naturality {i j} h := by
        change _ = _ ≫ 𝟙 E.curve
        rw [Category.comp_id]
        exact
          (provider E k σ i).map_y E (provider E k σ j) (provider_represents E k σ j) ((goodCover E k σ).trans h)
            ((goodCover E k σ).trans_map h) } }

@[simp] lemma gluedX_local (i : (goodCover E k σ).I₀) :
    colimit.ι (gluingData E k σ).functor i ≫ gluedX E k σ = (provider E k σ i).marking.x.val :=
  colimit.ι_desc _ _

@[simp] lemma gluedY_local (i : (goodCover E k σ).I₀) :
    colimit.ι (gluingData E k σ).functor i ≫ gluedY E k σ = (provider E k σ i).marking.y.val :=
  colimit.ι_desc _ _

lemma gluedX_over : gluedX E k σ ≫ E.p = (gluingData E k σ).toBase := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, gluedX_local, (provider E k σ i).marking.x.property]
  exact ((gluingData E k σ).ι_toBase i).symm

lemma gluedY_over : gluedY E k σ ≫ E.p = (gluingData E k σ).toBase := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, gluedY_local, (provider E k σ i).marking.y.property]
  exact ((gluingData E k σ).ι_toBase i).symm

lemma glued_local_over (i : (goodCover E k σ).I₀) :
    colimit.ι (gluingData E k σ).functor i ≫ (gluingData E k σ).toBase =
      (provider E k σ i).projection ≫ (goodCover E k σ).f i :=
  (gluingData E k σ).ι_toBase i

def gluedPointX : SchemeHomOver (gluingData E k σ).toBase E.p :=
  ⟨gluedX E k σ, gluedX_over E k σ⟩

def gluedPointY : SchemeHomOver (gluingData E k σ).toBase E.p :=
  ⟨gluedY E k σ, gluedY_over E k σ⟩

lemma gluedPointX_local (i : (goodCover E k σ).I₀) :
    GoodReductionJacobian.schemeHomOverComp (colimit.ι (gluingData E k σ).functor i)
      (glued_local_over E k σ i) (gluedPointX E k σ) = (provider E k σ i).marking.x :=
  Subtype.ext (gluedX_local E k σ i)

lemma gluedPointY_local (i : (goodCover E k σ).I₀) :
    GoodReductionJacobian.schemeHomOverComp (colimit.ι (gluingData E k σ).functor i)
      (glued_local_over E k σ i) (gluedPointY E k σ) = (provider E k σ i).marking.y :=
  Subtype.ext (gluedY_local E k σ i)

def gluedMarking : Marking E (gluingData E k σ).toBase where
  x := gluedPointX E k σ
  y := gluedPointY E k σ
  killed_x := by
    apply Subtype.ext
    apply colimit.hom_ext
    intro i
    have h := multiple_natural E _ _ (colimit.ι (gluingData E k σ).functor i)
      (glued_local_over E k σ i) 4 (gluedPointX E k σ)
    rw [gluedPointX_local, (provider E k σ i).marking.killed_x] at h
    exact congrArg Subtype.val (h.trans (SchemeLocal.one_natural E.law _ _
      (colimit.ι (gluingData E k σ).functor i) (glued_local_over E k σ i)).symm)
  killed_y := by
    apply Subtype.ext
    apply colimit.hom_ext
    intro i
    have h := multiple_natural E _ _ (colimit.ι (gluingData E k σ).functor i)
      (glued_local_over E k σ i) 4 (gluedPointY E k σ)
    rw [gluedPointY_local, (provider E k σ i).marking.killed_y] at h
    exact congrArg Subtype.val (h.trans (SchemeLocal.one_natural E.law _ _
      (colimit.ι (gluingData E k σ).functor i) (glued_local_over E k σ i)).symm)
  avoids := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    obtain ⟨i, zi, hi⟩ : ∃ (i : (goodCover E k σ).I₀)
        (zi : (provider E k σ i).space),
        (colimit.ι (gluingData E k σ).functor i) zi = z :=
      Scheme.IsLocallyDirected.ι_jointly_surjective (gluingData E k σ).functor z
    have h := congrArg Subtype.val (E.law.mul_natural _ _
      (colimit.ι (gluingData E k σ).functor i) (glued_local_over E k σ i)
      (multiple E _ n.val (gluedPointX E k σ)) (multiple E _ m.val (gluedPointY E k σ)))
    rw [multiple_natural, multiple_natural, gluedPointX_local, gluedPointY_local] at h
    apply Set.disjoint_left.mp ((provider E k σ i).marking.avoids n m hnm)
      (Set.mem_range_self zi)
    rw [← h]
    change (E.law.mul _ (multiple E _ n.val (gluedPointX E k σ))
      (multiple E _ m.val (gluedPointY E k σ))).val
        ((colimit.ι (gluingData E k σ).functor i) zi) ∈ Set.range E.zero
    change (colimit.ι (gluingData E k σ).functor i) zi = z at hi
    rw [hi]
    exact hz

def gluedPointCover : PointCover E where
  space := (gluingData E k σ).glued
  projection := (gluingData E k σ).toBase
  marking := gluedMarking E k σ

variable {T : Scheme.{u}} (t : T ⟶ S) (M : Marking E t)

def testClassifier (i : (goodCover E k σ).I₀) :
    SchemeHomOver (pullback.snd t ((goodCover E k σ).f i)) (provider E k σ i).projection :=
  (provider E k σ i).classify E (provider_represents E k σ i) _
    ((M.pull E (pullback.fst t ((goodCover E k σ).f i))).cast E pullback.condition)

lemma testClassifier_x (i : (goodCover E k σ).I₀) :
    (testClassifier E k σ t M i).val ≫ (provider E k σ i).marking.x.val =
      pullback.fst t ((goodCover E k σ).f i) ≫ M.x.val := by
  exact ((provider E k σ i).classify_x E (provider_represents E k σ i) _ _).trans
    (Marking.cast_x E _ _)

lemma testClassifier_y (i : (goodCover E k σ).I₀) :
    (testClassifier E k σ t M i).val ≫ (provider E k σ i).marking.y.val =
      pullback.fst t ((goodCover E k σ).f i) ≫ M.y.val := by
  exact ((provider E k σ i).classify_y E (provider_represents E k σ i) _ _).trans
    (Marking.cast_y E _ _)

abbrev testCover : T.OpenCover := (goodCover E k σ).pullback₁ t

lemma testCover_trans_fst {i j : (goodCover E k σ).I₀} (h : i ⟶ j) :
    (testCover E k σ t).trans h ≫ pullback.fst t ((goodCover E k σ).f j) =
      pullback.fst t ((goodCover E k σ).f i) :=
  (testCover E k σ t).trans_map h

lemma testCover_trans_snd {i j : (goodCover E k σ).I₀} (h : i ⟶ j) :
    (testCover E k σ t).trans h ≫ pullback.snd t ((goodCover E k σ).f j) =
      pullback.snd t ((goodCover E k σ).f i) ≫ (goodCover E k σ).trans h := by
  apply (cancel_mono ((goodCover E k σ).f j)).mp
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, testCover_trans_fst,
    Category.assoc, Scheme.Cover.trans_map, pullback.condition]

lemma testClassifier_trans {i j : (goodCover E k σ).I₀} (h : i ⟶ j) :
    (testCover E k σ t).trans h ≫ (testClassifier E k σ t M j).val =
      (testClassifier E k σ t M i).val ≫ (gluingData E k σ).functor.map h := by
  have hp : (gluingData E k σ).functor.map h ≫ (provider E k σ j).projection =
      (provider E k σ i).projection ≫ (goodCover E k σ).trans h :=
    (provider E k σ i).map_projection E (provider E k σ j)
      (provider_represents E k σ j) _ ((goodCover E k σ).trans_map h)
  have hx : (gluingData E k σ).functor.map h ≫ (provider E k σ j).marking.x.val =
      (provider E k σ i).marking.x.val :=
    (provider E k σ i).map_x E (provider E k σ j)
      (provider_represents E k σ j) _ ((goodCover E k σ).trans_map h)
  have hy : (gluingData E k σ).functor.map h ≫ (provider E k σ j).marking.y.val =
      (provider E k σ i).marking.y.val :=
    (provider E k σ i).map_y E (provider E k σ j)
      (provider_represents E k σ j) _ ((goodCover E k σ).trans_map h)
  apply (provider E k σ j).hom_ext E (provider_represents E k σ j)
  · rw [Category.assoc, (testClassifier E k σ t M j).property, testCover_trans_snd,
      Category.assoc, hp, ← Category.assoc, (testClassifier E k σ t M i).property]
  · rw [Category.assoc, testClassifier_x, ← Category.assoc, testCover_trans_fst,
      Category.assoc, hx, testClassifier_x]
  · rw [Category.assoc, testClassifier_y, ← Category.assoc, testCover_trans_fst,
      Category.assoc, hy, testClassifier_y]

def testMap (i : (goodCover E k σ).I₀) :
    pullback t ((goodCover E k σ).f i) ⟶ (gluingData E k σ).glued :=
  (testClassifier E k σ t M i).val ≫ colimit.ι (gluingData E k σ).functor i

lemma testMap_trans {i j : (goodCover E k σ).I₀} (h : i ⟶ j) :
    (testCover E k σ t).trans h ≫ testMap E k σ t M j = testMap E k σ t M i := by
  dsimp only [testMap]
  rw [← Category.assoc, testClassifier_trans, Category.assoc, colimit.w]

def globalClassifier : T ⟶ (gluingData E k σ).glued :=
  (testCover E k σ t).glueMorphismsOfLocallyDirected
    (testMap E k σ t M) (testMap_trans E k σ t M)

lemma globalClassifier_local (i : (goodCover E k σ).I₀) :
    pullback.fst t ((goodCover E k σ).f i) ≫ globalClassifier E k σ t M = testMap E k σ t M i :=
  (testCover E k σ t).map_glueMorphismsOfLocallyDirected _ _ i

lemma globalClassifier_over : globalClassifier E k σ t M ≫ (gluingData E k σ).toBase = t := by
  apply (testCover E k σ t).hom_ext
  intro i
  change pullback.fst t ((goodCover E k σ).f i) ≫ _ = _
  rw [← Category.assoc, globalClassifier_local]
  change ((testClassifier E k σ t M i).val ≫ colimit.ι (gluingData E k σ).functor i) ≫ _ = _
  rw [Category.assoc, glued_local_over, ← Category.assoc, (testClassifier E k σ t M i).property]
  exact pullback.condition.symm

lemma globalClassifier_x : globalClassifier E k σ t M ≫ gluedX E k σ = M.x.val := by
  apply (testCover E k σ t).hom_ext
  intro i
  change pullback.fst t ((goodCover E k σ).f i) ≫ _ = _
  rw [← Category.assoc, globalClassifier_local]
  change ((testClassifier E k σ t M i).val ≫ colimit.ι (gluingData E k σ).functor i) ≫ _ = _
  rw [Category.assoc, gluedX_local, testClassifier_x]
  rfl

lemma globalClassifier_y : globalClassifier E k σ t M ≫ gluedY E k σ = M.y.val := by
  apply (testCover E k σ t).hom_ext
  intro i
  change pullback.fst t ((goodCover E k σ).f i) ≫ _ = _
  rw [← Category.assoc, globalClassifier_local]
  change ((testClassifier E k σ t M i).val ≫ colimit.ι (gluingData E k σ).functor i) ≫ _ = _
  rw [Category.assoc, gluedY_local, testClassifier_y]
  rfl

lemma globalClassifier_unique (r : T ⟶ (gluingData E k σ).glued)
    (hr : r ≫ (gluingData E k σ).toBase = t)
    (hx : r ≫ gluedX E k σ = M.x.val) (hy : r ≫ gluedY E k σ = M.y.val) :
    r = globalClassifier E k σ t M := by
  apply (testCover E k σ t).hom_ext
  intro i
  change pullback.fst t ((goodCover E k σ).f i) ≫ r =
    pullback.fst t ((goodCover E k σ).f i) ≫ globalClassifier E k σ t M
  have hp : IsPullback (provider E k σ i).projection
      (colimit.ι (gluingData E k σ).functor i) ((goodCover E k σ).f i)
      (gluingData E k σ).toBase := (gluingData E k σ).isPullback_natTrans_ι_toBase i
  have e : pullback.snd t ((goodCover E k σ).f i) ≫ (goodCover E k σ).f i =
      (pullback.fst t ((goodCover E k σ).f i) ≫ r) ≫ (gluingData E k σ).toBase := by
    rw [Category.assoc, hr]
    exact pullback.condition.symm
  let l := hp.lift (pullback.snd t ((goodCover E k σ).f i))
    (pullback.fst t ((goodCover E k σ).f i) ≫ r) e
  have lp : l ≫ (provider E k σ i).projection = pullback.snd t ((goodCover E k σ).f i) :=
    hp.lift_fst _ _ _
  have li : l ≫ colimit.ι (gluingData E k σ).functor i =
      pullback.fst t ((goodCover E k σ).f i) ≫ r := hp.lift_snd _ _ _
  have le : l = (testClassifier E k σ t M i).val := by
    apply (provider E k σ i).hom_ext E (provider_represents E k σ i)
    · exact lp.trans (testClassifier E k σ t M i).property.symm
    · calc
        l ≫ (provider E k σ i).marking.x.val =
            l ≫ colimit.ι (gluingData E k σ).functor i ≫ gluedX E k σ := by rw [gluedX_local]
        _ = (pullback.fst t ((goodCover E k σ).f i) ≫ r) ≫ gluedX E k σ := by
          rw [← Category.assoc, li]
        _ = pullback.fst t ((goodCover E k σ).f i) ≫ M.x.val := by rw [Category.assoc, hx]
        _ = (testClassifier E k σ t M i).val ≫ (provider E k σ i).marking.x.val :=
          (testClassifier_x E k σ t M i).symm
    · calc
        l ≫ (provider E k σ i).marking.y.val =
            l ≫ colimit.ι (gluingData E k σ).functor i ≫ gluedY E k σ := by rw [gluedY_local]
        _ = (pullback.fst t ((goodCover E k σ).f i) ≫ r) ≫ gluedY E k σ := by
          rw [← Category.assoc, li]
        _ = pullback.fst t ((goodCover E k σ).f i) ≫ M.y.val := by rw [Category.assoc, hy]
        _ = (testClassifier E k σ t M i).val ≫ (provider E k σ i).marking.y.val :=
          (testClassifier_y E k σ t M i).symm
  rw [← li, le, globalClassifier_local]
  rfl

lemma gluedPointCover_represents : PointRepresents E (gluedPointCover E k σ) := by
  intro T t M
  refine ⟨⟨globalClassifier E k σ t M, globalClassifier_over E k σ t M⟩,
    ⟨globalClassifier_x E k σ t M, globalClassifier_y E k σ t M⟩, ?_⟩
  intro r hr
  apply Subtype.ext
  exact globalClassifier_unique E k σ t M r.val r.property hr.1 hr.2

end Gluing

#print axioms liftMarking
#print axioms Marking.pull
#print axioms markingEquiv
#print axioms affineMarkingEquiv
#print axioms affinePointCover_represents
#print axioms PointCover.toCover_represents
#print axioms relativeMarkingEquiv
#print axioms exists_local_point_cover
#print axioms LocalPointCover.baseChange_represents
#print axioms goodCover_locallyDirected
#print axioms gluingData
#print axioms gluedPointCover
#print axioms globalClassifier_x
end SchemeFourCover

/-- The full-four marking functor of every characteristic-zero scheme family is represented. -/
theorem scheme_four_cover :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∃ D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E,
        ArithmeticThetaEvenMarkingTorsorR0216.Represents E D := by
  intro k _ _ S σ E
  exact ⟨(SchemeFourCover.gluedPointCover E k σ).toCover E,
    SchemeFourCover.PointCover.toCover_represents E k σ _
      (SchemeFourCover.gluedPointCover_represents E k σ)⟩

#print axioms scheme_four_cover
end ArithmeticThetaEvenMarkingTorsorR0216
