import ClassifiedTateDiskTransferR0235
import TateCoordinateConstantMapR0235
import TateMarkingConstantTransferR0235
import RootTestPullbackCoherenceR0196

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaBoundaryConstantsR0235
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelConstantsR0234
namespace CompactHodgeConstantComparison
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]

/-- The actual pullback line, equipped with the prescribed open comparison. -/
def pullbackExtension (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) : Extension l L E Y where
  line := (Scheme.Modules.pullback F).obj H.line
  invertible := H.invertible.pullback F
  onOpen := squarePullbackIso Y.inclusion F f X.inclusion hF.2 H.line ≪≫
    (Scheme.Modules.pullback f).mapIso H.onOpen ≪≫ e

lemma compatible_iff (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) :
    CompactCompatible ι f F hF e H J a ↔
      (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom =
        (pullbackExtension ι f F hF e H).onOpen.hom := by
  simp only [CompactCompatible, pullbackExtension, squarePullbackIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

/-- Compatibility with the open identification forces compatibility with the
actual generic comparison on every target disk. -/
lemma compatible_diskGeneric (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (ha : CompactCompatible ι f F hF e H J a) (S : DiskTest l L E Y) :
    (Scheme.Modules.pullback (genericInclusion l)).map
        ((Scheme.Modules.pullback S.disk).map a.hom) ≫ (diskGenericIso l L J S).hom =
      (diskGenericIso l L (pullbackExtension ι f F hF e H) S).hom :=
  diskGenericIso_naturality l L (pullbackExtension ι f F hF e H) J S a.hom
    ((compatible_iff ι f F hF e H J a).mp ha)

/-- The full integral section is determined by its Laurent-series restriction.
Only one of the sections needs to be a frame. -/
lemma disk_section_eq_of_generic {L : ℕ} {E : LevelData l L}
    {Y : Compactification l L E} (J : Extension l L E Y) (S : DiskTest l L E Y)
    (η ξ : Γ((Scheme.Modules.pullback S.disk).obj J.line, ⊤))
    (hξ : IsFrame ((Scheme.Modules.pullback S.disk).obj J.line) ⊤ ξ)
    (h : res _ (V := ⊤) (by simp) ((diskGenericIso l L J S).hom.app _
      (Scheme.Modules.pullbackLocalSection (genericInclusion l) η)) =
      res _ (by simp) ((diskGenericIso l L J S).hom.app _
      (Scheme.Modules.pullbackLocalSection (genericInclusion l) ξ))) : η = ξ := by
  letI := generic_schematic l
  letI : QuasiCompact (genericInclusion l) := by
    unfold genericInclusion
    infer_instance
  apply pullback_injective_of_frame (genericInclusion l) _ ξ hξ
  apply (ConcreteCategory.bijective_of_isIso
    ((diskGenericIso l L J S).hom.app ((genericInclusion l) ⁻¹ᵁ ⊤))).1
  exact (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.res_bijective _
    (by simp) le_top).1 h

/-- Naturality of pullback composition under equality of the inner map. -/
lemma comp_congr_right {A B C : Scheme.{0}} (a : A ⟶ B)
    {b c : B ⟶ C} (h : b = c) (M : C.Modules) :
    (Scheme.Modules.pullback a).map (pullbackEqIso h M).hom ≫
      ((Scheme.Modules.pullbackComp a c).app M).hom =
    ((Scheme.Modules.pullbackComp a b).app M).hom ≫
      (pullbackEqIso (congrArg (fun q => a ≫ q) h) M).hom := by
  subst c
  simp [pullbackEqIso]

lemma comp_congr_left {A B C : Scheme.{0}} {a b : A ⟶ B}
    (h : a = b) (c : B ⟶ C) (M : C.Modules) :
    (pullbackEqIso h ((Scheme.Modules.pullback c).obj M)).hom ≫
      ((Scheme.Modules.pullbackComp b c).app M).hom =
    ((Scheme.Modules.pullbackComp a c).app M).hom ≫
      (pullbackEqIso (congrArg (fun q => q ≫ c) h) M).hom := by
  subst b
  simp [pullbackEqIso]

lemma eqIso_trans {A B : Scheme.{0}} {a b c : A ⟶ B}
    (h : a = b) (h' : b = c) (M : B.Modules) :
    (pullbackEqIso h M).hom ≫ (pullbackEqIso h' M).hom =
      (pullbackEqIso (h.trans h') M).hom := by
  subst b; subst c
  simp [pullbackEqIso]

/-- A fixed right-associated presentation of three successive pullbacks. -/
def tripleComp {A B C D : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (M : D.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pullback c).obj M)) ≅
      (Scheme.Modules.pullback (a ≫ (b ≫ c))).obj M :=
  (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b c).app M) ≪≫
    (Scheme.Modules.pullbackComp a (b ≫ c)).app M

lemma tripleComp_assoc {A B C D : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (M : D.Modules) :
    (tripleComp a b c M).hom =
      ((Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback c).obj M)).hom ≫
      ((Scheme.Modules.pullbackComp (a ≫ b) c).app M).hom ≫
      (pullbackEqIso (Category.assoc a b c) M).hom := by
  exact ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_assoc a b c M

/-- Collapse a pulled-back square, retaining the parenthesized map equality. -/
@[reassoc]
lemma square_post {A B C D E : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : B ⟶ D) (e : D ⟶ E)
    (h : b ≫ c = d ≫ e) (M : E.Modules) :
    (Scheme.Modules.pullback a).map (squarePullbackIso b c d e h M).hom ≫
      (tripleComp a d e M).hom =
    (tripleComp a b c M).hom ≫
      (pullbackEqIso (congrArg (fun q => a ≫ q) h) M).hom := by
  simp only [tripleComp, squarePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback a).map
    ((Scheme.Modules.pullbackComp d e).app M).inv), ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [comp_congr_right]

@[reassoc]
lemma square_pre {A B C D E : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D) (e : D ⟶ E)
    (h : a ≫ b = c ≫ d) (M : E.Modules) :
    (squarePullbackIso a b c d h ((Scheme.Modules.pullback e).obj M)).hom ≫
      (tripleComp c d e M).hom =
    (tripleComp a b e M).hom ≫
      (pullbackEqIso ((Category.assoc a b e).symm.trans
        ((congrArg (fun q => q ≫ e) h).trans (Category.assoc c d e))) M).hom := by
  rw [tripleComp_assoc, tripleComp_assoc]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc (pullbackEqIso h _).hom, comp_congr_left]
  simp only [Category.assoc, eqIso_trans]

/-- Coherence of the actual coefficient disk/open cube. -/
lemma square_cube {A B C D E G H I : Scheme.{0}}
    (u : A ⟶ B) (v : B ⟶ C) (w : C ⟶ H)
    (s : B ⟶ D) (t : D ⟶ H)
    (p : A ⟶ E) (q : E ⟶ C)
    (r : A ⟶ G) (i : G ⟶ D) (f : G ⟶ I)
    (z : E ⟶ I) (j : I ⟶ H)
    (h₁ : v ≫ w = s ≫ t) (h₂ : u ≫ s = r ≫ i)
    (h₃ : i ≫ t = f ≫ j) (h₄ : u ≫ v = p ≫ q)
    (h₅ : q ≫ w = z ≫ j) (h₆ : p ≫ z = r ≫ f)
    (M : H.Modules) :
    (Scheme.Modules.pullback u).map (squarePullbackIso v w s t h₁ M).hom ≫
      (squarePullbackIso u s r i h₂ ((Scheme.Modules.pullback t).obj M)).hom ≫
      (Scheme.Modules.pullback r).map (squarePullbackIso i t f j h₃ M).hom =
    (squarePullbackIso u v p q h₄ ((Scheme.Modules.pullback w).obj M)).hom ≫
      (Scheme.Modules.pullback p).map (squarePullbackIso q w z j h₅ M).hom ≫
      (squarePullbackIso p z r f h₆ ((Scheme.Modules.pullback j).obj M)).hom := by
  apply (cancel_mono (tripleComp r f j M).hom).mp
  simp only [Category.assoc]
  rw [square_post, square_pre, square_pre_assoc, square_post_assoc,
    square_post_assoc, square_pre_assoc]
  simp only [Category.assoc, eqIso_trans]

/-- Schematic density detects maps into an invertible sheaf. -/
lemma hom_eq_of_pullback {X Y : Scheme.{0}} (p : Y ⟶ X)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    (a b : M ⟶ N) (h : (Scheme.Modules.pullback p).map a =
      (Scheme.Modules.pullback p).map b) : a = b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.pullback_local_injective_of_invertible
    p N hN U
  change Scheme.Modules.pullbackLocalSection p (a.app U s) =
    Scheme.Modules.pullbackLocalSection p (b.app U s)
  rw [Scheme.Modules.pullbackLocalSection_app, Scheme.Modules.pullbackLocalSection_app, h]

/-- At most one compact comparison extends the supplied open comparison,
without assuming algebraic closure or canonicity. -/
lemma compact_comparison_unique (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a b : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (ha : CompactCompatible ι f F hF e H J a)
    (hb : CompactCompatible ι f F hF e H J b) : a = b := by
  letI := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.inclusion_schematic l L E Y
  letI := compact_noetherian l L E Y
  letI := Y.openImmersion
  apply Iso.ext
  apply hom_eq_of_pullback Y.inclusion J.invertible
  apply (cancel_mono J.onOpen.hom).mp
  exact ha.trans hb.symm

/-- The disk comparison uses exactly the specified compact isomorphism. -/
def diskComparison (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (H : Extension k L D X) (J : Extension l L E Y)
    (F : Y.space ⟶ X.space) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.disk ≫ F = diskMap ι ≫ T.disk) :
    (Scheme.Modules.pullback (diskMap ι)).obj ((Scheme.Modules.pullback T.disk).obj H.line) ≅
      (Scheme.Modules.pullback S.disk).obj J.line :=
  squarePullbackIso (diskMap ι) T.disk S.disk F h.symm H.line ≪≫
    (Scheme.Modules.pullback S.disk).mapIso a

/-- Remove the differential identification to express restriction in the
actual open Hodge fiber. -/
def diskOpenIso {L : ℕ} {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    (Scheme.Modules.pullback (genericInclusion k)).obj
      ((Scheme.Modules.pullback T.disk).obj H.line) ≅
      (Scheme.Modules.pullback T.base).obj (weight D) :=
  squarePullbackIso (genericInclusion k) T.disk T.base X.inclusion T.extends_eq.2.1 H.line ≪≫
    (Scheme.Modules.pullback T.base).mapIso H.onOpen

lemma diskOpenIso_eq {L : ℕ} {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X) :
    (diskOpenIso H T).hom ≫ (openTestIso k L T.toTest).hom =
      (diskGenericIso k L H T).hom := by
  simp only [diskOpenIso, diskGenericIso, squarePullbackIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

/-- The full coefficient cube, followed by the prescribed open Hodge map. -/
lemma disk_open_comparison (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (ha : CompactCompatible ι f F hF e H J a)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.disk ≫ F = diskMap ι ≫ T.disk)
    (hb : S.base ≫ f = punctureMap ι ≫ T.base) :
    (Scheme.Modules.pullback (genericInclusion l)).map (diskComparison ι H J F a T S h).hom ≫
      (diskOpenIso J S).hom =
    (squarePullbackIso (genericInclusion l) (diskMap ι) (punctureMap ι)
      (genericInclusion k) (ClassifiedTateDiskTransfer.generic_square ι)
      ((Scheme.Modules.pullback T.disk).obj H.line)).hom ≫
      (Scheme.Modules.pullback (punctureMap ι)).map (diskOpenIso H T).hom ≫
      (testComparison ι T.toTest S.toTest f e hb).hom := by
  have hn := squarePullbackIso_naturality (genericInclusion l) S.disk S.base Y.inclusion
    S.extends_eq.2.1 a.hom
  have hc := square_cube (genericInclusion l) (diskMap ι) T.disk S.disk F
    (punctureMap ι) (genericInclusion k) S.base Y.inclusion f T.base X.inclusion
    h.symm S.extends_eq.2.1 hF.2 (ClassifiedTateDiskTransfer.generic_square ι)
    T.extends_eq.2.1 hb.symm H.line
  have ht := squarePullbackIso_naturality (punctureMap ι) T.base S.base f hb.symm H.onOpen.hom
  change (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom =
    (squarePullbackIso Y.inclusion F f X.inclusion hF.2 H.line).hom ≫
      (Scheme.Modules.pullback f).map H.onOpen.hom ≫ e.hom at ha
  simp only [diskComparison, diskOpenIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback (genericInclusion l)).map
    ((Scheme.Modules.pullback S.disk).map a.hom)), ← hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  rw [reassoc_of% ht]
  rfl

/-- Naturality on global sections with a fixed top-open presentation. -/
lemma map_section_top {X Y : Scheme.{0}} (p : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback p).map a).app ⊤ (Scheme.Modules.pullbackLocalSection p s) =
      Scheme.Modules.pullbackLocalSection p (a.app ⊤ s) :=
  (Scheme.Modules.pullbackLocalSection_app p a s).symm

lemma square_section_top {A B C D : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules) (s : Γ(M, ⊤)) :
    (squarePullbackIso a b c d h M).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection b s)) =
      Scheme.Modules.pullbackLocalSection c (Scheme.Modules.pullbackLocalSection d s) := by
  have hs := squarePullbackIso_section a b c d h M ⊤ s ⊤ (by simp) (by simp)
  simp only [res_refl] at hs
  exact hs

lemma extendsGenerator_open {L : ℕ} {D : LevelData k L} {X : Compactification k L D}
    (H : Extension k L D X) (T : DiskTest k L D X)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) :
    (diskOpenIso H T).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericInclusion k) η) = testGenerator T.toTest := by
  apply (ConcreteCategory.bijective_of_isIso ((openTestIso k L T.toTest).hom.app ⊤)).1
  have h := hη.2
  simp only [res_refl] at h
  have he := congrArg (fun q => q.app ⊤
    (Scheme.Modules.pullbackLocalSection (genericInclusion k) η)) (diskOpenIso_eq H T)
  exact he.trans (h.trans (ClassifiedTateDiskTransfer.test_generator T.toTest).symm)

lemma disk_generator_transport (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (ha : CompactCompatible ι f F hF e H J a)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.disk ≫ F = diskMap ι ≫ T.disk)
    (hb : TestCompatible ι T.toTest S.toTest f e)
    (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤))
    (hη : ExtendsGenerator k L H T η) :
    ExtendsGenerator l L J S ((diskComparison ι H J F a T S h).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (diskMap ι) η)) := by
  obtain ⟨hb, hgen⟩ := hb
  have hc := disk_open_comparison ι f F hF e H J a ha T S h hb
  have hs := square_section_top (genericInclusion l) (diskMap ι)
    (punctureMap ι) (genericInclusion k) (ClassifiedTateDiskTransfer.generic_square ι)
    ((Scheme.Modules.pullback T.disk).obj H.line) η
  simp only [res_refl] at hgen
  let η' := (diskComparison ι H J F a T S h).hom.app ⊤
    (Scheme.Modules.pullbackLocalSection (diskMap ι) η)
  refine ⟨?_, ?_⟩
  · exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      (diskComparison ι H J F a T S h) _ (pullback_frame (diskMap ι) _ η hη.1)
  simp only [res_refl]
  have hη' : (diskOpenIso J S).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericInclusion l) η') = testGenerator S.toTest := by
    have hc' := congrArg (fun q => q.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericInclusion l)
        (Scheme.Modules.pullbackLocalSection (diskMap ι) η))) hc
    change (diskOpenIso J S).hom.app ⊤
        (((Scheme.Modules.pullback (genericInclusion l)).map
          (diskComparison ι H J F a T S h).hom).app ⊤
          (Scheme.Modules.pullbackLocalSection (genericInclusion l)
            (Scheme.Modules.pullbackLocalSection (diskMap ι) η))) =
      (testComparison ι T.toTest S.toTest f e hb).hom.app ⊤
        (((Scheme.Modules.pullback (punctureMap ι)).map (diskOpenIso H T).hom).app ⊤
          ((squarePullbackIso (genericInclusion l) (diskMap ι) (punctureMap ι)
            (genericInclusion k) (ClassifiedTateDiskTransfer.generic_square ι)
            ((Scheme.Modules.pullback T.disk).obj H.line)).hom.app ⊤
            (Scheme.Modules.pullbackLocalSection (genericInclusion l)
              (Scheme.Modules.pullbackLocalSection (diskMap ι) η)))) at hc'
    rw [hs, map_section_top, map_section_top, extendsGenerator_open H T η hη] at hc'
    exact hc'.trans hgen
  have he := congrArg (fun q => q.app ⊤
    (Scheme.Modules.pullbackLocalSection (genericInclusion l) η')) (diskOpenIso_eq J S)
  exact he.symm.trans ((congrArg (fun t => (openTestIso l L S.toTest).hom.app ⊤ t)
    hη').trans (ClassifiedTateDiskTransfer.test_generator S.toTest))

lemma disk_frame_transfer (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line)
    (ha : CompactCompatible ι f F hF e H J a)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.disk ≫ F = diskMap ι ≫ T.disk)
    (hb : TestCompatible ι T.toTest S.toTest f e) :
    DiskFrameCompatible ι H J F a T S h := by
  intro η ξ hη hξ
  simp only [res_refl]
  exact extendsGenerator_unique l L J S _ ξ
    (disk_generator_transport ι f F hF e H J a ha T S h hb η hη) hξ

section MarkingDescent
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaFullLevelCoverR0175

/-- The pointed Tate coefficient map respects the already specified target law. -/
lemma tate_law_baseChange (ι : k →+* l) {L : ℕ}
    (A : TateLevel k L) (B : TateLevel l L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b) :
    IsBaseChange (LaurentSeries k) (TateCurve k L) A.law
      (LaurentSeries l) (TateCurve l L) B.law (laurentMap ι) b := by
  letI := B.elliptic
  obtain ⟨G, hG, hc⟩ := TateMarkingConstantTransfer.law_exists ι L b hb A
  have hone : (G.one (𝟙 _)).val = (B.law.one (𝟙 _)).val := by
    rw [hG.1, B.originLaw.1]
  have he : G = B.law :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext G B.law
      (fun t x y => WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
        (TateCurve l L).toProjective G B.law hone t x y)
      (by
        intro Z t
        apply Subtype.ext
        rw [hG.1, B.originLaw.1])
  exact he ▸ hc

/-- Descent of an arbitrary target marking retains both literal point maps. -/
lemma marking_descends (ι : k →+* l) {L : ℕ} (hL : 0 < L)
    (A : TateLevel k L) (B : TateLevel l L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b) :
    ∃ A' : TateLevel k L, A'.law = A.law ∧ Transfers ι A' B b := by
  letI := A.elliptic
  letI := B.elliptic
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  let hc := tate_law_baseChange ι A B b hb
  let M := BaseChange.down hc A.originLaw B.originLaw B.marking
  obtain ⟨C, hx, hy⟩ := EveryGeometricBoundaryTateDisk.full_marking_descends
    (LaurentSeries k) (TateCurve k L) A.law A.originLaw L hL A.marking
    (LaurentSeries l) ((𝟙 (Puncture l)) ≫ punctureMap ι) M
  let A' : TateLevel k L := ⟨A.elliptic, A.law, A.originLaw, C⟩
  refine ⟨A', rfl, hc, ?_⟩
  intro i j
  have hp := congrArg Subtype.val
    (BaseChange.point_combination hc A.originLaw B.originLaw (𝟙 (Puncture l))
      B.marking.x B.marking.y i.val j.val)
  have hn := Representability.combination_comp (LaurentSeries k) (TateCurve k L)
    A.law (𝟙 (Puncture k)) ((𝟙 (Puncture l)) ≫ punctureMap ι)
    ((𝟙 (Puncture l)) ≫ punctureMap ι) (Category.comp_id _)
    C.x C.y M.x M.y hx hy i.val j.val
  simp only [Category.id_comp] at hn
  exact hp.trans hn.symm

/-- Algebraic closure supplies a rational full marking, so every target
marking descends along the fixed coordinate-preserving coefficient map. -/
lemma all_markings_descend [IsAlgClosed k] (ι : k →+* l)
    {L : ℕ} (hL : 3 ≤ L) (heven : Even L) (B : TateLevel l L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b) :
    ∃ A : TateLevel k L, Transfers ι A B b := by
  letI : NeZero L := ⟨by omega⟩
  letI : NeZero (L : k) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne L)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k L
  obtain ⟨A, _⟩ := tate_full_level_marking k L hL heven ζ hζ
  obtain ⟨A', _, ht⟩ := marking_descends ι (by omega) A B b hb
  exact ⟨A', ht⟩

/-- Every target disk test is paired with a source test through the literal
coefficient maps, including the normalized open generator. -/
lemma all_tests_descend [IsAlgClosed k] (ι : k →+* l)
    {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (he : HodgeCompatible ι D E f e)
    (X : Compactification k L D) (Y : Compactification l L E)
    (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (S : DiskTest l L E Y) :
    ∃ T : DiskTest k L D X, TestCompatible ι T.toTest S.toTest f e ∧
      S.disk ≫ F = diskMap ι ≫ T.disk := by
  obtain ⟨b, hb, _⟩ := tate_coordinate_constant_map k l ι L hL heven
  obtain ⟨A, ht⟩ := all_markings_descend ι hL heven S.level b hb
  obtain ⟨t, htc, _⟩ := TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D A
  obtain ⟨V, hVA, hVt⟩ := (tate_hodge_comparison_tests k L hL heven D).1 A t htc
  obtain ⟨d, hd, _⟩ := tate_cusp_disk_extension k L hL heven D A X t htc
  let T : DiskTest k L D X := { toTest := V, disk := d, extends_eq := hVt.symm ▸ hd }
  have hT : Transfers ι T.level S.level b := by
    change Transfers ι V.level S.level b
    rw [hVA]
    exact ht
  exact ⟨T, classified_tate_disk_transfer k l ι L hL heven D E f hf e he X Y F hF T S b hb hT⟩

end MarkingDescent

/-- The actual pullback of the source canonical lattice is canonical on
every target disk, without assuming the compact comparison exists. -/
lemma pullbackExtension_canonical [IsAlgClosed k] (ι : k →+* l)
    {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (he : HodgeCompatible ι D E f e)
    (X : Compactification k L D) (Y : Compactification l L E)
    (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (H : Extension k L D X) (hH : Canonical k L H) :
    Canonical l L (pullbackExtension ι f F hF e H) := by
  let J := pullbackExtension ι f F hF e H
  apply (canonical_iff_exists l L J).mpr
  intro S
  obtain ⟨T, ht, hd⟩ := all_tests_descend ι hL heven D E f hf e he X Y F hF S
  obtain ⟨η, hη, _⟩ := hH T
  have ha : CompactCompatible ι f F hF e H J (Iso.refl _) := by
    apply (compatible_iff ι f F hF e H J (Iso.refl _)).mpr
    simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  exact ⟨_, disk_generator_transport ι f F hF e H J (Iso.refl _) ha T S hd ht η hη⟩

section CanonicalLocalComparison
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- The comparison scalar between two canonical lattices is the image of
an actual power-series unit at each prescribed cusp. -/
lemma canonical_comparison_scalar_unit {L : ℕ} {D : LevelData k L}
    {X : Compactification k L D}
    (H J : Extension k L D X) (hH : Canonical k L H) (hJ : Canonical k L J)
    (T : DiskTest k L D X) (U : X.space.Opens)
    (u : Γ(H.line, U)) (hu : IsFrame H.line U u)
    (v : Γ(J.line, U)) (hv : IsFrame J.line U v)
    (hd : (⊤ : (Disk k).Opens) ≤ T.disk ⁻¹ᵁ U)
    (ho : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U))
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u) =
      r • J.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion v)) :
    ∃ w : (PowerSeries k)ˣ,
      algebraMap (PowerSeries k) (LaurentSeries k) (w : PowerSeries k) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
        (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho r) := by
  let η := res ((Scheme.Modules.pullback T.disk).obj H.line) hd
    (Scheme.Modules.pullbackLocalSection T.disk u)
  let ξ := res ((Scheme.Modules.pullback T.disk).obj J.line) hd
    (Scheme.Modules.pullbackLocalSection T.disk v)
  have hη : IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η :=
    frame_restrict _ _ _ (pullback_frame _ _ _ hu)
  have hξ : IsFrame ((Scheme.Modules.pullback T.disk).obj J.line) ⊤ ξ :=
    frame_restrict _ _ _ (pullback_frame _ _ _ hv)
  obtain ⟨a, ha, _⟩ := disk_coefficient_exists k L H T η hη
  obtain ⟨b, hb, _⟩ := disk_coefficient_exists k L J T ξ hξ
  obtain ⟨a₀, ha₀⟩ := (extendsGenerator_iff_coefficient_unit k L H T η hη a ha).mp (hH T).exists
  obtain ⟨b₀, hb₀⟩ := (extendsGenerator_iff_coefficient_unit k L J T ξ hξ b hb).mp (hJ T).exists
  have hc : diskRestriction k L H T η =
      T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho r • diskRestriction k L J T ξ := by
    rw [diskRestriction_local_section k L H T U u hd ho,
      diskRestriction_local_section k L J T U v hd ho, hr,
      Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
      InitialHodgeSection.res_smul]
    rfl
  have hh : scalar (LaurentSeries k) a * T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho r =
      scalar (LaurentSeries k) b := by
    apply (diskRestriction_frame k L J T ξ hξ ⊤ le_rfl).1
    simp only [InitialHodgeSection.res_self]
    rw [mul_smul, ← hc, ha, hb]
  have hval : a * (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (T.base.appLE (X.inclusion ⁻¹ᵁ U) ⊤ ho r) = b := by
    have he := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom hh
    simp only [map_mul, scalar] at he
    have hn (z : LaurentSeries k) :
        (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv z) = z :=
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv_hom_id z
    rw [hn a, hn b] at he
    exact he
  have ha0 : a ≠ 0 := disk_coefficient_ne_zero k L H T η hη a ha
  refine ⟨b₀ * a₀⁻¹, ?_⟩
  apply mul_left_cancel₀ ha0
  rw [hval, ← ha₀, ← hb₀, ← map_mul]
  congr 1
  simp only [Units.val_mul]
  rw [mul_comm, mul_assoc, Units.inv_mul, mul_one]

open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

/-- Completed regularity descends to a neighborhood in the actual compact curve. -/
lemma comparison_scalar_lift {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H J : Extension k L D X) (hH : Canonical k L H) (hJ : Canonical k L J)
    (T : DiskTest k L D X) (U : X.space.Opens) [IsIntegral U.toScheme]
    (u : Γ(H.line, U)) (hu : IsFrame H.line U u)
    (v : Γ(J.line, U)) (hv : IsFrame J.line U v)
    (hU : T.disk (closedPoint k) ∈ U)
    (r : Γ(OpenBase k L D, X.inclusion ⁻¹ᵁ U))
    (hr : H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u) =
      r • J.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion v)) :
    ∃ (V : X.space.Opens) (_ : T.disk (closedPoint k) ∈ V) (hVU : V ≤ U)
      (q : Γ(X.space, V)), X.inclusion.app V q =
        (OpenBase k L D).presheaf.map
          (homOfLE (show X.inclusion ⁻¹ᵁ V ≤ X.inclusion ⁻¹ᵁ U from fun _ hx => hVU hx)).op r := by
  letI := X.openImmersion
  letI : IsDomain (CuspStalk k L D X T.disk) :=
    (compact_stalk_normal k L D X (T.disk (closedPoint k))).1
  obtain ⟨β, θ, _, hβ, hβT, _, hθ, _, _⟩ :=
    disk_shared_center_fraction_maps k L hL heven D X T T rfl
  have hd := (Scheme.preimage_eq_top_of_closedPoint_mem T.disk hU).ge
  have hT : (⊤ : (Puncture k).Opens) ≤ T.base ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z _
    change X.inclusion (T.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← T.extends_eq.2.1, Scheme.Hom.comp_apply]
    exact hd (Set.mem_univ _)
  have hβU : (⊤ : (Spec (CommRingCat.of
      (FractionRing (CuspStalk k L D X T.disk)))).Opens) ≤ β ⁻¹ᵁ (X.inclusion ⁻¹ᵁ U) := by
    intro z _
    let w : Puncture k := (⊥ : PrimeSpectrum (LaurentSeries k))
    have hz : Spec.map (CommRingCat.ofHom θ) w = z := Subsingleton.elim _ _
    change X.inclusion (β z) ∈ U
    rw [← hz]
    change X.inclusion ((Spec.map (CommRingCat.ofHom θ) ≫ β) w) ∈ U
    rw [hβT]
    exact hT (Set.mem_univ _)
  have hi : ∃ a : CuspStalk k L D X T.disk,
      algebraMap _ (FractionRing (CuspStalk k L D X T.disk)) a =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing (CuspStalk k L D X T.disk)))).hom
          (β.appLE (X.inclusion ⁻¹ᵁ U) ⊤ hβU r) := by
    apply integral_of_completed_order_nonneg k L hL heven D X T _ θ hθ
    rw [field_section_factor θ β T.base hβT _ hβU hT r]
    obtain ⟨b, hb⟩ := canonical_comparison_scalar_unit H J hH hJ T U u hu v hv hd hT r hr
    rw [← hb]
    exact ArithmeticThetaCompactUnaryR0183.CompactNormalizedPowerExtensionR0183.integral_series_order k _
  obtain ⟨a, ha⟩ := hi
  exact local_scalar_lift X.inclusion (T.disk (closedPoint k)) U hU β hβ hβU r a ha

lemma scalar_lift_frame_image {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    {M N : Y.Modules} {P : Z.Modules}
    (eM : (Scheme.Modules.pullback p).obj M ≅ P)
    (eN : (Scheme.Modules.pullback p).obj N ≅ P)
    (U : Y.Opens) (u : Γ(M, U)) (v : Γ(N, U)) (r : Γ(Z, p ⁻¹ᵁ U))
    (hr : r • eN.hom.app _ (Scheme.Modules.pullbackLocalSection p v) =
      eM.hom.app _ (Scheme.Modules.pullbackLocalSection p u))
    (V : Y.Opens) (hVU : V ≤ U) (q : Γ(Y, V))
    (hq : p.app V q = Z.presheaf.map
      (homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hVU hx)).op r) :
    eN.hom.app _ (Scheme.Modules.pullbackLocalSection p (q • res N hVU v)) =
      eM.hom.app _ (Scheme.Modules.pullbackLocalSection p (res M hVU u)) := by
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, hq,
    ← InitialSectionNaturality.pullback_res, ← hom_res,
    ← InitialHodgeSection.res_smul, hr, hom_res, InitialSectionNaturality.pullback_res]

/-- On every compact neighborhood a source frame has a regular image in the
second canonical lattice. -/
lemma comparison_local_lifts [IsAlgClosed k] {L : ℕ} (hL : 3 ≤ L) (heven : Even L)
    {D : LevelData k L} {X : Compactification k L D}
    (H J : Extension k L D X) (hH : Canonical k L H) (hJ : Canonical k L J)
    (x : X.space) :
    ∃ (V : X.space.Opens) (u : Γ(H.line, V)) (v : Γ(J.line, V)),
      x ∈ V ∧ IsFrame H.line V u ∧
      J.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion v) =
        H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u) := by
  letI := X.openImmersion
  by_cases hx : x ∈ Set.range X.inclusion
  · obtain ⟨W, u, hxW, hu⟩ := local_frame_exists H.invertible x
    let V := W ⊓ X.inclusion.opensRange
    let u' := res H.line (inf_le_left : V ≤ W) u
    have hs := (ConcreteCategory.bijective_of_isIso (J.onOpen.hom.app (X.inclusion ⁻¹ᵁ V))).comp
      (Scheme.Modules.bijective_unit_app_of_le_opensRange X.inclusion J.line V inf_le_right)
    obtain ⟨v, hv⟩ := hs.surjective
      (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u'))
    exact ⟨V, u', v, ⟨hxW, hx⟩, frame_restrict _ _ _ hu, hv⟩
  · obtain ⟨T, hTx⟩ := (tate_hodge_comparison_tests k L hL heven D).2 X x hx
    obtain ⟨W, u, hxW, hu, hWI⟩ := integral_frame_neighborhood k L H x
    obtain ⟨Z, v, hxZ, hv⟩ := local_frame_exists J.invertible x
    let U := W ⊓ Z
    have hxU : x ∈ U := ⟨hxW, hxZ⟩
    letI := hWI
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion
      (X.space.homOfLE (inf_le_left : U ≤ W))
    let u' := res H.line (inf_le_left : U ≤ W) u
    let v' := res J.line (inf_le_right : U ≤ Z) v
    have hu' : IsFrame H.line U u' := frame_restrict _ _ _ hu
    have hv' : IsFrame J.line U v' := frame_restrict _ _ _ hv
    have hvO := frame_iso J.onOpen _ (pullback_frame X.inclusion J.line v' hv')
    obtain ⟨r, hr⟩ := (hvO (X.inclusion ⁻¹ᵁ U) le_rfl).2
      (H.onOpen.hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion u'))
    rw [InitialHodgeSection.res_self] at hr
    obtain ⟨V, hTV, hVU, q, hq⟩ := comparison_scalar_lift hL heven H J hH hJ T U
      u' hu' v' hv' (hTx ▸ hxU) r hr.symm
    refine ⟨V, res H.line hVU u', q • res J.line hVU v', hTx ▸ hTV,
      frame_restrict _ _ _ hu', ?_⟩
    exact scalar_lift_frame_image X.inclusion H.onOpen J.onOpen U u' v' r hr V hVU q hq

open ArithmeticThetaLineRoot ArithmeticThetaCoverComparison ArithmeticThetaGlobalization

/-- A local source frame and its proposed image define an actual local sheaf map. -/
def mapFromFrame {Y : Scheme.{0}} {M N : Y.Modules} {U : Y.Opens}
    (u : Γ(M, U)) (hu : IsFrame M U u) (v : Γ(N, U)) :
    HomLine.compatibleMaps Y M N U :=
  ⟨fun V => (LinearMap.toSpanSingleton Γ(Y, V.val) Γ(N, V.val) (res N V.property v)).comp
      ((InitialHodgeSection.frame M u hu).equiv V.val V.property).symm.toLinearMap, by
    intro V W h s
    change ((InitialHodgeSection.frame M u hu).equiv W.val _).symm
        (M.presheaf.map (homOfLE h).op s) • res N _ v =
      res N h (((InitialHodgeSection.frame M u hu).equiv V.val _).symm s • res N _ v)
    rw [frame_coordinate_restrict, InitialHodgeSection.res_smul, InitialHodgeSection.res_res]⟩

lemma mapFromFrame_generator {Y : Scheme.{0}} {M N : Y.Modules} {U : Y.Opens}
    (u : Γ(M, U)) (hu : IsFrame M U u) (v : Γ(N, U)) :
    (mapFromFrame u hu v).val ⟨U, le_rfl⟩ u = v := by
  have he : (InitialHodgeSection.frame M u hu).equiv U le_rfl 1 = u := by
    change (1 : Γ(Y, U)) • res M le_rfl u = u
    rw [InitialHodgeSection.res_self, one_smul]
  change ((InitialHodgeSection.frame M u hu).equiv U le_rfl).symm u • res N le_rfl v = v
  have hc : ((InitialHodgeSection.frame M u hu).equiv U le_rfl).symm u = 1 := by
    apply ((InitialHodgeSection.frame M u hu).equiv U le_rfl).injective
    rw [LinearEquiv.apply_symm_apply]
    exact he.symm
  rw [hc, one_smul, InitialHodgeSection.res_self]

lemma mapFromFrame_open {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    {M N : Y.Modules} {P : Z.Modules}
    (eM : (Scheme.Modules.pullback p).obj M ≅ P)
    (eN : (Scheme.Modules.pullback p).obj N ≅ P)
    {U : Y.Opens} (u : Γ(M, U)) (hu : IsFrame M U u) (v : Γ(N, U))
    (hv : eN.hom.app _ (Scheme.Modules.pullbackLocalSection p v) =
      eM.hom.app _ (Scheme.Modules.pullbackLocalSection p u))
    (V : Y.Opens) (hV : V ≤ U) (s : Γ(M, V)) :
    eN.hom.app _ (Scheme.Modules.pullbackLocalSection p ((mapFromFrame u hu v).val ⟨V, hV⟩ s)) =
      eM.hom.app _ (Scheme.Modules.pullbackLocalSection p s) := by
  have hh := congrArg (res P (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hV hx)) hv
  rw [hom_res, InitialSectionNaturality.pullback_res p N hV v,
    hom_res, InitialSectionNaturality.pullback_res p M hV u] at hh
  obtain ⟨r, rfl⟩ := ((InitialHodgeSection.frame M u hu).equiv V hV).surjective s
  change eN.hom.app _ (Scheme.Modules.pullbackLocalSection p
    (((InitialHodgeSection.frame M u hu).equiv V hV).symm
      ((InitialHodgeSection.frame M u hu).equiv V hV r) • res N hV v)) = _
  rw [LinearEquiv.symm_apply_apply]
  change eN.hom.app _ (Scheme.Modules.pullbackLocalSection p (r • res N hV v)) =
    eM.hom.app _ (Scheme.Modules.pullbackLocalSection p (r • res M hV u))
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, hh]

/-- Regular local images of frames glue to a global map, with the prescribed
restriction along a schematically dense morphism. -/
lemma hom_of_local_frame_lifts {Y Z : Scheme.{0}} (p : Z ⟶ Y)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (M N : Y.Modules) (hN : Scheme.Modules.IsInvertible N) (P : Z.Modules)
    (eM : (Scheme.Modules.pullback p).obj M ≅ P)
    (eN : (Scheme.Modules.pullback p).obj N ≅ P)
    (hl : ∀ x : Y, ∃ (U : Y.Opens) (u : Γ(M, U)) (v : Γ(N, U)),
      x ∈ U ∧ IsFrame M U u ∧
        eN.hom.app _ (Scheme.Modules.pullbackLocalSection p v) =
          eM.hom.app _ (Scheme.Modules.pullbackLocalSection p u)) :
    ∃ a : M ⟶ N, (Scheme.Modules.pullback p).map a ≫ eN.hom = eM.hom := by
  classical
  choose U u v hx hu hv using hl
  let a (x : Y) := mapFromFrame (u x) (hu x) (v x)
  have hc : (⊤ : Y.Opens) ≤ iSup U := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨b, hb, _⟩ := HomLine.compatibleMaps_glue U ⊤ (fun _ => le_top) hc a (by
    intro i j
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro s
    apply pullback_local_injective_of_invertible p N hN V.val
    apply (ConcreteCategory.bijective_of_isIso (eN.hom.app _)).1
    exact (mapFromFrame_open p eM eN (u i) (hu i) (v i) (hv i)
      V.val (V.property.trans inf_le_left) s).trans
      (mapFromFrame_open p eM eN (u j) (hu j) (v j) (hv j)
        V.val (V.property.trans inf_le_right) s).symm)
  refine ⟨HomLine.toHom b, ?_⟩
  apply hom_ext_frames
  intro z
  refine ⟨p ⁻¹ᵁ U (p z), Scheme.Modules.pullbackLocalSection p (u (p z)),
    hx (p z), pullback_frame p M (u (p z)) (hu (p z)), ?_⟩
  change eN.hom.app _ (((Scheme.Modules.pullback p).map (HomLine.toHom b)).app _
    (Scheme.Modules.pullbackLocalSection p (u (p z)))) = _
  rw [← Scheme.Modules.pullbackLocalSection_app]
  have hb' := congrArg (fun c : HomLine.compatibleMaps Y M N (U (p z)) =>
    c.val ⟨U (p z), le_rfl⟩ (u (p z))) (hb (p z))
  change (HomLine.toHom b).app (U (p z)) (u (p z)) =
    (mapFromFrame (u (p z)) (hu (p z)) (v (p z))).val ⟨U (p z), le_rfl⟩ (u (p z)) at hb'
  rw [hb', mapFromFrame_generator]
  exact hv (p z)


/-- Two canonical lattices on the same compact curve have a unique normalized
comparison. Both directions are constructed by regular local extension. -/
lemma canonical_comparison_exists [IsAlgClosed k] {L : ℕ}
    (hL : 3 ≤ L) (heven : Even L) {D : LevelData k L}
    {X : Compactification k L D} (H J : Extension k L D X)
    (hH : Canonical k L H) (hJ : Canonical k L J) :
    ∃ a : H.line ≅ J.line,
      (Scheme.Modules.pullback X.inclusion).map a.hom ≫ J.onOpen.hom = H.onOpen.hom := by
  letI := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.inclusion_schematic k L D X
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  obtain ⟨a, ha⟩ := hom_of_local_frame_lifts X.inclusion H.line J.line J.invertible
    _ H.onOpen J.onOpen (comparison_local_lifts hL heven H J hH hJ)
  obtain ⟨b, hb⟩ := hom_of_local_frame_lifts X.inclusion J.line H.line H.invertible
    _ J.onOpen H.onOpen (comparison_local_lifts hL heven J H hJ hH)
  have hab : a ≫ b = 𝟙 H.line := by
    apply hom_eq_of_pullback X.inclusion H.invertible
    apply (cancel_mono H.onOpen.hom).mp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, hb, ha]
  have hba : b ≫ a = 𝟙 J.line := by
    apply hom_eq_of_pullback X.inclusion J.invertible
    apply (cancel_mono J.onOpen.hom).mp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, ha, hb]
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

#print axioms comparison_local_lifts
#print axioms canonical_comparison_exists

end CanonicalLocalComparison

#print axioms canonical_comparison_scalar_unit
#print axioms pullbackExtension_canonical
#print axioms all_tests_descend
#print axioms all_markings_descend
#print axioms disk_frame_transfer
#print axioms disk_open_comparison
#print axioms compact_comparison_unique
#print axioms square_cube
#print axioms square_pre
#print axioms square_post
#print axioms compatible_diskGeneric
#print axioms disk_section_eq_of_generic

end CompactHodgeConstantComparison
/-- The normalized open comparison extends uniquely across every cusp. -/
theorem compact_hodge_constant_comparison :
    ∀ (k l : Type) [Field k] [CharZero k] [IsAlgClosed k] [Field l] [CharZero l] [IsAlgClosed l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L), ∀ (f : Quiver.Hom (ArithmeticThetaLevelCompactificationR0179.OpenBase l L E) (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)), ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (ArithmeticThetaLevelConstantsR0234.weight D)) (ArithmeticThetaLevelConstantsR0234.weight E)), ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e → ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (F : Quiver.Hom (Y.space) (X.space)) (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l L E Y), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryHodgeR0182.Canonical l L J → ∃! a : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F).obj H.line) J.line, ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι f F hF e H J a := by
  intro k l _ _ _ _ _ _ ι L hL heven D E f hf e he X Y F hF H J hH hJ
  obtain ⟨a, ha⟩ := CompactHodgeConstantComparison.canonical_comparison_exists hL heven
    (CompactHodgeConstantComparison.pullbackExtension ι f F hF e H) J
    (CompactHodgeConstantComparison.pullbackExtension_canonical ι hL heven D E f hf e he X Y F hF H hH) hJ
  have hac : CompactCompatible ι f F hF e H J a :=
    (CompactHodgeConstantComparison.compatible_iff ι f F hF e H J a).mpr ha
  refine ⟨a, hac, ?_⟩
  intro b hb
  exact CompactHodgeConstantComparison.compact_comparison_unique ι f F hF e H J b a hb hac

#print axioms compact_hodge_constant_comparison

/-- Exact integral Tate-frame transport for the same compact comparison. -/
theorem compact_tate_frame_transfer :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L), ∀ (f : Quiver.Hom (ArithmeticThetaLevelCompactificationR0179.OpenBase l L E) (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)), ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (ArithmeticThetaLevelConstantsR0234.weight D)) (ArithmeticThetaLevelConstantsR0234.weight E)), ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e → ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (F : Quiver.Hom (Y.space) (X.space)) (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l L E Y), ∀ (a : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F).obj H.line) J.line), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι f F hF e H J a → ∀ (T : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (S : ArithmeticThetaBoundaryHodgeR0182.DiskTest l L E Y) (h : CategoryTheory.CategoryStruct.comp S.disk F = CategoryTheory.CategoryStruct.comp (ArithmeticThetaBoundaryConstantsR0235.diskMap ι) T.disk), ArithmeticThetaBoundaryConstantsR0235.TestCompatible ι T.toTest S.toTest f e → ArithmeticThetaBoundaryConstantsR0235.DiskFrameCompatible ι H J F a T S h := by
  intro k l _ _ _ _ ι L _ _ D E f _ e _ X Y F hF H J a ha T S h hc
  exact CompactHodgeConstantComparison.disk_frame_transfer ι f F hF e H J a ha T S h hc

#print axioms compact_tate_frame_transfer

end ArithmeticThetaBoundaryConstantsR0235
