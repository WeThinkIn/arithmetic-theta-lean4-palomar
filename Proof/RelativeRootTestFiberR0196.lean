module

public import RootTestPullbackCoherenceR0196

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192
namespace RelativeRootTestFiberR0196
open RootTestPullbackCoherenceR0196

variable {B Y T Z : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
  (H : SquareLine Y ((Scheme.Modules.pullback p).obj W)) (R : RootObject B W T)
  (l : Z ⟶ Y) (t : Z ⟶ T) (h : l ≫ p = t ≫ R.map)

def testRoot : SquareLine Z ((Scheme.Modules.pullback (t ≫ R.map)).obj W) :=
  ⟨(Scheme.Modules.pullback t).obj R.root.line, R.root.invertible.pullback t,
    squarePull t R.root ≪≫ (Scheme.Modules.pullbackComp t R.map).app W⟩

def levelRoot : SquareLine Z ((Scheme.Modules.pullback (t ≫ R.map)).obj W) :=
  ⟨(Scheme.Modules.pullback l).obj H.line, H.invertible.pullback l,
    squarePull l H ≪≫ (Scheme.Modules.pullbackComp l p).app W ≪≫
      (Scheme.Modules.pullbackCongr h).app W⟩

def flatten {S : Scheme.{0}} (f : S ⟶ Z)
    (w : (Scheme.Modules.pullback f).obj (testRoot R t).line ≅
      (Scheme.Modules.pullback f).obj (levelRoot H R l t h).line) : Lift p H R S where
  toLevel := f ≫ l
  toTest := f ≫ t
  triangle := by simp only [Category.assoc, h]
  iso := ((Scheme.Modules.pullbackComp f t).app R.root.line).symm ≪≫ w ≪≫
    (Scheme.Modules.pullbackComp f l).app H.line

lemma test_square {S : Scheme.{0}} (f : S ⟶ Z) :
    (squarePull f (testRoot R t)).hom ≫
      (Scheme.Modules.pullbackComp f (t ≫ R.map)).hom.app W ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f t R.map).symm).hom.app W =
    tensorPowerMap ((Scheme.Modules.pullbackComp f t).hom.app R.root.line) 2 ≫
      (squarePull (f ≫ t) R.root).hom ≫
      (Scheme.Modules.pullbackComp (f ≫ t) R.map).hom.app W := by
  rw [← Category.assoc (tensorPowerMap _ 2), square_comp]
  simp only [squarePull, testRoot, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [comp_assoc_reverse]
  rfl

lemma level_square {S : Scheme.{0}} (f : S ⟶ Z) :
    (squarePull f (levelRoot H R l t h)).hom ≫
      (Scheme.Modules.pullbackComp f (t ≫ R.map)).hom.app W ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f t R.map).symm).hom.app W =
    tensorPowerMap ((Scheme.Modules.pullbackComp f l).hom.app H.line) 2 ≫
      (squarePull (f ≫ l) H).hom ≫
      (Scheme.Modules.pullbackComp (f ≫ l) p).hom.app W ≫
      (Scheme.Modules.pullbackCongr (show (f ≫ l) ≫ p = (f ≫ t) ≫ R.map by
        simp only [Category.assoc, h])).hom.app W := by
  rw [← Category.assoc (tensorPowerMap _ 2), square_comp]
  simp only [squarePull, levelRoot, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [triangle_comp f l t p R.map h W]
  simp only [Functor.map_comp, Category.assoc]
  rfl

lemma compatible_flatten {S : Scheme.{0}} (f : S ⟶ Z)
    (w : (Scheme.Modules.pullback f).obj (testRoot R t).line ≅
      (Scheme.Modules.pullback f).obj (levelRoot H R l t h).line) :
    Compatible (flatten H R l t h f w) ↔
      IsSquareIsometry f (testRoot R t) (levelRoot H R l t h) w := by
  rw [SquareIsometryInterfaceAdapterR0192.isometry_iff]
  change _ ↔ tensorPowerMap w.hom 2 ≫ (squarePull f (levelRoot H R l t h)).hom =
    (squarePull f (testRoot R t)).hom
  let C := (Scheme.Modules.pullbackComp f t).app R.root.line
  let : IsIso (tensorPowerMap C.hom 2) := (tensorPowerIso C 2).isIso_hom
  unfold Compatible
  conv_lhs => rw [← cancel_epi (tensorPowerMap C.hom 2)]
  conv_rhs => rw [← cancel_mono ((Scheme.Modules.pullbackComp f (t ≫ R.map)).hom.app W ≫
    (Scheme.Modules.pullbackCongr (Category.assoc f t R.map).symm).hom.app W)]
  simp only [Category.assoc]
  rw [level_square H R l t h f, test_square R t f]
  simp only [flatten, Iso.trans_hom, Iso.symm_hom, Iso.app, tensorPowerMap_comp, Category.assoc]
  have hc : tensorPowerMap C.hom 2 ≫ tensorPowerMap C.inv 2 = 𝟙 _ := by
    rw [← tensorPowerMap_comp, C.hom_inv_id, tensorPowerMap_id]
  change tensorPowerMap C.hom 2 ≫ tensorPowerMap C.inv 2 ≫ _ = _ ↔ _
  rw [← Category.assoc (tensorPowerMap C.hom 2) (tensorPowerMap C.inv 2), hc]
  simp only [Category.id_comp]
  rfl

lemma sameLift_iff_eq {S : Scheme.{0}} (d e : Lift p H R S) : SameLift d e ↔ d = e := by
  constructor
  · rintro ⟨hy, ht, he⟩
    cases d with
    | mk dy dt dh di =>
      cases e with
      | mk ey et eh ei =>
        dsimp at hy ht he
        subst ey
        subst et
        change di ≪≫ Iso.refl _ = Iso.refl _ ≪≫ ei at he
        have hi : di = ei := by simpa using he
        cases hi
        rfl
  · rintro rfl
    exact ⟨rfl, rfl, by change d.iso ≪≫ Iso.refl _ = Iso.refl _ ≪≫ d.iso; simp⟩

lemma flatten_injective {S : Scheme.{0}} (f : S ⟶ Z) :
    Function.Injective (flatten H R l t h f) := by
  intro u v he
  obtain ⟨hy, ht, hi⟩ := (sameLift_iff_eq H R _ _).mpr he
  change (flatten H R l t h f u).iso ≪≫ Iso.refl _ =
    Iso.refl _ ≪≫ (flatten H R l t h f v).iso at hi
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp f t).app R.root.line).inv).1
  apply (cancel_mono ((Scheme.Modules.pullbackComp f l).app H.line).hom).1
  simpa [flatten, Category.assoc] using congrArg Iso.hom hi

lemma flatten_transport {S P : Scheme.{0}} (a : P ⟶ Z)
    (e : (Scheme.Modules.pullback a).obj (testRoot R t).line ≅
      (Scheme.Modules.pullback a).obj (levelRoot H R l t h).line)
    (f : S ⟶ Z) (g : S ⟶ P) (hg : g ≫ a = f) :
    SameLift (reindex (flatten H R l t h a e) g)
      (flatten H R l t h f
        (transportIsometry a (testRoot R t) (levelRoot H R l t h) e f g hg)) := by
  subst f
  refine ⟨(Category.assoc _ _ _).symm, (Category.assoc _ _ _).symm, ?_⟩
  have hc {K : Scheme.{0}} (b : Z ⟶ K) (M : K.Modules) :
      (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp a b).app M) ≪≫
          (Scheme.Modules.pullbackComp g (a ≫ b)).app M =
        (Scheme.Modules.pullbackComp g a).app ((Scheme.Modules.pullback b).obj M) ≪≫
          (Scheme.Modules.pullbackComp (g ≫ a) b).app M ≪≫
          (Scheme.Modules.pullbackCongr (Category.assoc g a b)).app M := by
    apply Iso.ext
    exact comp_assoc g a b M
  have hr : (reindex (flatten H R l t h a e) g).iso =
      ((Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp a t).app R.root.line) ≪≫
        (Scheme.Modules.pullbackComp g (a ≫ t)).app R.root.line).symm ≪≫
      (Scheme.Modules.pullback g).mapIso e ≪≫
      ((Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp a l).app H.line) ≪≫
        (Scheme.Modules.pullbackComp g (a ≫ l)).app H.line) := by
    simp [reindex, flatten]
  rw [hr, hc, hc]
  apply Iso.ext
  simp [flatten, transportIsometry, ArithmeticThetaCommonHalfHodgeR0185.along,
    Scheme.Modules.pullbackCongr, Iso.app, Category.assoc]
  erw [Category.id_comp]

def pairMap {S : Scheme.{0}} (d : Lift p H R S) : S ⟶ Limits.pullback p R.map :=
  Limits.pullback.lift d.toLevel d.toTest d.triangle

def encode {S : Scheme.{0}} (d : Lift p H R S) :
    (Scheme.Modules.pullback (pairMap H R d)).obj
        (testRoot R (Limits.pullback.snd p R.map)).line ≅
      (Scheme.Modules.pullback (pairMap H R d)).obj
        (levelRoot H R (Limits.pullback.fst p R.map) (Limits.pullback.snd p R.map)
          Limits.pullback.condition).line :=
  ArithmeticThetaCommonHalfHodgeR0185.along (pairMap H R d) (Limits.pullback.snd p R.map)
      d.toTest (Limits.pullback.lift_snd _ _ _) R.root.line ≪≫ d.iso ≪≫
    (ArithmeticThetaCommonHalfHodgeR0185.along (pairMap H R d) (Limits.pullback.fst p R.map)
      d.toLevel (Limits.pullback.lift_fst _ _ _) H.line).symm

lemma flatten_encode {S : Scheme.{0}} (d : Lift p H R S) :
    flatten H R (Limits.pullback.fst p R.map) (Limits.pullback.snd p R.map)
      Limits.pullback.condition (pairMap H R d) (encode H R d) = d := by
  apply (sameLift_iff_eq H R _ _).mp
  refine ⟨Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _, ?_⟩
  apply Iso.ext
  simp [flatten, encode, ArithmeticThetaCommonHalfHodgeR0185.along, Category.assoc]

lemma pairMap_flatten {S : Scheme.{0}} (f : S ⟶ Limits.pullback p R.map)
    (w : (Scheme.Modules.pullback f).obj (testRoot R (Limits.pullback.snd p R.map)).line ≅
      (Scheme.Modules.pullback f).obj
        (levelRoot H R (Limits.pullback.fst p R.map) (Limits.pullback.snd p R.map)
          Limits.pullback.condition).line) :
    pairMap H R (flatten H R (Limits.pullback.fst p R.map) (Limits.pullback.snd p R.map)
      Limits.pullback.condition f w) = f := by
  apply Limits.pullback.hom_ext <;> simp [pairMap, flatten]

lemma pairMap_reindex {S P : Scheme.{0}} (d : Lift p H R P) (g : S ⟶ P) :
    pairMap H R (reindex d g) = g ≫ pairMap H R d := by
  apply Limits.pullback.hom_ext <;> simp [pairMap, reindex, Category.assoc]

end RelativeRootTestFiberR0196
open RelativeRootTestFiberR0196

/-- Every relative square-root test fiber is represented by the accepted
square-isometry torsor on the actual categorical base product. -/
theorem relative_root_test_fiber
    (B Y : Scheme.{0}) (W : B.Modules) (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W))
    (h2 : IsUnit (2 : B.presheaf.obj (Opposite.op ⊤)))
    (T : Scheme.{0}) (R : RootObject B W T) :
    ∃ F : Fiber p H R, Represents F ∧ PairTorsor F := by
  let Z := Limits.pullback p R.map
  let l : Z ⟶ Y := Limits.pullback.fst p R.map
  let t : Z ⟶ T := Limits.pullback.snd p R.map
  have h : l ≫ p = t ≫ R.map := Limits.pullback.condition
  let A := testRoot R t
  let C := levelRoot H R l t h
  have h2Z : IsUnit (2 : Z.presheaf.obj (Opposite.op ⊤)) := by
    simpa only [map_ofNat] using h2.map (t ≫ R.map).appTop.hom
  obtain ⟨P, a, e, hfin, het, hsur, hdeg, he, hu⟩ :=
    square_isometry_interface_adapter Z ((Scheme.Modules.pullback (t ≫ R.map)).obj W) A C h2Z
  let F : Fiber p H R := ⟨P, flatten H R l t h a e⟩
  refine ⟨F, ⟨(compatible_flatten H R l t h a e).mpr he, ?_⟩,
    a, rfl, rfl, hfin, het, hsur, hdeg⟩
  intro S d hd
  let f := pairMap H R d
  let w := encode H R d
  have hw : IsSquareIsometry f A C w := by
    apply (compatible_flatten H R l t h f w).mp
    change Compatible (flatten H R (Limits.pullback.fst p R.map)
      (Limits.pullback.snd p R.map) Limits.pullback.condition (pairMap H R d) (encode H R d))
    rw [flatten_encode]
    exact hd
  have transfer (k : {k : S ⟶ P // k ≫ a = f}) :
      transportIsometry a A C e f k.val k.property = w ↔
        SameLift (reindex F.universal k.val) d := by
    rw [sameLift_iff_eq]
    have hk := (sameLift_iff_eq H R _ _).mp
      (flatten_transport H R l t h a e f k.val k.property)
    change _ ↔ reindex (flatten H R l t h a e) k.val = d
    rw [hk]
    have hd' : flatten H R l t h f w = d := flatten_encode H R d
    rw [← hd']
    exact (flatten_injective H R l t h f).eq_iff.symm
  obtain ⟨g, hg, huniq⟩ := hu S f w hw
  refine ⟨g.val, (transfer g).mp hg, ?_⟩
  intro k hk
  have hkbase : k ≫ a = f := by
    have hh := congrArg (pairMap H R) ((sameLift_iff_eq H R _ _).mp hk)
    change pairMap H R (reindex (flatten H R l t h a e) k) = f at hh
    rw [pairMap_reindex, pairMap_flatten] at hh
    exact hh
  exact congrArg Subtype.val (huniq ⟨k, hkbase⟩ ((transfer ⟨k, hkbase⟩).mpr hk))

#print axioms relative_root_test_fiber
end ArithmeticThetaMetaplecticTestsR0196
