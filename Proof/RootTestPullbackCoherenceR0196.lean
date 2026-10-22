module

public import MetaplecticTestDefinitionsR0196
public import SquareIsomorphismTorsor

@[expose] public section

/-! Coherence of the actual relative square-root test lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192
namespace RootTestPullbackCoherenceR0196
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149

lemma comp_assoc {S U T X : Scheme.{0}}
    (g : S ⟶ U) (q : U ⟶ T) (p : T ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).hom.app M) ≫
        (Scheme.Modules.pullbackComp g (q ≫ p)).hom.app M =
      (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackComp (g ≫ q) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M := by
  have hunit :
      (Scheme.Modules.pullbackComp g (q ≫ p)).inv.app M ≫
          (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).inv.app M) ≫
          (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback p).obj M) ≫
          (Scheme.Modules.pullbackComp (g ≫ q) p).hom.app M ≫
          (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M = 𝟙 _ := by
    have h := congrArg (fun k => k.app M)
      (Scheme.Modules.pseudofunctor_associativity g q p)
    simpa [NatTrans.comp_app, Scheme.Modules.pullbackCongr] using
      congrArg (fun k => k ≫ (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M) h
  have h := congrArg (fun k =>
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).hom.app M) ≫
        (Scheme.Modules.pullbackComp g (q ≫ p)).hom.app M ≫ k) hunit
  simpa [Category.assoc, ← Functor.map_comp] using h.symm

lemma power_natural {X Y : Scheme.{0}} (a : X ⟶ Y) {M N : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (e : M ⟶ N) (n : ℕ) :
    (pullback_tensorPower_iso X Y a M n).hom ≫
        tensorPowerMap ((Scheme.Modules.pullback a).map e) n =
      (Scheme.Modules.pullback a).map (tensorPowerMap e n) ≫
        (pullback_tensorPower_iso X Y a N n).hom := by
  apply hom_ext_frames
  intro x
  obtain ⟨U, s, hx, hs⟩ := local_frame_exists hM (a x)
  refine ⟨a ⁻¹ᵁ U, Scheme.Modules.pullbackLocalSection a
    (tensorPowerSection Y M n U s), hx,
    pullback_frame _ _ _ (tensorPower_frame M s hs n), ?_⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullback_tensorPower_local_section, tensorPowerMap_section,
    ← Scheme.Modules.pullbackLocalSection_app,
    ← Scheme.Modules.pullbackLocalSection_app, tensorPowerMap_section,
    pullback_tensorPower_local_section]

lemma power_comp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj M) n).hom ≫
        tensorPowerMap ((Scheme.Modules.pullbackComp a g).hom.app M) n =
      (Scheme.Modules.pullback a).map (pullback_tensorPower_iso Y Z g M n).inv ≫
        (Scheme.Modules.pullbackComp a g).hom.app (tensorPower Z M n) ≫
          (pullback_tensorPower_iso X Z (a ≫ g) M n).hom := by
  apply hom_ext_frames
  intro x
  obtain ⟨U, s, hx, hs⟩ := local_frame_exists hM (g (a x))
  refine ⟨a ⁻¹ᵁ (g ⁻¹ᵁ U), Scheme.Modules.pullbackLocalSection a
    (tensorPowerSection Y ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection g s)), hx,
    pullback_frame _ _ _ (tensorPower_frame _ _ (pullback_frame g M s hs) n), ?_⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullback_tensorPower_local_section]
  erw [tensorPowerMap_section, pullback_comp]
  rw [← pullback_tensorPower_local_section Y Z g M n U s,
    ← Scheme.Modules.pullbackLocalSection_app]
  have hcancel : (pullback_tensorPower_iso Y Z g M n).inv.app (g ⁻¹ᵁ U)
      ((pullback_tensorPower_iso Y Z g M n).hom.app (g ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection g (tensorPowerSection Z M n U s))) =
      Scheme.Modules.pullbackLocalSection g (tensorPowerSection Z M n U s) := by
    exact ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f (g ⁻¹ᵁ U))
      (pullback_tensorPower_iso Y Z g M n).hom_inv_id) _
  rw [hcancel]
  change _ = (pullback_tensorPower_iso X Z (a ≫ g) M n).hom.app _
    (((Scheme.Modules.pullbackComp a g).hom.app _).app _
      (Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection g
        (tensorPowerSection Z M n U s))))
  exact ((congrArg (fun v => (pullback_tensorPower_iso X Z (a ≫ g) M n).hom.app
      ((a ≫ g) ⁻¹ᵁ U) v) (pullback_comp a g (tensorPower Z M n) U
        (tensorPowerSection Z M n U s))).trans
      (pullback_tensorPower_local_section X Z (a ≫ g) M n U s)).symm

lemma power_natural_inv {X Y : Scheme.{0}} (a : X ⟶ Y) {M N : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (e : M ⟶ N) (n : ℕ) :
    tensorPowerMap ((Scheme.Modules.pullback a).map e) n ≫
        (pullback_tensorPower_iso X Y a N n).inv =
      (pullback_tensorPower_iso X Y a M n).inv ≫
        (Scheme.Modules.pullback a).map (tensorPowerMap e n) := by
  apply (cancel_epi (pullback_tensorPower_iso X Y a M n).hom).1
  rw [← Category.assoc, power_natural a hM e n]
  simp [Category.assoc]

lemma square_comp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (g : Y ⟶ Z)
    {W : Z.Modules} (A : SquareLine Z W) :
    tensorPowerMap ((Scheme.Modules.pullbackComp a g).hom.app A.line) 2 ≫
        (squarePull (a ≫ g) A).hom =
      (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv ≫
        (Scheme.Modules.pullback a).map (squarePull g A).hom ≫
        (Scheme.Modules.pullbackComp a g).hom.app W := by
  apply (cancel_epi (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).hom).1
  rw [← Category.assoc, power_comp a g A.line A.invertible 2]
  simp only [squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [← (Scheme.Modules.pullbackComp a g).hom.naturality A.square.hom]
  rfl

lemma comp_congr {X Y Z : Scheme.{0}} (a : X ⟶ Y) {u v : Y ⟶ Z}
    (h : u = v) (M : Z.Modules) :
    (Scheme.Modules.pullbackComp a u).hom.app M ≫
        (Scheme.Modules.pullbackCongr (congrArg (fun f => a ≫ f) h)).hom.app M =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackCongr h).hom.app M) ≫
        (Scheme.Modules.pullbackComp a v).hom.app M := by
  subst v
  simp [Scheme.Modules.pullbackCongr]

lemma comp_assoc_reverse {S U T X : Scheme.{0}}
    (g : S ⟶ U) (q : U ⟶ T) (p : T ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackComp (g ≫ q) p).hom.app M =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).hom.app M) ≫
        (Scheme.Modules.pullbackComp g (q ≫ p)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc g q p).symm).hom.app M := by
  have h := congrArg (fun k => k ≫
    (Scheme.Modules.pullbackCongr (Category.assoc g q p).symm).hom.app M)
    (comp_assoc g q p M)
  simpa [Category.assoc, Scheme.Modules.pullbackCongr] using h.symm

lemma triangle_comp {X S Y T B : Scheme.{0}} (a : X ⟶ S)
    (l : S ⟶ Y) (t : S ⟶ T) (p : Y ⟶ B) (r : T ⟶ B)
    (h : l ≫ p = t ≫ r) (W : B.Modules) :
    (Scheme.Modules.pullbackComp a l).hom.app ((Scheme.Modules.pullback p).obj W) ≫
        (Scheme.Modules.pullbackComp (a ≫ l) p).hom.app W ≫
        (Scheme.Modules.pullbackCongr (show (a ≫ l) ≫ p = (a ≫ t) ≫ r by
          simp only [Category.assoc, h])).hom.app W =
      (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackComp l p).hom.app W ≫
          (Scheme.Modules.pullbackCongr h).hom.app W) ≫
        (Scheme.Modules.pullbackComp a (t ≫ r)).hom.app W ≫
        (Scheme.Modules.pullbackCongr (Category.assoc a t r).symm).hom.app W := by
  rw [← Category.assoc, comp_assoc_reverse]
  have hh :
      (Scheme.Modules.pullbackCongr (Category.assoc a l p).symm).hom.app W ≫
        (Scheme.Modules.pullbackCongr (show (a ≫ l) ≫ p = (a ≫ t) ≫ r by
          simp only [Category.assoc, h])).hom.app W =
      (Scheme.Modules.pullbackCongr (congrArg (fun f => a ≫ f) h)).hom.app W ≫
        (Scheme.Modules.pullbackCongr (Category.assoc a t r).symm).hom.app W := by
    simp [Scheme.Modules.pullbackCongr]
  simp only [Category.assoc]
  rw [hh, ← Category.assoc ((Scheme.Modules.pullbackComp a (l ≫ p)).hom.app W),
    comp_congr a h W]
  simp [Functor.map_comp, Category.assoc]

lemma compatible_reindex {B Y T S S' : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d : Lift p H R S) (a : S' ⟶ S)
    (hd : Compatible d) : Compatible (reindex d a) := by
  let C := (Scheme.Modules.pullbackComp a d.toTest).app R.root.line
  let : IsIso (tensorPowerMap C.hom 2) := (tensorPowerIso C 2).isIso_hom
  apply (cancel_epi (tensorPowerMap C.hom 2)).1
  change tensorPowerMap C.hom 2 ≫
      tensorPowerMap (C.inv ≫ (Scheme.Modules.pullback a).map d.iso.hom ≫
        (Scheme.Modules.pullbackComp a d.toLevel).hom.app H.line) 2 ≫
      (squarePull (a ≫ d.toLevel) H).hom ≫
      (Scheme.Modules.pullbackComp (a ≫ d.toLevel) p).hom.app W ≫
      (Scheme.Modules.pullbackCongr (reindex d a).triangle).hom.app W =
    tensorPowerMap C.hom 2 ≫ (squarePull (a ≫ d.toTest) R.root).hom ≫
      (Scheme.Modules.pullbackComp (a ≫ d.toTest) R.map).hom.app W
  have hcancel : tensorPowerMap C.hom 2 ≫ tensorPowerMap C.inv 2 = 𝟙 _ := by
    rw [← tensorPowerMap_comp, C.hom_inv_id, tensorPowerMap_id]
  simp only [tensorPowerMap_comp, Category.assoc]
  rw [← Category.assoc (tensorPowerMap C.hom 2) (tensorPowerMap C.inv 2),
    hcancel, Category.id_comp]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullbackComp a d.toLevel).hom.app H.line) 2),
    square_comp a d.toLevel H]
  change _ = tensorPowerMap ((Scheme.Modules.pullbackComp a d.toTest).hom.app R.root.line) 2 ≫ _
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullbackComp a d.toTest).hom.app R.root.line) 2),
    square_comp a d.toTest R.root]
  simp only [Category.assoc]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullback a).map d.iso.hom) 2),
    power_natural_inv a (R.root.invertible.pullback d.toTest) d.iso.hom 2]
  simp only [Category.assoc]
  rw [triangle_comp a d.toLevel d.toTest p R.map d.triangle W,
    comp_assoc_reverse a d.toTest R.map W]
  have ha := congrArg (fun f => (Scheme.Modules.pullback a).map f) hd
  exact (by
    simpa only [Compatible, Functor.map_comp, Category.assoc, Iso.app,
      reindex, Functor.comp_obj] using
      congrArg (fun k =>
        (pullback_tensorPower_iso S' S a ((Scheme.Modules.pullback d.toTest).obj R.root.line) 2).inv ≫
          k ≫ (Scheme.Modules.pullbackComp a (d.toTest ≫ R.map)).hom.app W ≫
          (Scheme.Modules.pullbackCongr (Category.assoc a d.toTest R.map).symm).hom.app W) ha)

lemma comp_id {S Y : Scheme.{0}} (g : S ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 S) g).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp g)).hom.app M =
        (Scheme.Modules.pullbackId S).hom.app ((Scheme.Modules.pullback g).obj M) := by
  have h := congrArg (fun k => k.app M) (Scheme.Modules.pseudofunctor_right_unitality g)
  have hh : (Scheme.Modules.pullbackComp (𝟙 S) g).inv.app M ≫
      (Scheme.Modules.pullbackId S).hom.app ((Scheme.Modules.pullback g).obj M) =
        (Scheme.Modules.pullbackCongr (Category.id_comp g)).hom.app M := by
    simpa [Scheme.Modules.pullbackCongr] using h
  rw [← hh]
  simp

lemma reindex_id {B Y T S : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d : Lift p H R S) : SameLift (reindex d (𝟙 S)) d := by
  refine ⟨Category.id_comp _, Category.id_comp _, ?_⟩
  apply Iso.ext
  change (Scheme.Modules.pullbackComp (𝟙 S) d.toTest).inv.app R.root.line ≫
      (Scheme.Modules.pullback (𝟙 S)).map d.iso.hom ≫
      (Scheme.Modules.pullbackComp (𝟙 S) d.toLevel).hom.app H.line ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp d.toLevel)).hom.app H.line = _
  rw [comp_id, (Scheme.Modules.pullbackId S).hom.naturality d.iso.hom]
  simp only [Functor.id_map, ← Category.assoc]
  rw [← comp_id d.toTest R.root.line]
  simp

lemma reindex_comp {B Y T S S' S'' : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d : Lift p H R S) (a : S' ⟶ S) (b : S'' ⟶ S') :
    SameLift (reindex (reindex d a) b) (reindex d (b ≫ a)) := by
  refine ⟨(Category.assoc _ _ _).symm, (Category.assoc _ _ _).symm, ?_⟩
  have hc {Z : Scheme.{0}} (f : S ⟶ Z) (M : Z.Modules) :
      (Scheme.Modules.pullback b).mapIso ((Scheme.Modules.pullbackComp a f).app M) ≪≫
          (Scheme.Modules.pullbackComp b (a ≫ f)).app M =
        (Scheme.Modules.pullbackComp b a).app ((Scheme.Modules.pullback f).obj M) ≪≫
          (Scheme.Modules.pullbackComp (b ≫ a) f).app M ≪≫
          (Scheme.Modules.pullbackCongr (Category.assoc b a f)).app M := by
    apply Iso.ext
    exact comp_assoc b a f M
  change (((Scheme.Modules.pullbackComp b (a ≫ d.toTest)).app R.root.line).symm ≪≫
    (Scheme.Modules.pullback b).mapIso
      (((Scheme.Modules.pullbackComp a d.toTest).app R.root.line).symm ≪≫
        (Scheme.Modules.pullback a).mapIso d.iso ≪≫
        (Scheme.Modules.pullbackComp a d.toLevel).app H.line) ≪≫
    (Scheme.Modules.pullbackComp b (a ≫ d.toLevel)).app H.line) ≪≫ _ = _
  have hr : ((Scheme.Modules.pullbackComp b (a ≫ d.toTest)).app R.root.line).symm ≪≫
    (Scheme.Modules.pullback b).mapIso
      (((Scheme.Modules.pullbackComp a d.toTest).app R.root.line).symm ≪≫
        (Scheme.Modules.pullback a).mapIso d.iso ≪≫
        (Scheme.Modules.pullbackComp a d.toLevel).app H.line) ≪≫
    (Scheme.Modules.pullbackComp b (a ≫ d.toLevel)).app H.line =
      ((Scheme.Modules.pullback b).mapIso ((Scheme.Modules.pullbackComp a d.toTest).app R.root.line) ≪≫
        (Scheme.Modules.pullbackComp b (a ≫ d.toTest)).app R.root.line).symm ≪≫
      (Scheme.Modules.pullback b).mapIso ((Scheme.Modules.pullback a).mapIso d.iso) ≪≫
      ((Scheme.Modules.pullback b).mapIso ((Scheme.Modules.pullbackComp a d.toLevel).app H.line) ≪≫
        (Scheme.Modules.pullbackComp b (a ≫ d.toLevel)).app H.line) := by simp
  rw [hr, hc, hc]
  apply Iso.ext
  simp [reindex, ← Functor.comp_map, Scheme.Modules.pullbackCongr]
  erw [Category.id_comp]

end RootTestPullbackCoherenceR0196
/-- Square-compatible relative lifts form a coherent system under every test map. -/
theorem root_test_pullback_coherence
    (B Y : Scheme.{0}) (W : B.Modules) (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W))
    (T : Scheme.{0}) (R : RootObject B W T) (S : Scheme.{0})
    (d : Lift p H R S) (hd : Compatible d) :
    (∀ (S' : Scheme.{0}) (a : S' ⟶ S), Compatible (reindex d a)) ∧
      SameLift (reindex d (𝟙 S)) d ∧
      (∀ (S' S'' : Scheme.{0}) (a : S' ⟶ S) (b : S'' ⟶ S'),
        SameLift (reindex (reindex d a) b) (reindex d (b ≫ a))) := by
  exact ⟨fun _ a => RootTestPullbackCoherenceR0196.compatible_reindex d a hd,
    RootTestPullbackCoherenceR0196.reindex_id d,
    fun _ _ a b => RootTestPullbackCoherenceR0196.reindex_comp d a b⟩

#print axioms root_test_pullback_coherence
end ArithmeticThetaMetaplecticTestsR0196
