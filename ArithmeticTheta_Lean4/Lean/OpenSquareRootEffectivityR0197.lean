import RootDescentDefinitionsR0197

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe v
namespace ArithmeticThetaRootDescentR0197
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
namespace OpenSquareRootEffectivityR0197
open RootTestPullbackCoherenceR0196

lemma invertible_of_iso {X : Scheme.{0}} {M N : X.Modules}
    (e : M ≅ N) (hN : Scheme.Modules.IsInvertible N) :
    Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := hN.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e ≪≫ t⟩⟩

lemma invertible_of_open_cover {B : Scheme.{0}} {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ b : B, ∃ i, b ∈ Set.range (f i).base) (M : B.Modules)
    (hM : ∀ i, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (f i)).obj M)) :
    Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := hf x
  obtain ⟨U, hy, ⟨t⟩⟩ := (hM i).1 y
  let e : (U : Scheme.{0}) ≅ ↑(f i ''ᵁ U) := (f i).isoImage U
  have fact : (f i ''ᵁ U).ι = e.inv ≫ U.ι ≫ f i := by
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc]
  refine ⟨f i ''ᵁ U, ⟨y, hy, rfl⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr fact).app M ≪≫
    ((Scheme.Modules.pullbackComp e.inv (U.ι ≫ f i)).app M).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso
      (((Scheme.Modules.pullbackComp U.ι (f i)).app M).symm ≪≫ t) ≪≫
    Scheme.Modules.pullbackUnitIso e.inv

/-- Comparison to the specified common test map. -/
def compare {S X B : Scheme.{0}} (a : S ⟶ X) (f : X ⟶ B)
    (p : S ⟶ B) (h : a ≫ f = p) (M : B.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackComp a f).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

lemma canonical_hom {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    (f : ∀ i, V i ⟶ B) (M : B.Modules) {S : Scheme.{0}} (p : S ⟶ B)
    {i j : ι} (a : S ⟶ V i) (b : S ⟶ V j) (ha : a ≫ f i = p) (hb : b ≫ f j = p) :
    ((descent f).obj M).hom p a b ha hb =
      (compare a (f i) p ha M).hom ≫ (compare b (f j) p hb M).inv := by
  change (moduleFunctor.mapComp' (f i).op.toLoc a.op.toLoc p.op.toLoc _).inv.toNatTrans.app M ≫
      (moduleFunctor.mapComp' (f j).op.toLoc b.op.toLoc p.op.toLoc _).hom.toNatTrans.app M = _
  rw [P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar.Mdl_mapComp'_inv_app a (f i) M p ha,
    P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar.Mdl_mapComp'_hom_app b (f j) M p hb]
  simp [compare, Scheme.Modules.pullbackCongr, Category.assoc]

lemma power_compare {S X B : Scheme.{0}} (a : S ⟶ X) (f : X ⟶ B)
    (p : S ⟶ B) (h : a ≫ f = p) (M : B.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    (Scheme.Modules.pullback a).map (pullback_tensorPower_iso X B f M n).hom ≫
      (pullback_tensorPower_iso S X a ((Scheme.Modules.pullback f).obj M) n).hom ≫
      tensorPowerMap (compare a f p h M).hom n =
    (compare a f p h (tensorPower B M n)).hom ≫
      (pullback_tensorPower_iso S B p M n).hom := by
  subst p
  simp only [compare, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.app,
    Iso.trans_hom, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  rw [power_comp a f M hM n]
  simp [← Functor.map_comp]

/-- Tensor comparison commutes with the canonical descent transitions. -/
lemma power_transition {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    (f : ∀ i, V i ⟶ B) (M : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    {S : Scheme.{0}} (p : S ⟶ B) {i j : ι}
    (a : S ⟶ V i) (b : S ⟶ V j) (ha : a ≫ f i = p) (hb : b ≫ f j = p) :
    (Scheme.Modules.pullback a).map (pullback_tensorPower_iso (V i) B (f i) M 2).hom ≫
      (pullback_tensorPower_iso S (V i) a ((Scheme.Modules.pullback (f i)).obj M) 2).hom ≫
      tensorPowerMap (((descent f).obj M).hom p a b ha hb) 2 =
    (((descent f).obj (tensorPower B M 2)).hom p a b ha hb) ≫
      (Scheme.Modules.pullback b).map (pullback_tensorPower_iso (V j) B (f j) M 2).hom ≫
      (pullback_tensorPower_iso S (V j) b ((Scheme.Modules.pullback (f j)).obj M) 2).hom := by
  rw [canonical_hom, canonical_hom, tensorPowerMap_comp]
  haveI : IsIso (tensorPowerMap (compare b (f j) p hb M).hom 2) :=
    (tensorPowerIso (compare b (f j) p hb M) 2).isIso_hom
  apply (cancel_mono (tensorPowerMap (compare b (f j) p hb M).hom 2)).1
  simp only [Category.assoc]
  rw [← tensorPowerMap_comp, Iso.inv_hom_id, tensorPowerMap_id, Category.comp_id]
  rw [power_compare a (f i) p ha M hM 2]
  rw [power_compare b (f j) p hb M hM 2]
  simp

/-- Evaluation of an actual descent isomorphism on one member of the cover. -/
def componentIso {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    {f : ∀ i, V i ⟶ B} {M : B.Modules} {W : B.Modules}
    (D : RootDatum W f) (e : (descent f).obj M ≅ D.data) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj M ≅ D.data.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := congrArg (fun t => t.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun t => t.hom i) e.inv_hom_id

lemma pull_square_map {X Y : Scheme.{0}} (a : X ⟶ Y)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    {W : Y.Modules} (K : SquareLine Y W) (t : M ⟶ K.line) :
    (Scheme.Modules.pullback a).map (tensorPowerMap t 2 ≫ K.square.hom) =
      (pullback_tensorPower_iso X Y a M 2).hom ≫
        tensorPowerMap ((Scheme.Modules.pullback a).map t) 2 ≫ (squarePull a K).hom := by
  simp only [squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp]
  rw [← Category.assoc (pullback_tensorPower_iso X Y a M 2).hom,
    power_natural a hM t 2]
  simp [Category.assoc]

/-- The local square isomorphisms on the effective module. -/
def localSquare {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    {f : ∀ i, V i ⟶ B} {M W : B.Modules} (D : RootDatum W f)
    (e : (descent f).obj M ≅ D.data) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (tensorPower B M 2) ≅
      (Scheme.Modules.pullback (f i)).obj W :=
  pullback_tensorPower_iso (V i) B (f i) M 2 ≪≫
    tensorPowerIso (componentIso D e i) 2 ≪≫ D.square i

lemma localSquare_comm {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    {f : ∀ i, V i ⟶ B} {M W : B.Modules} (D : RootDatum W f)
    (e : (descent f).obj M ≅ D.data) (hM : Scheme.Modules.IsInvertible M)
    (hD : CompatibleSquares D) {S : Scheme.{0}} (p : S ⟶ B) {i j : ι}
    (a : S ⟶ V i) (b : S ⟶ V j) (ha : a ≫ f i = p) (hb : b ≫ f j = p) :
    (Scheme.Modules.pullback a).map (localSquare D e i).hom ≫
        ((descent f).obj W).hom p a b ha hb =
      ((descent f).obj (tensorPower B M 2)).hom p a b ha hb ≫
        (Scheme.Modules.pullback b).map (localSquare D e j).hom := by
  have hs := hD S p i j a b ha hb
  change tensorPowerMap (D.data.hom p a b ha hb) 2 ≫
      (squarePull b (localRoot D j)).hom ≫ (compare b (f j) p hb W).hom =
    (squarePull a (localRoot D i)).hom ≫ (compare a (f i) p ha W).hom at hs
  have he := e.hom.comm p a b ha hb
  change (Scheme.Modules.pullback a).map (e.hom.hom i) ≫ D.data.hom p a b ha hb =
    ((descent f).obj M).hom p a b ha hb ≫ (Scheme.Modules.pullback b).map (e.hom.hom j) at he
  have ht := congrArg (fun t => tensorPowerMap t 2) he
  rw [tensorPowerMap_comp, tensorPowerMap_comp] at ht
  have hi : (localSquare D e i).hom =
      (pullback_tensorPower_iso (V i) B (f i) M 2).hom ≫
        (tensorPowerMap (e.hom.hom i) 2 ≫ (localRoot D i).square.hom) := rfl
  have hj : (localSquare D e j).hom =
      (pullback_tensorPower_iso (V j) B (f j) M 2).hom ≫
        (tensorPowerMap (e.hom.hom j) 2 ≫ (localRoot D j).square.hom) := rfl
  rw [canonical_hom f W p a b ha hb]
  apply (cancel_mono (compare b (f j) p hb W).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi, hj, (Scheme.Modules.pullback a).map_comp,
    pull_square_map a (hM.pullback (f i)) (localRoot D i),
    (Scheme.Modules.pullback b).map_comp,
    pull_square_map b (hM.pullback (f j)) (localRoot D j)]
  simp only [Category.assoc]
  rw [← hs]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullback a).map (e.hom.hom i)) 2), ht]
  have hp := power_transition f M hM p a b ha hb
  simp only [← Category.assoc] at hp ⊢
  rw [hp]

/-- Gluing the square map uses the same module descent isomorphism. -/
def squareDescentIso {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    {f : ∀ i, V i ⟶ B} {M W : B.Modules} (D : RootDatum W f)
    (e : (descent f).obj M ≅ D.data) (hM : Scheme.Modules.IsInvertible M)
    (hD : CompatibleSquares D) :
    (descent f).obj (tensorPower B M 2) ≅ (descent f).obj W :=
  Pseudofunctor.DescentData.isoMk (localSquare D e)
    (fun {_} p {_ _} a b ha hb => localSquare_comm D e hM hD p a b ha hb)

end OpenSquareRootEffectivityR0197

open OpenSquareRootEffectivityR0197 in
/-- Compatible specified square roots glue along every jointly surjective family
of open immersions, with no restriction on the indexing universe. -/
theorem open_square_root_effectivity
    (B : Scheme.{0}) (ι : Type v) (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ B)
    (hf : ∀ i, IsOpenImmersion (f i))
    (hcover : ∀ b : B, ∃ i, b ∈ Set.range (f i).base)
    (W : B.Modules) (_hW : Scheme.Modules.IsInvertible W)
    (D : RootDatum W f) (hD : CompatibleSquares D) : Effective D := by
  letI : ∀ i, IsOpenImmersion (f i) := hf
  letI : (descent f).EssSurj := Scheme.Modules.toDescentData_essSurj_of_openCover f hcover
  let M := (descent f).objPreimage D.data
  let e : (descent f).obj M ≅ D.data := (descent f).objObjPreimageIso D.data
  have hM : Scheme.Modules.IsInvertible M := invertible_of_open_cover f hcover M
    (fun i => invertible_of_iso (componentIso D e i) (D.invertible i))
  let ff : (descent f).FullyFaithful := Classical.choice
    ((Functor.FullyFaithful.nonempty_iff_map_bijective (descent f)).2
      (Scheme.Modules.toDescentData_map_bijective_of_openCover f hcover))
  let sq : tensorPower B M 2 ≅ W := ff.preimageIso (squareDescentIso D e hM hD)
  refine ⟨⟨M, hM, sq⟩, e, ?_⟩
  intro i
  have hs := congrArg (fun t => t.hom i)
    (ff.map_preimage (squareDescentIso D e hM hD).hom)
  change (Scheme.Modules.pullback (f i)).map sq.hom = (localSquare D e i).hom at hs
  change tensorPowerMap (e.hom.hom i) 2 ≫ (D.square i).hom =
    (pullback_tensorPower_iso (V i) B (f i) M 2).inv ≫
      (Scheme.Modules.pullback (f i)).map sq.hom
  rw [hs]
  simp [localSquare, tensorPowerIso, componentIso, Category.assoc]

#print axioms open_square_root_effectivity
end ArithmeticThetaRootDescentR0197
