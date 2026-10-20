module

public import ActualMetaplecticPullbackR0206
public import MetaplecticFiberEquivalenceR0206

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

namespace NaturalComparisonProof
variable {k : Type} [Field k] [CharZero k] {L : ℕ}
  {A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L}
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C}
  {S T : Over (Base k)}

/-- Full-level rigidity makes the actual line-forgetful functor faithful. -/
lemma line_faithful (H : HodgeUniversal k L A B C Q) (G : GroupoidData L S.left)
    {X Y : G.Objects} (f g : X ⟶ Y)
    (hl : (G.arrow _ _ f).line.hom = (G.arrow _ _ g).line.hom) : f = g := by
  obtain ⟨b, ⟨p, hp, _⟩, _⟩ := H.1.1 S.left S.hom X.family X.marking
  obtain ⟨c, ⟨q, hq, _⟩, _⟩ := H.1.1 S.left S.hom Y.family Y.marking
  have hf := H.1.2.2 S.left S.left S.hom S.hom Y.family X.family Y.marking X.marking
    (𝟙 S.left) (G.arrow _ _ f).curve.hom (Category.id_comp _) (G.arrow _ _ f).marked
    c b q p hq hp
  have hg := H.1.2.2 S.left S.left S.hom S.hom Y.family X.family Y.marking X.marking
    (𝟙 S.left) (G.arrow _ _ g).curve.hom (Category.id_comp _) (G.arrow _ _ g).marked
    c b q p hq hp
  apply FiberEquivalenceProof.hom_ext G f g _ hl
  apply hq.2.1.hom_ext
  · exact hf.2.symm.trans hg.2
  · exact (G.arrow _ _ f).marked.1.w.trans (G.arrow _ _ g).marked.1.w.symm

/-- The normalized root square transports to an actual arrow between any
two models of the same marked family classifier. -/
lemma arrow_of_square (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m n : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family))
    (K : SquareLine S.left (Cotangent n.family))
    (l : J.line ≅ K.line)
    (hs : tensorPowerMap l.hom 2 ≫ K.square.hom ≫ n.hodge.inv =
      J.square.hom ≫ m.hodge.inv) :
    ∃ f : Arrow ⟨m.family, m.marking, J⟩ ⟨n.family, n.marking, K⟩,
      f.line.hom = l.hom := by
  obtain ⟨g, ⟨hg, ht⟩, _⟩ := marked_cartesian_reconstruction k L hL heven A B C Q
    S.left S.left S.hom S.hom n.family m.family n.marking m.marking (𝟙 S.left)
    b.val b.val n.curve m.curve (Category.id_comp _) n.classifies m.classifies
    (Category.id_comp _).symm
  let : IsIso g := hg.1.isIso_fst_of_isIso
  let d := ActualGroupoidProof.backward g hg.1 hg.2.1
  have hd : n.hodge.hom ≫ d.hom = m.hodge.hom :=
    FiberEquivalenceProof.hodge_backward H n m g hg ht
  refine ⟨{
    curve := asIso g
    marked := hg
    cotangent := d.symm
    canonical := ActualGroupoidProof.backward_canonical g hg.1 hg.2.1
    line := l
    square := ?_
  }, rfl⟩
  apply (cancel_mono d.hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := congrArg (fun q => q ≫ m.hodge.hom) hs
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [← hd] at hh
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh

lemma common_root_arrow (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m n : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family))
    (K : SquareLine S.left (Cotangent n.family))
    (r : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
      (ModularHodge k L A B C Q) (Over.mk b.val))
    (e : r.line ≅ J.line) (f : r.line ≅ K.line)
    (he : tensorPowerMap e.hom 2 ≫ J.square.hom = r.square.hom ≫ m.hodge.hom)
    (hf : tensorPowerMap f.hom 2 ≫ K.square.hom = r.square.hom ≫ n.hodge.hom) :
    ∃ g : Arrow ⟨m.family, m.marking, J⟩ ⟨n.family, n.marking, K⟩,
      g.line.hom = e.inv ≫ f.hom := by
  apply arrow_of_square hL heven H m n J K (e.symm ≪≫ f)
  simp only [Iso.trans_hom, Iso.symm_hom, tensorPowerMap_comp, Category.assoc]
  rw [← Category.assoc (tensorPowerMap f.hom 2), hf]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun q => tensorPowerMap e.inv 2 ≫ q ≫ m.hodge.inv) he
  simp only [← Category.assoc, ← tensorPowerMap_comp, Iso.inv_hom_id,
    tensorPowerMap_id, Category.id_comp] at hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

lemma square_pull_map {U V : Scheme.{0}} (a : V ⟶ U)
    {M N : U.Modules} (J : SquareLine U M) (K : SquareLine U N)
    (l : J.line ⟶ K.line) (d : M ⟶ N)
    (h : tensorPowerMap l 2 ≫ K.square.hom = J.square.hom ≫ d) :
    tensorPowerMap ((Scheme.Modules.pullback a).map l) 2 ≫ (squarePull a K).hom =
      (squarePull a J).hom ≫ (Scheme.Modules.pullback a).map d := by
  simp only [squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc,
    ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.power_natural_inv
      a J.invertible l 2]
  simp only [Category.assoc]
  rw [← Functor.map_comp, h, Functor.map_comp]

variable {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (ES : FiberComparison k L A B C Q S GS) (ET : FiberComparison k L A B C Q T GT)
    (a : T ⟶ S) (P : PullbackData GS GT a.left)

/-- Objectwise existence fixes the entire line map, including its sign. -/
lemma component_exists (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q) (r : RootFiber k L A B C Q S) :
    ∃ f : (rootReindex k L A B C Q a ⋙ ET.equiv.functor).obj r ⟶
        (ES.equiv.functor ⋙ P.functor).obj r,
      (GT.arrow _ _ f).line.hom =
        ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫
          (Scheme.Modules.pullback a.left).map (ES.line.hom.app r) ≫
            (P.line (ES.equiv.functor.obj r)).inv := by
  let rr := (rootReindex k L A B C Q a).obj r
  let X := ES.equiv.functor.obj r
  let Y := ET.equiv.functor.obj rr
  let Z := P.functor.obj X
  have hz : Classifies k L A B C Q T.hom Z.family Z.marking
      (a.left ≫ r.1.val) (P.curve X ≫ ES.curve r) :=
    SchemeFullLevelUniversal.classifies_comp A (Over.w a) (P.marked X) (ES.classifies r)
  obtain ⟨eZ, heZ, _⟩ := H.2.1 T.left T.hom Z.family Z.marking
    (a.left ≫ r.1.val) (P.curve X ≫ ES.curve r) hz
  let m : FiberEquivalenceProof.Model rr.1 :=
    ⟨Y.family, Y.marking, ET.curve rr, ET.classifies rr, ET.cotangent rr, ET.canonical rr⟩
  let n : FiberEquivalenceProof.Model rr.1 :=
    ⟨Z.family, Z.marking, P.curve X ≫ ES.curve r, hz, eZ, heZ⟩
  let u : rr.2.line ≅ Z.root.line :=
    (Scheme.Modules.pullback a.left).mapIso (ES.line.app r) ≪≫ (P.line X).symm
  have hn := H.2.2 S.left T.left X.family Z.family a.left (P.curve X)
    (P.marked X).2.1 r.1.val (ES.curve r) (ES.cotangent r) eZ (P.cotangent X)
    (ES.canonical r) heZ (P.canonical X)
  have hu : tensorPowerMap u.hom 2 ≫ Z.root.square.hom = rr.2.square.hom ≫ eZ.hom := by
    change tensorPowerMap
      ((Scheme.Modules.pullback a.left).map (ES.line.hom.app r) ≫ (P.line X).inv) 2 ≫
        Z.root.square.hom = _
    rw [← P.square X]
    simp only [tensorPowerMap_comp, Category.assoc]
    rw [← Category.assoc (tensorPowerMap (P.line X).inv 2), ← tensorPowerMap_comp,
      Iso.inv_hom_id, tensorPowerMap_id, Category.id_comp]
    calc
      _ = (tensorPowerMap ((Scheme.Modules.pullback a.left).map (ES.line.hom.app r)) 2 ≫
          (squarePull a.left X.root).hom) ≫ (P.cotangent X).hom :=
        (Category.assoc _ _ _).symm
      _ = ((squarePull a.left r.2).hom ≫
          (Scheme.Modules.pullback a.left).map (ES.cotangent r).hom) ≫ (P.cotangent X).hom :=
        congrArg (fun q => q ≫ (P.cotangent X).hom)
          (square_pull_map a.left r.2 X.root (ES.line.hom.app r) (ES.cotangent r).hom (ES.square r))
      _ = (squarePull a.left r.2).hom ≫
          (Scheme.Modules.pullbackComp a.left r.1.val).hom.app _ ≫ eZ.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun q => (squarePull a.left r.2).hom ≫ q) hn)
      _ = rr.2.square.hom ≫ eZ.hom := by
        change _ = (((squarePull a.left r.2).hom ≫
          (Scheme.Modules.pullbackComp a.left r.1.val).hom.app _) ≫
          (Scheme.Modules.pullbackCongr (show a.left ≫ r.1.val = a.left ≫ r.1.val from rfl)).hom.app _) ≫ eZ.hom
        simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
          NatTrans.id_app, Category.comp_id, Category.assoc]
  obtain ⟨f, hf⟩ := common_root_arrow hL heven H m n Y.root Z.root rr.2
    (ET.line.app rr) u (ET.square rr) hu
  refine ⟨(GT.arrow _ _).symm f, ?_⟩
  simp only [Equiv.apply_symm_apply]
  simpa only [u, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv] using hf

lemma reindex_line_map {r s : RootFiber k L A B C Q S} (f : r ⟶ s) :
    (rootForget k L A B C Q T).map ((rootReindex k L A B C Q a).map f) =
      (Scheme.Modules.pullback a.left).map ((rootForget k L A B C Q S).map f) := by
  rcases r with ⟨b, r⟩
  rcases s with ⟨c, s⟩
  rcases f with ⟨f⟩
  rfl

lemma normalized_naturality (H : HodgeUniversal k L A B C Q)
    (e : ∀ r, (rootReindex k L A B C Q a ⋙ ET.equiv.functor).obj r ⟶
      (ES.equiv.functor ⋙ P.functor).obj r)
    (he : ∀ r, (GT.arrow _ _ (e r)).line.hom =
      ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫
        (Scheme.Modules.pullback a.left).map (ES.line.hom.app r) ≫
          (P.line (ES.equiv.functor.obj r)).inv)
    {r s : RootFiber k L A B C Q S} (f : r ⟶ s) :
    (rootReindex k L A B C Q a ⋙ ET.equiv.functor).map f ≫ e s =
      e r ≫ (ES.equiv.functor ⋙ P.functor).map f := by
  apply line_faithful H GT
  simp only [GT.line_comp, he, Functor.comp_map]
  apply (cancel_mono (P.line (ES.equiv.functor.obj s)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [P.line_natural (ES.equiv.functor.obj r) (ES.equiv.functor.obj s) (ES.equiv.functor.map f)]
  simp only [Iso.inv_hom_id_assoc]
  have ht := ET.line.inv.naturality ((rootReindex k L A B C Q a).map f)
  change (GT.arrow _ _ (ET.equiv.functor.map ((rootReindex k L A B C Q a).map f))).line.hom ≫
      ET.line.inv.app ((rootReindex k L A B C Q a).obj s) =
    ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫
      (rootForget k L A B C Q T).map ((rootReindex k L A B C Q a).map f) at ht
  rw [reindex_line_map a f] at ht
  have hs := congrArg ((Scheme.Modules.pullback a.left).map) (ES.line.hom.naturality f)
  change (Scheme.Modules.pullback a.left).map
      ((rootForget k L A B C Q S).map f ≫ ES.line.hom.app s) =
    (Scheme.Modules.pullback a.left).map
      (ES.line.hom.app r ≫ (GS.arrow _ _ (ES.equiv.functor.map f)).line.hom) at hs
  simp only [Functor.map_comp] at hs
  calc
    _ = ((GT.arrow _ _ (ET.equiv.functor.map ((rootReindex k L A B C Q a).map f))).line.hom ≫
        ET.line.inv.app ((rootReindex k L A B C Q a).obj s)) ≫
          (Scheme.Modules.pullback a.left).map (ES.line.hom.app s) := (Category.assoc _ _ _).symm
    _ = (ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫
        (Scheme.Modules.pullback a.left).map ((rootForget k L A B C Q S).map f)) ≫
          (Scheme.Modules.pullback a.left).map (ES.line.hom.app s) :=
      congrArg (fun q => q ≫ (Scheme.Modules.pullback a.left).map (ES.line.hom.app s)) ht
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun q => ET.line.inv.app ((rootReindex k L A B C Q a).obj r) ≫ q) hs)

lemma normalized_exists_unique (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q) :
    ∃! e : rootReindex k L A B C Q a ⋙ ET.equiv.functor ≅ ES.equiv.functor ⋙ P.functor,
      BaseChangeCompatible k L A B C Q ES ET a P e := by
  choose f hf using component_exists ES ET a P hL heven H
  let e := NatIso.ofComponents (fun r => asIso (f r))
    (fun g => normalized_naturality ES ET a P H f hf g)
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext r
  exact line_faithful H GT _ _ ((he' r).trans (hf r).symm)

end NaturalComparisonProof
/-- The unique line-normalized comparison for arbitrary choices, followed by
one fixed quotient and a simultaneous system over every small test scheme. -/
theorem natural_metaplectic_comparison :
    (∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C), ArithmeticThetaSchemeHodgeR0205.HodgeUniversal k L A B C Q → ∀ (S T : CategoryTheory.Over (ArithmeticThetaLocalWeierstrassR0203.Base k)) (GS : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L S.left) (GT : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L T.left) (ES : ArithmeticThetaMetaplecticComparisonR0206.FiberComparison k L A B C Q S GS) (ET : ArithmeticThetaMetaplecticComparisonR0206.FiberComparison k L A B C Q T GT) (a : Quiver.Hom T S) (P : ArithmeticThetaMetaplecticComparisonR0206.PullbackData GS GT (CategoryTheory.Over.Hom.left a)), ∃! e : CategoryTheory.Iso (CategoryTheory.Functor.comp (ArithmeticThetaMetaplecticComparisonR0206.rootReindex k L A B C Q a) ET.equiv.functor) (CategoryTheory.Functor.comp ES.equiv.functor P.functor), ArithmeticThetaMetaplecticComparisonR0206.BaseChangeCompatible k L A B C Q ES ET a P e) ∧ (∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L), ∃ (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C), ArithmeticThetaSchemeHodgeR0205.HodgeUniversal k L A B C Q ∧ ArithmeticThetaMetaplecticComparisonR0206.ComparisonSystem k L A B C Q) := by
  constructor
  · intro k _ _ L hL heven A B C Q H S T GS GT ES ET a P
    exact NaturalComparisonProof.normalized_exists_unique ES ET a P hL heven H
  · intro k _ _ L hL heven A
    obtain ⟨B, hB, C, Q, H⟩ := scheme_hodge_universal k L hL heven A
    let G : ∀ S : Over (Base k), GroupoidData L S.left :=
      fun S => Classical.choice (actual_metaplectic_groupoid L S.left)
    let E : ∀ S : Over (Base k), FiberComparison k L A B C Q S (G S) :=
      fun S => Classical.choice (metaplectic_fiber_equivalence k L hL heven A B C Q H S (G S))
    refine ⟨B, hB, C, Q, H, G, E, ?_⟩
    intro S T a
    obtain ⟨P⟩ := actual_metaplectic_pullback L S.left T.left (G S) (G T) a.left
    exact ⟨P, NaturalComparisonProof.normalized_exists_unique (E S) (E T) a P hL heven H⟩

#print axioms natural_metaplectic_comparison
end ArithmeticThetaMetaplecticComparisonR0206
