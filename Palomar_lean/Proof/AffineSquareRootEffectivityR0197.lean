module

public import RootDescentDefinitionsR0197
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
public import RootTestPullbackCoherenceR0196
public import CompactDiscriminantSectionR0182

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaRootDescentR0197
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaCoverComparison ArithmeticThetaSquareLinesR0192
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196
namespace AffineSquareRootEffectivityR0197

def triangle {S Y B : Scheme.{0}} (a : S ⟶ Y) (q : Y ⟶ B)
    (p : S ⟶ B) (h : a ≫ q = p) (M : B.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackComp a q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

lemma canonical_hom {B Y S : Scheme.{0}} (q : Y ⟶ B) (M : B.Modules)
    (p : S ⟶ B) (a b : S ⟶ Y) (ha : a ≫ q = p) (hb : b ≫ q = p) :
    ((descent (fun _ : Unit => q)).obj M).hom p (i₁ := ()) (i₂ := ()) a b ha hb =
      (triangle a q p ha M).hom ≫ (triangle b q p hb M).inv := by
  change (moduleFunctor.mapComp' q.op.toLoc a.op.toLoc p.op.toLoc _).inv.toNatTrans.app M ≫
    (moduleFunctor.mapComp' q.op.toLoc b.op.toLoc p.op.toLoc _).hom.toNatTrans.app M = _
  rw [P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar.Mdl_mapComp'_inv_app a q M p ha,
    P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar.Mdl_mapComp'_hom_app b q M p hb]
  simp [triangle, Scheme.Modules.pullbackCongr]

lemma power_triangle {S Y B : Scheme.{0}} (a : S ⟶ Y) (q : Y ⟶ B)
    (p : S ⟶ B) (h : a ≫ q = p) (M : B.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    (Scheme.Modules.pullback a).map (pullback_tensorPower_iso Y B q M n).hom ≫
      (pullback_tensorPower_iso S Y a ((Scheme.Modules.pullback q).obj M) n).hom ≫
      tensorPowerMap (triangle a q p h M).hom n =
    (triangle a q p h (tensorPower B M n)).hom ≫
      (pullback_tensorPower_iso S B p M n).hom := by
  subst p
  simp only [triangle, Scheme.Modules.pullbackCongr, Iso.trans_hom,
    Iso.app_hom, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  rw [power_comp a q M hM n]
  simp [← Functor.map_comp, ← Category.assoc]

lemma power_triangle_inv {S Y B : Scheme.{0}} (a : S ⟶ Y) (q : Y ⟶ B)
    (p : S ⟶ B) (h : a ≫ q = p) (M : B.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    (pullback_tensorPower_iso S B p M n).hom ≫
      tensorPowerMap (triangle a q p h M).inv n =
    (triangle a q p h (tensorPower B M n)).inv ≫
      (Scheme.Modules.pullback a).map (pullback_tensorPower_iso Y B q M n).hom ≫
      (pullback_tensorPower_iso S Y a ((Scheme.Modules.pullback q).obj M) n).hom := by
  let T := triangle a q p h M
  letI : IsIso (tensorPowerMap T.hom n) := (tensorPowerIso T n).isIso_hom
  apply (cancel_mono (tensorPowerMap T.hom n)).1
  simp only [Category.assoc]
  rw [← tensorPowerMap_comp, T.inv_hom_id, tensorPowerMap_id, Category.comp_id]
  change _ = (triangle a q p h (tensorPower B M n)).inv ≫
    ((Scheme.Modules.pullback a).map (pullback_tensorPower_iso Y B q M n).hom ≫
      (pullback_tensorPower_iso S Y a ((Scheme.Modules.pullback q).obj M) n).hom ≫
      tensorPowerMap (triangle a q p h M).hom n)
  rw [power_triangle a q p h M hM n]
  simp [Category.assoc]

/-- The local square map after identifying the effective line with the datum. -/
def localSquare {B Y : Scheme.{0}} (q : Y ⟶ B) {W : B.Modules}
    (D : RootDatum W (fun _ : Unit => q)) (L : B.Modules)
    (e : (descent (fun _ : Unit => q)).obj L ≅ D.data) (i : Unit) :
    (Scheme.Modules.pullback q).obj (tensorPower B L 2) ≅
      (Scheme.Modules.pullback q).obj W :=
  pullback_tensorPower_iso Y B q L 2 ≪≫
    tensorPowerIso
      { hom := e.hom.hom i
        inv := e.inv.hom i
        hom_inv_id := by
          have h := congrArg (fun z => z.hom i) e.hom_inv_id
          exact h
        inv_hom_id := by
          have h := congrArg (fun z => z.hom i) e.inv_hom_id
          exact h } 2 ≪≫ D.square i

lemma transported_square {B Y S : Scheme.{0}} (q : Y ⟶ B) {W : B.Modules}
    (D : RootDatum W (fun _ : Unit => q)) (L : B.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (e : (descent (fun _ : Unit => q)).obj L ≅ D.data)
    (p : S ⟶ B) (a : S ⟶ Y) (ha : a ≫ q = p) (i : Unit) :
    (triangle a q p ha (tensorPower B L 2)).inv ≫
        (Scheme.Modules.pullback a).map (localSquare q D L e i).hom ≫
        (triangle a q p ha W).hom =
      (pullback_tensorPower_iso S B p L 2).hom ≫
        tensorPowerMap ((triangle a q p ha L).inv ≫
          (Scheme.Modules.pullback a).map (e.hom.hom i)) 2 ≫
        (squarePull a (localRoot D i)).hom ≫ (triangle a q p ha W).hom := by
  simp only [tensorPowerMap_comp, Category.assoc]
  rw [← Category.assoc (pullback_tensorPower_iso S B p L 2).hom,
    power_triangle_inv a q p ha L hL 2]
  simp only [Category.assoc, squarePull, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  dsimp only [localRoot]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullback a).map (e.hom.hom i)) 2)]
  erw [power_natural_inv a (hL.pullback q) (e.hom.hom i) 2]
  simp [localSquare, tensorPowerIso, Functor.map_comp, Category.assoc]

/-- Square compatibility gives an isomorphism of the canonical descent data. -/
def squareDescentIso {B Y : Scheme.{0}} (q : Y ⟶ B) {W : B.Modules}
    (D : RootDatum W (fun _ : Unit => q)) (hD : CompatibleSquares D)
    (L : B.Modules) (hL : Scheme.Modules.IsInvertible L)
    (e : (descent (fun _ : Unit => q)).obj L ≅ D.data) :
    (descent (fun _ : Unit => q)).obj (tensorPower B L 2) ≅
      (descent (fun _ : Unit => q)).obj W :=
  Pseudofunctor.DescentData.isoMk (fun i => localSquare q D L e i) (by
    intro S p i j a b ha hb
    cases i
    cases j
    have he := e.hom.comm p (i₁ := ()) (i₂ := ()) a b ha hb
    change (Scheme.Modules.pullback a).map (e.hom.hom ()) ≫ D.data.hom p (i₁ := ()) (i₂ := ()) a b ha hb =
      ((descent (fun _ : Unit => q)).obj L).hom p (i₁ := ()) (i₂ := ()) a b ha hb ≫
        (Scheme.Modules.pullback b).map (e.hom.hom ()) at he
    rw [canonical_hom] at he
    have he' : ((triangle a q p ha L).inv ≫
        (Scheme.Modules.pullback a).map (e.hom.hom ())) ≫ D.data.hom p (i₁ := ()) (i₂ := ()) a b ha hb =
      (triangle b q p hb L).inv ≫ (Scheme.Modules.pullback b).map (e.hom.hom ()) := by
      rw [Category.assoc, he]
      simp [Category.assoc]
    have hs : tensorPowerMap (D.data.hom p (i₁ := ()) (i₂ := ()) a b ha hb) 2 ≫
        (squarePull b (localRoot D ())).hom ≫ (triangle b q p hb W).hom =
      (squarePull a (localRoot D ())).hom ≫ (triangle a q p ha W).hom := by
      simpa only [triangle, Iso.trans_hom, Category.assoc] using hD S p () () a b ha hb
    have ht : (triangle a q p ha (tensorPower B L 2)).inv ≫
        (Scheme.Modules.pullback a).map (localSquare q D L e ()).hom ≫
        (triangle a q p ha W).hom =
      (triangle b q p hb (tensorPower B L 2)).inv ≫
        (Scheme.Modules.pullback b).map (localSquare q D L e ()).hom ≫
        (triangle b q p hb W).hom := by
      rw [transported_square q D L hL e, transported_square q D L hL e]
      rw [← hs]
      simp only [Category.assoc]
      rw [← Category.assoc (tensorPowerMap ((triangle a q p ha L).inv ≫
        (Scheme.Modules.pullback a).map (e.hom.hom ())) 2),
        ← tensorPowerMap_comp, he']
    change (Scheme.Modules.pullback a).map (localSquare q D L e ()).hom ≫
      ((descent (fun _ : Unit => q)).obj W).hom p (i₁ := ()) (i₂ := ()) a b ha hb =
      ((descent (fun _ : Unit => q)).obj (tensorPower B L 2)).hom p (i₁ := ()) (i₂ := ()) a b ha hb ≫
        (Scheme.Modules.pullback b).map (localSquare q D L e ()).hom
    rw [canonical_hom, canonical_hom]
    have ht' := congrArg (fun z => (triangle a q p ha (tensorPower B L 2)).hom ≫ z ≫
      (triangle b q p hb W).inv) ht
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using ht')

end AffineSquareRootEffectivityR0197

/-- Effective affine faithfully flat descent of the specified square root. -/
theorem affine_square_root_effectivity
    (B Y : Scheme.{0}) (q : Y ⟶ B) (hq : IsAffineHom q) (hf : Flat q)
    (hs : Surjective q) (W : B.Modules) (hW : Scheme.Modules.IsInvertible W)
    (D : RootDatum W (fun _ : Unit => q)) (hD : CompatibleSquares D) : Effective D := by
  letI := hq
  letI := hf
  letI := hs
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
      q D.data D.invertible
  have hP := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorPower_invertible L hL 2
  let E := AffineSquareRootEffectivityR0197.squareDescentIso q D hD L hL e
  have ff := Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective q
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

#print axioms affine_square_root_effectivity

end ArithmeticThetaRootDescentR0197
