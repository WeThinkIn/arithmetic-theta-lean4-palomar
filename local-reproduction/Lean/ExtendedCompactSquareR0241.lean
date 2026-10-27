import ExtendedMetaplecticDefinitionsR0241

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaActualLevelR0208
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196

private lemma nested_square {X Y Z : Scheme.{0}} (a : X ⟶ Y) (g : Y ⟶ Z)
    {W : Z.Modules} (A : SquareLine Z W) :
    (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback a).map (squarePull g A).hom =
    tensorPowerMap ((Scheme.Modules.pullbackComp a g).hom.app A.line) 2 ≫
      (squarePull (a ≫ g) A).hom ≫ (Scheme.Modules.pullbackComp a g).inv.app W := by
  rw [← Category.assoc, square_comp]
  simp

private lemma square_congr {X Z : Scheme.{0}} {f g : X ⟶ Z} (h : f = g)
    {W : Z.Modules} (A : SquareLine Z W) :
    tensorPowerMap ((Scheme.Modules.pullbackCongr h).hom.app A.line) 2 ≫
      (squarePull g A).hom =
    (squarePull f A).hom ≫ (Scheme.Modules.pullbackCongr h).hom.app W := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

private lemma square_triangle {X Y Y' Z : Scheme.{0}}
    (a : X ⟶ Y) (g : Y ⟶ Z) (b : X ⟶ Y') (j : Y' ⟶ Z)
    (h : a ≫ g = b ≫ j) {W : Z.Modules} (A : SquareLine Z W) :
    tensorPowerMap (((Scheme.Modules.pullbackComp a g).app A.line ≪≫
      (Scheme.Modules.pullbackCongr h).app A.line ≪≫
      ((Scheme.Modules.pullbackComp b j).app A.line).symm).inv) 2 ≫
      (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback a).map (squarePull g A).hom ≫
      ((Scheme.Modules.pullbackComp a g).app W ≪≫
        (Scheme.Modules.pullbackCongr h).app W ≪≫
        ((Scheme.Modules.pullbackComp b j).app W).symm).hom =
    (pullback_tensorPower_iso X Y' b ((Scheme.Modules.pullback j).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback b).map (squarePull j A).hom := by
  rw [← Category.assoc (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv, nested_square,
    nested_square b j]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, tensorPowerMap_comp, Category.assoc]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullbackComp a g).inv.app A.line) 2),
    ← tensorPowerMap_comp]
  simp only [Iso.inv_hom_id_app, tensorPowerMap_id, Category.id_comp]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp a g).inv.app W),
    Iso.inv_hom_id_app, Category.id_comp]
  rw [← Category.assoc (squarePull (a ≫ g) A).hom, ← square_congr h A]
  simp only [Category.assoc]
  rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullbackCongr h).inv.app A.line) 2)
    (tensorPowerMap ((Scheme.Modules.pullbackCongr h).hom.app A.line) 2), ← tensorPowerMap_comp]
  simp

/-- The compact square, with its fixed normalization, is the cotangent square
of the pullback of the original marked family. -/
theorem extended_compact_square :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (n h : ℕ) (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h)
      (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
      (u : ArithmeticThetaCompactModularityR0209.Universal G.root),
      tensorPowerMap (actualLineComparison ι G u).hom 2 ≫
        (restrictedCompactSquare ι G u).hom = (pulledObject ι G u).root.square.hom := by
  intro k l _ _ _ _ ι n h A G u
  let K : SquareLine G.cover.space
      ((Scheme.Modules.pullback (ArithmeticThetaCompactModularityR0209.compactMap G.root)).obj
        G.hodge.line) :=
    ⟨ArithmeticThetaCompactModularityR0209.line G.root,
      G.half.invertible.pullback G.cover.map,
      ArithmeticThetaCompactModularityR0209.compactSquare G.root⟩
  have ht := square_triangle (inclusion ι G) (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (toOldInterior ι G) (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)
    pullback.condition K
  rw [show (pulledObject ι G u).root.square.hom = _ from
    ((pull _ (toOldInterior ι G)).square (oldObject G u)).symm]
  simp only [actualLineComparison, Iso.trans_hom, Iso.symm_hom,
    tensorPowerMap_comp, Category.assoc]
  congr 1
  simp only [restrictedCompactSquare, compactSquare, hodgeComparison, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [K, squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at ht
  unfold lineComparison
  erw [reassoc_of% ht]
  simp only [squarePull, oldObject, object,
    ArithmeticThetaMetaplecticComparisonR0206.FiberEquivalenceProof.obj,
    ArithmeticThetaCompactModularityR0209.openSquare, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

#print axioms extended_compact_square
end ArithmeticThetaExtendedMetaplecticR0241
