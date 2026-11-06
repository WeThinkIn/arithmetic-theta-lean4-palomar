module
public import OutputFactorBridge
public import LevelFactorBridge
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
noncomputable section
namespace PalomarSquare918
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaActualLevelR0208 ArithmeticThetaExtendedMetaplecticR0241
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


def SquareTriangle : Prop :=
∀ {X Y Y' Z : Scheme.{0}}
    (a : X ⟶ Y) (g : Y ⟶ Z) (b : X ⟶ Y') (j : Y' ⟶ Z)
    (h : a ≫ g = b ≫ j) {W : Z.Modules} (A : SquareLine Z W),
    tensorPowerMap (((Scheme.Modules.pullbackComp a g).app A.line ≪≫
      (Scheme.Modules.pullbackCongr h).app A.line ≪≫
      ((Scheme.Modules.pullbackComp b j).app A.line).symm).inv) 2 ≫
      (pullback_tensorPower_iso X Y a ((Scheme.Modules.pullback g).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback a).map (squarePull g A).hom ≫
      ((Scheme.Modules.pullbackComp a g).app W ≪≫
        (Scheme.Modules.pullbackCongr h).app W ≪≫
        ((Scheme.Modules.pullbackComp b j).app W).symm).hom =
    (pullback_tensorPower_iso X Y' b ((Scheme.Modules.pullback j).obj A.line) 2).inv ≫
      (Scheme.Modules.pullback b).map (squarePull j A).hom

theorem square_triangle : SquareTriangle := by
  intro X Y Y' Z a g b j h W A
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

theorem recover_square (htriangle : SquareTriangle) : PalomarLevel911.SquareTransport := by
  intro k l _ _ _ _ ι n h A G u
  let K : SquareLine G.cover.space
      ((Scheme.Modules.pullback (ArithmeticThetaCompactModularityR0209.compactMap G.root)).obj
        G.hodge.line) :=
    ⟨ArithmeticThetaCompactModularityR0209.line G.root,
      G.half.invertible.pullback G.cover.map,
      ArithmeticThetaCompactModularityR0209.compactSquare G.root⟩
  have ht := htriangle (inclusion ι G) (ArithmeticThetaScalarExtensionR0240.projection ι G)
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

theorem recover_all
 (hm : PalomarFactored882.MatrixCore) (hl : PalomarFactored882.CompactLevel)
 (hs : PalomarOutput913.SolverCertificates) (ho : PalomarOutput913.OutputFromCertificate)
 (hd : PalomarExtension908.DiskTransport)
 (hi : PalomarLevel911.InteriorTransport) (hc : PalomarLevel911.ClassifierTransport)
 (hq : SquareTriangle) (ha : PalomarLevel911.ArrowTransport) (ht : PalomarLevel911.StandardLevel) :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaExtendedMetaplecticR0241.ExtendedLevel ι G ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := PalomarOutput913.recover_from_components hm hl hs ho hd
 (PalomarLevel911.recover_level hi hc (recover_square hq) ha ht)

theorem original_cyclotomic_extended_modularity :
∀ (n h d : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ R : Matrix (Fin h) (Fin d) ℚ, ArithmeticThetaAdaptiveSolverR0230.Relations A R → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ (G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A) (o : ArithmeticThetaAdaptiveSolverR0230.Result h), ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ∀ (l : Type) [Field l] [CharZero l] (ι : (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) →+* l), ArithmeticThetaExtendedMetaplecticR0241.ExtendedLevel ι G ∧ ArithmeticThetaScalarExtensionR0240.OutputImage ι G o ∧ ∃ D : ArithmeticThetaScalarExtensionR0240.DiskLift ι G, ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback D.map).obj (ArithmeticThetaScalarExtensionR0240.line ι G)) ⊤ (ArithmeticThetaScalarExtensionR0240.frame ι G D) ∧ AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion l) D.map) ∧ ArithmeticThetaScalarExtensionR0240.Expansion ι G D := recover_all PalomarFactored882.matrix_core PalomarFactored882.compact_level
 PalomarOutput913.solver_certificates PalomarOutput913.output_from_certificate
 PalomarExtension908.disk_transport PalomarLevel911.interior_transport
 PalomarLevel911.classifier_transport square_triangle PalomarLevel911.arrow_transport
 PalomarLevel911.standard_level
end PalomarSquare918
