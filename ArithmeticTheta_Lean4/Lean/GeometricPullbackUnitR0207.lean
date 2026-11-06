import MetaplecticStackDefinitionsR0207

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticStackR0207
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

namespace GeometricPullbackUnitProof
variable {L : ℕ} {S : Scheme.{0}} {G : GroupoidData L S}
    (P : PullbackData G G (𝟙 S))

/-- The actual Cartesian projection over the identity, together with the
specified line comparison, is an arrow in the existing groupoid. -/
def componentArrow (X : G.Objects) : Arrow (P.functor.obj X) X := by
  letI : IsIso (P.curve X) := (P.marked X).1.isIso_fst_of_isIso
  exact {
    curve := asIso (P.curve X)
    marked := P.marked X
    cotangent := (P.cotangent X).symm ≪≫ (Scheme.Modules.pullbackId S).app _
    canonical := by
      simpa using P.canonical X
    line := P.line X ≪≫ (Scheme.Modules.pullbackId S).app X.root.line
    square := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, tensorPowerMap_comp,
        Category.assoc]
      rw [ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.square_id]
      rw [← P.square X]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
  }

def component (X : G.Objects) : P.functor.obj X ⟶ X :=
  (G.arrow _ _).symm (componentArrow P X)

lemma component_curve (X : G.Objects) :
    (G.arrow _ _ (component P X)).curve.hom = P.curve X := by
  simp only [component, Equiv.apply_symm_apply, componentArrow, asIso_hom]

lemma component_line (X : G.Objects) :
    (G.arrow _ _ (component P X)).line.hom =
      (P.line X).hom ≫ (Scheme.Modules.pullbackId S).hom.app X.root.line := by
  simp only [component, Equiv.apply_symm_apply, componentArrow, Iso.trans_hom, Iso.app_hom]

lemma naturality {X Y : G.Objects} (f : X ⟶ Y) :
    P.functor.map f ≫ component P Y = component P X ≫ f := by
  apply (G.arrow _ _).injective
  apply ActualGroupoidProof.arrow_ext
  · simp only [G.curve_comp, component_curve]
    exact P.curve_natural X Y f
  · simp only [G.line_comp, component_line]
    rw [← Category.assoc, P.line_natural X Y f, Category.assoc]
    exact congrArg (fun q => (P.line X).hom ≫ q)
      ((Scheme.Modules.pullbackId S).hom.naturality (G.arrow _ _ f).line.hom)

def comparison : P.functor ≅ 𝟭 G.Objects :=
  NatIso.ofComponents (fun X => asIso (component P X)) (fun f => naturality P f)

lemma normalized : UnitNormalized P (comparison P) := by
  intro X
  exact ⟨component_curve P X, component_line P X⟩

lemma unique (e : P.functor ≅ 𝟭 G.Objects) (he : UnitNormalized P e) :
    e = comparison P := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (G.arrow _ _).injective
  apply ActualGroupoidProof.arrow_ext
  · exact (he X).1.trans ((normalized P X).1.symm)
  · exact (he X).2.trans ((normalized P X).2.symm)

end GeometricPullbackUnitProof

/-- The unique identity comparison with both geometric normalizations,
for arbitrary level, base scheme, and accepted choices of pullback data. -/
theorem geometric_pullback_unit :
    ∀ (L : ℕ) (S : AlgebraicGeometry.Scheme.{0})
      (G : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L S)
      (P : ArithmeticThetaMetaplecticComparisonR0206.PullbackData G G
        (CategoryTheory.CategoryStruct.id S)),
      ∃! e : CategoryTheory.Iso P.functor (CategoryTheory.Functor.id G.Objects),
        ArithmeticThetaMetaplecticStackR0207.UnitNormalized P e := by
  intro L S G P
  exact ⟨GeometricPullbackUnitProof.comparison P,
    GeometricPullbackUnitProof.normalized P, GeometricPullbackUnitProof.unique P⟩

#print axioms geometric_pullback_unit
end ArithmeticThetaMetaplecticStackR0207
