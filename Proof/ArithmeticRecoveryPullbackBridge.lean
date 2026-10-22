module
public import GeometricPullbackCompositionR0207
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaMetaplecticStackR0207.GeometricCompositionProof
namespace PalomarPullback678
variable {L : ℕ} {S T : Scheme.{0}} {GS : GroupoidData L S} {GT : GroupoidData L T}
  {a : T ⟶ S} (P Q : PullbackData GS GT a)
/-- Preserve both actual curve projections and the specified line comparisons. -/
def Normalized (e : P.functor ≅ Q.functor) : Prop :=
  ∀ X, (GT.arrow _ _ (e.hom.app X)).curve.hom ≫ Q.curve X = P.curve X ∧
    (GT.arrow _ _ (e.hom.app X)).line.hom ≫ (Q.line X).hom = (P.line X).hom

def component (X : GS.Objects) : P.functor.obj X ⟶ Q.functor.obj X :=
  (GT.arrow _ _).symm (comparison (ofPull P X) (ofPull Q X))

lemma component_curve (X : GS.Objects) :
    (GT.arrow _ _ (component P Q X)).curve.hom ≫ Q.curve X = P.curve X := by
  change (GT.arrow _ _ ((GT.arrow _ _).symm _)).curve.hom ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact comparisonCurve_fst (ofPull P X) (ofPull Q X)

lemma component_line (X : GS.Objects) :
    (GT.arrow _ _ (component P Q X)).line.hom ≫ (Q.line X).hom = (P.line X).hom := by
  change (GT.arrow _ _ ((GT.arrow _ _).symm _)).line.hom ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact comparison_line (ofPull P X) (ofPull Q X)

lemma normalized_ext {X Y : GS.Objects}
    (f g : P.functor.obj X ⟶ Q.functor.obj Y)
    (hc : (GT.arrow _ _ f).curve.hom ≫ Q.curve Y = (GT.arrow _ _ g).curve.hom ≫ Q.curve Y)
    (hl : (GT.arrow _ _ f).line.hom ≫ (Q.line Y).hom =
      (GT.arrow _ _ g).line.hom ≫ (Q.line Y).hom) : f = g := by
  apply (GT.arrow _ _).injective
  apply ActualGroupoidProof.arrow_ext
  · apply (Q.marked Y).1.hom_ext
    · exact hc
    · exact (GT.arrow _ _ f).marked.1.w.trans (GT.arrow _ _ g).marked.1.w.symm
  · exact (cancel_mono (Q.line Y).hom).mp hl

lemma component_natural {X Y : GS.Objects} (f : X ⟶ Y) :
    P.functor.map f ≫ component P Q Y = component P Q X ≫ Q.functor.map f := by
  apply normalized_ext P Q
  · simp only [GT.curve_comp, Category.assoc]
    rw [component_curve, P.curve_natural, Q.curve_natural, ← Category.assoc, component_curve]
  · simp only [GT.line_comp, Category.assoc]
    rw [component_line, P.line_natural, Q.line_natural, ← Category.assoc, component_line]

/-- Any two actual pullback constructions have a unique curve- and line-normalized
natural isomorphism. This asserts uniqueness up to the specified isomorphism,
not equality of implementation-dependent choices of objects. -/
theorem existsUnique_normalized : ∃! e : P.functor ≅ Q.functor, Normalized P Q e := by
  let e := NatIso.ofComponents (fun X => asIso (component P Q X))
    (fun f => component_natural P Q f)
  have he : Normalized P Q e := fun X => ⟨component_curve P Q X, component_line P Q X⟩
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact normalized_ext P Q _ _ ((hd X).1.trans (he X).1.symm)
    ((hd X).2.trans (he X).2.symm)
/-- The original selected pullback is canonically equivalent to every admissible
actual geometric pullback, with a uniquely normalized natural isomorphism. -/
theorem selected_pull_unique_normalized (L : ℕ) {S T : Scheme.{0}} (a : T ⟶ S)
    (Q : PullbackData (ArithmeticThetaMetaplecticStackR0207.group L S)
      (ArithmeticThetaMetaplecticStackR0207.group L T) a) :
    ∃! e : (ArithmeticThetaMetaplecticStackR0207.pull L a).functor ≅ Q.functor,
      Normalized (ArithmeticThetaMetaplecticStackR0207.pull L a) Q e :=
  existsUnique_normalized _ Q
end PalomarPullback678
