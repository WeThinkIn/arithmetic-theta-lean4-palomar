module
public import RootClassifyingMapR0199
import Lean
@[expose] public section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaStackLevelR0199
open ArithmeticThetaStackLevelR0199.RootClassifyingMapR0199
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local instance] CategoryTheory.uliftCategory
noncomputable section
namespace PalomarClassifier667
variable {B : Scheme.{0}} (F : Pseudofunctor (LocallyDiscrete (Over B)ᵒᵖ) Cat.{0,1})
  (Y : Over B) (x : F.obj (.mk (.op Y)))
/-- The actual object components and every strong naturality isomorphism are prescribed. -/
def Normalized (t : Pseudofunctor.StrongTrans (representable Y) F) : Prop :=
  (∀ S, t.app S = (component F Y x S.as.unop).toCatHom) ∧
  (∀ {S T : LocallyDiscrete (Over B)ᵒᵖ} (a : S ⟶ T),
    HEq (t.naturality a) (Cat.Hom.isoMk (comparison F Y x a.as.unop)))
theorem normalized_original : Normalized F Y x (classify F Y x) := by
  exact ⟨fun _ => rfl, fun _ => HEq.rfl⟩
theorem strongTrans_ext {t u : Pseudofunctor.StrongTrans (representable Y) F}
    (ha : ∀ S, t.app S = u.app S)
    (hn : ∀ {S T : LocallyDiscrete (Over B)ᵒᵖ} (a : S ⟶ T),
      HEq (t.naturality a) (u.naturality a)) : t = u := by
  have he := funext ha
  cases t with
  | mk app naturality nn ni nc =>
    cases u with
    | mk app' naturality' nn' ni' nc' =>
      dsimp at he hn
      cases he
      have he' : @naturality = @naturality' := by
        funext S T a
        exact eq_of_heq (hn a)
      cases he'
      rfl
theorem normalized_iff_original (t : Pseudofunctor.StrongTrans (representable Y) F) :
    Normalized F Y x t ↔ t = classify F Y x := by
  constructor
  · intro h
    exact strongTrans_ext F Y h.1 h.2
  · rintro rfl
    exact normalized_original F Y x
theorem canonicalClassifyingMap : ∃! t, Normalized F Y x t := by
  refine ⟨classify F Y x, normalized_original F Y x, ?_⟩
  intro t ht
  exact (normalized_iff_original F Y x t).mp ht
def canonical : Pseudofunctor.StrongTrans (representable Y) F :=
  (canonicalClassifyingMap F Y x).exists.choose
theorem canonical_eq_original : canonical F Y x = classify F Y x :=
  (normalized_iff_original F Y x _).mp (canonicalClassifyingMap F Y x).exists.choose_spec
#print axioms canonical_eq_original
end PalomarClassifier667
