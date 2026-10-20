module

public import SchemeThetaNaturalityDefinitionsR0262

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259

namespace SchemeCommutatorNaturality
open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
open ArithmeticThetaRelativeThetaNaturalityR0258
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)

/-- Identify the frozen expanded comparison with general conjugated pullback. -/
lemma transportedLift_eq (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (h : g' ≫ f = f ≫ g) (α : Lift E m g) :
    ArithmeticThetaSchemeThetaNaturalityR0262.transportedLift E F b f hc hz m g g' h α =
      MidpointNaturalityProof.transport f
        (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E F b f hc hz m)
        g g' h.symm α := by
  simp [ArithmeticThetaSchemeThetaNaturalityR0262.transportedLift,
    MidpointNaturalityProof.transport, PullbackLifts.lift, PullbackLifts.squareNat,
    Scheme.Modules.pullbackCongr, Iso.trans_assoc]
  rfl

/-- Commutators are transported as equations of whole-sheaf isomorphisms. -/
lemma commutator (m : ℕ) (P Q : point E) (P' Q' : point F)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (α' : Lift F m (translation F P')) (β' : Lift F m (translation F Q'))
    (c : Γ(S, ⊤)ˣ)
    (hα : LiftCorresponds E F b f hc hz m _ _ α α')
    (hβ : LiftCorresponds E F b f hc hz m _ _ β β')
    (hab : Commutator E m P Q α β c) :
    Commutator F m P' Q' α' β' (baseUnit b c) := by
  obtain ⟨hf, hα⟩ := hα
  obtain ⟨hg, hβ⟩ := hβ
  rw [transportedLift_eq] at hα hβ
  obtain ⟨h, hh⟩ := hab
  let h' := SchemePrimitiveThetaCommutator.translations_commute F P' Q'
  have heq : PullbackLifts.compLift (translation E P) (translation E Q) α β =
      (Scheme.Modules.pullbackCongr h).app (thetaLine E m) ≪≫
        PullbackLifts.compLift (translation E Q) (translation E P) β α ≪≫
          smulIso (scalar E c) (thetaLine E m) := by
    simpa only [compose, scaled, changeMap, PullbackLifts.compLift, Iso.trans_assoc] using hh
  refine ⟨h', ?_⟩
  simpa only [compose, scaled, changeMap, PullbackLifts.compLift, Iso.trans_assoc] using
    (GeometricNaturalityProof.transport_commutation f
      (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E F b f hc hz m)
      _ _ _ _ hf.symm hg.symm h h' α β α' β' hα.symm hβ.symm
      (scalar E c) (scalar F (baseUnit b c))
      (SchemePrimitiveThetaCommutator.scalar_square E F b f hc c) heq)

/-- Primitive differences stay units under the actual map of global base rings. -/
lemma primitive_map (m : ℕ) (c : Γ(S, ⊤)ˣ) (hp : PrimitiveUnit m c) :
    PrimitiveUnit m (baseUnit b c) := by
  constructor
  · change (Units.map b.appTop.hom.toMonoidHom c) ^ m = 1
    rw [← map_pow, hp.1, map_one]
  · intro i hi
    change IsUnit (b.appTop.hom (c : Γ(S, ⊤)) ^ i.val - 1)
    rw [← map_pow, ← map_one b.appTop.hom, ← map_sub]
    exact (hp.2 i hi).map b.appTop.hom

end SchemeCommutatorNaturality

/-- Canonical transport of the geometric commutator and its primitive base unit. -/
theorem scheme_commutator_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ m : ℕ, ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f → ∀ (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m)) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F (2*m)), CategoryTheory.CategoryStruct.comp N.x.val f = CategoryTheory.CategoryStruct.comp b M.x.val → CategoryTheory.CategoryStruct.comp N.y.val f = CategoryTheory.CategoryStruct.comp b M.y.val → ∀ (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x)) (β : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y)) (α' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.x)) (β' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.y)), ∀ c : (S.presheaf.obj (Opposite.op ⊤))ˣ, ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E F b f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x) (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.x) α α' → ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E F b f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y) (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.y) β β' → ArithmeticThetaSchemeThetaMarkingR0259.Commutator E m M.x M.y α β c → ArithmeticThetaSchemeThetaMarkingR0259.Commutator F m N.x N.y α' β' (ArithmeticThetaSchemeThetaNaturalityR0262.baseUnit b c) ∧ (ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c → ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := T) m (ArithmeticThetaSchemeThetaNaturalityR0262.baseUnit b c)) := by
  intro k _ _ S σ E T F b f hc hz m hm M N hx hy α β α' β' c hα hβ hab
  exact ⟨SchemeCommutatorNaturality.commutator E F b f hc hz m M.x M.y N.x N.y
    α β α' β' c hα hβ hab, SchemeCommutatorNaturality.primitive_map b m c⟩

#print axioms scheme_commutator_naturality
end ArithmeticThetaSchemeThetaNaturalityR0262
