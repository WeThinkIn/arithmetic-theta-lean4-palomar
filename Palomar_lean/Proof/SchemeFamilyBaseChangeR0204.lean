module

public import SchemeLevelDefinitionsR0204
public import SchemeLocalWeierstrassR0203

@[expose] public section

/-! Arbitrary scheme base change of elliptic group families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
namespace SchemeFamilyBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203

section Transport
variable {S A : Scheme.{u}} {f : A ⟶ S}
variable {B : Scheme.{u}} (ι : B ⟶ S)
def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ B}
    (x : SchemeHomOver t' (pullback.snd f ι)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ B}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (pullback.snd f ι) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ B}
    (x : SchemeHomOver t' (pullback.snd f ι)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ B}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ B}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ B}
    (x : SchemeHomOver t' (pullback.snd f ι)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ B) :
    SchemeHomOver t' (pullback.snd f ι) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ B) (t' : T' ⟶ B) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (pullback.snd f ι)) :
    baseChangePointToBase ι (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

def baseChangeLaw (G : SchemeLaw f) : SchemeLaw (pullback.snd f ι) where
  mul t' x y := baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y))
  one t' := baseChangePointOfBase ι (G.one _)
  inv t' x := baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x))
  mul_assoc t' x y z := by
    simp only [baseChangePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [baseChangePointToBase_ofBase, G.one_mul, baseChangePointOfBase_toBase]
  mul_one t' x := by
    simp only [baseChangePointToBase_ofBase, G.mul_one, baseChangePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [baseChangePointToBase_ofBase, G.inv_mul_cancel]
  mul_comm t x y := by
    simp only [G.mul_comm]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [GoodReductionJacobian.schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x)
          (baseChangePointToBase ι y))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
      rw [h, ← baseChangePointToBase_schemeHomOverComp, ← baseChangePointToBase_schemeHomOverComp]
    · rw [GoodReductionJacobian.schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      exact hψ

end Transport

/-- The identity is the pullback of the actual identity section. -/
theorem baseChangeLaw_zero {S T : Scheme.{u}} (E : Family S) (b : T ⟶ S) :
    ((baseChangeLaw b E.law).one (𝟙 T)).val ≫ pullback.fst E.p b = b ≫ E.zero := by
  change (pullback.lift _ _ _) ≫ _ = _
  rw [pullback.lift_fst]
  have h := congrArg Subtype.val
    (SchemeLocal.one_natural E.law (𝟙 S) ((𝟙 T) ≫ b) b (by simp))
  exact h.symm

/-- Geometry and the transported law are carried by the same pullback scheme. -/
def baseChangeFamily {S T : Scheme.{u}} (E : Family S) (b : T ⟶ S) : Family T := by
  letI := E.proper
  letI := E.dimension
  letI := E.connected
  exact
    { curve := pullback E.p b
      p := pullback.snd E.p b
      law := baseChangeLaw b E.law
      proper := inferInstance
      dimension := inferInstance
      connected := inferInstance }

theorem baseChangeFamily_multiplicative {S T : Scheme.{u}}
    (E : Family S) (b : T ⟶ S) :
    Multiplicative E (baseChangeFamily E b) b (pullback.fst E.p b) := by
  intro U t x y x' y' hx hy
  have hx' : x' = baseChangePointToBase b x := Subtype.ext hx
  have hy' : y' = baseChangePointToBase b y := Subtype.ext hy
  subst x'; subst y'
  change _ = (pullback.lift _ _ _) ≫ pullback.fst E.p b
  rw [pullback.lift_fst]

end SchemeFamilyBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 SchemeFamilyBaseChange

/-- Every elliptic group family admits base change along every scheme morphism. -/
theorem scheme_family_base_change
    (S T : Scheme.{u}) (E : Family S) (b : T ⟶ S) :
    ∃ (F : Family T) (f : F.curve ⟶ E.curve),
      IsPullback f F.p E.p b ∧ F.zero ≫ f = b ≫ E.zero ∧
        Multiplicative E F b f := by
  exact ⟨baseChangeFamily E b, pullback.fst E.p b,
    IsPullback.of_hasPullback E.p b, baseChangeLaw_zero E b,
    baseChangeFamily_multiplicative E b⟩

#print axioms scheme_family_base_change
end ArithmeticThetaSchemeLevelR0204
