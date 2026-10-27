import SchemeMillerPhaseR0215

/-! Naturality of the exact global Miller ratio along marked Cartesian maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemePhaseNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

private lemma mul_val_eq {S : Scheme.{u}} (E : Family S)
    {U : Scheme.{u}} {t t' : U ⟶ S} (h : t = t')
    (x y : SchemeHomOver t E.p) (x' y' : SchemeHomOver t' E.p)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (E.law.mul t x y).val = (E.law.mul t' x' y').val := by
  subst t'
  have hxx : x = x' := Subtype.ext hx
  have hyy : y = y' := Subtype.ext hy
  subst x'
  subst y'
  rfl

/-- Composition retains the original ring, equation, law and both level sections. -/
def composeTest {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (M : FullLevel E 4) (N : FullLevel F 4) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hb : MarkedCartesian E F M N b f)
    (P : AffineTest F N) : AffineTest E M where
  ring := P.ring
  equation := P.equation
  elliptic := P.elliptic
  law := P.law
  originLaw := P.originLaw
  base := P.base ≫ b
  comparison := P.comparison ≫ f
  cartesian := P.cartesian.paste_horiz hb.1
  zero_eq := by rw [← Category.assoc, P.zero_eq, Category.assoc, hb.2.1, Category.assoc]
  mul_eq := by
    intro U t x y x' y' hx hy
    let px : SchemeHomOver (t ≫ P.base) F.p :=
      ⟨x.val ≫ P.comparison, by
        rw [Category.assoc, P.cartesian.w, ← Category.assoc, x.property]⟩
    let py : SchemeHomOver (t ≫ P.base) F.p :=
      ⟨y.val ≫ P.comparison, by
        rw [Category.assoc, P.cartesian.w, ← Category.assoc, y.property]⟩
    let ex : SchemeHomOver ((t ≫ P.base) ≫ b) E.p :=
      ⟨x'.val, by rw [Category.assoc]; exact x'.property⟩
    let ey : SchemeHomOver ((t ≫ P.base) ≫ b) E.p :=
      ⟨y'.val, by rw [Category.assoc]; exact y'.property⟩
    have hF := P.mul_eq U t x y px py rfl rfl
    have hE := hb.2.2.1 U (t ≫ P.base) px py ex ey
      (by simpa only [px, ex, Category.assoc] using hx)
      (by simpa only [py, ey, Category.assoc] using hy)
    have ht := mul_val_eq E (Category.assoc t P.base b) ex ey x' y' rfl rfl
    exact ht.symm.trans (hE.trans ((congrArg (fun q => q ≫ f) hF).trans
      (Category.assoc _ _ _)))
  level := P.level
  x_eq := by rw [← Category.assoc, P.x_eq, Category.assoc, hb.2.2.2.1, Category.assoc]
  y_eq := by rw [← Category.assoc, P.y_eq, Category.assoc, hb.2.2.2.2, Category.assoc]

lemma pullback_phase {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (M : FullLevel E 4) (N : FullLevel F 4) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hb : MarkedCartesian E F M N b f)
    (z : Γ(S, ⊤)) (hz : MillerPhase E M z) : MillerPhase F N (b.appTop z) := by
  intro P
  have h := hz (composeTest E F M N b f hb P)
  simpa only [affineScalar, composeTest, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

end SchemePhaseNaturality

/-- The normalized global phase commutes with every marked Cartesian base change. -/
theorem scheme_phase_naturality :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (hb : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (w : T.presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.MillerPhase F N w → b.appTop z = w := by
  intro k _ _ S σ E M T τ F N b f _ hb z w hz hw
  exact (scheme_miller_phase k T τ F N).1.unique
    (SchemePhaseNaturality.pullback_phase E F M N b f hb z hz) hw

#print axioms scheme_phase_naturality
end ArithmeticThetaSchemeFourCharacterR0215
