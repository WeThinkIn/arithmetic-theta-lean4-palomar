import SchemeKatoUnitDefinitionsR0250
import PointedCartesianGroupLawR0204

/-! Represented multiplication and its pointed Cartesian base changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaSchemeKatoUnitR0250
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeDiscriminantR0244

namespace SchemeTorsionCartesian

lemma one_val {S : Scheme.{u}} (E : Family S) {U : Scheme.{u}} (t : U ⟶ S) :
    (E.law.one t).val = t ≫ E.zero := by
  exact (congrArg Subtype.val
    (SchemeLocal.one_natural E.law (𝟙 S) t t (Category.comp_id t))).symm

lemma multiple_natural {S : Scheme.{u}} (E : Family S)
    {U V : Scheme.{u}} (t : U ⟶ S) (s : V ⟶ S)
    (a : V ⟶ U) (ha : a ≫ t = s) (n : ℕ) (x : SchemeHomOver t E.p) :
    schemeHomOverComp a ha (multiple E t n x) =
      multiple E s n (schemeHomOverComp a ha x) := by
  induction n with
  | zero => exact SchemeLocal.one_natural E.law t s a ha
  | succ n ih =>
    change schemeHomOverComp a ha (E.law.mul _ _ _) = E.law.mul _ _ _
    rw [E.law.mul_natural, ih]

lemma multiplication_over {S : Scheme.{u}} (E : Family S) (n : ℕ) :
    multiplication E n ≫ E.p = E.p :=
  (multiple E E.p n ⟨𝟙 E.curve, Category.id_comp E.p⟩).property

lemma comparison_multiple {S T : Scheme.{u}} (E : Family S) (H : Family T)
    (b : T ⟶ S) (C : Comparison E H b) (hm : Multiplicative E H b C.map)
    {U : Scheme.{u}} (t : U ⟶ T) (x : SchemeHomOver t H.p) (n : ℕ) :
    (multiple H t n x).val ≫ C.map =
      (multiple E (t ≫ b) n (PointedCartesianGroupLaw.pointEquiv C.cartesian t x)).val := by
  induction n with
  | zero =>
    change (H.law.one t).val ≫ C.map = (E.law.one (t ≫ b)).val
    rw [one_val, one_val, Category.assoc, C.pointed, Category.assoc]
  | succ n ih =>
    exact (hm U t (multiple H t n x) x
      (multiple E (t ≫ b) n (PointedCartesianGroupLaw.pointEquiv C.cartesian t x))
      (PointedCartesianGroupLaw.pointEquiv C.cartesian t x) ih.symm rfl).symm

lemma comparison_multiplication {k : Type u} [Field k] [CharZero k]
    {S T : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (H : Family T)
    (b : T ⟶ S) (C : Comparison E H b) (n : ℕ) :
    multiplication H n ≫ C.map = C.map ≫ multiplication E n := by
  have hm := pointed_cartesian_group_law k S T σ E H b C.map C.cartesian C.pointed
  have hc := comparison_multiple E H b C hm H.p ⟨𝟙 H.curve, Category.id_comp H.p⟩ n
  have hn := congrArg Subtype.val
    (multiple_natural E E.p (H.p ≫ b) C.map C.cartesian.w n
      ⟨𝟙 E.curve, Category.id_comp E.p⟩)
  exact hc.trans hn.symm

end SchemeTorsionCartesian

/-- The actual multiplication square and both defining ideals commute with every
pointed Cartesian comparison. This includes zero and one without exceptions. -/
theorem scheme_torsion_cartesian :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S),
    ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S),
      b ≫ σ = τ → ∀ C : Comparison E H b, ∀ n : ℕ,
      IsPullback C.map (multiplication H n) (multiplication E n) C.map ∧
      (identityIdeal E).comap C.map = identityIdeal H ∧
      (torsionIdeal E n).comap C.map = torsionIdeal H n ∧
      complement H n = (TopologicalSpace.Opens.map C.map.base).obj (complement E n) := by
  intro k _ _ S σ E T τ H b _ C n
  have hm := SchemeTorsionCartesian.comparison_multiplication σ E H b C n
  have hp : IsPullback C.map (multiplication H n ≫ H.p)
      (multiplication E n ≫ E.p) b := by
    simpa only [SchemeTorsionCartesian.multiplication_over] using C.cartesian
  have hi : (identityIdeal E).comap C.map = identityIdeal H :=
    ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.ideal_comap
      E H b C.map C.cartesian C.pointed
  have ht : (torsionIdeal E n).comap C.map = torsionIdeal H n := by
    unfold torsionIdeal
    rw [← Scheme.IdealSheafData.comap_comp, ← hm,
      Scheme.IdealSheafData.comap_comp, hi]
  refine ⟨hp.of_bot hm.symm C.cartesian, hi, ht, ?_⟩
  unfold complement
  rw [← ht, Scheme.IdealSheafData.support_comap]
  rfl

#print axioms scheme_torsion_cartesian
end ArithmeticThetaSchemeKatoUnitR0250
