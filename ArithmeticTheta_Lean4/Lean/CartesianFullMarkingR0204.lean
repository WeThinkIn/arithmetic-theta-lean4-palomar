import SchemeLevelDefinitionsR0204

/-! Unique Cartesian transport of full markings over arbitrary schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203

namespace CartesianFullMarking

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)

/-- Restriction retains the actual section and the prescribed base map. -/
def restrict (x : SchemeHomOver (𝟙 S) E.p) :
    SchemeHomOver ((𝟙 T) ≫ b) E.p :=
  ⟨b ≫ x.val, by rw [Category.assoc, x.property]; simp⟩

lemma mul_comp (hm : Multiplicative E F b f)
    (x y : SchemeHomOver (𝟙 T) F.p) (x' y' : SchemeHomOver (𝟙 S) E.p)
    (hx : x.val ≫ f = b ≫ x'.val) (hy : y.val ≫ f = b ≫ y'.val) :
    (F.law.mul (𝟙 T) x y).val ≫ f = b ≫ (E.law.mul (𝟙 S) x' y').val := by
  have h := hm T (𝟙 T) x y (restrict E b x') (restrict E b y') hx.symm hy.symm
  have hn := congrArg Subtype.val
    (E.law.mul_natural (𝟙 S) ((𝟙 T) ≫ b) b (by simp) x' y')
  exact h.symm.trans hn.symm

/-- Recursive multiples commute with the given pointed group comparison. -/
lemma multiple_comp (hzero : F.zero ≫ f = b ≫ E.zero)
    (hm : Multiplicative E F b f)
    (x : SchemeHomOver (𝟙 T) F.p) (x' : SchemeHomOver (𝟙 S) E.p)
    (hx : x.val ≫ f = b ≫ x'.val) (n : ℕ) :
    (multiple F (𝟙 T) n x).val ≫ f = b ≫ (multiple E (𝟙 S) n x').val := by
  induction n with
  | zero => exact hzero
  | succ n ih => exact mul_comp E F b f hm _ _ _ _ ih hx

/-- The Cartesian lift of an actual section. -/
def lift (hp : IsPullback f F.p E.p b) (x : SchemeHomOver (𝟙 S) E.p) :
    SchemeHomOver (𝟙 T) F.p :=
  ⟨hp.lift (b ≫ x.val) (𝟙 T) (by rw [Category.assoc, x.property]; simp),
    hp.lift_snd _ _ _⟩

lemma lift_comp (hp : IsPullback f F.p E.p b) (x : SchemeHomOver (𝟙 S) E.p) :
    (lift E F b f hp x).val ≫ f = b ≫ x.val := hp.lift_fst _ _ _

lemma section_ext (hp : IsPullback f F.p E.p b)
    {x y : SchemeHomOver (𝟙 T) F.p} (h : x.val ≫ f = y.val ≫ f) : x = y :=
  Subtype.ext (hp.hom_ext h (x.property.trans y.property.symm))

lemma lift_killed (hp : IsPullback f F.p E.p b)
    (hzero : F.zero ≫ f = b ≫ E.zero) (hm : Multiplicative E F b f)
    (L : ℕ) (x : SchemeHomOver (𝟙 S) E.p)
    (hx : multiple E (𝟙 S) L x = E.law.one (𝟙 S)) :
    multiple F (𝟙 T) L (lift E F b f hp x) = F.law.one (𝟙 T) := by
  apply section_ext E F b f hp
  rw [multiple_comp E F b f hzero hm _ x (lift_comp E F b f hp x), hx]
  exact hzero.symm

/-- Both lifted labels form a full marking, including at levels zero and one. -/
def up (hp : IsPullback f F.p E.p b)
    (hzero : F.zero ≫ f = b ≫ E.zero) (hm : Multiplicative E F b f)
    (L : ℕ) (M : FullLevel E L) : FullLevel F L where
  x := lift E F b f hp M.x
  y := lift E F b f hp M.y
  killed_x := lift_killed E F b f hp hzero hm L M.x M.killed_x
  killed_y := lift_killed E F b f hp hzero hm L M.y M.killed_y
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨t, ht⟩
    have hc := mul_comp E F b f hm
      (multiple F (𝟙 T) i.val (lift E F b f hp M.x))
      (multiple F (𝟙 T) j.val (lift E F b f hp M.y))
      (multiple E (𝟙 S) i.val M.x) (multiple E (𝟙 S) j.val M.y)
      (multiple_comp E F b f hzero hm _ M.x (lift_comp E F b f hp M.x) i.val)
      (multiple_comp E F b f hzero hm _ M.y (lift_comp E F b f hp M.y) j.val)
    apply Set.disjoint_left.mp (M.avoids i j hij) (Set.mem_range_self (b z))
    refine ⟨b t, ?_⟩
    have H := congrArg (fun a => f a) ht
    change (F.zero ≫ f) t = _ at H
    rw [hzero] at H
    have Hc := congrArg (fun a : T ⟶ E.curve => a z) hc
    exact H.trans Hc

lemma fullLevel_ext {L : ℕ} {M N : FullLevel F L}
    (hx : M.x = N.x) (hy : M.y = N.y) : M = N := by
  cases M
  cases N
  cases hx
  cases hy
  rfl

end CartesianFullMarking

/-- Full markings lift uniquely along every pointed multiplicative Cartesian square. -/
theorem cartesian_full_marking :
    ∀ (S T : Scheme.{u}) (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
      (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
      (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve),
      CategoryTheory.IsPullback f F.p E.p b →
      CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero →
      ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f →
      ∀ (L : ℕ) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E L),
      ∃! N : ArithmeticThetaSchemeLevelR0204.FullLevel F L,
        CategoryTheory.CategoryStruct.comp N.x.val f = CategoryTheory.CategoryStruct.comp b M.x.val ∧
        CategoryTheory.CategoryStruct.comp N.y.val f = CategoryTheory.CategoryStruct.comp b M.y.val := by
  intro S T E F b f hp hzero hm L M
  refine ⟨CartesianFullMarking.up E F b f hp hzero hm L M,
    ⟨CartesianFullMarking.lift_comp E F b f hp M.x,
     CartesianFullMarking.lift_comp E F b f hp M.y⟩, ?_⟩
  intro N hN
  apply CartesianFullMarking.fullLevel_ext
  · exact CartesianFullMarking.section_ext E F b f hp
      (hN.1.trans (CartesianFullMarking.lift_comp E F b f hp M.x).symm)
  · exact CartesianFullMarking.section_ext E F b f hp
      (hN.2.trans (CartesianFullMarking.lift_comp E F b f hp M.y).symm)

end ArithmeticThetaSchemeLevelR0204

#print axioms ArithmeticThetaSchemeLevelR0204.cartesian_full_marking
