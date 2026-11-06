module

public import MarkedAffineTestComparisonR0215
public import ArbitraryPhaseBaseChangeR0214
public import Mathlib.AlgebraicGeometry.AffineSpace

@[expose] public section

/-! Exact scheme Miller phase: comparison and gluing of accepted affine ratios. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemeMillerPhase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 (baseMap)
open ArithmeticThetaArbitraryFourCharacterR0214

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- The already proved exact ratio in each test ring. -/
def phase (P : AffineTest E M) : P.ring := by
  letI := P.elliptic
  exact Classical.choose (arbitrary_geometric_phase P.ring P.equation P.law
    P.originLaw P.level).1

lemma phase_spec (P : AffineTest E M) :
    ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase
      P.ring P.equation P.law P.level (phase E M P) := by
  letI := P.elliptic
  exact (Classical.choose_spec (arbitrary_geometric_phase P.ring P.equation P.law
    P.originLaw P.level).1).1

/-- A base factorization induces the actual pointed Cartesian curve map. -/
lemma phase_natural (P Q : AffineTest E M)
    (f : Base Q.ring ⟶ Base P.ring) (hf : f ≫ P.base = Q.base) :
    (Spec.preimage f).hom (phase E M P) = phase E M Q := by
  letI := P.elliptic
  letI := Q.elliptic
  let ι : P.ring →+* Q.ring := (Spec.preimage f).hom
  have hι : baseMap P.ring Q.ring ι = f := Spec.map_preimage f
  have hw : Q.comparison ≫ E.p =
      (structureMap Q.ring Q.equation ≫ f) ≫ P.base := by
    rw [Category.assoc, hf]
    exact Q.cartesian.w
  let b := P.cartesian.lift Q.comparison (structureMap Q.ring Q.equation ≫ f) hw
  have hb : b ≫ P.comparison = Q.comparison := P.cartesian.lift_fst _ _ _
  have hp : b ≫ structureMap P.ring P.equation =
      structureMap Q.ring Q.equation ≫ f := P.cartesian.lift_snd _ _ _
  have hc : IsPullback b (structureMap Q.ring Q.equation)
      (structureMap P.ring P.equation) (baseMap P.ring Q.ring ι) := by
    rw [hι]
    apply IsPullback.of_right _ hp P.cartesian
    rw [hb, hf]
    exact Q.cartesian
  have ho : origin Q.ring Q.equation ≫ b =
      baseMap P.ring Q.ring ι ≫ origin P.ring P.equation := by
    rw [hι]
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hb, Category.assoc, P.zero_eq, ← Category.assoc, hf]
      exact Q.zero_eq
    · rw [Category.assoc, hp, ← Category.assoc,
        ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.origin_over,
        Category.id_comp, Category.assoc,
        ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.origin_over, Category.comp_id]
  have hBC := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.pointed_base_change
    P.law Q.law P.originLaw Q.originLaw ι b hc ho
  have hx : Q.level.x.val ≫ b = baseMap P.ring Q.ring ι ≫ P.level.x.val := by
    rw [hι]
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hb, Category.assoc, P.x_eq, ← Category.assoc, hf]
      exact Q.x_eq
    · rw [Category.assoc, hp, ← Category.assoc, Q.level.x.property,
        Category.id_comp, Category.assoc, P.level.x.property, Category.comp_id]
  have hy : Q.level.y.val ≫ b = baseMap P.ring Q.ring ι ≫ P.level.y.val := by
    rw [hι]
    apply P.cartesian.hom_ext
    · rw [Category.assoc, hb, Category.assoc, P.y_eq, ← Category.assoc, hf]
      exact Q.y_eq
    · rw [Category.assoc, hp, ← Category.assoc, Q.level.y.property,
        Category.id_comp, Category.assoc, P.level.y.property, Category.comp_id]
  exact arbitrary_phase_base_change P.ring P.equation P.law P.originLaw P.level
    Q.ring Q.equation Q.law Q.originLaw Q.level ι b hBC ⟨hx, hy⟩
    _ _ (phase_spec E M P) (phase_spec E M Q)

/-- Interpret the exact affine ratio as a regular function on its spectrum. -/
def phaseSection (P : AffineTest E M) : Γ(Base P.ring, ⊤) :=
  (Scheme.ΓSpecIso (.of P.ring)).inv (phase E M P)

lemma phaseSection_natural (P Q : AffineTest E M)
    (f : Base Q.ring ⟶ Base P.ring) (hf : f ≫ P.base = Q.base) :
    f.appTop (phaseSection E M P) = phaseSection E M Q := by
  have h := congrArg (fun h : CommRingCat.of P.ring ⟶ Γ(Base Q.ring, ⊤) =>
    h (phase E M P)) (Scheme.ΓSpecIso_inv_naturality (Spec.preimage f))
  simp only [Spec.map_preimage, ConcreteCategory.comp_apply] at h
  exact h.symm.trans (congrArg (Scheme.ΓSpecIso (.of Q.ring)).inv
    (phase_natural E M P Q f hf))

private lemma mul_val_eq {T : Scheme.{u}} {t t' : T ⟶ S} (h : t = t')
    (x y : SchemeHomOver t E.p) (x' y' : SchemeHomOver t' E.p)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (E.law.mul t x y).val = (E.law.mul t' x' y').val := by
  subst t'
  have hxx : x = x' := Subtype.ext hx
  have hyy : y = y' := Subtype.ext hy
  subst x'
  subst y'
  rfl

/-- Pull an actual marked test back along an arbitrary affine map.
The auxiliary isomorphism only records the chosen affine ring presentation. -/
lemma exists_test_over (P : AffineTest E M)
    (A : Type u) [CommRing A] [Algebra ℚ A] (f : Base A ⟶ Base P.ring) :
    ∃ Q : AffineTest E M, ∃ e : Base A ≅ Base Q.ring,
      e.hom ≫ Q.base = f ≫ P.base := by
  classical
  letI := P.elliptic
  let ι : P.ring →+* A := (Spec.preimage f).hom
  have hι : baseMap P.ring A ι = f := Spec.map_preimage f
  let V := P.equation.map ι
  obtain ⟨c, _, hc, ho, _⟩ :=
    ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_comparison
      P.equation ι
  obtain ⟨J, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      ι (structureMap P.ring P.equation) (structureMap A V) c hc P.law
  have hJ : IsOriginLaw A V J := by
    constructor
    · intro T t
      apply hc.hom_ext
      · simp only [hj, P.originLaw.1, Category.assoc]
        rw [ho]
      · rw [Category.assoc,
          ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.origin_over,
          Category.comp_id]
        exact (J.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hc.hom_ext
      · rw [hm, hm, P.originLaw.2]
      · exact (J.mul t x y).property.trans (J.mul t y x).property.symm
  have hBC := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.pointed_base_change
    P.law J P.originLaw hJ ι c hc ho
  let B : ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law 4
      ((𝟙 (Base A)) ≫ baseMap P.ring A ι) :=
    ArithmeticThetaFullLevelCoverR0175.BaseChange.restrict P.level
      (baseMap P.ring A ι) (by simp)
  let N := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up
    hBC P.originLaw hJ B
  have hNx : N.x.val ≫ c = baseMap P.ring A ι ≫ P.level.x.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_x
      hBC P.originLaw hJ B
  have hNy : N.y.val ≫ c = baseMap P.ring A ι ≫ P.level.y.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_y
      hBC P.originLaw hJ B
  let Q : AffineTest E M :=
    { ring := A, equation := V, elliptic := inferInstance
      law := J, originLaw := hJ
      base := baseMap P.ring A ι ≫ P.base
      comparison := c ≫ P.comparison
      cartesian := hc.paste_horiz P.cartesian
      zero_eq := by rw [← Category.assoc, ho, Category.assoc, P.zero_eq, Category.assoc]; rfl
      mul_eq := by
        intro T t x y x' y' hx hy
        let px : SchemeHomOver (t ≫ baseMap P.ring A ι)
            (structureMap P.ring P.equation) :=
          ⟨x.val ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.property]; rfl⟩
        let py : SchemeHomOver (t ≫ baseMap P.ring A ι)
            (structureMap P.ring P.equation) :=
          ⟨y.val ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.property]; rfl⟩
        have hh := P.mul_eq T (t ≫ baseMap P.ring A ι) px py
          ⟨x'.val, by rw [Category.assoc]; exact x'.property⟩
          ⟨y'.val, by rw [Category.assoc]; exact y'.property⟩
          (by simpa only [px, Category.assoc] using hx)
          (by simpa only [py, Category.assoc] using hy)
        have hh' := hh.trans (congrArg (fun q => q ≫ P.comparison) (hm t x y).symm)
        exact (mul_val_eq E (Category.assoc t _ _) _ _ x' y' rfl rfl).symm.trans
          (hh'.trans (Category.assoc _ _ _))
      level := N
      x_eq := by rw [← Category.assoc, hNx, Category.assoc, P.x_eq, Category.assoc]
      y_eq := by rw [← Category.assoc, hNy, Category.assoc, P.y_eq, Category.assoc] }
  refine ⟨Q, Iso.refl _, ?_⟩
  change 𝟙 _ ≫ (baseMap P.ring A ι ≫ P.base) = f ≫ P.base
  rw [Category.id_comp, hι]

/-- Agreement on any common base, proved on an affine cover using actual
base-changed tests. The base need not be affine, reduced or quasicompact. -/
lemma overlap (P Q : AffineTest E M) (X : Scheme.{u})
    (f : X ⟶ Base P.ring) (g : X ⟶ Base Q.ring)
    (h : f ≫ P.base = g ≫ Q.base) :
    f.appTop (phaseSection E M P) = g.appTop (phaseSection E M Q) := by
  apply X.affineOpenCover.openCover.ext_elem
  intro i
  let A := X.affineOpenCover.X i
  let a : Base A ⟶ X := X.affineOpenCover.f i
  change a.appTop (f.appTop (phaseSection E M P)) =
    a.appTop (g.appTop (phaseSection E M Q))
  let ι : P.ring →+* A := (Spec.preimage (a ≫ f)).hom
  letI : Algebra ℚ A := (ι.comp (algebraMap ℚ P.ring)).toAlgebra
  obtain ⟨R, e, he⟩ := exists_test_over E M P A (a ≫ f)
  have hP : (e.inv ≫ a ≫ f) ≫ P.base = R.base := by
    rw [Category.assoc, Category.assoc, ← Category.assoc a, ← he,
      Iso.inv_hom_id_assoc]
  have hQ : (e.inv ≫ a ≫ g) ≫ Q.base = R.base := by
    rw [Category.assoc, Category.assoc, ← h]
    exact hP
  have hp := phaseSection_natural E M P R (e.inv ≫ a ≫ f) hP
  have hq := phaseSection_natural E M Q R (e.inv ≫ a ≫ g) hQ
  have hh := congrArg e.hom.appTop (hp.trans hq.symm)
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    Iso.hom_inv_id_assoc] using hh

/-- Gluing regular functions through the represented affine-line functor. -/
private lemma glue_sections {X : Scheme.{u}} (C : X.OpenCover)
    (t : ∀ i, Γ(C.X i, ⊤))
    (h : ∀ i j, (pullback.fst (C.f i) (C.f j)).appTop (t i) =
      (pullback.snd (C.f i) (C.f j)).appTop (t j)) :
    ∃ z : Γ(X, ⊤), ∀ i, (C.f i).appTop z = t i := by
  let g := fun i => (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u+1}).symm (fun _ => t i)
  have hg : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ g i =
      pullback.snd (C.f i) (C.f j) ≫ g j := by
    intro i j
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u+1}).injective
    funext x
    simpa only [AffineSpace.toSpecMvPolyIntEquiv_comp, g, Equiv.apply_symm_apply]
      using h i j
  let q := C.glueMorphisms g hg
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv PUnit.{u+1} q PUnit.unit, ?_⟩
  intro i
  have hh := congrArg (fun q => AffineSpace.toSpecMvPolyIntEquiv PUnit.{u+1} q PUnit.unit)
    (C.ι_glueMorphisms g hg i)
  simpa only [AffineSpace.toSpecMvPolyIntEquiv_comp, g, Equiv.apply_symm_apply] using hh

/-- The marked charts supplied by the accepted predecessor form an actual open cover. -/
def cover (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) : S.OpenCover := by
  classical
  let P := fun s => Classical.choose (MarkedAffineTestComparison.coverage E M k σ s)
  have hP := fun s => Classical.choose_spec (MarkedAffineTestComparison.coverage E M k σ s)
  exact { I₀ := S, X := fun s => Base (P s).ring, f := fun s => (P s).base
          mem₀ := by
            rw [Scheme.presieve₀_mem_precoverage_iff]
            exact ⟨fun s => ⟨s, (hP s).2⟩, fun s => (hP s).1⟩ }

/-- Descent supplies a section and equality on every affine test, not just the
chosen open charts. -/
lemma exists_section (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) :
    ∃ z : Γ(S, ⊤), ∀ P : AffineTest E M,
      P.base.appTop z = phaseSection E M P := by
  classical
  let P := fun s => Classical.choose (MarkedAffineTestComparison.coverage E M k σ s)
  let C := cover E M k σ
  obtain ⟨z, hz⟩ := glue_sections C (fun s => phaseSection E M (P s))
    (fun s t => overlap E M (P s) (P t) _ _ _ (pullback.condition ..))
  change ∀ s : S, (P s).base.appTop z = phaseSection E M (P s) at hz
  refine ⟨z, ?_⟩
  intro Q
  apply Scheme.OpenCover.ext_elem _ _ (C.pullback₁ Q.base)
  intro s
  change S at s
  change (pullback.fst Q.base (P s).base).appTop (Q.base.appTop z) =
    (pullback.fst Q.base (P s).base).appTop (phaseSection E M Q)
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hz s]
  exact (overlap E M Q (P s) _ _ _ (pullback.condition ..)).symm

/-- All marked affine tests jointly detect equality of global regular functions. -/
lemma section_ext (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (a b : Γ(S, ⊤)) (h : ∀ P : AffineTest E M,
      affineScalar E M P a = affineScalar E M P b) : a = b := by
  classical
  apply (cover E M k σ).ext_elem
  intro s
  change S at s
  let P := Classical.choose (MarkedAffineTestComparison.coverage E M k σ s)
  change P.base.appTop a = P.base.appTop b
  exact (Scheme.ΓSpecIso (.of P.ring)).commRingCatIsoToRingEquiv.injective (h P)

lemma exists_unique (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) :
    ∃! z : Γ(S, ⊤), MillerPhase E M z := by
  obtain ⟨z, hz⟩ := exists_section E M k σ
  have hphase : MillerPhase E M z := by
    intro P
    change ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase P.ring P.equation
      P.law P.level ((Scheme.ΓSpecIso (.of P.ring)).hom (P.base.appTop z))
    rw [hz P]
    simpa only [phaseSection, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] using phase_spec E M P
  refine ⟨z, hphase, ?_⟩
  intro w hw
  apply section_ext E M k σ w z
  intro P
  letI := P.elliptic
  exact (arbitrary_geometric_phase P.ring P.equation P.law P.originLaw P.level).1.unique
    (hw P) (hphase P)

lemma square (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (z : Γ(S, ⊤)) (hz : MillerPhase E M z) : z^2 = -1 := by
  apply section_ext E M k σ
  intro P
  letI := P.elliptic
  have h := ((arbitrary_geometric_phase P.ring P.equation P.law P.originLaw P.level).2
    _ (hz P)).2.2.1
  simpa only [affineScalar, map_pow, map_neg, map_one] using h

lemma primitive (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (z : Γ(S, ⊤)) (hz : z^2 = -1) (hn : Nontrivial Γ(S, ⊤)) :
    IsPrimitiveRoot z 4 := by
  letI := hn
  let ι : k →+* Γ(S, ⊤) := σ.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : Algebra k Γ(S, ⊤) := ι.toAlgebra
  letI : CharZero Γ(S, ⊤) := charZero_of_injective_algebraMap (algebraMap k Γ(S, ⊤)).injective
  have hfour : z^4 = 1 := by
    calc
      z^4 = (z^2)^2 := by ring
      _ = 1 := by rw [hz]; ring
  have hord : orderOf z = 4 := orderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [show (2:ℕ)^1 = 2 by decide, hz]; norm_num) hfour
  rw [← hord]
  exact IsPrimitiveRoot.orderOf _

end SchemeMillerPhase

open CategoryTheory AlgebraicGeometry

/-- The exact normalized Miller ratio descends to a unique global regular
function and retains its affine geometric pairing identification on every test. -/
theorem scheme_miller_phase :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z) ∧ (∀ z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → IsUnit z ∧ z^2 = -1 ∧ (Nontrivial (S.presheaf.obj (Opposite.op ⊤)) → IsPrimitiveRoot z 4) ∧ (∀ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase P.ring P.equation P.law P.level (ArithmeticThetaSchemeFourCharacterR0215.affineScalar E M P z))) := by
  intro k _ _ S σ E M
  refine ⟨SchemeMillerPhase.exists_unique E M k σ, ?_⟩
  intro z hz
  have hs := SchemeMillerPhase.square E M k σ z hz
  have hu : IsUnit z := isUnit_iff_exists_inv.mpr ⟨-z, by
    calc
      z*(-z) = -(z^2) := by ring
      _ = 1 := by rw [hs]; ring⟩
  refine ⟨hu, hs, SchemeMillerPhase.primitive k σ z hs, ?_⟩
  intro P
  letI := P.elliptic
  exact ((ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase
    P.ring P.equation P.law P.originLaw P.level).2 _ (hz P)).1

#print axioms scheme_miller_phase
end ArithmeticThetaSchemeFourCharacterR0215
