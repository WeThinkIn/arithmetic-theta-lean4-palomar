module

public import ArbitraryFramedPresentationR0203
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLocalWeierstrassR0203
namespace SchemeLocal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section AffineRestriction
variable {S A : Scheme.{u}} {f : A ⟶ S}
variable {R : Type u} [CommRing R] (ι : Base R ⟶ S)
def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t' (pullback.snd f ι)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (pullback.snd f ι) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t' (pullback.snd f ι)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t' (pullback.snd f ι)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t' (pullback.snd f ι) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (pullback.snd f ι)) :
    baseChangePointToBase ι (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

def affineLaw (G : SchemeLaw f) : RelativeGroupLaw R (pullback.snd f ι) where
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


end AffineRestriction

/-- Multiplication naturality forces the identity to be natural as well. -/
lemma one_natural {S A : Scheme.{u}} {f : A ⟶ S} (G : SchemeLaw f)
    {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  letI : Group (SchemeHomOver t' f) :=
    { mul := G.mul t', one := G.one t', inv := G.inv t'
      mul_assoc := G.mul_assoc t', one_mul := G.one_mul t', mul_one := G.mul_one t'
      inv_mul_cancel := G.inv_mul_cancel t' }
  let a := GoodReductionJacobian.schemeHomOverComp ψ hψ (G.one t)
  have h : a * a = a := by
    change G.mul t' a a = a
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  exact mul_left_cancel (h.trans (mul_one a).symm)

lemma affineLaw_comm {S A : Scheme.{u}} {f : A ⟶ S} (G : SchemeLaw f)
    {R : Type u} [CommRing R] (b : Base R ⟶ S) :
    (affineLaw b G).IsCommutative := by
  intro T t x y
  change baseChangePointOfBase b (G.mul _ _ _) = baseChangePointOfBase b (G.mul _ _ _)
  rw [G.mul_comm]

lemma affineLaw_zero {S : Scheme.{u}} (E : Family S)
    {R : Type u} [CommRing R] (b : Base R ⟶ S) :
    ((affineLaw b E.law).one (𝟙 _)).val ≫ pullback.fst E.p b = b ≫ E.zero := by
  change (pullback.lift _ _ _) ≫ _ = _
  rw [pullback.lift_fst]
  have h := congrArg Subtype.val (one_natural E.law (𝟙 S) ((𝟙 (Base R)) ≫ b) b (by simp))
  exact h.symm

lemma mul_val_congr {S A T : Scheme.{u}} {f : A ⟶ S} (G : SchemeLaw f)
    {t t' : T ⟶ S} (h : t = t') (x y : SchemeHomOver t f)
    (x' y' : SchemeHomOver t' f) (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (G.mul t x y).val = (G.mul t' x' y').val := by
  subst t'
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  subst x'; subst y'; rfl

/-- The intermediate chart records actual maps and their pointwise group compatibility. -/
structure FramedChart {S : Scheme.{u}} (E : Family S) where
  ring : Type u
  [commRing : CommRing ring]
  Q : FramedCurve ring
  base : Base ring ⟶ S
  openImmersion : IsOpenImmersion base
  comparison : Q.target ⟶ E.curve
  cartesian : IsPullback comparison Q.structureMap E.p base
  zero_eq : Q.zero ≫ comparison = base ≫ E.zero
  comm : Q.law.IsCommutative
  mul_eq : ∀ (T : Scheme.{u}) (t : T ⟶ Base ring)
    (x y : SchemeHomOver t Q.structureMap)
    (x' y' : SchemeHomOver (t ≫ base) E.p),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (E.law.mul _ x' y').val = (Q.law.mul t x y).val ≫ comparison

/-- Refine an affine neighbourhood by a principal open trivializing the identity cotangent. -/
theorem exists_framedChart {S : Scheme.{u}} (E : Family S) (s : S) :
    ∃ C : FramedChart E, s ∈ Set.range C.base := by
  obtain ⟨R, b, hb, r, hr⟩ := S.exists_Spec_apply_eq s
  letI := hb
  letI := E.proper
  letI := E.dimension
  letI := E.connected
  let f := pullback.snd E.p b
  let L := affineLaw b E.law
  let N := (Scheme.Modules.pullback (L.one (𝟙 _)).val).obj f.kaehler
  have hN : Scheme.Modules.IsInvertible N :=
    FiniteTypeApproximation.identity_cotangent_invertible f L
  obtain ⟨n, a, ha, htriv, _, _⟩ :=
    Scheme.Modules.IsInvertible.exists_finite_away_cover_trivial N hN
  let cov := Scheme.affineOpenCoverOfSpanRangeEqTop a ha
  obtain ⟨r', hr'⟩ := cov.covers r
  let i : Fin n := cov.idx r
  let A := Localization.Away (a i)
  let c : Base A ⟶ Base R := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := pullback.snd f c
  let K := L.baseChange c
  have hz : (K.one (𝟙 _)).val ≫ pullback.fst f c = c ≫ (L.one (𝟙 _)).val := by
    have h := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 (Base A)) ≫ c) c (by simp))
    change (pullback.lift _ _ _) ≫ pullback.fst f c = _
    rw [pullback.lift_fst]
    exact h.symm
  obtain ⟨η⟩ := htriv i
  let η' := η.symm ≪≫
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso
      f g (pullback.fst f c) (IsPullback.of_hasPullback f c)
      (L.one (𝟙 _)).val (K.one (𝟙 _)).val hz
  let Q : FramedCurve A :=
    { target := pullback f c, structureMap := g, law := K
      geometry := { smooth := inferInstance, proper := inferInstance
                    connectedFibres := g.isConnected_preimage_singleton
                    hasGroupLaw := ⟨K⟩ }
      dimension := inferInstance, hodge := ⟨η'⟩ }
  let π := pullback.fst f c ≫ pullback.fst E.p b
  have hzero : Q.zero ≫ π = (c ≫ b) ≫ E.zero := by
    change (K.one (𝟙 _)).val ≫ (pullback.fst f c ≫ pullback.fst E.p b) = _
    rw [← Category.assoc, hz, Category.assoc]
    change c ≫ ((affineLaw b E.law).one (𝟙 _)).val ≫ pullback.fst E.p b = _
    rw [affineLaw_zero, Category.assoc]
  let C : FramedChart E :=
    { ring := A, Q := Q, base := c ≫ b, openImmersion := inferInstance
      comparison := π
      cartesian := (IsPullback.of_hasPullback f c).paste_horiz (IsPullback.of_hasPullback E.p b)
      zero_eq := hzero
      comm := RelativeGroupLaw.IsCommutative.baseChange c (affineLaw_comm E.law b)
      mul_eq := by
        intro T t x y x' y' hx hy
        let x₀ := RelativeGroupLaw.baseChangePointToBase c x
        let y₀ := RelativeGroupLaw.baseChangePointToBase c y
        have hx' : x' = baseChangePointToBase b x₀ := by
          apply Subtype.ext
          simpa only [x₀, y₀, baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
            π, Category.assoc] using hx
        have hy' : y' = baseChangePointToBase b y₀ := by
          apply Subtype.ext
          simpa only [x₀, y₀, baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
            π, Category.assoc] using hy
        subst x'; subst y'
        change _ = (pullback.lift _ _ _) ≫ π
        simp only [π, ← Category.assoc, pullback.lift_fst]
        change _ = (pullback.lift _ _ _) ≫ pullback.fst E.p b
        rw [pullback.lift_fst]
        exact mul_val_congr E.law (Category.assoc t c b).symm _ _ _ _ rfl rfl }
  refine ⟨C, r', ?_⟩
  change b (c r') = s
  exact (congrArg b hr').trans hr


/-- Present a framed chart and transport its given law along the pointed isomorphism. -/
theorem FramedChart.exists_presentation {S : Scheme.{u}} (E : Family S)
    (C : FramedChart E) (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) :
    ∃ P : LocalPresentation k S σ E, Set.range P.base = Set.range C.base := by
  letI := C.commRing
  let scalar : k →+* C.ring := (Spec.preimage (C.base ≫ σ)).hom
  letI : Algebra k C.ring := scalar.toAlgebra
  letI : Algebra ℚ C.ring := Algebra.compHom C.ring (algebraMap ℚ k)
  obtain ⟨W, hW, e, he, hz⟩ := arbitrary_framed_presentation C.ring C.Q
  obtain ⟨G, hm, h1⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso e he C.Q.law
  have hinv : e.inv ≫ C.Q.structureMap = ArithmeticThetaRelativeKatoR0169.structureMap C.ring W := by
    rw [← he, e.inv_hom_id_assoc]
  let back {T : Scheme.{u}} {t : T ⟶ Base C.ring}
      (x : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap C.ring W)) :
      SchemeHomOver t C.Q.structureMap :=
    ⟨x.val ≫ e.inv, by rw [Category.assoc, hinv, x.property]⟩
  have hmul : ∀ (T : Scheme.{u}) (t : T ⟶ Base C.ring)
      (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap C.ring W)),
      (G.mul t x y).val = (C.Q.law.mul t (back x) (back y)).val ≫ e.hom := by
    intro T t x y
    simpa only [back, Category.assoc, e.inv_hom_id, Category.comp_id] using hm t (back x) (back y)
  let G' : ArithmeticThetaRelativeKatoR0169.Law C.ring W :=
    { mul := G.mul, one := G.one, inv := G.inv
      mul_assoc := G.mul_assoc, one_mul := G.one_mul, mul_one := G.mul_one
      inv_mul_cancel := G.inv_mul_cancel, mul_natural := G.mul_natural }
  have hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw C.ring W G' := by
    constructor
    · intro T t
      change (G.one t).val = _
      rw [h1]
      have h := congrArg Subtype.val (C.Q.law.one_natural (𝟙 _) t t (by simp))
      change t ≫ C.Q.zero = (C.Q.law.one t).val at h
      rw [← h, Category.assoc, hz]
    · intro T t x y
      apply Subtype.ext
      change (G.mul t x y).val = (G.mul t y x).val
      rw [hmul, hmul, C.comm]
  have sq : IsPullback e.inv (ArithmeticThetaRelativeKatoR0169.structureMap C.ring W)
      C.Q.structureMap (𝟙 (Base C.ring)) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hinv⟩
  let P : LocalPresentation k S σ E :=
    { ring := C.ring, equation := W, elliptic := hW, base := C.base
      openImmersion := C.openImmersion
      base_eq := (Spec.map_preimage (C.base ≫ σ)).symm
      comparison := e.inv ≫ C.comparison
      cartesian := by simpa only [Category.id_comp] using sq.paste_horiz C.cartesian
      zero_eq := by rw [← hz, Category.assoc, e.hom_inv_id_assoc, C.zero_eq]
      law := G', originLaw := hG
      mul_eq := by
        intro T t x y x' y' hx hy
        change _ = (G.mul t x y).val ≫ (e.inv ≫ C.comparison)
        rw [hmul, Category.assoc, e.hom_inv_id_assoc]
        apply C.mul_eq T t (back x) (back y) x' y'
        · simpa only [back, Category.assoc] using hx
        · simpa only [back, Category.assoc] using hy }
  exact ⟨P, rfl⟩

end SchemeLocal

open CategoryTheory AlgebraicGeometry
/-- Every point of an arbitrary characteristic-zero base has an affine pointed
Weierstrass presentation preserving multiplication on all test schemes. -/
theorem scheme_local_weierstrass
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ Base k) (E : Family S) (s : S) :
    ∃ P : LocalPresentation k S σ E, s ∈ Set.range P.base := by
  obtain ⟨C, hC⟩ := SchemeLocal.exists_framedChart E s
  obtain ⟨P, hP⟩ := C.exists_presentation E k σ
  exact ⟨P, hP.symm ▸ hC⟩

#print axioms scheme_local_weierstrass
end ArithmeticThetaLocalWeierstrassR0203
