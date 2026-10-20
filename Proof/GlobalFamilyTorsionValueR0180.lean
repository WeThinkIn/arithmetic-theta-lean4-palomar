module

public import EllipticFamilyWeierstrassAtlasR0180

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaOpenHodgeR0180
namespace GlobalFamilyTorsionValueR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176

/-- The actual section transported through a Cartesian test. -/
def testPoint {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _) :
    Base R ⟶ Curve R W :=
  C.cartesian.lift (baseMap S R C.scalar ≫ P) (𝟙 _) (by simp [hP])

lemma testPoint_over {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _) :
    testPoint C P hP ≫ structureMap R W = 𝟙 _ := C.cartesian.lift_snd _ _ _

lemma testPoint_map {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _) :
    testPoint C P hP ≫ C.map = baseMap S R C.scalar ≫ P := C.cartesian.lift_fst _ _ _

lemma testPoint_torsion {S R : Type u} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _)
    (N : ℕ) (hNP : P ≫ E.law.schemeNsmul N = zero E) :
    testPoint C P hP ≫ G.schemeNsmul N = origin R W := by
  apply C.cartesian.hom_ext
  · rw [Category.assoc, C.nsmul_eq, ← Category.assoc, testPoint_map,
      Category.assoc, hNP, C.origin_eq]
  · rw [Category.assoc, G.schemeNsmul_over, testPoint_over]
    exact (WeierstrassProjModel.kwZeroSect R W).property.symm

lemma testPoint_ne_zero {S R : Type u} [CommRing S] [CommRing R] [IsDomain R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : Test S E R W G) (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _)
    (hne : Disjoint (Set.range P) (Set.range (zero E))) :
    testPoint C P hP ≠ origin R W := by
  intro he
  have H := (testPoint_map C P hP).symm.trans
    ((congrArg (fun f => f ≫ C.map) he).trans C.origin_eq)
  let x := baseMap S R C.scalar (genericPoint (Base R))
  have hx : P x = zero E x := congrArg (fun f : Base R ⟶ E.curve =>
    f (genericPoint (Base R))) H
  exact Set.disjoint_left.mp hne ⟨x, rfl⟩ ⟨x, hx.symm⟩

/-- Existence for the specified law, without replacing it by an existentially
chosen group law. -/
lemma normalized_exists (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) : ∃ g, Normalized R W G c g := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  obtain ⟨f, hf, _⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6
  let g := C.field.symm f
  have hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g) := by
    simpa only [g, RingEquiv.apply_symm_apply] using hf
  refine ⟨g, (RelativeExistence.relative_of_generic R W G hG C c hc hc6 g hg).1, ?_⟩
  intro D
  exact RelativeExistence.comparison_independent R W G C D c hc hc6 g hg

lemma normalized_unique (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) {g g' : (Curve R W).functionField}
    (hg : Normalized R W G c g) (hg' : Normalized R W G c g') : g = g' := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  obtain ⟨f, _, hf⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law C.originLaw c hc hc6
  exact C.field.injective ((hf _ (hg.2 C)).trans (hf _ (hg'.2 C)).symm)

/-- Every test has a unique unit value for the actual transported section. -/
lemma test_value_exists {S : Type u} [CommRing S] (E : EllipticFamily S)
    (c N : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (hN : 0 < N) (hcN : Nat.Coprime c N)
    (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _)
    (hNP : P ≫ E.law.schemeNsmul N = zero E)
    (hne : Disjoint (Set.range P) (Set.range (zero E)))
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G) :
    ∃! v : R, IsUnit v ∧ ∀ g, Normalized R W G c g →
      HasValue R W (testPoint C P hP) g v := by
  obtain ⟨g, hg⟩ := normalized_exists R W G hG c hc hc6
  obtain ⟨_, v, hv, hu⟩ := relative_torsion_unit_value R W G hG c hc hc6 g hg
    (testPoint C P hP) (testPoint_over C P hP) N hN
    (testPoint_torsion C P hP N hNP) (testPoint_ne_zero C P hP hne) hcN
  refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
  · intro g' hg'
    rw [← normalized_unique R W G hG c hc hc6 hg hg']
    exact hv.2
  · intro w hw
    exact hu w ⟨hw.1, hw.2 g hg⟩

/-- A factorization of base maps uniquely induces the comparison of tests. -/
lemma test_factor {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    {V : WeierstrassCurve T} {H : Law T V}
    (C : Test S E R W G) (D : Test S E T V H)
    (ρ : R →+* T) (hρ : D.scalar = ρ.comp C.scalar) :
    ∃ b : Curve T V ⟶ Curve R W,
      IsBaseChange R W G T V H ρ b ∧ b ≫ C.map = D.map := by
  have hb : baseMap S T D.scalar = baseMap R T ρ ≫ baseMap S R C.scalar := by
    simp only [hρ, baseMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let b := C.cartesian.lift D.map (structureMap T V ≫ baseMap R T ρ)
    (by rw [D.cartesian.w, hb, Category.assoc])
  have hbm : b ≫ C.map = D.map := C.cartesian.lift_fst _ _ _
  have hbs : b ≫ structureMap R W = structureMap T V ≫ baseMap R T ρ :=
    C.cartesian.lift_snd _ _ _
  refine ⟨b, ⟨?_, ?_, ?_⟩, hbm⟩
  · apply IsPullback.of_right _ hbs C.cartesian
    rw [hbm, ← hb]
    exact D.cartesian
  · apply C.cartesian.hom_ext
    · simp only [Category.assoc, hbm, D.origin_eq, C.origin_eq, baseMap, hρ, CommRingCat.ofHom_comp, Spec.map_comp]
    · have hV : origin T V ≫ structureMap T V = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect T V).property
      have hW : origin R W ≫ structureMap R W = 𝟙 _ :=
        (WeierstrassProjModel.kwZeroSect R W).property
      rw [Category.assoc, hbs, ← Category.assoc, hV, Category.id_comp,
        Category.assoc, hW, Category.comp_id]
      rfl
  · intro n
    apply C.cartesian.hom_ext
    · rw [Category.assoc, hbm, D.nsmul_eq, Category.assoc, C.nsmul_eq,
        ← Category.assoc, hbm]
    · rw [Category.assoc, hbs, ← Category.assoc, H.schemeNsmul_over,
        Category.assoc, G.schemeNsmul_over, hbs]

lemma test_value_natural {S : Type u} [CommRing S] (E : EllipticFamily S)
    (c N : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (hN : 0 < N) (hcN : Nat.Coprime c N)
    (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _)
    (hNP : P ≫ E.law.schemeNsmul N = zero E)
    (hne : Disjoint (Set.range P) (Set.range (zero E)))
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G)
    (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T]
    [IsIntegrallyClosed T] [Algebra ℚ T] (V : WeierstrassCurve T) [V.IsElliptic]
    [IsIntegral (Curve T V)] [IsLocallyNoetherian (Curve T V)]
    [IsIntegral (GenericCurve T V)] [IsLocallyNoetherian (GenericCurve T V)]
    (H : Law T V) (hH : IsOriginLaw T V H) (D : Test S E T V H)
    (ρ : R →+* T) (hρ : D.scalar = ρ.comp C.scalar)
    {v : R} (hv : ∀ g, Normalized R W G c g → HasValue R W (testPoint C P hP) g v) :
    ∀ g, Normalized T V H c g → HasValue T V (testPoint D P hP) g (ρ v) := by
  obtain ⟨b, hb, hbm⟩ := test_factor C D ρ hρ
  have hpoint : testPoint D P hP ≫ b = baseMap R T ρ ≫ testPoint C P hP := by
    apply C.cartesian.hom_ext
    · rw [Category.assoc, hbm, testPoint_map, Category.assoc, testPoint_map,
        ← Category.assoc]
      congr 1
      simp only [hρ, baseMap, CommRingCat.ofHom_comp, Spec.map_comp]
    · rw [Category.assoc, hb.1.w, ← Category.assoc, testPoint_over, Category.id_comp,
        Category.assoc, testPoint_over, Category.comp_id]
      rfl
  obtain ⟨g, hg⟩ := normalized_exists R W G hG c hc hc6
  intro gs hgs
  obtain ⟨w, hw, _⟩ := relative_torsion_value_naturality R W G hG T V H hH ρ b hb
    c hc hc6 g hg gs hgs (testPoint C P hP) (testPoint_over C P hP) N hN
    (testPoint_torsion C P hP N hNP) (testPoint_ne_zero C P hP hne) hcN
    (testPoint D P hP) (testPoint_over D P hP) hpoint
  have he : w = v := TorsionUnitValue.hasValue_unique R W _ g hw.2.1 (hv g hg)
  exact he ▸ hw.2.2.2

/-- Genuine pointed Weierstrass tests remain available after any ring map. -/
lemma test_base_change {S R T : Type u} [CommRing S] [CommRing R] [CommRing T]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (hG : IsOriginLaw R W G) (C : Test S E R W G) (ρ : R →+* T) :
    ∃ (H : Law T (W.map ρ)) (_hH : IsOriginLaw T (W.map ρ) H)
      (D : Test S E T (W.map ρ) H), D.scalar = ρ.comp C.scalar := by
  letI := ρ.toAlgebra
  obtain ⟨α, hα⟩ := WeierstrassProjModel.projModel_isPullback_baseChange_ring W.toProjective T
  obtain ⟨b, hb, he⟩ := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.pointed_cartesian
    ρ (structureMap T (W.map ρ)) α hα G (WeierstrassProjModel.kwZeroSect T (W.map ρ))
  have he' : origin T (W.map ρ) ≫ b = baseMap R T ρ ≫ origin R W := he.trans (hG.1 _)
  obtain ⟨H, hm, ho⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      ρ (structureMap R W) (structureMap T (W.map ρ)) b hb G
  have hH : IsOriginLaw T (W.map ρ) H := by
    constructor
    · intro X t
      apply hb.hom_ext
      · simp only [ho, hG.1, Category.assoc, he', baseMap]
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z) (WeierstrassProjModel.kwZeroSect T (W.map ρ)).property).trans
            (Category.comp_id t)).symm)
    · intro X t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hn := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    ρ (structureMap T (W.map ρ)) b hb G H hm ho
  refine ⟨H, hH, ⟨ρ.comp C.scalar, b ≫ C.map, ?_, ?_, ?_⟩, rfl⟩
  · simpa only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp] using hb.paste_horiz C.cartesian
  · rw [← Category.assoc, he', Category.assoc, C.origin_eq, ← Category.assoc]
    congr 1
    simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · intro n
    rw [← Category.assoc, hn, Category.assoc, C.nsmul_eq, Category.assoc]

section Values
variable {S : Type u} [CommRing S] {E : EllipticFamily S}

/-- Packaging of precisely the torsion hypotheses used for local evaluation. -/
structure Datum (E : EllipticFamily S) where
  c : ℕ
  N : ℕ
  hc : 1 < c
  hc6 : Nat.Coprime c 6
  hN : 0 < N
  hcN : Nat.Coprime c N
  point : Base S ⟶ E.curve
  over_eq : point ≫ E.projection = 𝟙 _
  torsion : point ≫ E.law.schemeNsmul N = zero E
  nonidentity : Disjoint (Set.range point) (Set.range (zero E))

variable (d : Datum E)
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
local instance curveIntegral : IsIntegral (Curve R W) := (relative_curve_geometry R W).1
local instance curveNoetherian : IsLocallyNoetherian (Curve R W) := (relative_curve_geometry R W).2.1
local instance genericIntegral : IsIntegral (GenericCurve R W) := (relative_curve_geometry R W).2.2.2.1
local instance genericNoetherian : IsLocallyNoetherian (GenericCurve R W) :=
  (relative_curve_geometry R W).2.2.2.2.1

variable {R W} (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G)

def value : R := Classical.choose (test_value_exists E d.c d.N d.hc d.hc6 d.hN d.hcN
  d.point d.over_eq d.torsion d.nonidentity R W G hG C)

lemma value_property : IsUnit (value d G hG C) ∧ ∀ g, Normalized R W G d.c g →
    HasValue R W (testPoint C d.point d.over_eq) g (value d G hG C) :=
  (Classical.choose_spec (test_value_exists E d.c d.N d.hc d.hc6 d.hN d.hcN
    d.point d.over_eq d.torsion d.nonidentity R W G hG C)).1

lemma value_natural
    (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T]
    [IsIntegrallyClosed T] [Algebra ℚ T] (V : WeierstrassCurve T) [V.IsElliptic]
    (H : Law T V) (hH : IsOriginLaw T V H) (D : Test S E T V H)
    (ρ : R →+* T) (hρ : D.scalar = ρ.comp C.scalar) :
    ρ (value d G hG C) = value d H hH D := by
  obtain ⟨g, hg⟩ := normalized_exists T V H hH d.c d.hc d.hc6
  exact TorsionUnitValue.hasValue_unique T V _ g
    (test_value_natural E d.c d.N d.hc d.hc6 d.hN d.hcN
      d.point d.over_eq d.torsion d.nonidentity R W G hG C T V H hH D ρ hρ
      (value_property d G hG C).2 g hg)
    ((value_property d H hH D).2 g hg)

lemma values_agree_on_field
    (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T]
    [IsIntegrallyClosed T] [Algebra ℚ T] (V : WeierstrassCurve T) [V.IsElliptic]
    (H : Law T V) (hH : IsOriginLaw T V H) (D : Test S E T V H)
    (K : Type u) [Field K] [Algebra ℚ K] (ρ : R →+* K) (σ : T →+* K)
    (he : ρ.comp C.scalar = σ.comp D.scalar) :
    ρ (value d G hG C) = σ (value d H hH D) := by
  obtain ⟨J, hJ, B, hB⟩ := test_base_change hG C ρ
  exact (value_natural d G hG C K (W.map ρ) J hJ B ρ hB).trans
    (value_natural d H hH D K (W.map ρ) J hJ B σ (hB.trans he)).symm

lemma scalar_natural {A B : Type u} [CommRing A] [CommRing B]
    (ρ : A →+* B) (v : A) :
    (baseMap A B ρ).appTop (scalar A v) = scalar B (ρ v) :=
  (congrArg (fun f : CommRingCat.of A ⟶ Γ(Base B, ⊤) => f v)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))).symm

/-- Local values agree as regular sections on every common integral test
scheme. Only a field comparison is used to detect equality. -/
lemma values_agree_on_integral
    (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T]
    [IsIntegrallyClosed T] [Algebra ℚ T] (V : WeierstrassCurve T) [V.IsElliptic]
    (H : Law T V) (hH : IsOriginLaw T V H) (D : Test S E T V H)
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Base R) (g : X ⟶ Base T)
    (he : f ≫ baseMap S R C.scalar = g ≫ baseMap S T D.scalar) :
    f.appTop (scalar R (value d G hG C)) = g.appTop (scalar T (value d H hH D)) := by
  let K := X.functionField
  let j := X.fromSpecStalk (genericPoint X)
  let ρ : R →+* K := (Spec.preimage (j ≫ f)).hom
  let σ : T →+* K := (Spec.preimage (j ≫ g)).hom
  have hρ : baseMap R K ρ = j ≫ f := Spec.map_preimage _
  have hσ : baseMap T K σ = j ≫ g := Spec.map_preimage _
  letI : Algebra ℚ K := (ρ.comp (algebraMap ℚ R)).toAlgebra
  have he' : ρ.comp C.scalar = σ.comp D.scalar := by
    suffices hh : CommRingCat.ofHom (ρ.comp C.scalar) = CommRingCat.ofHom (σ.comp D.scalar) from
      congrArg CommRingCat.Hom.hom hh
    apply Spec.map_injective
    change baseMap S K (ρ.comp C.scalar) = baseMap S K (σ.comp D.scalar)
    simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp]
    change baseMap R K ρ ≫ baseMap S R C.scalar = baseMap T K σ ≫ baseMap S T D.scalar
    rw [hρ, hσ, Category.assoc, Category.assoc, he]
  have hv := values_agree_on_field d G hG C T V H hH D K ρ σ he'
  have hr := scalar_natural ρ (value d G hG C)
  have hs := scalar_natural σ (value d H hH D)
  rw [hρ, Scheme.Hom.comp_appTop] at hr
  rw [hσ, Scheme.Hom.comp_appTop] at hs
  have hh : j.appTop (f.appTop (scalar R (value d G hG C))) =
      j.appTop (g.appTop (scalar T (value d H hH D))) :=
    hr.trans ((congrArg (scalar K) hv).trans hs.symm)
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  apply X.germToFunctionField_injective ⊤
  have hj : j.appTop ≫ (Scheme.ΓSpecIso K).hom = X.germToFunctionField ⊤ := by
    dsimp only [j]
    rw [Scheme.fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id]
    rw [(Spec (X.presheaf.stalk (genericPoint X))).presheaf.map_id]
    dsimp only [K, Scheme.functionField]
    simp only [Category.comp_id, Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
  have hhh := congrArg (Scheme.ΓSpecIso K).hom hh
  change (j.appTop ≫ (Scheme.ΓSpecIso K).hom) (f.appTop (scalar R (value d G hG C))) =
    (j.appTop ≫ (Scheme.ΓSpecIso K).hom) (g.appTop (scalar T (value d H hH D))) at hhh
  rw [hj] at hhh
  exact hhh

lemma image_section_pull {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : Z ⟶ X) (t : Γ(X, ⊤))
    (e : (⊤ : Z.Opens) ≤ (g ≫ f) ⁻¹ᵁ (f ''ᵁ ⊤)) :
    (g ≫ f).appLE (f ''ᵁ ⊤) ⊤ e ((f.appIso ⊤).inv t) = g.appTop t := by
  have he := Scheme.Hom.appLE_comp_appLE g f (f ''ᵁ ⊤) ⊤ ⊤
    (Scheme.Hom.preimage_image_eq f ⊤).ge le_top
  rw [← he, CommRingCat.comp_apply, ← Scheme.Hom.appIso_hom', Iso.inv_hom_id_apply]
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

lemma restriction_top {X : Scheme.{u}} (O U : X.Opens) (h : O ≤ U) (s : Γ(X, U)) :
    O.topIso.hom (O.ι.appLE U ⊤ (fun x _ => h x.property) s) =
      X.presheaf.map (homOfLE h).op s := by
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appLE, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

/-- The regular unit representatives on two chart images agree on their
intersection, with the empty intersection handled by sheaf separatedness. -/
lemma chart_sections_compatible (C D : Chart S E) :
    letI := C.openImmersion
    letI := D.openImmersion
    let f := baseMap S C.ring C.comparison.scalar
    let g := baseMap S D.ring D.comparison.scalar
    (Base S).presheaf.map (homOfLE (show f ''ᵁ ⊤ ⊓ g ''ᵁ ⊤ ≤ f ''ᵁ ⊤ from inf_le_left)).op
      ((@Scheme.Hom.appIso _ _ f C.openImmersion ⊤).inv
        (scalar C.ring (value d C.law C.originLaw C.comparison))) =
    (Base S).presheaf.map (homOfLE (show f ''ᵁ ⊤ ⊓ g ''ᵁ ⊤ ≤ g ''ᵁ ⊤ from inf_le_right)).op
      ((@Scheme.Hom.appIso _ _ g D.openImmersion ⊤).inv
        (scalar D.ring (value d D.law D.originLaw D.comparison))) := by
  letI := C.openImmersion
  letI := D.openImmersion
  let f := baseMap S C.ring C.comparison.scalar
  let g := baseMap S D.ring D.comparison.scalar
  let O : (Base S).Opens := f ''ᵁ ⊤ ⊓ g ''ᵁ ⊤
  by_cases hO : Nonempty O
  · letI := hO
    have hf : Set.range O.ι ⊆ Set.range f := by
      rintro _ ⟨x, rfl⟩
      exact (x.property.1 : x.val ∈ f ''ᵁ ⊤) |> fun ⟨y, _, hy⟩ => ⟨y, hy⟩
    have hg : Set.range O.ι ⊆ Set.range g := by
      rintro _ ⟨x, rfl⟩
      exact (x.property.2 : x.val ∈ g ''ᵁ ⊤) |> fun ⟨y, _, hy⟩ => ⟨y, hy⟩
    let a := IsOpenImmersion.lift f O.ι hf
    let b := IsOpenImmersion.lift g O.ι hg
    have ha : a ≫ f = O.ι := IsOpenImmersion.lift_fac _ _ _
    have hb : b ≫ g = O.ι := IsOpenImmersion.lift_fac _ _ _
    letI : IsOpenImmersion (a ≫ f) := ha.symm ▸ inferInstance
    letI : IsOpenImmersion a := IsOpenImmersion.of_comp a f
    letI : IsIntegral O := isIntegral_of_isOpenImmersion a
    have he := values_agree_on_integral d C.law C.originLaw C.comparison
      D.ring D.equation D.law D.originLaw D.comparison O a b (ha.trans hb.symm)
    have ea : (⊤ : O.toScheme.Opens) ≤ O.ι ⁻¹ᵁ (f ''ᵁ ⊤) := fun x _ => x.property.1
    have eb : (⊤ : O.toScheme.Opens) ≤ O.ι ⁻¹ᵁ (g ''ᵁ ⊤) := fun x _ => x.property.2
    have hpa := image_section_pull f a
      (scalar C.ring (value d C.law C.originLaw C.comparison)) (by rw [ha]; exact ea)
    have hpb := image_section_pull g b
      (scalar D.ring (value d D.law D.originLaw D.comparison)) (by rw [hb]; exact eb)
    simp only [ha] at hpa
    simp only [hb] at hpb
    have hh := congrArg O.topIso.hom (hpa.trans (he.trans hpb.symm))
    exact (restriction_top O (f ''ᵁ ⊤) inf_le_left _).symm.trans
      (hh.trans (restriction_top O (g ''ᵁ ⊤) inf_le_right _))
  · apply TopCat.Presheaf.section_ext (Base S).sheaf O
    intro x hx
    exact (hO ⟨⟨x, hx⟩⟩).elim

lemma image_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Γ(Y, ⊤)) :
    (f.appIso ⊤).hom (Y.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s) =
      f.appTop s := by
  rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

lemma atlas_value (A : Atlas S E) :
    ∃! v : S, IsUnit v ∧ ∀ i, (A.chart i).comparison.scalar v =
      value d (A.chart i).law (A.chart i).originLaw (A.chart i).comparison := by
  let f (i : Fin A.count) := baseMap S (A.chart i).ring (A.chart i).comparison.scalar
  letI (i : Fin A.count) : IsOpenImmersion (f i) := (A.chart i).openImmersion
  let U (i : Fin A.count) : (Base S).Opens := f i ''ᵁ ⊤
  let t (i : Fin A.count) : Γ(Base S, U i) := (f i |>.appIso ⊤).inv
    (scalar (A.chart i).ring (value d (A.chart i).law (A.chart i).originLaw (A.chart i).comparison))
  have hcover : (⊤ : (Base S).Opens) ≤ ⨆ i, U i := by
    intro x _
    obtain ⟨i, y, hy⟩ := A.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, trivial, hy⟩
  have hcompat : TopCat.Presheaf.IsCompatible (Base S).presheaf U t :=
    fun i j => chart_sections_compatible d (A.chart i) (A.chart j)
  obtain ⟨s, hs, huniq⟩ := (Base S).sheaf.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover t hcompat
  have hsunit : IsUnit s := by
    apply (Base S).toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
    intro x hx
    obtain ⟨i, y, hy⟩ := A.covers x
    have hxi : x ∈ U i := ⟨y, trivial, hy⟩
    have ht : IsUnit (t i) := ((value_property d (A.chart i).law
      (A.chart i).originLaw (A.chart i).comparison).1.map
      (Scheme.ΓSpecIso (CommRingCat.of (A.chart i).ring)).inv.hom).map (f i |>.appIso ⊤).inv.hom
    have hu := ht.map ((Base S).presheaf.germ (U i) x hxi).hom
    rw [← hs i] at hu
    change IsUnit ((Base S).presheaf.germ (U i) x hxi
      ((Base S).presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op s)) at hu
    rw [(Base S).presheaf.germ_res_apply] at hu
    exact hu
  let v := (Scheme.ΓSpecIso (CommRingCat.of S)).hom s
  have hv : scalar S v = s := (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply s
  have hlocal (i : Fin A.count) : (A.chart i).comparison.scalar v =
      value d (A.chart i).law (A.chart i).originLaw (A.chart i).comparison := by
    apply (Scheme.ΓSpecIso (CommRingCat.of (A.chart i).ring)).commRingCatIsoToRingEquiv.symm.injective
    change scalar (A.chart i).ring ((A.chart i).comparison.scalar v) = _
    rw [← scalar_natural (A.chart i).comparison.scalar v, hv]
    exact (image_restrict (f i) s).symm.trans
      ((congrArg (f i |>.appIso ⊤).hom (hs i)).trans (Iso.inv_hom_id_apply _ _))
  refine ⟨v, ⟨hsunit.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom, hlocal⟩, ?_⟩
  intro w hw
  have hwres (i : Fin A.count) : (Base S).presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op
      (scalar S w) = t i := by
    apply (f i |>.appIso ⊤).commRingCatIsoToRingEquiv.injective
    change (f i |>.appIso ⊤).hom
      ((Base S).presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (scalar S w)) =
      (f i |>.appIso ⊤).hom (t i)
    rw [image_restrict (f i), scalar_natural (A.chart i).comparison.scalar w, hw.2 i]
    exact (Iso.inv_hom_id_apply _ _).symm
  have he : scalar S w = s := huniq _ hwres
  simpa only [scalar, Iso.inv_hom_id_apply] using
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom he

/-- Equality on the finite atlas determines the value on every normal-affine
test, even when its base map is a specialization. -/
lemma atlas_value_test (A : Atlas S E) (v : S)
    (hv : ∀ i, (A.chart i).comparison.scalar v =
      value d (A.chart i).law (A.chart i).originLaw (A.chart i).comparison) :
    C.scalar v = value d G hG C := by
  let K := FractionRing R
  let σ := algebraMap R K
  let q := baseMap R K σ ≫ baseMap S R C.scalar
  let x := genericPoint (Base K)
  obtain ⟨i, y, hy⟩ := A.covers (q x)
  let B := A.chart i
  let f := baseMap S B.ring B.comparison.scalar
  letI : IsOpenImmersion f := B.openImmersion
  have hq : Set.range q ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    have hz : z = x := Subsingleton.elim _ _
    exact hz ▸ ⟨y, hy⟩
  let a := IsOpenImmersion.lift f q hq
  let ρ : B.ring →+* K := (Spec.preimage a).hom
  have hρ : baseMap B.ring K ρ = a := Spec.map_preimage _
  have he : ρ.comp B.comparison.scalar = σ.comp C.scalar := by
    suffices hh : CommRingCat.ofHom (ρ.comp B.comparison.scalar) =
        CommRingCat.ofHom (σ.comp C.scalar) from congrArg CommRingCat.Hom.hom hh
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change baseMap B.ring K ρ ≫ f = q
    rw [hρ]
    exact IsOpenImmersion.lift_fac _ _ _
  have hval := values_agree_on_field d B.law B.originLaw B.comparison R W G hG C K ρ σ he
  apply IsFractionRing.injective R K
  change σ (C.scalar v) = σ (value d G hG C)
  calc
    σ (C.scalar v) = ρ (B.comparison.scalar v) :=
      (congrArg (fun τ : S →+* K => τ v) he).symm
    _ = ρ (value d B.law B.originLaw B.comparison) := congrArg ρ (hv i)
    _ = _ := hval

lemma datum_value (A : Atlas S E) : ∃! v : S, IsKatoValue E d.c d.point v := by
  obtain ⟨v, hv, huniq⟩ := atlas_value d A
  refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
  · intro R _ _ _ _ _ W _ _ _ _ _ G hG C P' hP' hmap g hg
    have he : P' = testPoint C d.point d.over_eq := C.cartesian.hom_ext
      (hmap.trans (testPoint_map C d.point d.over_eq).symm)
      (hP'.trans (testPoint_over C d.point d.over_eq).symm)
    rw [he, atlas_value_test d G hG C A v hv.2]
    exact (value_property d G hG C).2 g hg
  · intro w hw
    apply huniq w
    refine ⟨hw.1, ?_⟩
    intro i
    let B := A.chart i
    obtain ⟨g, hg⟩ := normalized_exists B.ring B.equation B.law B.originLaw d.c d.hc d.hc6
    exact TorsionUnitValue.hasValue_unique B.ring B.equation _ g
      (hw.2 B.ring B.equation B.law B.originLaw B.comparison
        (testPoint B.comparison d.point d.over_eq)
        (testPoint_over B.comparison d.point d.over_eq)
        (testPoint_map B.comparison d.point d.over_eq) g hg)
      ((value_property d B.law B.originLaw B.comparison).2 g hg)

end Values
end GlobalFamilyTorsionValueR0180
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
/-- Descent of the normalized Kato unit value, on the entire smooth affine
base and against every prescribed normal-affine Cartesian test. -/
theorem global_family_torsion_value
    (k : Type u) [Field k] [CharZero k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (E : EllipticFamily S) (c N : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (hN : 0 < N) (hcN : Nat.Coprime c N) (P : Base S ⟶ E.curve)
    (hP : P ≫ E.projection = 𝟙 _) (hNP : P ≫ E.law.schemeNsmul N = zero E)
    (hne : Disjoint (Set.range P) (Set.range (zero E))) :
    ∃! v : S, IsKatoValue E c P v := by
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k S hS E
  exact GlobalFamilyTorsionValueR0180.datum_value
    ⟨c, N, hc, hc6, hN, hcN, P, hP, hNP, hne⟩ A

#print axioms global_family_torsion_value
end ArithmeticThetaOpenHodgeR0180
