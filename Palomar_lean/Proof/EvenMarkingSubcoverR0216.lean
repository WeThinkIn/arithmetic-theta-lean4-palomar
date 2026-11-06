module

public import SchemeFourCoverGeometryR0216
public import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
public import SchemePhaseNaturalityR0215
public import SchemeFourMarkingActionR0215
public import SchemeThetaEvaluationR0213

@[expose] public section

-- Preserve original field inference without overriding specialized local-ring instances.
attribute [local instance 999] HenselianLocalRing.toIsLocalRing

/-! Construction tools for the fixed-characteristic, fixed-phase subcover.
All comparisons below are comparisons of the actual scheme morphisms. -/
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaEvenMarkingTorsorR0216.EvenMarkingSubcover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaUniversalEvaluationR0213
open SchemeFourCover

variable {S : Scheme.{u}} (E : Family S)

/-- Restrict a universal marking along an arbitrary map into its parameter scheme. -/
def restrictCover (D : Cover E) {X : Scheme.{u}} (j : X ⟶ D.space) : Cover E :=
  let F := SchemeFamilyBaseChange.baseChangeFamily D.family j
  let f := pullback.fst D.family.p j
  let hc : Cartesian D.family F j f :=
    ⟨IsPullback.of_hasPullback D.family.p j,
      SchemeFamilyBaseChange.baseChangeLaw_zero D.family j,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative D.family j⟩
  { space := X
    projection := j ≫ D.projection
    family := F
    comparison := f ≫ D.comparison
    cartesian := cartesian_comp E D.family F D.projection D.comparison D.cartesian j f hc
    marking := liftMarking D.family F j f hc ((ofFullLevel D.family D.marking).pull D.family j
      |>.cast D.family (Category.comp_id j)) }

lemma restrictCover_map (D : Cover E) {X : Scheme.{u}} (j : X ⟶ D.space) :
    CoverMap E (restrictCover E D j) D j (pullback.fst D.family.p j) := by
  refine ⟨rfl, ⟨IsPullback.of_hasPullback D.family.p j,
    SchemeFamilyBaseChange.baseChangeLaw_zero D.family j,
    SchemeFamilyBaseChange.baseChangeFamily_multiplicative D.family j, ?_, ?_⟩, rfl⟩
  · exact liftPoint_comp D.family _ j _
      ⟨IsPullback.of_hasPullback D.family.p j,
        SchemeFamilyBaseChange.baseChangeLaw_zero D.family j,
        SchemeFamilyBaseChange.baseChangeFamily_multiplicative D.family j⟩ _
  · exact liftPoint_comp D.family _ j _
      ⟨IsPullback.of_hasPullback D.family.p j,
        SchemeFamilyBaseChange.baseChangeLaw_zero D.family j,
        SchemeFamilyBaseChange.baseChangeFamily_multiplicative D.family j⟩ _

/-- The prescribed characteristic and phase are preserved under marked pullback. -/
lemma matches_pullback (P : EvenPoint E) (z : Γ(S, ⊤))
    {B T : Scheme.{u}} (G : Family B) (F : Family T)
    (M : FullLevel G 4) (N : FullLevel F 4)
    (b : B ⟶ S) (f : G.curve ⟶ E.curve)
    (q : T ⟶ B) (h : F.curve ⟶ G.curve)
    (hq : MarkedCartesian G F M N q h) (hm : Matches E P z G M b f) :
    Matches E P z F N (q ≫ b) (h ≫ f) := by
  constructor
  · rw [← Category.assoc, SchemeThetaEvaluation.evenPoint_natural G M F N q h hq,
      Category.assoc, hm.1, Category.assoc]
  · simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
      SchemePhaseNaturality.pullback_phase G F M N q h hq (b.appTop z) hm.2

/-- Exact equations on the parameter scheme characterize matching test markings. -/
lemma matches_iff (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E)
    (w : Γ(D.space, ⊤)) (hw : MillerPhase D.family D.marking w)
    {T : Scheme.{u}} (F : Family T) (N : FullLevel F 4)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (q : T ⟶ D.space) (h : F.curve ⟶ D.family.curve)
    (_hq : q ≫ D.projection = b)
    (hh : MarkedCartesian D.family F D.marking N q h) (hf : h ≫ D.comparison = f) :
    Matches E P z F N b f ↔
      q ≫ evenPoint D.family D.marking ≫ D.comparison = b ≫ P.point.val ∧
      q.appTop w = b.appTop z := by
  have hp := SchemePhaseNaturality.pullback_phase D.family F D.marking N q h hh w hw
  have he : evenPoint F N ≫ f = q ≫ evenPoint D.family D.marking ≫ D.comparison := by
    rw [← hf, ← Category.assoc,
      SchemeThetaEvaluation.evenPoint_natural D.family D.marking F N q h hh,
      Category.assoc]
  constructor
  · intro hm
    refine ⟨he.symm.trans hm.1, ?_⟩
    exact (scheme_miller_phase k T (b ≫ σ) F N).1.unique hp hm.2
  · rintro ⟨heq, hwq⟩
    exact ⟨he.trans heq, hwq ▸ hp⟩

/-- Roots of minus one are units, including in the zero ring. -/
lemma unit_of_square {R : Type*} [CommRing R] (a : R) (ha : a^2 = -1) : IsUnit a :=
  isUnit_iff_exists_inv.mpr ⟨-a, by calc
    a * (-a) = -(a^2) := by ring
    _ = 1 := by rw [ha]; ring⟩

/-- The equal-phase locus is the basic open of the sum of the two roots. -/
def phaseOpen (X : Scheme.{u}) (a b : Γ(X, ⊤)) : X.Opens := X.basicOpen (a + b)

lemma phaseOpen_clopen (X : Scheme.{u}) (a b : Γ(X, ⊤))
    (ha : a^2 = -1) (hb : b^2 = -1) (h2 : IsUnit (2 : Γ(X, ⊤))) :
    IsClopen (phaseOpen X a b : Set X) := by
  have hprod : (a + b) * (a - b) = 0 := by
    calc
      (a + b) * (a - b) = a^2 - b^2 := by ring
      _ = 0 := by rw [ha, hb, sub_self]
  have hsum : (a + b) + (a - b) = 2*a := by ring
  have hu : IsUnit ((a + b) + (a - b)) := hsum ▸ h2.mul (unit_of_square a ha)
  have hinf : X.basicOpen (a + b) ⊓ X.basicOpen (a - b) = ⊥ := by
    rw [← X.basicOpen_mul, hprod, X.basicOpen_zero]
  have hsup : X.basicOpen (a + b) ⊔ X.basicOpen (a - b) = ⊤ := by
    apply top_unique
    simpa only [X.basicOpen_of_isUnit hu] using
      (X.basicOpen_add_le (f := a+b) (g := a-b))
  have hcompl : (phaseOpen X a b : Set X) = (X.basicOpen (a-b) : Set X)ᶜ := by
    ext x
    have hi : ¬ (x ∈ X.basicOpen (a+b) ∧ x ∈ X.basicOpen (a-b)) := by
      intro hh
      have : x ∈ (X.basicOpen (a+b) ⊓ X.basicOpen (a-b)) := hh
      rw [hinf] at this
      exact this
    have hs : x ∈ X.basicOpen (a+b) ∨ x ∈ X.basicOpen (a-b) := by
      change x ∈ (X.basicOpen (a+b) ⊔ X.basicOpen (a-b))
      rw [hsup]; trivial
    change x ∈ X.basicOpen (a+b) ↔ x ∉ X.basicOpen (a-b)
    tauto
  exact ⟨hcompl ▸ (X.basicOpen (a-b)).isOpen.isClosed_compl,
    (phaseOpen X a b).isOpen⟩

lemma unit_of_basicOpen_eq_top (X : Scheme.{u}) (a : Γ(X, ⊤))
    (h : X.basicOpen a = ⊤) : IsUnit a := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply (X.mem_basicOpen a x hx).mp
  rw [h]; trivial

/-- Equality here is equality of regular functions, not equality at geometric points. -/
lemma phaseOpen_universal (X : Scheme.{u}) (a b : Γ(X, ⊤))
    (ha : a^2 = -1) (hb : b^2 = -1) (h2 : IsUnit (2 : Γ(X, ⊤)))
    {T : Scheme.{u}} (q : T ⟶ X) :
    Set.range q ⊆ (phaseOpen X a b : Set X) ↔ q.appTop a = q.appTop b := by
  have he : Set.range q ⊆ (phaseOpen X a b : Set X) ↔
      T.basicOpen (q.appTop (a+b)) = ⊤ := by
    rw [← q.preimage_basicOpen_top]
    constructor
    · intro h
      apply top_unique
      intro x _
      exact h (Set.mem_range_self x)
    · intro h
      rintro _ ⟨x, rfl⟩
      have : x ∈ q ⁻¹ᵁ X.basicOpen (a+b) := by rw [h]; trivial
      exact this
  rw [he]
  constructor
  · intro h
    have hu := unit_of_basicOpen_eq_top T _ h
    apply sub_eq_zero.mp
    apply hu.mul_right_eq_zero.mp
    rw [← map_sub, ← map_mul]
    have hp : (a+b)*(a-b) = 0 := by
      calc
        (a+b)*(a-b) = a^2-b^2 := by ring
        _ = 0 := by rw [ha, hb, sub_self]
    rw [hp, map_zero]
  · intro h
    apply T.basicOpen_of_isUnit
    rw [map_add, h, ← two_mul]
    have htwo : IsUnit (2 : Γ(T, ⊤)) := by
      have hu := h2.map q.appTop.hom
      change IsUnit (q.appTop (2 : Γ(X, ⊤))) at hu
      simpa only [map_ofNat] using hu
    exact htwo.mul ((unit_of_square b hb).map q.appTop.hom)

/-- Relative separatedness constructs the actual scheme equalizer. -/
lemma closed_equalizer {B X Y : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B)
    [IsSeparated πY] (a b : X ⟶ Y) (ha : a ≫ πY = πX) (hb : b ≫ πY = πX) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧ j ≫ a = j ≫ b ∧
      ∀ (T : Scheme.{u}) (q : T ⟶ X), q ≫ a = q ≫ b →
        ∃! r : T ⟶ Z, r ≫ j = q := by
  let a' : Over.mk πX ⟶ Over.mk πY := Over.homMk a ha
  let b' : Over.mk πX ⟶ Over.mk πY := Over.homMk b hb
  let j := (equalizer.ι a' b').left
  have hj : IsClosedImmersion j := by
    letI : IsSeparated (Over.mk πY).hom := ‹IsSeparated πY›
    exact isClosedImmersion_equalizer_ι_left a' b'
  letI := hj
  refine ⟨(equalizer a' b').left, j, hj, ?_, ?_⟩
  · exact congrArg (fun h => h.left) (equalizer.condition a' b')
  · intro T q hq
    let q' : Over.mk (q ≫ πX) ⟶ Over.mk πX := Over.homMk q rfl
    have h : q' ≫ a' = q' ≫ b' := by ext; exact hq
    let r := (equalizer.lift q' h).left
    have hr : r ≫ j = q := congrArg (fun h => h.left) (equalizer.lift_ι q' h)
    exact ⟨r, hr, fun r' hr' => (cancel_mono j).mp (hr'.trans hr.symm)⟩

/-- Composition of marking-preserving comparisons retains the original maps. -/
lemma marked_comp {B T : Scheme.{u}} (G : Family B) (F : Family T)
    (M : FullLevel E 4) (N : FullLevel G 4) (L : FullLevel F 4)
    (b : B ⟶ S) (f : G.curve ⟶ E.curve) (q : T ⟶ B) (h : F.curve ⟶ G.curve)
    (hf : MarkedCartesian E G M N b f) (hh : MarkedCartesian G F N L q h) :
    MarkedCartesian E F M L (q ≫ b) (h ≫ f) := by
  have hc := cartesian_comp E G F b f ⟨hf.1, hf.2.1, hf.2.2.1⟩ q h
    ⟨hh.1, hh.2.1, hh.2.2.1⟩
  refine ⟨hc.1, hc.2.1, hc.2.2, ?_, ?_⟩
  · rw [← Category.assoc, hh.2.2.2.1, Category.assoc, hf.2.2.2.1, Category.assoc]
  · rw [← Category.assoc, hh.2.2.2.2, Category.assoc, hf.2.2.2.2, Category.assoc]

/-- Once the two exact equations define a subobject, full-cover representation
restricts to representation of the prescribed markings on every test scheme. -/
lemma represents_subcover (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (D C : Cover E) (hD : Represents E D)
    (j : C.space ⟶ D.space) (h : C.family.curve ⟶ D.family.curve)
    [Mono j] (hc : CoverMap E C D j h)
    (w : Γ(D.space, ⊤)) (hw : MillerPhase D.family D.marking w)
    (hself : Matches E P z C.family C.marking C.projection C.comparison)
    (hlift : ∀ (T : Scheme.{u}) (q : T ⟶ D.space),
      q ≫ evenPoint D.family D.marking ≫ D.comparison =
        (q ≫ D.projection) ≫ P.point.val →
      q.appTop w = (q ≫ D.projection).appTop z →
      ∃ r : T ⟶ C.space, r ≫ j = q) : RepresentsEven E P z C := by
  refine ⟨hself, ?_⟩
  intro T F N b f hF hm
  obtain ⟨q, ⟨g, hg, hgf⟩, huniq⟩ := hD T F N b f hF
  have heq := (matches_iff E k σ P z D w hw F N b f q.val g q.property hg hgf).mp hm
  obtain ⟨r, hr⟩ := hlift T q.val (by simpa only [q.property] using heq.1)
    (by simpa only [q.property] using heq.2)
  have hrb : r ≫ C.projection = b := by
    rw [← hc.1, ← Category.assoc, hr, q.property]
  have hx : N.x.val ≫ f = r ≫ C.marking.x.val ≫ C.comparison := by
    rw [← hgf, ← Category.assoc, hg.2.2.2.1, Category.assoc,
      ← hc.2.2, ← Category.assoc C.marking.x.val, hc.2.1.2.2.2.1,
      Category.assoc, ← Category.assoc r j, hr]
  have hy : N.y.val ≫ f = r ≫ C.marking.y.val ≫ C.comparison := by
    rw [← hgf, ← Category.assoc, hg.2.2.2.2, Category.assoc,
      ← hc.2.2, ← Category.assoc C.marking.y.val, hc.2.1.2.2.2.2,
      Category.assoc, ← Category.assoc r j, hr]
  obtain ⟨gC, hgC, hgCf⟩ := marked_factor E k σ C.family F
    C.projection C.comparison C.cartesian b f hF r hrb C.marking N hx hy
  refine ⟨⟨r, hrb⟩, ⟨gC, hgC, hgCf⟩, ?_⟩
  rintro r' ⟨g', hg', hgf'⟩
  have hr'b : (r'.val ≫ j) ≫ D.projection = b := by
    rw [Category.assoc, hc.1, r'.property]
  have hr'D : (⟨r'.val ≫ j, hr'b⟩ : {q : T ⟶ D.space // q ≫ D.projection = b}) = q := by
    apply huniq
    refine ⟨g' ≫ h, ?_, ?_⟩
    · exact marked_comp D.family C.family F D.marking C.marking N j h r'.val g' hc.2.1 hg'
    · rw [Category.assoc, hc.2.2, hgf']
  apply Subtype.ext
  apply (cancel_mono j).mp
  exact (congrArg Subtype.val hr'D).trans hr.symm

lemma two_unit (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (σ : X ⟶ Base k) :
    IsUnit (2 : Γ(X, ⊤)) := by
  let ι : k →+* Γ(X, ⊤) := σ.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have h : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map ι

/-- Over an affine base, equality of prime-to-characteristic torsion sections
is a clopen scheme condition. The proof uses the actual multiplication kernel. -/
lemma affine_torsion_equality (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (.of R)) (G : GoodReductionJacobian.RelativeGroupLaw R f)
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
      (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f]
    (n : ℕ) (hn : IsUnit (n : R)) (x y : SchemeHomOver (𝟙 (Spec (.of R))) f)
    (hx : G.nsmul (𝟙 _) n x = G.one (𝟙 _))
    (hy : G.nsmul (𝟙 _) n y = G.one (𝟙 _)) :
    ∃ U : (Spec (.of R)).Opens, IsClopen (U : Set (Spec (.of R))) ∧
      ∀ {T : Scheme.{u}} (q : T ⟶ Spec (.of R)),
        Set.range q ⊆ (U : Set (Spec (.of R))) ↔ q ≫ x.val = q ≫ y.val := by
  let m := G.schemeNsmul n
  let z := (G.one (𝟙 (Spec (.of R)))).val
  let p := pullback.snd m z
  let i := pullback.fst m z
  have hz : z ≫ f = 𝟙 _ := (G.one (𝟙 _)).property
  letI : Etale m := SchemeFourCoverGeometry.etale_nsmul_relative G hc n hn
  letI : Etale p := MorphismProperty.pullback_snd _ _ (inferInstance : Etale m)
  letI : IsClosedImmersion z := by
    haveI : IsClosedImmersion (z ≫ f) := by rw [hz]; infer_instance
    exact IsClosedImmersion.of_comp z f
  letI : IsClosedImmersion i := MorphismProperty.pullback_fst _ _
    (inferInstance : IsClosedImmersion z)
  have hip : i ≫ f = p := by
    calc
      i ≫ f = i ≫ m ≫ f := by rw [G.schemeNsmul_over]
      _ = p ≫ z ≫ f := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [hz, Category.comp_id]
  letI : IsSeparated p := hip ▸ (inferInstance : IsSeparated (i ≫ f))
  have hmul (a : SchemeHomOver (𝟙 (Spec (.of R))) f)
      (ha : G.nsmul (𝟙 _) n a = G.one (𝟙 _)) : a.val ≫ m = z := by
    have H := congrArg Subtype.val (G.nsmul_natural f (𝟙 _) a.val a.property n
      (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := f)))
    have hid : GoodReductionJacobian.schemeHomOverComp a.val a.property
        (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := f)) = a := by
      apply Subtype.ext; exact Category.comp_id _
    rw [hid, ha] at H
    exact H
  let sx : Spec (.of R) ⟶ pullback m z := pullback.lift x.val (𝟙 _) (by simpa using hmul x hx)
  let sy : Spec (.of R) ⟶ pullback m z := pullback.lift y.val (𝟙 _) (by simpa using hmul y hy)
  have hsx : sx ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  have hsy : sy ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  have H := isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated p sx sy hsx hsy
  refine ⟨_, H.1, ?_⟩
  intro T q
  rw [H.2 q]
  constructor
  · intro h
    have hh := congrArg (fun a => a ≫ i) h
    simpa only [Category.assoc, sx, sy, i, pullback.lift_fst] using hh
  · intro h
    apply pullback.hom_ext
    · simpa only [Category.assoc, sx, sy, pullback.lift_fst] using h
    · simp only [Category.assoc, sx, sy, pullback.lift_snd]

/-- The prescribed P3 attached to a full marking is actual two-torsion. -/
lemma evenPoint_two_torsion (M : FullLevel E 4) :
    multiple E (𝟙 S) 2
      (E.law.mul (𝟙 S) (multiple E (𝟙 S) 2 M.x) (multiple E (𝟙 S) 2 M.y)) =
      E.law.one (𝟙 S) := by
  letI := SchemeFourMarkingActionR0215.pointGroup E (𝟙 S)
  have hx : M.x^4 = 1 :=
    (SchemeFourMarkingActionR0215.multiple_pow E (𝟙 S) 4 M.x).symm.trans M.killed_x
  have hy : M.y^4 = 1 :=
    (SchemeFourMarkingActionR0215.multiple_pow E (𝟙 S) 4 M.y).symm.trans M.killed_y
  simp only [SchemeFourMarkingActionR0215.multiple_pow]
  change (M.x^2 * M.y^2)^2 = 1
  rw [mul_pow, ← pow_mul, ← pow_mul]
  exact (congrArg₂ (· * ·) hx hy).trans (one_mul _)

/-- Repackage the same operations over an affine base; no group law is chosen. -/
def affineFamilyLaw (R : Type u) [CommRing R] (F : Family (Spec (.of R))) :
    GoodReductionJacobian.RelativeGroupLaw R F.p where
  mul := F.law.mul
  one := F.law.one
  inv := F.law.inv
  mul_assoc := F.law.mul_assoc
  one_mul := F.law.one_mul
  mul_one := F.law.mul_one
  inv_mul_cancel := F.law.inv_mul_cancel
  mul_natural := F.law.mul_natural

lemma affineFamilyLaw_nsmul (R : Type u) [CommRing R] (F : Family (Spec (.of R)))
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (n : ℕ) (x : SchemeHomOver t F.p) :
    (affineFamilyLaw R F).nsmul t n x = multiple F t n x := by
  induction n with
  | zero => rfl
  | succ n ih => change F.law.mul t ((affineFamilyLaw R F).nsmul t n x) x = _; rw [ih]; rfl

lemma affine_family_two_torsion_equality (R : Type u) [CommRing R]
    (F : Family (Spec (.of R))) (h2 : IsUnit (2 : R))
    (x y : SchemeHomOver (𝟙 (Spec (.of R))) F.p)
    (hx : multiple F (𝟙 _) 2 x = F.law.one (𝟙 _))
    (hy : multiple F (𝟙 _) 2 y = F.law.one (𝟙 _)) :
    ∃ U : (Spec (.of R)).Opens, IsClopen (U : Set (Spec (.of R))) ∧
      ∀ {T : Scheme.{u}} (q : T ⟶ Spec (.of R)),
        Set.range q ⊆ (U : Set (Spec (.of R))) ↔ q ≫ x.val = q ≫ y.val := by
  letI := F.proper
  letI := F.dimension
  exact affine_torsion_equality R F.p (affineFamilyLaw R F) F.law.mul_comm 2 h2 x y
    ((affineFamilyLaw_nsmul R F (𝟙 _) 2 x).trans hx)
    ((affineFamilyLaw_nsmul R F (𝟙 _) 2 y).trans hy)

/-- Lift an actual section through a Cartesian family comparison. -/
def pullSection {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)
    (x : SchemeHomOver (𝟙 S) E.p) : SchemeHomOver (𝟙 B) F.p :=
  liftPoint E F b f hc (GoodReductionJacobian.schemeHomOverComp b (Category.comp_id b) x)

lemma pullSection_comp {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)
    (x : SchemeHomOver (𝟙 S) E.p) : (pullSection E F b f hc x).val ≫ f = b ≫ x.val :=
  liftPoint_comp E F b f hc _

lemma pullSection_killed {B : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)
    (x : SchemeHomOver (𝟙 S) E.p) (n : ℕ) (hx : multiple E (𝟙 S) n x = E.law.one (𝟙 S)) :
    multiple F (𝟙 B) n (pullSection E F b f hc x) = F.law.one (𝟙 B) := by
  let xb := GoodReductionJacobian.schemeHomOverComp b (Category.comp_id b) x
  have hxb : multiple E b n xb = E.law.one b := by
    dsimp only [xb]
    rw [← multiple_natural E (𝟙 S) b b (Category.comp_id b), hx]
    exact SchemeLocal.one_natural E.law (𝟙 S) b b (Category.comp_id b)
  apply CartesianFullMarking.section_ext E F b f hc.1
  rw [multiple_comp E F b f hc _ xb (pullSection_comp E F b f hc x), hxb, one_val]
  exact hc.2.1.symm

lemma pullSection_equal_iff {B T : Scheme.{u}} (F : Family B) (b : B ⟶ S)
    (f : F.curve ⟶ E.curve) (hc : Cartesian E F b f)
    (x y : SchemeHomOver (𝟙 S) E.p) (q : T ⟶ B) :
    q ≫ (pullSection E F b f hc x).val = q ≫ (pullSection E F b f hc y).val ↔
      (q ≫ b) ≫ x.val = (q ≫ b) ≫ y.val := by
  constructor
  · intro h
    have hh := congrArg (fun g => g ≫ f) h
    simpa only [Category.assoc, pullSection_comp] using hh
  · intro h
    apply hc.1.hom_ext
    · simpa only [Category.assoc, pullSection_comp] using h
    · simp only [Category.assoc, (pullSection E F b f hc x).property,
        (pullSection E F b f hc y).property]

/-- A monomorphism with exactly the test maps landing in an open is that open immersion. -/
lemma openImmersion_of_open_locus {X Z : Scheme.{u}} (j : Z ⟶ X) [Mono j]
    (U : X.Opens) (hj : Set.range j ⊆ (U : Set X))
    (hlift : ∀ (T : Scheme.{u}) (q : T ⟶ X), Set.range q ⊆ (U : Set X) →
      ∃ r : T ⟶ Z, r ≫ j = q) : IsOpenImmersion j := by
  let a := IsOpenImmersion.lift U.ι j (by simpa only [Scheme.Opens.range_ι] using hj)
  have ha : a ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨b, hb⟩ := hlift U U.ι (by rw [Scheme.Opens.range_ι])
  let e : Z ≅ U :=
    { hom := a, inv := b
      hom_inv_id := by apply (cancel_mono j).mp; rw [Category.assoc, hb, ha, Category.id_comp]
      inv_hom_id := by apply (cancel_mono U.ι).mp; rw [Category.assoc, ha, hb, Category.id_comp] }
  letI : IsIso a := e.isIso_hom
  rw [← ha]
  infer_instance

/-- Equality of two-torsion sections is an open condition on an arbitrary
characteristic-zero scheme; the equalizer is tested on all schemes. -/
lemma two_torsion_equalizer_open (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (x y : SchemeHomOver (𝟙 S) E.p)
    (hx : multiple E (𝟙 S) 2 x = E.law.one (𝟙 S))
    (hy : multiple E (𝟙 S) 2 y = E.law.one (𝟙 S))
    {Z : Scheme.{u}} (j : Z ⟶ S) [Mono j] (hj : j ≫ x.val = j ≫ y.val)
    (hlift : ∀ (T : Scheme.{u}) (q : T ⟶ S), q ≫ x.val = q ≫ y.val →
      ∃ r : T ⟶ Z, r ≫ j = q) : IsOpenImmersion j := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsOpenImmersion) S.affineOpenCover.openCover
  intro v
  let R := S.affineOpenCover.X v
  let a : Spec (.of R) ⟶ S := S.affineOpenCover.f v
  let F := SchemeFamilyBaseChange.baseChangeFamily E a
  let f := pullback.fst E.p a
  have hc : Cartesian E F a f :=
    ⟨IsPullback.of_hasPullback E.p a, SchemeFamilyBaseChange.baseChangeLaw_zero E a,
      SchemeFamilyBaseChange.baseChangeFamily_multiplicative E a⟩
  let xa := pullSection E F a f hc x
  let ya := pullSection E F a f hc y
  have h2 : IsUnit (2 : R) := by
    have H := (two_unit k (a ≫ σ)).map (Scheme.ΓSpecIso (.of R)).hom.hom
    simpa only [map_ofNat] using H
  obtain ⟨U, _, hU⟩ := affine_family_two_torsion_equality R F h2 xa ya
    (pullSection_killed E F a f hc x 2 hx) (pullSection_killed E F a f hc y 2 hy)
  let p := pullback.snd j a
  let i := pullback.fst j a
  change IsOpenImmersion p
  apply openImmersion_of_open_locus p U
  · apply (hU p).mpr
    apply (pullSection_equal_iff E F a f hc x y p).mpr
    rw [← pullback.condition, Category.assoc, Category.assoc, hj]
  · intro T q hq
    have hxy := (pullSection_equal_iff E F a f hc x y q).mp ((hU q).mp hq)
    obtain ⟨r, hr⟩ := hlift T (q ≫ a) hxy
    exact ⟨pullback.lift r q hr, pullback.lift_snd _ _ _⟩

/-- The fixed P3 equalizer is open for the original arbitrary-base family. -/
lemma characteristic_equalizer_open (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (D : Cover E) {Z : Scheme.{u}} (j : Z ⟶ D.space) [Mono j]
    (hj : j ≫ evenPoint D.family D.marking ≫ D.comparison =
      (j ≫ D.projection) ≫ P.point.val)
    (hlift : ∀ (T : Scheme.{u}) (q : T ⟶ D.space),
      q ≫ evenPoint D.family D.marking ≫ D.comparison = (q ≫ D.projection) ≫ P.point.val →
      ∃ r : T ⟶ Z, r ≫ j = q) : IsOpenImmersion j := by
  let x := D.family.law.mul (𝟙 D.space) (multiple D.family (𝟙 D.space) 2 D.marking.x)
    (multiple D.family (𝟙 D.space) 2 D.marking.y)
  let y := pullSection E D.family D.projection D.comparison D.cartesian P.point
  have hiff {T : Scheme.{u}} (q : T ⟶ D.space) : q ≫ x.val = q ≫ y.val ↔
      q ≫ evenPoint D.family D.marking ≫ D.comparison = (q ≫ D.projection) ≫ P.point.val := by
    constructor
    · intro h
      have hh := congrArg (fun g => g ≫ D.comparison) h
      simpa only [Category.assoc, x, evenPoint, y, pullSection_comp] using hh
    · intro h
      apply D.cartesian.1.hom_ext
      · simpa only [Category.assoc, x, evenPoint, y, pullSection_comp] using h
      · simp only [Category.assoc, x.property, y.property]
  exact two_torsion_equalizer_open D.family k (D.projection ≫ σ) x y
    (evenPoint_two_torsion D.family D.marking)
    (pullSection_killed E D.family D.projection D.comparison D.cartesian P.point 2 P.killed)
    j ((hiff j).mpr hj) (fun T q hq => hlift T q ((hiff q).mp hq))

/-- The simultaneous characteristic and phase equations have an actual clopen
representing locus. The phase equation is imposed by a clopen restriction. -/
lemma exists_equation_locus (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1) (D : Cover E)
    (w : Γ(D.space, ⊤)) (hw : MillerPhase D.family D.marking w) :
    ∃ (X : Scheme.{u}) (j : X ⟶ D.space), IsOpenImmersion j ∧ IsClosedImmersion j ∧
      (j ≫ evenPoint D.family D.marking ≫ D.comparison = (j ≫ D.projection) ≫ P.point.val) ∧
      (j.appTop w = (j ≫ D.projection).appTop z) ∧
      ∀ (T : Scheme.{u}) (q : T ⟶ D.space),
        q ≫ evenPoint D.family D.marking ≫ D.comparison = (q ≫ D.projection) ≫ P.point.val →
        q.appTop w = (q ≫ D.projection).appTop z → ∃ r : T ⟶ X, r ≫ j = q := by
  letI := E.proper
  let a := evenPoint D.family D.marking ≫ D.comparison
  let b := D.projection ≫ P.point.val
  have ha : a ≫ E.p = D.projection := by
    dsimp only [a]
    rw [Category.assoc, D.cartesian.1.w, ← Category.assoc,
      SchemeThetaEvaluation.evenPoint_over, Category.id_comp]
  have hb : b ≫ E.p = D.projection := by
    dsimp only [b]
    rw [Category.assoc, P.point.property, Category.comp_id]
  obtain ⟨Y, i, hi, hei, hYi⟩ := closed_equalizer D.projection E.p a b ha hb
  letI := hi
  letI : IsOpenImmersion i := characteristic_equalizer_open E k σ P D i
    (by simpa only [a, b, Category.assoc] using hei)
    (fun T q hq => by
      obtain ⟨r, hr, _⟩ := hYi T q (by simpa only [a, b, Category.assoc] using hq)
      exact ⟨r, hr⟩)
  let wa := i.appTop w
  let zb := (i ≫ D.projection).appTop z
  have hwa : wa^2 = -1 := by
    change (i.appTop w)^2 = -1
    rw [← map_pow, (scheme_miller_phase k D.space (D.projection ≫ σ)
      D.family D.marking).2 w hw |>.2.1, map_neg, map_one]
  have hzb : zb^2 = -1 := by
    change ((i ≫ D.projection).appTop z)^2 = -1
    rw [← map_pow, hz, map_neg, map_one]
  have htwo := two_unit k ((i ≫ D.projection) ≫ σ)
  let U := phaseOpen Y wa zb
  have hU := phaseOpen_clopen Y wa zb hwa hzb htwo
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hU.1)
  have heU : U.ι.appTop wa = U.ι.appTop zb :=
    (phaseOpen_universal Y wa zb hwa hzb htwo U.ι).mp
      (by rw [Scheme.Opens.range_ι])
  refine ⟨U, U.ι ≫ i, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · change (U.ι ≫ i) ≫ a = (U.ι ≫ i) ≫ b
    rw [Category.assoc, Category.assoc, hei]
  · simpa only [wa, zb, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using heU
  · intro T q hchar hphase
    obtain ⟨r, hr, _⟩ := hYi T q (by simpa only [a, b, Category.assoc] using hchar)
    have he : r.appTop wa = r.appTop zb := by
      change r.appTop (i.appTop w) = r.appTop ((i ≫ D.projection).appTop z)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hr,
        ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hr]
      exact hphase
    have hmem : Set.range r ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact (phaseOpen_universal Y wa zb hwa hzb htwo r).mpr he
    refine ⟨IsOpenImmersion.lift U.ι r hmem, ?_⟩
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hr]

/-- The actual clopen representing subcover is finite étale. The degree and
surjectivity still have to be established to obtain the frozen target. -/
lemma exists_finite_etale_representing_subcover (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ Base k) (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1)
    (D : Cover E) (hD : Represents E D) :
    ∃ (C : Cover E) (j : C.space ⟶ D.space) (h : C.family.curve ⟶ D.family.curve),
      CoverMap E C D j h ∧ IsOpenImmersion j ∧ IsClosedImmersion j ∧
      RepresentsEven E P z C ∧ IsFinite C.projection ∧ Etale C.projection := by
  obtain ⟨w, hw, _⟩ := (scheme_miller_phase k D.space (D.projection ≫ σ)
    D.family D.marking).1
  obtain ⟨X, j, hjo, hj, hchar, hphase, hlift⟩ := exists_equation_locus E k σ P z hz D w hw
  letI := hj
  letI := hjo
  let C := restrictCover E D j
  let h := pullback.fst D.family.p j
  have hc : CoverMap E C D j h := restrictCover_map E D j
  have hm : Matches E P z C.family C.marking C.projection C.comparison :=
    (matches_iff E k σ P z D w hw C.family C.marking C.projection C.comparison j h
      hc.1 hc.2.1 hc.2.2).mpr ⟨hchar, hphase⟩
  have hrep : RepresentsEven E P z C :=
    represents_subcover E k σ P z D C hD j h hc w hw hm hlift
  have hgeom := scheme_four_cover_geometry k S σ E D hD
  letI : IsFinite D.projection := hgeom.1
  have hfin : IsFinite C.projection := by
    change IsFinite (j ≫ D.projection)
    infer_instance
  letI : Etale D.projection := hgeom.2.1
  have het : Etale C.projection := by
    change Etale (j ≫ D.projection)
    infer_instance
  exact ⟨C, j, h, hc, hjo, hj, hrep, hfin, het⟩

/-- Coordinates of P3 after changing a basis by the columns of A. -/
abbrev doubleColumnSum (A : ArithmeticThetaFourTorsion.Mat4) : Fin 2 → ZMod 4 :=
  fun i => 2 * (A i 0 + A i 1)

lemma unit_four_iff (d : ZMod 4) : IsUnit d ↔ d = 1 ∨ d = 3 := by
  revert d
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Each nonzero two-torsion characteristic and each invertible determinant
select exactly sixteen change matrices. This is a kernel-checked finite count. -/
lemma matrix_fiber_count : ∀ (p : Fin 2 → ZMod 4), 2 • p = 0 → p ≠ 0 →
    ∀ d : ZMod 4, IsUnit d →
      Fintype.card {A : ArithmeticThetaFourTorsion.Mat4 // A.det = d ∧ doubleColumnSum A = p} = 16 := by
  intro p hp hp0 d hd
  rcases (unit_four_iff d).mp hd with rfl | rfl <;>
    revert hp hp0 <;> revert p <;> decide

lemma roots_minus_one_eq_or_neg {K : Type*} [Field K] (a b : K)
    (ha : a^2 = -1) (hb : b^2 = -1) : b = a ∨ b = -a := by
  have h : (b-a)*(b+a) = 0 := by
    calc
      (b-a)*(b+a) = b^2-a^2 := by ring
      _ = 0 := by rw [ha, hb, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_iff_add_eq_zero.mpr h)

/-- The determinant exponent distinguishes the two possible Miller phases. -/
lemma phase_exponent_iff {K : Type*} [Field K] [CharZero K] (a : K) (ha : a^2 = -1)
    (d e : ZMod 4) (hd : IsUnit d) (he : IsUnit e) :
    a ^ d.val = a ^ e.val ↔ d = e := by
  have hne : a ≠ -a := by
    have hu : a ≠ 0 := (unit_of_square a ha).ne_zero
    intro h
    apply hu
    have htwo : (2 : K) * a = 0 := by linear_combination h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hcube : a^3 = -a := by calc
    a^3 = a^2*a := by ring
    _ = -a := by rw [ha]; ring
  rcases (unit_four_iff d).mp hd with rfl | rfl <;>
    rcases (unit_four_iff e).mp he with rfl | rfl <;>
    norm_num [show (1 : ZMod 4).val = 1 from rfl,
      show (3 : ZMod 4).val = 3 from rfl, hcube, hne, hne.symm] <;> decide

/-- The numerical fiber of a prescribed primitive phase and characteristic. -/
lemma matrix_phase_fiber_count {K : Type*} [Field K] [CharZero K]
    (a z : K) (ha : a^2 = -1) (hz : z^2 = -1)
    (p : Fin 2 → ZMod 4) (hp : 2 • p = 0) (hp0 : p ≠ 0) :
    Nat.card {A : ArithmeticThetaFourTorsion.Mat4 //
      IsUnit A.det ∧ doubleColumnSum A = p ∧ a ^ A.det.val = z} = 16 := by
  classical
  obtain ⟨d, hd, hdz⟩ : ∃ d : ZMod 4, IsUnit d ∧ a ^ d.val = z := by
    rcases roots_minus_one_eq_or_neg a z ha hz with h | h
    · exact ⟨1, isUnit_one, by simpa only [show (1 : ZMod 4).val = 1 from rfl, pow_one] using h.symm⟩
    · refine ⟨3, (unit_four_iff 3).mpr (Or.inr rfl), ?_⟩
      change a^3 = z
      calc
        a^3 = a^2*a := by ring
        _ = -a := by rw [ha]; ring
        _ = z := h.symm
  have hpred (A : ArithmeticThetaFourTorsion.Mat4) :
      (IsUnit A.det ∧ doubleColumnSum A = p ∧ a ^ A.det.val = z) ↔
        (A.det = d ∧ doubleColumnSum A = p) := by
    constructor
    · rintro ⟨hA, hpA, hzA⟩
      exact ⟨(phase_exponent_iff a ha A.det d hA hd).mp (hzA.trans hdz.symm), hpA⟩
    · rintro ⟨hA, hpA⟩
      exact ⟨hA ▸ hd, hpA, hA ▸ hdz⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hpred), Nat.card_eq_fintype_card]
  exact matrix_fiber_count p hp hp0 d hd

/-- A parameter point induces the actual marking on any chosen Cartesian test family. -/
lemma marking_over_parameter (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (C : Cover E) {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hF : Cartesian E F b f)
    (q : T ⟶ C.space) (hq : q ≫ C.projection = b) :
    ∃ (N : FullLevel F 4) (h : F.curve ⟶ C.family.curve),
      MarkedCartesian C.family F C.marking N q h ∧ h ≫ C.comparison = f := by
  let M := (pushMarking E C.family C.projection C.comparison C.cartesian C.marking).pull E q
    |>.cast E hq
  let N := liftMarking E F b f hF M
  have hx : N.x.val ≫ f = q ≫ C.marking.x.val ≫ C.comparison := by
    rw [show N.x.val ≫ f = M.x.val from liftPoint_comp E F b f hF M.x]
    simp only [M, Marking.cast_x, Marking.pull_x, pushMarking, pushPoint]
  have hy : N.y.val ≫ f = q ≫ C.marking.y.val ≫ C.comparison := by
    rw [show N.y.val ≫ f = M.y.val from liftPoint_comp E F b f hF M.y]
    simp only [M, Marking.cast_y, Marking.pull_y, pushMarking, pushPoint]
  obtain ⟨h, hh, hf⟩ := marked_factor E k σ C.family F C.projection C.comparison C.cartesian
    b f hF q hq C.marking N hx hy
  exact ⟨N, h, hh, hf⟩

/-- Representation identifies actual parameter points with compatible markings
on any fixed Cartesian test family, without quotienting markings by isomorphisms. -/
def compatibleMarkingEquiv (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (C : Cover E) (hC : RepresentsEven E P z C)
    {T : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hF : Cartesian E F b f) :
    {N : FullLevel F 4 // Matches E P z F N b f} ≃
      {q : T ⟶ C.space // q ≫ C.projection = b} := by
  classical
  let classify := fun N : {N : FullLevel F 4 // Matches E P z F N b f} =>
    (hC.2 T F N.val b f hF N.property).choose
  have hclass (N : {N : FullLevel F 4 // Matches E P z F N b f}) :
      ∃ h : F.curve ⟶ C.family.curve,
        MarkedCartesian C.family F C.marking N.val (classify N).val h ∧ h ≫ C.comparison = f :=
    (hC.2 T F N.val b f hF N.property).choose_spec.1
  apply Equiv.ofBijective classify
  constructor
  · intro N M hNM
    obtain ⟨h, hh, hf⟩ := hclass N
    obtain ⟨g, hg, gf⟩ := hclass M
    apply Subtype.ext
    apply SchemeFourMarkingActionR0215.fullLevel_ext F
    · apply CartesianFullMarking.section_ext E F b f hF.1
      have hn := congrArg (fun a => a ≫ C.comparison) hh.2.2.2.1
      have hm := congrArg (fun a => a ≫ C.comparison) hg.2.2.2.1
      simp only [Category.assoc, hf] at hn
      simp only [Category.assoc, gf] at hm
      exact hn.trans ((congrArg (fun q : {q : T ⟶ C.space // q ≫ C.projection = b} =>
        q.val ≫ C.marking.x.val ≫ C.comparison) hNM).trans hm.symm)
    · apply CartesianFullMarking.section_ext E F b f hF.1
      have hn := congrArg (fun a => a ≫ C.comparison) hh.2.2.2.2
      have hm := congrArg (fun a => a ≫ C.comparison) hg.2.2.2.2
      simp only [Category.assoc, hf] at hn
      simp only [Category.assoc, gf] at hm
      exact hn.trans ((congrArg (fun q : {q : T ⟶ C.space // q ≫ C.projection = b} =>
        q.val ≫ C.marking.y.val ≫ C.comparison) hNM).trans hm.symm)
  · intro q
    obtain ⟨N, h, hh, hf⟩ := marking_over_parameter E k σ C F b f hF q.val q.property
    have hm : Matches E P z F N b f := by
      have H := matches_pullback E P z C.family F C.marking N C.projection C.comparison
        q.val h hh hC.1
      simpa only [q.property, hf] using H
    refine ⟨⟨N, hm⟩, ?_⟩
    exact ((hC.2 T F N b f hF hm).choose_spec.2 q ⟨h, hh, hf⟩).symm

/-- Sections of a Cartesian pullback over the identity are the original
parameter points over the specified base map. -/
def pullbackSectionEquiv {X B T : Scheme.{u}} (p : X ⟶ B) (b : T ⟶ B) :
    {q : T ⟶ pullback p b // q ≫ pullback.snd p b = 𝟙 T} ≃
      {q : T ⟶ X // q ≫ p = b} where
  toFun q := ⟨q.val ≫ pullback.fst p b, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, q.property, Category.id_comp]⟩
  invFun q := ⟨pullback.lift q.val (𝟙 T) (by simpa using q.property), pullback.lift_snd _ _ _⟩
  left_inv q := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans q.property.symm
  right_inv q := Subtype.ext (pullback.lift_fst _ _ _)

/-- Actual geometric rank equals the number of matching markings on any
chosen Cartesian model of the geometric fiber. -/
lemma finrank_eq_compatible_markings (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (C : Cover E) (hC : RepresentsEven E P z C)
    [IsFinite C.projection] [Etale C.projection]
    (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
    (F : Family (Spec (.of K))) (f : F.curve ⟶ E.curve) (hF : Cartesian E F b f) :
    C.projection.finrank (b (IsLocalRing.closedPoint K)) =
      Nat.card {N : FullLevel F 4 // Matches E P z F N b f} := by
  let q := pullback.snd C.projection b
  have hq : IsFinite q := MorphismProperty.pullback_snd _ _ inferInstance
  have heq : Etale q := MorphismProperty.pullback_snd _ _ inferInstance
  letI := hq
  letI := heq
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id K)) = 𝟙 (Spec (.of K)) := by simp
  have hr := finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed q K (RingHom.id K)
  rw [hid] at hr
  have hidpt : (𝟙 (Spec (.of K))) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint K := rfl
  rw [hidpt] at hr
  rw [← Scheme.Hom.finrank_of_isPullback (pullback.fst C.projection b) q C.projection b
    (IsPullback.of_hasPullback C.projection b), hr]
  exact (Nat.card_congr (pullbackSectionEquiv C.projection b)).trans
    (Nat.card_congr (compatibleMarkingEquiv E k σ P z C hC F b f hF).symm)

#print axioms finrank_eq_compatible_markings
#print axioms compatibleMarkingEquiv

namespace SplitCounting
open ArithmeticThetaMarkingR0115 ArithmeticThetaFourTorsion
open ArithmeticThetaGeometricPairingR0118
variable {K : Type u} [Field K] [DecidableEq K] {e : Fin 3 → K}

lemma act_injective (b : Marking K e) (hb : IsBasis K e b) : Function.Injective (act K e b) := by
  intro A B h
  ext i j
  have hh : coordinates K e b (fun i => A i j) =
      coordinates K e b (fun i => B i j) := congrFun h j
  exact congrFun (hb.2.1 hh) i

lemma basis_act_unit (b : Marking K e) (hb : IsBasis K e b)
    (A : Mat4) (hA : IsUnit A.det) : IsBasis K e (act K e b A) := by
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  let B : Mat4 := ↑U⁻¹
  have hl : B * A = 1 := by rw [← hU]; exact U.inv_val
  have hr : A * B = 1 := by rw [← hU]; exact U.val_inv
  refine ⟨act_four_torsion b hb.1 A, ?_, ?_⟩
  · intro z w hzw
    rw [coordinates_act b hb.1, coordinates_act b hb.1] at hzw
    have h := congrArg (fun v => B.mulVec v) (hb.2.1 hzw)
    simpa only [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec] using h
  · intro P hP
    obtain ⟨z, hz⟩ := hb.2.2 P hP
    refine ⟨B.mulVec z, ?_⟩
    rw [coordinates_act b hb.1, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec, hz]

lemma exists_change (b c : Marking K e) (hb : IsBasis K e b) (hc : IsBasis K e c) :
    ∃ A : Mat4, IsUnit A.det ∧ act K e b A = c := by
  choose v hv using fun j => hb.2.2 (c j) (hc.1 j)
  choose w hw using fun j => hc.2.2 (b j) (hb.1 j)
  let A : Mat4 := fun i j => v j i
  let B : Mat4 := fun i j => w j i
  have hA : act K e b A = c := funext hv
  have hB : act K e c B = b := funext hw
  have hAB : A*B = 1 := by
    apply act_injective b hb
    rw [← act_mul b hb.1, hA, hB, act_one]
  refine ⟨A, isUnit_iff_exists_inv.mpr ⟨B.det, ?_⟩, hA⟩
  rw [← Matrix.det_mul, hAB, Matrix.det_one]

/-- Every actual basis is a unique invertible column change of a chosen basis. -/
def basisEquiv (b : Marking K e) (hb : IsBasis K e b) :
    {A : Mat4 // IsUnit A.det} ≃ {c : Marking K e // IsBasis K e c} :=
  Equiv.ofBijective (fun A => ⟨act K e b A.val, basis_act_unit b hb A.val A.property⟩)
    ⟨fun A B h => Subtype.ext (act_injective b hb (congrArg Subtype.val h)), by
      rintro ⟨c, hc⟩
      obtain ⟨A, hA, hac⟩ := exists_change b c hb hc
      exact ⟨⟨A, hA⟩, Subtype.ext hac⟩⟩

lemma phase_act_unit [CharZero K] (he : Function.Injective e)
    (b : Marking K e) (hb : IsBasis K e b) (A : Mat4) (hA : IsUnit A.det) :
    phase K e (act K e b A) = phase K e b ^ A.det.val := by
  obtain ⟨D, _⟩ := geometric_four_character K e he
  have h := pairing_coordinates K e he D b hb (fun i => A i 0) (fun i => A i 1)
  change pairing K e D (act K e b A 0) (act K e b A 1) =
    pairing K e D (b 0) (b 1) ^ (A 0 0*A 1 1-A 1 0*A 0 1).val at h
  simpa only [marking_pairing_identification K e he D b hb,
    marking_pairing_identification K e he D (act K e b A) (basis_act_unit b hb A hA),
    Matrix.det_fin_two, mul_comm] using h

lemma phase_square [CharZero K] (he : Function.Injective e)
    (b : Marking K e) (hb : IsBasis K e b) : phase K e b ^ 2 = -1 := by
  have h := (generator_s_miller_phase K e he b hb).2.1
  have hh : (phase K e b ^ 2)^2 = 1 := by rw [← pow_mul]; exact h.pow_eq_one
  exact (sq_eq_one_iff.mp hh).resolve_left (h.pow_ne_one_of_pos_of_lt (by decide) (by decide))

lemma characteristic_act (b : Marking K e) (hb : IsBasis K e b) (A : Mat4) :
    2 • act K e b A 0 + 2 • act K e b A 1 = coordinates K e b (doubleColumnSum A) := by
  have h := coordinates_act b hb.1 A (fun _ => 2)
  have hv : (2 : ZMod 4).val = 2 := rfl
  have hm : A.mulVec (fun _ => 2) = doubleColumnSum A := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, doubleColumnSum]
    ring
  simpa only [coordinates, hv, hm] using h

lemma coordinates_double (b : Marking K e) (hb : IsBasis K e b) (p : Fin 2 → ZMod 4) :
    coordinates K e b (2 • p) = 2 • coordinates K e b p := by
  have hterm (i : Fin 2) : ((2 : ZMod 4)*p i).val • b i = 2 • ((p i).val • b i) := by
    rw [ZMod.val_mul, show (2 : ZMod 4).val = 2 from rfl,
      ← nsmul_eq_mod_nsmul _ (hb.1 i), mul_nsmul, smul_comm]
  simp only [coordinates, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, hterm, nsmul_add]

/-- The exact geometric phase and the specified nonzero two-torsion point
cut out sixteen bases of the actual split-cubic point group. -/
lemma compatible_basis_count [CharZero K] (he : Function.Injective e)
    (b : Marking K e) (hb : IsBasis K e b)
    (P : (ArithmeticThetaMarkingR0115.Curve K e).Point)
    (hP : 2 • P = 0) (hP0 : P ≠ 0) (z : K) (hz : z^2 = -1) :
    Nat.card {c : Marking K e // IsBasis K e c ∧
      2 • c 0 + 2 • c 1 = P ∧ phase K e c = z} = 16 := by
  have hP4 : 4 • P = 0 := by
    rw [show 4 = 2*2 from rfl, mul_nsmul, hP, nsmul_zero]
  obtain ⟨p, hp⟩ := hb.2.2 P hP4
  have hp2 : 2 • p = 0 := by
    apply hb.2.1
    rw [coordinates_double b hb, hp, hP]
    simp [coordinates]
  have hp0 : p ≠ 0 := by
    intro h
    apply hP0
    rw [← hp, h]
    simp [coordinates]
  let f : {A : Mat4 // IsUnit A.det ∧ doubleColumnSum A = p ∧ phase K e b ^ A.det.val = z} →
      {c : Marking K e // IsBasis K e c ∧ 2 • c 0 + 2 • c 1 = P ∧ phase K e c = z} :=
    fun A => ⟨act K e b A.val, basis_act_unit b hb A.val A.property.1,
      by rw [characteristic_act b hb, A.property.2.1, hp],
      (phase_act_unit he b hb A.val A.property.1).trans A.property.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro A B h
      apply Subtype.ext
      exact act_injective b hb (congrArg Subtype.val h)
    · rintro ⟨c, hc, hcP, hcz⟩
      obtain ⟨A, hA, hac⟩ := exists_change b c hb hc
      have hAp : doubleColumnSum A = p := by
        apply hb.2.1
        rw [← characteristic_act b hb, hac, hcP, hp]
      have hAz : phase K e b ^ A.det.val = z := by
        rw [← phase_act_unit he b hb A hA, hac, hcz]
      exact ⟨⟨A, hA, hAp, hAz⟩, Subtype.ext hac⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact matrix_phase_fiber_count (phase K e b) z (phase_square he b hb) hz p hp2 hp0

#print axioms compatible_basis_count
#print axioms basisEquiv
#print axioms phase_act_unit
end SplitCounting

namespace FieldCounting
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaRelativeFourCharacterR0211
open ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

/-- Over a field the actual projective sections and affine points are equivalent,
with the exact group law and coordinate evaluation used by the phase theorem. -/
lemma evaluation_equiv (K : Type u) [Field K] [CharZero K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G) :
    ∃ ev : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K))
        (structureMap K W) ≃ (W.toProjective.baseChange K).toAffine.Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      ∀ P x y, HasCoordinates K W P.val x y →
        ∃ h, ev P = Point.some x y h := by
  obtain ⟨ev, hev, _, hcoord⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by simpa [origin] using hG.1 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K)))
  let t := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have ht : t = 𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K) := by simp [t]
  have H : ∃ e : SchemeHomOver t (structureMap K W) ≃ (W.toProjective.baseChange K).toAffine.Point,
      (∀ P Q, e (G.mul t P Q) = e P + e Q) ∧
      ∀ P x y, HasCoordinates K W P.val x y → ∃ h, e P = Point.some x y h := by
    refine ⟨ev K, hev.1 K, ?_⟩
    intro P x y hP
    obtain ⟨_, χ, hχ, hx, hy⟩ := hP
    obtain ⟨h, hh⟩ := hcoord K P χ hχ
    subst x
    subst y
    exact ⟨h, hh⟩
  rw [ht] at H
  exact H

/-- Completing the square is a bijective change of the actual point group. -/
def completeEquiv {K : Type u} [Field K] [CharZero K] [DecidableEq K]
    (V : WeierstrassCurve K) :
    V.toAffine.Point ≃+ ((completeChange V) • V).toAffine.Point :=
  AddEquiv.ofBijective (completeMap V)
    ⟨Point.vcFun_rightInverse.injective, Point.vcFun_leftInverse.surjective⟩

lemma basis_transport {K : Type u} [Field K] [DecidableEq K]
    {e e' : Fin 3 → K}
    (f : (ArithmeticThetaMarkingR0115.Curve K e).Point ≃+
      (ArithmeticThetaMarkingR0115.Curve K e').Point)
    (b : ArithmeticThetaMarkingR0115.Marking K e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis K e b) :
    ArithmeticThetaMarkingR0115.IsBasis K e' (f ∘ b) := by
  have hc (v : Fin 2 → ZMod 4) :
      ArithmeticThetaMarkingR0115.coordinates K e' (f ∘ b) v =
      f (ArithmeticThetaMarkingR0115.coordinates K e b v) := by
    simp only [ArithmeticThetaMarkingR0115.coordinates, Function.comp_apply,
      map_add, map_nsmul]
  refine ⟨fun i => by rw [Function.comp_apply, ← map_nsmul, hb.1 i, map_zero], ?_, ?_⟩
  · intro v w hvw
    rw [hc, hc] at hvw
    exact hb.2.1 (f.injective hvw)
  · intro P hP
    obtain ⟨v, hv⟩ := hb.2.2 (f.symm P) (by rw [← map_nsmul, hP, map_zero])
    exact ⟨v, by rw [hc, hv, f.apply_symm_apply]⟩

open ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175

/-- A basis of the split point group gives actual projective marking sections. -/
def basisToMark {K : Type u} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (G : Law K W) (hG : IsOriginLaw K W G)
    (e : Fin 3 → K)
    (ev : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K))
      (structureMap K W) ≃ (ArithmeticThetaMarkingR0115.Curve K e).Point)
    (hm : ∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q)
    (hz : ev (G.one (𝟙 _)) = 0)
    (b : ArithmeticThetaMarkingR0115.Marking K e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis K e b) :
    ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _) where
  x := ev.symm (b 0)
  y := ev.symm (b 1)
  killed_x := by
    apply ev.injective
    rw [eval_nsmul _ ev hm hz, ev.apply_symm_apply, hb.1, hz]
  killed_y := by
    apply ev.injective
    rw [eval_nsmul _ ev hm hz, ev.apply_symm_apply, hb.1, hz]
  avoids := by
    intro i j hij
    apply (eval_avoids hG _ ev hm hz _ _ i.val j.val).mpr
    simp only [ev.apply_symm_apply]
    intro h
    have hc : ArithmeticThetaMarkingR0115.coordinates K e b
        ![(i.val : ZMod 4), (j.val : ZMod 4)] =
        ArithmeticThetaMarkingR0115.coordinates K e b 0 := by
      simpa [ArithmeticThetaMarkingR0115.coordinates, ZMod.val_natCast,
        Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using h
    have hh := hb.2.1 hc
    have hi := congrArg (fun v : Fin 2 → ZMod 4 => (v 0).val) hh
    have hj := congrArg (fun v : Fin 2 → ZMod 4 => (v 1).val) hh
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
      ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] at hi hj
    exact hij.elim (fun h => h hi) (fun h => h hj)

lemma castPoint_trans {K : Type u} [Field K] [DecidableEq K]
    {V₁ V₂ V₃ : WeierstrassCurve K} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃)
    (P : V₁.toAffine.Point) :
    castPoint h₂ (castPoint h₁ P) = castPoint (h₁.trans h₂) P := by
  subst V₂
  subst V₃
  rfl

/-- One fixed completion of the original equation identifies every actual
marking and its exact Miller phase on the same split elliptic curve. -/
lemma exists_split_evaluation (K : Type u) [Field K] [CharZero K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G)
    (M₀ : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _)) :
    ∃ (e : Fin 3 → K), Function.Injective e ∧
      ∃ ev : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K))
        (structureMap K W) ≃ (ArithmeticThetaMarkingR0115.Curve K e).Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      ev (G.one (𝟙 _)) = 0 ∧
      ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _),
        ArithmeticThetaMarkingR0115.IsBasis K e (fun i => ev (![M.x, M.y] i)) ∧
        ∀ z : K, ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z ↔
          ArithmeticThetaMarkingR0115.phase K e (fun i => ev (![M.x, M.y] i)) = z := by
  obtain ⟨ev₀, hm₀, hc₀⟩ := evaluation_equiv K W G hG
  let V := W.map (RingHom.id K)
  let ev₁ : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K))
      (structureMap K W) ≃ V.toAffine.Point := ev₀
  have hc : ∀ P x y, HasCoordinates K W P.val x y →
      ∃ h, ev₁ P = Point.some ((RingHom.id K) x) ((RingHom.id K) y) h := hc₀
  obtain ⟨w₀, hw₀, _⟩ :=
    (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase K W G hG M₀).1
  obtain ⟨_, e, he, hV, _⟩ := phase_comparison W G hG K (RingHom.id K) ev₁ hc M₀ w₀
    ((ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase K W G hG M₀).2 w₀ hw₀).1
  let ev := (ev₁.trans (completeEquiv V).toEquiv).trans (castPoint hV).toEquiv
  have hm (P Q) : ev (G.mul (𝟙 _) P Q) = ev P + ev Q := by
    change castPoint hV (completeMap V (ev₀ (G.mul (𝟙 _) P Q))) = _
    rw [hm₀, map_add, map_add]
    rfl
  have hz : ev (G.one (𝟙 _)) = 0 := by
    have hh := hm (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at hh
    exact add_left_cancel (show ev (G.one (𝟙 _)) + ev (G.one (𝟙 _)) =
      ev (G.one (𝟙 _)) + 0 by simpa using hh.symm)
  refine ⟨e, he, ev, hm, hz, ?_⟩
  intro M
  have hp (z : K) (hz : ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z) :
      ArithmeticThetaMarkingR0115.phase K e (fun i => ev (![M.x, M.y] i)) = z := by
    have H := (phase_comparison W G hG K (RingHom.id K) ev₁ hc M z
      ((ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase K W G hG M).2 z hz).1).1
    have H' := phaseOn_cast hV (fun i => completeMap V (ev₁ (![M.x, M.y] i)))
    rw [phaseOn_split] at H'
    exact H'.trans H.symm
  obtain ⟨w, hw, _⟩ :=
    (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase K W G hG M).1
  obtain ⟨_, e', he', hV', hB⟩ := phase_comparison W G hG K (RingHom.id K) ev₁ hc M w
    ((ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase K W G hG M).2 w hw).1
  refine ⟨?_, fun z => ⟨hp z, fun hz => ?_⟩⟩
  · have HB := basis_transport (castPoint (hV'.symm.trans hV)) _ hB
    change ArithmeticThetaMarkingR0115.IsBasis K e
      (fun i => castPoint hV (completeMap V (ev₁ (![M.x, M.y] i))))
    simpa only [Function.comp_def, castPoint_trans] using HB
  · have hwz : w = z := (hp w hw).symm.trans hz
    exact hwz ▸ hw

/-- The count of sixteen holds for actual projective sections with the
prescribed nonidentity characteristic and normalized affine Miller phase. -/
lemma affine_compatible_count (K : Type u) [Field K] [CharZero K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G)
    (M₀ : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _))
    (P : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K)) (structureMap K W))
    (hP : G.nsmul (𝟙 _) 2 P = G.one (𝟙 _)) (hP0 : P ≠ G.one (𝟙 _))
    (z : K) (hz : z^2 = -1) :
    Nat.card {M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _) //
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) = P ∧
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z} = 16 := by
  obtain ⟨e, he, ev, hm, hzero, hmark⟩ := exists_split_evaluation K W G hG M₀
  let B := fun M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _) =>
    fun i : Fin 2 => ev (![M.x, M.y] i)
  have hchar (M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _)) :
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) = P ↔
      2 • B M 0 + 2 • B M 1 = ev P := by
    rw [← ev.injective.eq_iff, hm, eval_nsmul _ ev hm hzero, eval_nsmul _ ev hm hzero]
    rfl
  let f : {M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _) //
        G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) = P ∧
        ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z} →
      {b : ArithmeticThetaMarkingR0115.Marking K e //
        ArithmeticThetaMarkingR0115.IsBasis K e b ∧
        2 • b 0 + 2 • b 1 = ev P ∧ ArithmeticThetaMarkingR0115.phase K e b = z} :=
    fun M => ⟨B M.val, (hmark M.val).1, (hchar M.val).mp M.property.1,
      ((hmark M.val).2 z).mp M.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro M N h
      have hh := congrArg Subtype.val h
      apply Subtype.ext
      apply marking_ext
      · apply congrArg Subtype.val
        apply ev.injective
        exact congrFun hh 0
      · apply congrArg Subtype.val
        apply ev.injective
        exact congrFun hh 1
    · rintro ⟨b, hb, hp, hz'⟩
      let M := basisToMark W G hG e ev hm hzero b hb
      have hB : B M = b := by
        funext i
        fin_cases i <;> simp [B, M, basisToMark]
      have hM : G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) = P ∧
          ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z := by
        refine ⟨(hchar M).mpr (by rw [hB]; exact hp), ((hmark M).2 z).mpr ?_⟩
        change ArithmeticThetaMarkingR0115.phase K e (B M) = z
        rw [hB]
        exact hz'
      exact ⟨⟨M, hM⟩, Subtype.ext hB⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  exact SplitCounting.compatible_basis_count he (B M₀) (hmark M₀).1 (ev P)
    (by rw [← eval_nsmul _ ev hm hzero, hP, hzero])
    (fun h => hP0 (ev.injective (h.trans hzero.symm))) z hz

lemma geometric_compatible_count (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G)
    (P : SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base K)) (structureMap K W))
    (hP : G.nsmul (𝟙 _) 2 P = G.one (𝟙 _)) (hP0 : P ≠ G.one (𝟙 _))
    (z : K) (hz : z^2 = -1) :
    Nat.card {M : ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _) //
      G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y) = P ∧
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K W G M z} = 16 := by
  classical
  have hc := SchemeFourCoverGeometry.marking_card_geometric K W G hG 4 (by decide) K
  simp only [show algebraMap K K = RingHom.id K from rfl, CommRingCat.ofHom_id,
    Spec.map_id, SchemeFourCoverGeometry.levelDegree_four] at hc
  have hn : Nonempty (ArithmeticThetaFullLevelCoverR0175.FullLevel K W G 4 (𝟙 _)) :=
    Nat.card_pos_iff.mp (by rw [hc]; decide) |>.1
  obtain ⟨M₀⟩ := hn
  exact affine_compatible_count K W G hG M₀ P hP hP0 z hz

#print axioms affine_compatible_count
#print axioms exists_split_evaluation
#print axioms basisToMark
#print axioms evaluation_equiv
end FieldCounting

namespace AffineModel
open ArithmeticThetaRelativeKatoR0169

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (b : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ S)
    (f : ArithmeticThetaRelativeKatoR0169.Curve R W ⟶ E.curve)
    (hc : IsPullback f (structureMap R W) E.p b)

/-- An actual Weierstrass model with geometry inherited through its specified
Cartesian comparison to the original elliptic family. -/
def family : Family (ArithmeticThetaLocalWeierstrassR0203.Base R) where
  curve := ArithmeticThetaRelativeKatoR0169.Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul, mul_one := G.mul_one
           inv_mul_cancel := G.inv_mul_cancel, mul_comm := hG.2, mul_natural := G.mul_natural }
  proper := MorphismProperty.of_isPullback hc E.proper
  dimension := by
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.of_isPullback hc E.dimension
  connected := MorphismProperty.of_isPullback hc E.connected

lemma family_zero : (family E W G hG b f hc).zero = origin R W := by
  change (G.one (𝟙 (ArithmeticThetaLocalWeierstrassR0203.Base R))).val = _
  simpa only [Category.id_comp] using hG.1 (𝟙 (ArithmeticThetaLocalWeierstrassR0203.Base R))

lemma multiple_eq {T : Scheme.{u}} (t : T ⟶ ArithmeticThetaLocalWeierstrassR0203.Base R)
    (n : ℕ) (x : SchemeHomOver t (structureMap R W)) :
    multiple (family E W G hG b f hc) t n x = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih => change G.mul t (multiple (family E W G hG b f hc) t n x) x = G.mul t (G.nsmul t n x) x; rw [ih]

def levelEquiv : FullLevel (family E W G hG b f hc) 4 ≃
    ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 _) where
  toFun M :=
    { x := M.x, y := M.y
      killed_x := by rw [← multiple_eq E W G hG b f hc]; exact M.killed_x
      killed_y := by rw [← multiple_eq E W G hG b f hc]; exact M.killed_y
      avoids := by
        intro i j hij
        have h := M.avoids i j hij
        rw [multiple_eq, multiple_eq, family_zero] at h
        exact h }
  invFun M :=
    { x := M.x, y := M.y
      killed_x := by rw [multiple_eq]; exact M.killed_x
      killed_y := by rw [multiple_eq]; exact M.killed_y
      avoids := by
        intro i j hij
        rw [multiple_eq, multiple_eq, family_zero]
        exact M.avoids i j hij }
  left_inv M := SchemeFourMarkingActionR0215.fullLevel_ext _ _ _ rfl rfl
  right_inv M := ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175.marking_ext _ _ rfl rfl

variable [Algebra ℚ R] [W.IsElliptic]

/-- The identity affine test retains the original equation and both sections. -/
def identityTest (M : FullLevel (family E W G hG b f hc) 4) :
    AffineTest (family E W G hG b f hc) M where
  ring := R
  equation := W
  elliptic := inferInstance
  law := G
  originLaw := hG
  base := 𝟙 _
  comparison := 𝟙 _
  cartesian := IsPullback.of_horiz_isIso ⟨by simp; rfl⟩
  zero_eq := by simp only [Category.comp_id, Category.id_comp]; exact (family_zero E W G hG b f hc).symm
  mul_eq := by
    intro T t x y x' y' hx hy
    have hx' : x' = x := Subtype.ext (by simpa only [Category.comp_id] using hx)
    have hy' : y' = y := Subtype.ext (by simpa only [Category.comp_id] using hy)
    subst x'; subst y'
    simp only [Category.comp_id]
    rfl
  level := levelEquiv E W G hG b f hc M
  x_eq := by simp only [Category.comp_id, Category.id_comp]; rfl
  y_eq := by simp only [Category.comp_id, Category.id_comp]; rfl

lemma phase_iff (k : Type u) [Field k] [CharZero k]
    (σ : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ Base k)
    (M : FullLevel (family E W G hG b f hc) 4) (w : Γ(Base R, ⊤)) :
    MillerPhase (family E W G hG b f hc) M w ↔
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G
        (levelEquiv E W G hG b f hc M) ((Scheme.ΓSpecIso (.of R)).hom w) := by
  have ht (a : Γ(Base R, ⊤)) :
      affineScalar _ M (identityTest E W G hG b f hc M) a =
        (Scheme.ΓSpecIso (.of R)).hom a := by simp [affineScalar, identityTest]
  constructor
  · intro hw
    have H := hw (identityTest E W G hG b f hc M)
    change ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G
      (levelEquiv E W G hG b f hc M) (affineScalar _ M (identityTest E W G hG b f hc M) w) at H
    rwa [ht] at H
  · intro hw
    obtain ⟨a, ha, _⟩ := (scheme_miller_phase k _ σ (family E W G hG b f hc) M).1
    have ha' := ha (identityTest E W G hG b f hc M)
    rw [ht] at ha'
    have he := (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase
      R W G hG (levelEquiv E W G hG b f hc M)).1.unique ha' hw
    have hae : a = w := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1 he
    exact hae ▸ ha

/-- Compatible markings on an actual Cartesian geometric model have cardinal
sixteen, with both conditions transported through the original family map. -/
lemma matching_count (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (V : WeierstrassCurve K) [V.IsElliptic] (H : Law K V) (hH : IsOriginLaw K V H)
    (a : Base K ⟶ S) (g : ArithmeticThetaRelativeKatoR0169.Curve K V ⟶ E.curve)
    (hpb : IsPullback g (structureMap K V) E.p a)
    (hF : Cartesian E (family E V H hH a g hpb) a g)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1) :
    Nat.card {M : FullLevel (family E V H hH a g hpb) 4 //
      Matches E P z (family E V H hH a g hpb) M a g} = 16 := by
  classical
  let F := family E V H hH a g hpb
  let Q := pullSection E F a g hF P.point
  let w : K := (Scheme.ΓSpecIso (.of K)).hom (a.appTop z)
  have hw : w^2 = -1 := by
    have hh := congrArg (fun z => (Scheme.ΓSpecIso (.of K)).hom (a.appTop z)) hz
    simpa only [map_pow, map_neg, map_one] using hh
  have hQ : H.nsmul (𝟙 _) 2 Q = H.one (𝟙 _) := by
    rw [← multiple_eq E V H hH a g hpb]
    exact pullSection_killed E F a g hF P.point 2 P.killed
  have hQ0 : Q ≠ H.one (𝟙 _) := by
    intro heq
    have hq := pullSection_comp E F a g hF P.point
    have hzero : (H.one (𝟙 _)).val ≫ g = a ≫ E.zero := hF.2.1
    rw [show pullSection E F a g hF P.point = H.one (𝟙 _) from heq, hzero] at hq
    have hpt := congrArg (fun f : Base K ⟶ E.curve => f (IsLocalRing.closedPoint K)) hq
    exact Set.disjoint_left.mp P.avoids ⟨a (IsLocalRing.closedPoint K), hpt.symm⟩
      ⟨a (IsLocalRing.closedPoint K), rfl⟩
  let ev := levelEquiv E V H hH a g hpb
  have hchar (M : FullLevel F 4) :
      evenPoint F M ≫ g = a ≫ P.point.val ↔
      H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 (ev M).x) (H.nsmul (𝟙 _) 2 (ev M).y) = Q := by
    have hc : evenPoint F M =
        (H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 (ev M).x) (H.nsmul (𝟙 _) 2 (ev M).y)).val := by
      dsimp only [evenPoint]
      rw [multiple_eq, multiple_eq]
      rfl
    rw [hc]
    constructor
    · intro hh
      apply CartesianFullMarking.section_ext E F a g hpb
      exact hh.trans (pullSection_comp E F a g hF P.point).symm
    · intro hh
      rw [hh]
      exact pullSection_comp E F a g hF P.point
  have hmatches (M : FullLevel F 4) : Matches E P z F M a g ↔
      H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 (ev M).x) (H.nsmul (𝟙 _) 2 (ev M).y) = Q ∧
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K V H (ev M) w :=
    and_congr (hchar M) (phase_iff E V H hH a g hpb K (𝟙 _) M (a.appTop z))
  let e : {M : FullLevel F 4 // Matches E P z F M a g} ≃
      {M : ArithmeticThetaFullLevelCoverR0175.FullLevel K V H 4 (𝟙 _) //
        H.mul (𝟙 _) (H.nsmul (𝟙 _) 2 M.x) (H.nsmul (𝟙 _) 2 M.y) = Q ∧
        ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase K V H M w} :=
    ev.subtypeEquiv hmatches
  exact (Nat.card_congr e).trans (FieldCounting.geometric_compatible_count K V H hH Q hQ hQ0 w hw)

#print axioms matching_count
#print axioms phase_iff
end AffineModel


/-- The constructed subcover has degree sixteen on every point of every
allowed base; only the test fiber is extended to an algebraically closed field. -/
lemma representing_even_rank (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (P : EvenPoint E) (z : Γ(S, ⊤)) (hz : z^2 = -1)
    (C : Cover E) (hC : RepresentsEven E P z C)
    [IsFinite C.projection] [Etale C.projection] :
    ∀ s : S, C.projection.finrank s = 16 := by
  classical
  intro s
  obtain ⟨L, q, hq⟩ := scheme_local_weierstrass k S σ E s
  letI := L.commRing
  letI := L.algebra
  letI := L.elliptic
  letI : Algebra ℚ L.ring := Algebra.compHom L.ring (algebraMap ℚ k)
  let K := AlgebraicClosure q.asIdeal.ResidueField
  letI : Algebra ℚ q.asIdeal.ResidueField :=
    ((algebraMap L.ring q.asIdeal.ResidueField).comp (algebraMap ℚ L.ring)).toAlgebra
  letI : CharZero q.asIdeal.ResidueField := Algebra.charZero_of_charZero ℚ _
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap q.asIdeal.ResidueField K).injective
  let ι := algebraMap L.ring K
  let t := Spec.map (CommRingCat.ofHom ι)
  have ht : t (IsLocalRing.closedPoint K) = q := by
    change PrimeSpectrum.comap (algebraMap L.ring K) _ = q
    rw [IsScalarTower.algebraMap_eq L.ring q.asIdeal.ResidueField K, PrimeSpectrum.comap_comp]
    exact Set.mem_singleton_iff.mp (PrimeSpectrum.residueField_comap q ▸ Set.mem_range_self _)
  let V := L.equation.map ι
  obtain ⟨c, _, hc, ho, _⟩ :=
    ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_comparison L.equation ι
  obtain ⟨G, hm, hone⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      ι (ArithmeticThetaRelativeKatoR0169.structureMap L.ring L.equation)
      (ArithmeticThetaRelativeKatoR0169.structureMap K V) c hc L.law
  have hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K V G := by
    constructor
    · intro T a
      apply hc.hom_ext
      · simp only [hone, L.originLaw.1, Category.assoc]
        dsimp only [V]
        rw [ho]
      · rw [Category.assoc,
          ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.origin_over,
          Category.comp_id]
        exact (G.one a).property
    · intro T a x y
      apply Subtype.ext
      apply hc.hom_ext
      · rw [hm, hm, L.originLaw.2]
      · exact (G.mul a x y).property.trans (G.mul a y x).property.symm
  let b := t ≫ L.base
  let f := c ≫ L.comparison
  have hpb : IsPullback f (ArithmeticThetaRelativeKatoR0169.structureMap K V) E.p b :=
    hc.paste_horiz L.cartesian
  let F := AffineModel.family E V G hG b f hpb
  let F₀ := SchemeLocalClassifier.family L
  have hF₀ : Cartesian E F₀ L.base L.comparison :=
    ⟨L.cartesian, by rw [SchemeLocalClassifier.family_zero]; exact L.zero_eq, L.mul_eq⟩
  have hF' : Cartesian F₀ F t c := by
    refine ⟨hc, ?_, ?_⟩
    · rw [AffineModel.family_zero, SchemeLocalClassifier.family_zero]
      exact ho
    · intro T a x y x' y' hx hy
      let xx : SchemeHomOver (a ≫ t) F₀.p :=
        ⟨x.val ≫ c, by
          change (x.val ≫ c) ≫ ArithmeticThetaRelativeKatoR0169.structureMap L.ring L.equation = _
          rw [Category.assoc, hc.w, ← Category.assoc]
          exact congrArg (fun v : T ⟶ Base K => v ≫ t) x.property⟩
      let yy : SchemeHomOver (a ≫ t) F₀.p :=
        ⟨y.val ≫ c, by
          change (y.val ≫ c) ≫ ArithmeticThetaRelativeKatoR0169.structureMap L.ring L.equation = _
          rw [Category.assoc, hc.w, ← Category.assoc]
          exact congrArg (fun v : T ⟶ Base K => v ≫ t) y.property⟩
      have hxx : x' = xx := Subtype.ext hx
      have hyy : y' = yy := Subtype.ext hy
      subst x'; subst y'
      exact (hm a x y).symm
  have hF : Cartesian E F b f :=
    cartesian_comp E F₀ F L.base L.comparison hF₀ t c hF'
  have hs : b (IsLocalRing.closedPoint K) = s := by
    change L.base (t (IsLocalRing.closedPoint K)) = s
    rw [ht]
    exact hq
  rw [← hs, finrank_eq_compatible_markings E k σ P z C hC K b F f hF]
  exact AffineModel.matching_count E K V G hG b f hpb hF P z hz

#print axioms representing_even_rank

#print axioms matrix_phase_fiber_count
#print axioms characteristic_equalizer_open
#print axioms two_torsion_equalizer_open
#print axioms evenPoint_two_torsion
#print axioms affine_family_two_torsion_equality
#print axioms affine_torsion_equality
#print axioms exists_finite_etale_representing_subcover
#print axioms exists_equation_locus
#print axioms represents_subcover
#print axioms closed_equalizer
#print axioms marked_comp
#print axioms phaseOpen_clopen
#print axioms phaseOpen_universal
#print axioms restrictCover_map
#print axioms matches_pullback
#print axioms matches_iff
end ArithmeticThetaEvenMarkingTorsorR0216.EvenMarkingSubcover

namespace ArithmeticThetaEvenMarkingTorsorR0216
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

/-- The actual fixed-characteristic, fixed-Miller-phase subcover is clopen,
finite étale, surjective, and of degree sixteen over every allowed base. -/
theorem even_marking_subcover :
∀ (k : Type u) [Field k] [CharZero k]
(S : AlgebraicGeometry.Scheme.{u})
(σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
(E : ArithmeticThetaLocalWeierstrassR0203.Family S),
∀ (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
(z : S.presheaf.obj (Opposite.op ⊤)), z^2 = -1 →
∀ (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E),
ArithmeticThetaEvenMarkingTorsorR0216.Represents E D →
∃ (C : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
(j : Quiver.Hom C.space D.space) (h : Quiver.Hom C.family.curve D.family.curve),
ArithmeticThetaEvenMarkingTorsorR0216.CoverMap E C D j h ∧
AlgebraicGeometry.IsOpenImmersion j ∧ AlgebraicGeometry.IsClosedImmersion j ∧
ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z C ∧
ArithmeticThetaEvenMarkingTorsorR0216.Geometry E C 16 := by
  intro k _ _ S σ E P z hz D hD
  obtain ⟨C, j, h, hj, hopen, hclosed, hC, hfinite, hetale⟩ :=
    EvenMarkingSubcover.exists_finite_etale_representing_subcover E k σ P z hz D hD
  letI := hfinite
  letI := hetale
  have hr := EvenMarkingSubcover.representing_even_rank E k σ P z hz C hC
  refine ⟨C, j, h, hj, hopen, hclosed, hC, hfinite, hetale, ?_, hr⟩
  apply C.projection.one_le_finrank_iff_surjective.mp
  intro s
  change 1 ≤ C.projection.finrank s
  rw [hr]
  decide

#print axioms even_marking_subcover
end ArithmeticThetaEvenMarkingTorsorR0216
