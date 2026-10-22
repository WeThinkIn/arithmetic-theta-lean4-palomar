module

public import EllipticFamilyWeierstrassAtlasR0180
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
public import CyclicQuotientArbitraryBaseChangeR0173
public import FramedSchemeQuotientR0174
public import PointedRelativeGroupHomR0173

@[expose] public section

/-! Global cyclic kernel and its actual Cartesian chart transports. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaOpenHodgeR0180
namespace GlobalLevelCyclicQuotientR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
abbrev sections := SchemeHomOver (𝟙 (Base R)) E.projection
abbrev sectionGroup : CommGroup (sections E) :=
  { E.law.pointGroup (𝟙 (Base R)) with mul_comm := E.commutative (𝟙 _) }

lemma nsmul_pow {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t E.projection) (n : ℕ) :
    letI := E.law.pointGroup t
    E.law.nsmul t n x = x ^ n := by
  letI := E.law.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [E.law.nsmul_succ, ih]; exact (pow_succ x n).symm

lemma comp_nsmul {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t E.projection) (n : ℕ) :
    x.val ≫ E.law.schemeNsmul n = (E.law.nsmul t n x).val := by
  exact congrArg Subtype.val (E.law.nsmul_natural E.projection t x.val x.property n
    GoodReductionJacobian.RelativeGroupLaw.idPoint)

lemma pow_mod {H : Type*} [Monoid H] {x : H} {L : ℕ}
    (hx : x ^ L = 1) (n : ℕ) : x ^ (n % L) = x ^ n := by
  exact pow_eq_pow_of_modEq (by simp [Nat.ModEq]) hx

def translate (t : sections E) : E.curve ⟶ E.curve :=
  (E.law.mul (E.projection) ⟨𝟙 _, Category.id_comp _⟩
    ⟨E.projection ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩).val

lemma translate_section (z t : sections E) :
    z.val ≫ translate E t = (E.law.mul (𝟙 (Base R)) z t).val := by
  have h := E.law.mul_natural (E.projection) (𝟙 (Base R)) z.val z.property
    ⟨𝟙 _, Category.id_comp _⟩
    ⟨E.projection ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩
  have h₁ : GoodReductionJacobian.schemeHomOverComp z.val z.property
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (E.projection) (E.projection)) = z :=
    Subtype.ext (Category.comp_id _)
  have h₂ : GoodReductionJacobian.schemeHomOverComp z.val z.property
      (⟨E.projection ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩ :
        SchemeHomOver (E.projection) (E.projection)) = t := by
    apply Subtype.ext
    dsimp [GoodReductionJacobian.schemeHomOverComp]
    rw [← Category.assoc, z.property, Category.id_comp]
  exact (congrArg Subtype.val h).trans (by rw [h₁, h₂])

lemma disjoint_of_product (s t d : sections E)
    (ht : E.law.mul (𝟙 (Base R)) t d = E.law.one (𝟙 (Base R)))
    (hs : Disjoint (Set.range (E.law.mul (𝟙 (Base R)) s d).val)
      (Set.range (zero E))) :
    Disjoint (Set.range s.val) (Set.range t.val) := by
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have he := congrArg (fun q => (translate E d) q) hab
  change (s.val ≫ translate E d) a = (t.val ≫ translate E d) b at he
  rw [translate_section, translate_section, ht] at he
  exact (Set.disjoint_iff_forall_ne.mp hs) ⟨a, rfl⟩ ⟨b, rfl⟩ he

/-- Distinct reduced coordinate pairs have disjoint images over the entire base. -/
lemma coordinate_disjoint {L : ℕ} (hL : 0 < L)
    (A : FamilyLevel R E L)
    (i j k l : ℕ) (hi : i < L) (hj : j < L) (hk : k < L) (hl : l < L)
    (hne : i ≠ k ∨ j ≠ l) :
    Disjoint
      (Set.range (E.law.mul (𝟙 (Base R)) (E.law.nsmul (𝟙 (Base R)) i A.x)
        (E.law.nsmul (𝟙 (Base R)) j A.y)).val)
      (Set.range (E.law.mul (𝟙 (Base R)) (E.law.nsmul (𝟙 (Base R)) k A.x)
        (E.law.nsmul (𝟙 (Base R)) l A.y)).val) := by
  letI := sectionGroup E
  have hx : A.x ^ L = 1 := by
    have h := A.killed_x
    rw [comp_nsmul, nsmul_pow] at h
    apply Subtype.ext
    exact h
  have hy : A.y ^ L = 1 := by
    have h := A.killed_y
    rw [comp_nsmul, nsmul_pow] at h
    apply Subtype.ext
    exact h
  let d := A.x ^ (L-k) * A.y ^ (L-l)
  have prod (a b : ℕ) : (A.x ^ a * A.y ^ b) * d =
      A.x ^ (a+(L-k)) * A.y ^ (b+(L-l)) := by
    simp only [pow_add]
    dsimp [d]
    ac_rfl
  apply disjoint_of_product E _ _ d
  · simp only [nsmul_pow]
    change (A.x ^ k * A.y ^ l) * d = 1
    rw [prod, Nat.add_sub_of_le (Nat.le_of_lt hk), Nat.add_sub_of_le (Nat.le_of_lt hl), hx, hy, one_mul]
  · have hn : (i+(L-k)) % L ≠ 0 ∨ (j+(L-l)) % L ≠ 0 := by
      have hi' : i + (L-k) < 2*L := by omega
      have hj' : j + (L-l) < 2*L := by omega
      have aux (a : ℕ) (ha : a < 2*L) : a % L = 0 → a = 0 ∨ a = L := by
        intro h
        have hd := Nat.mod_add_div a L
        have hq : a / L < 2 := (Nat.div_lt_iff_lt_mul hL).mpr (by omega)
        interval_cases h : a / L <;> simp_all
      have hh₁ := aux _ hi'
      have hh₂ := aux _ hj'
      omega
    have ha := A.avoids ⟨(i+(L-k)) % L, Nat.mod_lt _ hL⟩
      ⟨(j+(L-l)) % L, Nat.mod_lt _ hL⟩ hn
    simp only [nsmul_pow] at ha ⊢
    change Disjoint (Set.range ((A.x ^ i * A.y ^ j) * d).val) _
    rw [prod]
    rw [pow_mod hx, pow_mod hy] at ha
    exact ha


lemma nsmul_comp (z : sections E) (a b : ℕ) :
    (E.law.nsmul (𝟙 (Base R)) a z).val ≫ E.law.schemeNsmul b =
      (E.law.nsmul (𝟙 (Base R)) (a*b) z).val := by
  rw [comp_nsmul]
  apply congrArg Subtype.val
  letI := E.law.pointGroup (𝟙 (Base R))
  simp only [nsmul_pow, pow_mul]

/-- Exact fiberwise cyclic section on the original family. -/
structure Cyclic (m : ℕ) where
  point : Base R ⟶ E.curve
  over_eq : point ≫ E.projection = 𝟙 _
  killed : point ≫ E.law.schemeNsmul m = zero E
  disjoint : ∀ i j : Fin m, i ≠ j →
    Disjoint (Set.range (point ≫ E.law.schemeNsmul i.val))
      (Set.range (point ≫ E.law.schemeNsmul j.val))

lemma cyclic_of_level {L : ℕ} (hL : 0 < L) (A : FamilyLevel R E L)
    (m : ℕ) (hm : 0 < m) (hmL : m ∣ L) :
    ∃ P : Cyclic E m, P.point = (E.law.nsmul (𝟙 _) (L/m) A.x).val := by
  have hc : L / m * m = L := Nat.div_mul_cancel hmL
  have hcpos : 0 < L / m := Nat.div_pos (Nat.le_of_dvd hL hmL) hm
  have hc_lt (i : Fin m) : L / m * i.val < L := by
    have := Nat.mul_lt_mul_of_pos_left i.isLt hcpos
    omega
  refine ⟨⟨(E.law.nsmul (𝟙 _) (L/m) A.x).val,
    (E.law.nsmul (𝟙 _) (L/m) A.x).property, ?_, ?_⟩, rfl⟩
  · rw [nsmul_comp, hc, ← comp_nsmul]
    exact A.killed_x
  · intro i j hij
    rw [nsmul_comp, nsmul_comp]
    have hne : L/m * i.val ≠ L/m * j.val := by
      intro h
      apply hij
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_left hcpos h
    simpa only [E.law.nsmul_zero, E.law.mul_one] using
      coordinate_disjoint E hL A (L/m*i.val) 0 (L/m*j.val) 0
        (hc_lt i) hL (hc_lt j) hL (Or.inl hne)

variable {S : Type u} [CommRing S] {F : EllipticFamily S}
  {W : WeierstrassCurve R} {G : Law R W}

/-- Lift an actual section through the supplied Cartesian square. -/
def liftSection (C : Test S F R W G) (P : Base S ⟶ F.curve)
    (hP : P ≫ F.projection = 𝟙 _) : Base R ⟶ Curve R W :=
  C.cartesian.lift (baseMap S R C.scalar ≫ P) (𝟙 _) (by simp [Category.assoc, hP])

lemma liftSection_map (C : Test S F R W G) (P : Base S ⟶ F.curve)
    (hP : P ≫ F.projection = 𝟙 _) :
    liftSection C P hP ≫ C.map = baseMap S R C.scalar ≫ P :=
  C.cartesian.lift_fst _ _ _

lemma liftSection_over (C : Test S F R W G) (P : Base S ⟶ F.curve)
    (hP : P ≫ F.projection = 𝟙 _) :
    liftSection C P hP ≫ structureMap R W = 𝟙 _ :=
  C.cartesian.lift_snd _ _ _

/-- Cyclic sections transport through every specified Cartesian test, preserving
all their actual multiples and disjointness, without a field extension. -/
def testCyclic (C : Test S F R W G) {m : ℕ} (P : Cyclic F m) :
    ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G m where
  point := liftSection C P.point P.over_eq
  over_eq := liftSection_over C P.point P.over_eq
  killed := by
    apply C.cartesian.hom_ext
    · rw [Category.assoc, C.nsmul_eq, ← Category.assoc, liftSection_map,
        Category.assoc, P.killed, C.origin_eq]
    · rw [Category.assoc, G.schemeNsmul_over, liftSection_over]
      exact (WeierstrassProjModel.kwZeroSect R W).property.symm
  disjoint := by
    intro i j hij
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have h := congrArg C.map.base hab
    change ((liftSection C P.point P.over_eq ≫ G.schemeNsmul i.val) ≫ C.map) a =
      ((liftSection C P.point P.over_eq ≫ G.schemeNsmul j.val) ≫ C.map) b at h
    have he (n : ℕ) :
        (liftSection C P.point P.over_eq ≫ G.schemeNsmul n) ≫ C.map =
          baseMap S R C.scalar ≫ P.point ≫ F.law.schemeNsmul n := by
      rw [Category.assoc, C.nsmul_eq, ← Category.assoc, liftSection_map, Category.assoc]
    rw [he, he] at h
    exact Set.disjoint_iff_forall_ne.mp (P.disjoint i j hij) ⟨_, rfl⟩ ⟨_, rfl⟩ h

lemma testCyclic_multiple (C : Test S F R W G) {m : ℕ} (P : Cyclic F m) (i : Fin m) :
    (testCyclic C P).point ≫ G.schemeNsmul i.val ≫ C.map =
      baseMap S R C.scalar ≫ P.point ≫ F.law.schemeNsmul i.val := by
  change liftSection C P.point P.over_eq ≫ G.schemeNsmul i.val ≫ C.map = _
  rw [C.nsmul_eq, ← Category.assoc, liftSection_map, Category.assoc]


/-- The scheme-theoretic global kernel uses the prescribed labeled sections. -/
def multiple {n : ℕ} (P : Cyclic E n) (i : Fin n) : Base R ⟶ E.curve :=
  P.point ≫ E.law.schemeNsmul i.val

def kernelIdeal {n : ℕ} (P : Cyclic E n) : E.curve.IdealSheafData :=
  ⨅ i : Fin n, (multiple E P i).ker

open ArithmeticThetaRelativeCyclicQuotientR0173 (splitStructure component)

lemma split_kernel {n : ℕ} (P : Cyclic E n) :
    IsFinite ((kernelIdeal E P).subschemeι ≫ E.projection) ∧
    Etale ((kernelIdeal E P).subschemeι ≫ E.projection) ∧
    ∃ e : (kernelIdeal E P).subscheme ≅ Spec (CommRingCat.of (Fin n → R)),
      e.hom ≫ splitStructure R n = (kernelIdeal E P).subschemeι ≫ E.projection ∧
      ∀ i : Fin n, component R n i ≫ e.inv ≫ (kernelIdeal E P).subschemeι =
        multiple E P i := by
  let s (i : Fin n) := multiple E P i
  have hs (i : Fin n) : s i ≫ E.projection = 𝟙 _ := by
    dsimp [s, multiple]
    rw [Category.assoc, E.law.schemeNsmul_over, P.over_eq]
  letI : IsProper (E.projection) :=
    E.proper
  have hsc (i : Fin n) : IsClosedImmersion (s i) := by
    have : IsClosedImmersion (s i ≫ E.projection) := by rw [hs i]; infer_instance
    exact IsClosedImmersion.of_comp (s i) (E.projection)
  let m : (∐ fun _ : Fin n => Base R) ⟶ E.curve := Sigma.desc s
  have hm : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
      (fun i j hij => P.disjoint i j hij)
  let I := kernelIdeal E P
  have hker : I = m.ker := by
    rw [← m.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin n => Base R))]
    change (⨅ i, (s i).ker) = _
    congr 1
    funext i
    congr 1
    exact (Sigma.ι_desc s i).symm
  have hker' : I.subschemeι.ker = m.ker := by
    rw [I.ker_subschemeι, hker]
  let f : (∐ fun _ : Fin n => Base R) ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι m hker'.le
  have hf : f ≫ I.subschemeι = m := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ hker'
  let q := sigmaSpec (fun _ : Fin n => CommRingCat.of (R))
  have : IsOpenImmersion q := by
    classical
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have ht : DFinsupp.single (β := fun _ : Fin n => R) j 1 j ∈ y.asIdeal :=
      (PrimeSpectrum.ext_iff.mp heq).le
        (x := DFinsupp.single j 1)
        (show DFinsupp.single (β := fun _ : Fin n => R) j 1 i ∈ x.asIdeal by
          simp [hij.symm])
    simp [← Ideal.eq_top_iff_one, y.2.ne_top] at ht
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin n => R)).surjective x
    refine ⟨Sigma.ι (fun _ : Fin n => Base R) i y, ?_⟩
    change (Sigma.ι (fun _ : Fin n => Spec (CommRingCat.of (R))) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : Fin n => Spec (CommRingCat.of (R))) i ≫ q =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i)) from
        ι_sigmaSpec _ i]
    exact hy
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩
  let e : I.subscheme ≅ Spec (CommRingCat.of (Fin n → R)) :=
    (asIso f).symm ≪≫ asIso q
  have hq : q ≫ splitStructure R n = m ≫ E.projection := by
    apply Sigma.hom_ext
    intro i
    simp only [q, ι_sigmaSpec_assoc, m, Sigma.ι_desc_assoc]
    rw [hs i]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i)) ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi (fun _ : Fin n => RingHom.id (R)))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of (R)) using 1
    congr 1
  have he : e.hom ≫ splitStructure R n = I.subschemeι ≫ E.projection := by
    apply (cancel_epi f).mp
    simpa [e, Category.assoc, ← hf] using hq
  have hl (i : Fin n) : component R n i ≫ e.inv ≫ I.subschemeι = s i := by
    rw [show component R n i = Sigma.ι (fun _ : Fin n => Base R) i ≫ q from
      (ι_sigmaSpec (fun _ : Fin n => CommRingCat.of (R)) i).symm]
    simp [e, Category.assoc, hf, m]
  have : IsFinite (splitStructure R n) := ArithmeticThetaRelativeCyclicQuotientR0173.SplitCyclicKernelR0173.split_finite R n
  have : Etale (splitStructure R n) := ArithmeticThetaRelativeCyclicQuotientR0173.SplitCyclicKernelR0173.split_etale R n
  refine ⟨?_, ?_, e, he, hl⟩
  · change IsFinite (I.subschemeι ≫ E.projection)
    rw [← he]
    infer_instance
  · change Etale (I.subschemeι ≫ E.projection)
    rw [← he]
    infer_instance


/-- The accepted normal-affine construction applies to the actual transported
cyclic point on each chart, with its precise kernel and finite étale degree. -/
lemma chart_quotient (C : Chart S F) {n : ℕ} (hn : 0 < n) (P : Cyclic F n) :
    Nonempty (ArithmeticThetaCyclicPresentationR0174.FramedQuotient C.ring
      C.equation C.law (testCyclic C.comparison P)) :=
  ArithmeticThetaCyclicPresentationR0174.framed_scheme_quotient C.ring C.equation
    C.law C.originLaw n hn (testCyclic C.comparison P)


open ArithmeticThetaRelativeCyclicQuotientR0173.FramedSchemeQuotientR0174 (factor_of_cover)

def generator {n : ℕ} (P : Cyclic E n) : sections E := ⟨P.point, P.over_eq⟩

lemma multiple_over {n : ℕ} (P : Cyclic E n) (i : Fin n) :
    multiple E P i ≫ E.projection = 𝟙 _ := by
  rw [multiple, Category.assoc, E.law.schemeNsmul_over, P.over_eq]

lemma multiple_eq_nsmul {n : ℕ} (P : Cyclic E n) (i : Fin n) :
    multiple E P i = (E.law.nsmul (𝟙 _) i.val (generator E P)).val :=
  comp_nsmul E (𝟙 _) (generator E P) i.val

lemma generator_killed {n : ℕ} (P : Cyclic E n) :
    E.law.nsmul (𝟙 _) n (generator E P) = E.law.one (𝟙 _) := by
  apply Subtype.ext
  rw [← comp_nsmul]
  exact P.killed

lemma nsmul_mod {n : ℕ} (P : Cyclic E n) (a : ℕ) :
    E.law.nsmul (𝟙 _) (a % n) (generator E P) =
      E.law.nsmul (𝟙 _) a (generator E P) := by
  letI := E.law.pointGroup (𝟙 (Base R))
  have hk : generator E P ^ n = 1 := by
    rw [← nsmul_pow]; exact generator_killed E P
  simp only [nsmul_pow]
  exact pow_mod hk a

def sectionAt {T : Scheme.{u}} (t : T ⟶ Base R) (p : sections E) :
    SchemeHomOver t E.projection :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) p
def multipleAt {n : ℕ} (P : Cyclic E n) {T : Scheme.{u}}
    (t : T ⟶ Base R) (i : Fin n) : SchemeHomOver t (E.projection) :=
  sectionAt E t (E.law.nsmul (𝟙 _) i.val (generator E P))

lemma multipleAt_val {n : ℕ} (P : Cyclic E n) {T : Scheme.{u}}
    (t : T ⟶ Base R) (i : Fin n) :
    (multipleAt E P t i).val = t ≫ multiple E P i := by
  rw [multiple_eq_nsmul]; rfl

lemma multipleAt_natural {n : ℕ} (P : Cyclic E n)
    {T U : Scheme.{u}} (t : T ⟶ Base R) (a : U ⟶ T) (i : Fin n) :
    GoodReductionJacobian.schemeHomOverComp a rfl (multipleAt E P t i) =
      multipleAt E P (a ≫ t) i := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

lemma multipleAt_mul {n : ℕ} (hn : 0 < n)
    (P : Cyclic E n) {T : Scheme.{u}} (t : T ⟶ Base R) (i j : Fin n) :
    E.law.mul t (multipleAt E P t i) (multipleAt E P t j) =
      multipleAt E P t ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ := by
  unfold multipleAt sectionAt
  rw [← E.law.mul_natural, nsmul_mod E P]
  congr 1
  letI := E.law.pointGroup (𝟙 (Base R))
  simp only [nsmul_pow]
  exact (pow_add (generator E P) i.val j.val).symm

lemma multipleAt_zero {n : ℕ} (hn : 0 < n)
    (P : Cyclic E n) {T : Scheme.{u}} (t : T ⟶ Base R) :
    multipleAt E P t ⟨0, hn⟩ = E.law.one t := by
  exact E.law.one_natural (𝟙 _) t t (Category.comp_id t)

lemma multipleAt_inv {n : ℕ} (hn : 0 < n)
    (P : Cyclic E n) {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n) :
    E.law.inv t (multipleAt E P t i) =
      multipleAt E P t ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩ := by
  letI := E.law.pointGroup t
  apply inv_eq_of_mul_eq_one_right
  change E.law.mul t _ _ = E.law.one t
  rw [multipleAt_mul E hn P]
  have he : (i.val + (n - i.val) % n) % n = 0 := by
    rw [Nat.add_mod_mod, Nat.add_sub_of_le (Nat.le_of_lt i.isLt), Nat.mod_self]
  simpa only [he] using multipleAt_zero E hn P t


section Kernel
variable {n : ℕ} (hn : 0 < n) (P : Cyclic E n)
include hn
/-- The accepted split-kernel isomorphism, with no new representability premise. -/
def kernelSplitIso : (kernelIdeal E P).subscheme ≅ Spec (CommRingCat.of (Fin n → R)) :=
  (split_kernel E P).2.2.choose

lemma kernelSplitIso_component (i : Fin n) :
    component R n i ≫ (kernelSplitIso E P).inv ≫
      (kernelIdeal E P).subschemeι = multiple E P i :=
  (split_kernel E P).2.2.choose_spec.2 i

/-- A cover of the actual ideal subscheme by its labeled sections. -/
def kernelCover : (kernelIdeal E P).subscheme.OpenCover :=
  by
  let q := sigmaSpec (fun _ : Fin n => CommRingCat.of R)
  have : IsOpenImmersion q := by
    classical
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have ht : DFinsupp.single (β := fun _ : Fin n => R) j 1 j ∈ y.asIdeal :=
      (PrimeSpectrum.ext_iff.mp heq).le
        (x := DFinsupp.single j 1)
        (show DFinsupp.single (β := fun _ : Fin n => R) j 1 i ∈ x.asIdeal by
          simp [hij.symm])
    simp [← Ideal.eq_top_iff_one, y.2.ne_top] at ht
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin n => R)).surjective x
    refine ⟨Sigma.ι (fun _ : Fin n => Base R) i y, ?_⟩
    change (Sigma.ι (fun _ : Fin n => Base R) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : Fin n => Base R) i ≫ q = component R n i from
      ι_sigmaSpec _ i]
    exact hy
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr
    ⟨inferInstance, inferInstance⟩
  exact (sigmaOpenCover (fun _ : Fin n => Base R)).pushforwardIso
    (sigmaSpec (fun _ : Fin n => CommRingCat.of R) ≫ (kernelSplitIso E P).inv)

lemma kernelCover_component (i : Fin n) :
    (kernelCover E P).f i ≫ (kernelIdeal E P).subschemeι =
      multiple E P i := by
  change (Sigma.ι (fun _ : Fin n => Base R) i ≫ sigmaSpec _ ≫ _) ≫ _ = _
  rw [← Category.assoc, ι_sigmaSpec]
  exact kernelSplitIso_component E hn P i

lemma multipleAt_factors {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n) :
    ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = (multipleAt E P t i).val := by
  refine ⟨t ≫ (kernelCover E P).f i, ?_⟩
  rw [Category.assoc, kernelCover_component E hn P, multipleAt_val]

/-- On the pullback of a labeled kernel chart, a factoring point is exactly
that labeled multiple, with the test scheme's original structural morphism. -/
lemma kernel_local_point {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (E.projection))
    (e : T ⟶ (kernelIdeal E P).subscheme)
    (he : e ≫ (kernelIdeal E P).subschemeι = x.val) (i : Fin n) :
    let C := kernelCover E P
    GoodReductionJacobian.schemeHomOverComp ((C.pullback₁ e).f i)
      (show (C.pullback₁ e).f i ≫ t = (C.pullback₁ e).f i ≫ t from rfl) x =
        multipleAt E P ((C.pullback₁ e).f i ≫ t) i := by
  dsimp only
  let C := kernelCover E P
  have hh : (C.pullback₁ e).f i ≫ x.val = C.pullbackHom e i ≫ multiple E P i := by
    rw [← he, ← Category.assoc, ← C.pullbackHom_map, Category.assoc,
      kernelCover_component E hn P]
  have ht : C.pullbackHom e i = (C.pullback₁ e).f i ≫ t := by
    have z := congrArg (fun f => f ≫ E.projection) hh
    simp only [Category.assoc, x.property, multiple_over] at z
    exact (Category.comp_id _).symm.trans z.symm
  apply Subtype.ext
  change (C.pullback₁ e).f i ≫ x.val = _
  rw [multipleAt_val, hh, ht]



lemma kernel_one_closed {T : Scheme.{u}} (t : T ⟶ Base R) :
    ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = (E.law.one t).val := by
  simpa only [multipleAt_zero E hn P] using
    multipleAt_factors E hn P t ⟨0, hn⟩

lemma kernel_mul_multiple {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n)
    (y : SchemeHomOver t (E.projection))
    (e : T ⟶ (kernelIdeal E P).subscheme)
    (he : e ≫ (kernelIdeal E P).subschemeι = y.val) :
    ∃ e' : T ⟶ (kernelIdeal E P).subscheme,
      e' ≫ (kernelIdeal E P).subschemeι =
        (E.law.mul t (multipleAt E P t i) y).val := by
  let C := (kernelCover E P).pullback₁ e
  apply factor_of_cover _ _ C
  intro j
  have hh := E.law.mul_natural t (C.f j ≫ t) (C.f j) rfl (multipleAt E P t i) y
  rw [multipleAt_natural, kernel_local_point E hn P t y e he j,
    multipleAt_mul E hn P] at hh
  obtain ⟨z, hz⟩ := multipleAt_factors E hn P (C.f j ≫ t)
    ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩
  exact ⟨z, hz.trans (congrArg Subtype.val hh).symm⟩

/-- The actual ideal subscheme is closed under the source group operation on
all scheme-valued points. This supplies the subgroup hypothesis for a scheme
quotient theorem, including on disconnected and nonreduced test schemes. -/
lemma kernel_mul_closed {T : Scheme.{u}} (t : T ⟶ Base R)
    (x y : SchemeHomOver t (E.projection))
    (hx : ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = x.val)
    (hy : ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = y.val) :
    ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = (E.law.mul t x y).val := by
  obtain ⟨e, he⟩ := hx
  obtain ⟨d, hd⟩ := hy
  let C := (kernelCover E P).pullback₁ e
  apply factor_of_cover _ _ C
  intro i
  let yi := GoodReductionJacobian.schemeHomOverComp (C.f i) rfl y
  have hh := E.law.mul_natural t (C.f i ≫ t) (C.f i) rfl x y
  rw [kernel_local_point E hn P t x e he i] at hh
  obtain ⟨z, hz⟩ := kernel_mul_multiple E hn P (C.f i ≫ t) i yi (C.f i ≫ d)
    (by change (C.f i ≫ d) ≫ _ = C.f i ≫ y.val; rw [Category.assoc, hd])
  exact ⟨z, hz.trans (congrArg Subtype.val hh).symm⟩

lemma kernel_inv_closed {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (E.projection))
    (hx : ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = x.val) :
    ∃ e : T ⟶ (kernelIdeal E P).subscheme,
      e ≫ (kernelIdeal E P).subschemeι = (E.law.inv t x).val := by
  obtain ⟨e, he⟩ := hx
  let C := (kernelCover E P).pullback₁ e
  apply factor_of_cover _ _ C
  intro i
  let ti := C.f i ≫ t
  let xi := GoodReductionJacobian.schemeHomOverComp (C.f i) rfl x
  have hx' : xi = multipleAt E P ti i := kernel_local_point E hn P t x e he i
  have hinv : GoodReductionJacobian.schemeHomOverComp (C.f i) rfl (E.law.inv t x) = E.law.inv ti xi := by
    letI := E.law.pointGroup ti
    have hh := E.law.mul_natural t ti (C.f i) rfl (E.law.inv t x) x
    rw [E.law.inv_mul_cancel, E.law.one_natural] at hh
    exact eq_inv_of_mul_eq_one_left hh.symm
  rw [hx', multipleAt_inv E hn P] at hinv
  obtain ⟨z, hz⟩ := multipleAt_factors E hn P ti
    ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩
  exact ⟨z, hz.trans (congrArg Subtype.val hinv).symm⟩

end Kernel


/-- A finite set in a single base fiber lies in a genuine affine open of the
original curve: use one Cartesian Weierstrass chart, then its projective embedding. -/
lemma affine_fiber_set (A : Atlas R E) (x : Base R) (Z : Set E.curve)
    (hZ : Z.Finite) (hbase : ∀ z ∈ Z, E.projection z = x) :
    ∃ U : E.curve.Opens, IsAffineOpen U ∧ Z ⊆ U := by
  classical
  obtain ⟨i, y, hy⟩ := A.covers x
  let C := A.chart i
  letI := C.openImmersion
  letI : IsOpenImmersion C.comparison.map :=
    MorphismProperty.of_isPullback C.comparison.cartesian.flip (show
      IsOpenImmersion (baseMap R C.ring C.comparison.scalar) from inferInstance)
  have hlift (z : E.curve) (hz : z ∈ Z) : ∃ w, C.comparison.map w = z := by
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback C.comparison.cartesian z y
      ((hbase z hz).trans hy.symm)
    exact ⟨w, hw⟩
  have hpre : (C.comparison.map ⁻¹' Z).Finite :=
    Set.Finite.preimage C.comparison.map.isOpenEmbedding.injective.injOn hZ
  obtain ⟨V, hV, hmem⟩ := exists_isAffineOpen_forall_mem_of_isImmersion_proj
    (WeierstrassProjModel.projModelGradingCR C.equation.toProjective)
    (𝟙 (Curve C.ring C.equation)) hpre.toFinset
  refine ⟨C.comparison.map ''ᵁ V, hV.image_of_isOpenImmersion _, ?_⟩
  intro z hz
  obtain ⟨w, hw⟩ := hlift z hz
  exact ⟨w, hmem w (hpre.mem_toFinset.mpr (by change C.comparison.map w ∈ Z; rw [hw]; exact hz)), hw⟩

lemma affine_orbit (A : Atlas R E) {n : ℕ} (P : Cyclic E n) (x : E.curve) :
    ∃ U : E.curve.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback ((kernelIdeal E P).subschemeι ≫ E.projection) E.projection),
        (pullback.snd ((kernelIdeal E P).subschemeι ≫ E.projection) E.projection) r = x → (E.law.action (kernelIdeal E P).subschemeι) r ∈ U := by
  let ι := (kernelIdeal E P).subschemeι
  let s := pullback.snd (ι ≫ E.projection) E.projection
  let t := E.law.action ι
  letI : IsFinite (ι ≫ E.projection) := (split_kernel E P).1
  have hZ : (t '' (s ⁻¹' {x})).Finite := (s.finite_preimage_singleton x).image t
  have hb : ∀ z ∈ t '' (s ⁻¹' {x}), E.projection z = E.projection x := by
    rintro _ ⟨r, hr, rfl⟩
    change (t ≫ E.projection) r = E.projection x
    rw [E.law.action_over]
    change E.projection (s r) = E.projection x
    exact congrArg E.projection hr
  obtain ⟨U, hU, hZU⟩ := affine_fiber_set E A (E.projection x) _ hZ hb
  exact ⟨U, hU, fun r hr => hZU ⟨r, hr, rfl⟩⟩


lemma geometry : GoodReductionJacobian.AbelianSchemePropertyBundle R E.projection := by
  letI := E.smooth
  letI := E.proper
  letI := E.connected
  exact ⟨inferInstance, inferInstance, fun x => E.projection.isConnected_preimage_singleton x,
    ⟨E.law⟩⟩

section Construction
variable {n : ℕ} (hn : 0 < n) (P : Cyclic E n)
include hn
theorem scheme_quotient_exists (A : Atlas R E) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Base R) (H : GoodReductionJacobian.RelativeGroupLaw R g)
      (p : E.curve ⟶ Y) (hp : p ≫ g = E.projection)
      (w : pullback.snd ((kernelIdeal E P).subschemeι ≫ E.projection)
          (E.projection) ≫ p =
        E.law.action (kernelIdeal E P).subschemeι ≫ p),
      GoodReductionJacobian.AbelianSchemePropertyBundle R g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t g),
        H.mul t x y = H.mul t y x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t (E.projection)),
        (⟨(E.law.mul t x y).val ≫ p, by rw [Category.assoc, hp, (E.law.mul t x y).property]⟩ :
          SchemeHomOver t g) = H.mul t
            ⟨x.val ≫ p, by rw [Category.assoc, hp, x.property]⟩
            ⟨y.val ≫ p, by rw [Category.assoc, hp, y.property]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x : SchemeHomOver t (E.projection)),
        (⟨x.val ≫ p, by rw [Category.assoc, hp, x.property]⟩ : SchemeHomOver t g) = H.one t ↔
          ∃ e : T ⟶ (kernelIdeal E P).subscheme,
            e ≫ (kernelIdeal E P).subschemeι = x.val) ∧
      IsPullback (pullback.snd ((kernelIdeal E P).subschemeι ≫ E.projection)
          (E.projection))
        (E.law.action (kernelIdeal E P).subschemeι) p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  letI : IsFinite ((kernelIdeal E P).subschemeι ≫ E.projection) := (split_kernel E P).1
  letI : Etale ((kernelIdeal E P).subschemeι ≫ E.projection) := (split_kernel E P).2.1
  exact E.law.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
    (geometry E) E.commutative (kernelIdeal E P).subschemeι
    (fun t => kernel_one_closed E hn P t)
    (fun t x y hx hy => kernel_mul_closed E hn P t x y hx hy)
    (fun t x hx => kernel_inv_closed E hn P t x hx)
    (affine_orbit E A P)
lemma kernel_finrank (x : Base R) :
    ((kernelIdeal E P).subschemeι ≫ E.projection).finrank x = n := by
  letI : Nontrivial R := x.nontrivial
  obtain ⟨hf, he, e, hw, _⟩ := split_kernel E P
  letI : IsFinite (splitStructure R n) := ArithmeticThetaRelativeCyclicQuotientR0173.SplitCyclicKernelR0173.split_finite R n
  letI : Etale (splitStructure R n) := ArithmeticThetaRelativeCyclicQuotientR0173.SplitCyclicKernelR0173.split_etale R n
  rw [← hw, Scheme.Hom.finrank_comp_left_of_isIso]
  change (Spec.map (CommRingCat.ofHom (algebraMap R (Fin n → R)))).finrank x = n
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simp

/-- Every finite-flat quotient with the constructed action relation is étale,
and its rank is exactly the number of labeled kernel components. -/
lemma quotient_etale_finrank {Y : Scheme.{u}} (p : E.curve ⟶ Y)
    [IsFinite p] [Flat p] [Surjective p]
    (hrel : IsPullback
      (pullback.snd ((kernelIdeal E P).subschemeι ≫ E.projection) (E.projection))
      (E.law.action (kernelIdeal E P).subschemeι) p p) :
    Etale p ∧ ∀ y, p.finrank y = n := by
  have hk := split_kernel E P
  letI : IsFinite ((kernelIdeal E P).subschemeι ≫ E.projection) := hk.1
  letI : Etale ((kernelIdeal E P).subschemeι ≫ E.projection) := hk.2.1
  refine ⟨?_, ?_⟩
  · exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hrel ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  · intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hrel.flip,
      Scheme.Hom.finrank_pullback_snd]
    exact kernel_finrank E hn P _

/-- An intermediate scheme quotient with its exact kernel functor. -/
structure SchemeQuotient where
  target : Scheme.{u}
  structureMap : target ⟶ Base R
  law : GoodReductionJacobian.RelativeGroupLaw R structureMap
  map : E.curve ⟶ target
  over_eq : map ≫ structureMap = E.projection
  geometry : GoodReductionJacobian.AbelianSchemePropertyBundle R structureMap
  commutative : ∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t structureMap),
    law.mul t x y = law.mul t y x
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  degree : ∀ y, map.finrank y = n
  preserves_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Base R)
    (x y : SchemeHomOver t (E.projection)),
    (⟨(E.law.mul t x y).val ≫ map, by rw [Category.assoc, over_eq, (E.law.mul t x y).property]⟩ :
      SchemeHomOver t structureMap) = law.mul t
        ⟨x.val ≫ map, by rw [Category.assoc, over_eq, x.property]⟩
        ⟨y.val ≫ map, by rw [Category.assoc, over_eq, y.property]⟩
  kernel : ∀ {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (E.projection)),
    (⟨x.val ≫ map, by rw [Category.assoc, over_eq, x.property]⟩ : SchemeHomOver t structureMap) =
      law.one t ↔ ∃ e : T ⟶ (kernelIdeal E P).subscheme,
        e ≫ (kernelIdeal E P).subschemeι = x.val

/-- No quotient map or target is assumed: all intermediate data are constructed. -/
theorem schemeQuotient_nonempty (A : Atlas R E) : Nonempty (SchemeQuotient E P) := by
  obtain ⟨Y, g, H, p, hp, w, hg, hcomm, hf, hflat, hfp, hsurj, hmul, hker, hrel, hcoeq⟩ :=
    scheme_quotient_exists E hn P A
  letI := hf
  letI := hflat
  letI := hsurj
  have het := quotient_etale_finrank E hn P p hrel
  exact ⟨⟨Y, g, H, p, hp, hg, hcomm, hf, het.1, hsurj, het.2, hmul, hker⟩⟩

end Construction


namespace SchemeQuotient
variable {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P)
include hn
/-- The quotient origin is its group identity section. -/
def zero : Base R ⟶ Q.target := (Q.law.one (𝟙 _)).val

lemma zero_over : Q.zero E P ≫ Q.structureMap = 𝟙 _ := (Q.law.one (𝟙 _)).property

lemma one_val {T : Scheme.{u}} (t : T ⟶ Base R) :
    (Q.law.one t).val = t ≫ Q.zero E P :=
  (congrArg Subtype.val (Q.law.one_natural (𝟙 _) t t (Category.comp_id t))).symm

lemma map_origin : ArithmeticThetaOpenHodgeR0180.zero E ≫ Q.map = Q.zero E P := by
  have h := (Q.kernel (𝟙 _) (E.law.one (𝟙 _))).mpr (kernel_one_closed E hn P (𝟙 _))
  have hv := congrArg Subtype.val h
  exact hv

lemma kernel_square : (kernelIdeal E P).subschemeι ≫ Q.map =
    ((kernelIdeal E P).subschemeι ≫ E.projection) ≫
      Q.zero E P := by
  let t := (kernelIdeal E P).subschemeι ≫ E.projection
  let x : SchemeHomOver t (E.projection) :=
    ⟨(kernelIdeal E P).subschemeι, rfl⟩
  have h := (Q.kernel t x).mpr ⟨𝟙 _, Category.id_comp _⟩
  exact (congrArg Subtype.val h).trans (Q.one_val E hn P t)

lemma kernel_pullback : IsPullback (kernelIdeal E P).subschemeι
    ((kernelIdeal E P).subschemeι ≫ E.projection)
    Q.map (Q.zero E P) := by
  let ι := (kernelIdeal E P).subschemeι
  let π := E.projection
  have hs (s : PullbackCone Q.map (Q.zero E P)) : s.fst ≫ π = s.snd := by
    have h := congrArg (fun f => f ≫ Q.structureMap) s.condition
    simpa only [Category.assoc, Q.over_eq, Q.zero_over E hn P, Category.comp_id] using h
  have hfac (s : PullbackCone Q.map (Q.zero E P)) : ∃ e : s.pt ⟶ _, e ≫ ι = s.fst := by
    apply (Q.kernel s.snd ⟨s.fst, hs s⟩).mp
    apply Subtype.ext
    exact s.condition.trans (Q.one_val E hn P s.snd).symm
  choose lift hlift using hfac
  apply IsPullback.of_isLimit (c := PullbackCone.mk ι (ι ≫ π) (Q.kernel_square E hn P))
  refine PullbackCone.IsLimit.mk _ lift hlift ?_ ?_
  · intro s
    rw [← Category.assoc, hlift, hs]
  · intro s m hm _
    exact (cancel_mono ι).mp (hm.trans (hlift s).symm)

/-- Exact equality of ideal sheaves, derived from the actual Cartesian
kernel square rather than only equality of closed-point sets. -/
lemma kernel_ideal : (Q.zero E P).ker.comap Q.map = kernelIdeal E P := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  have : IsClosedImmersion (Q.zero E P) := by
    have : IsClosedImmersion (Q.zero E P ≫ Q.structureMap) := by
      rw [Q.zero_over E hn P]; infer_instance
    exact IsClosedImmersion.of_comp _ Q.structureMap
  let h := Q.kernel_pullback E hn P
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]
  exact (kernelIdeal E P).ker_subschemeι

/-- Relative dimension descends along the actual finite étale quotient map. -/
lemma smooth_dimension_one : SmoothOfRelativeDimension 1 Q.structureMap := by
  letI : Etale Q.map := Q.etale
  letI : Surjective Q.map := Q.surjective
  letI : Smooth Q.structureMap := Q.geometry.smooth
  classical
  cases isEmpty_or_nonempty E.curve with
  | inl he =>
    letI := he
    exact ⟨fun y => by obtain ⟨x, _⟩ := Q.map.surjective y; exact isEmptyElim x⟩
  | inr he =>
    letI := he
    haveI : SmoothOfRelativeDimension 1 (Q.map ≫ Q.structureMap) := by
      rw [Q.over_eq]
      exact E.smooth
    exact (SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
      Q.map Q.structureMap 1 0).1
  
  
end SchemeQuotient


namespace SchemeQuotient
variable {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P)

abbrev family : EllipticFamily R where
  curve := Q.target
  projection := Q.structureMap
  law := Q.law
  commutative := Q.commutative
  proper := Q.geometry.proper
  smooth := Q.smooth_dimension_one E hn P
  connected := ⟨by
    intro K _ a V fst snd hpb
    letI : IsIntegral V := Q.geometry.geometricallyIntegral_of_commRing.1 a fst snd hpb
    infer_instance⟩

abbrev arrow : Pointed R E (Q.family E hn P) where
  map := Q.map
  over_eq := Q.over_eq
  zero_eq := Q.map_origin E hn P

lemma arrow_hom : IsHom (Q.arrow E hn P) := fun _ t x y => Q.preserves_mul t x y
end SchemeQuotient

variable {H : EllipticFamily R}

/-- The induced homomorphism uses the actual point groups and pointed morphism. -/
def pointHom (f : Pointed R E H) (hf : IsHom f) {T : Scheme.{u}} (t : T ⟶ Base R) :
    letI := E.law.pointGroup t
    letI := H.law.pointGroup t
    SchemeHomOver t E.projection →* SchemeHomOver t H.projection := by
  letI := E.law.pointGroup t
  letI := H.law.pointGroup t
  exact {
    toFun := imagePoint f t
    map_one' := by
      apply Subtype.ext
      have he := congrArg Subtype.val (E.law.one_natural (𝟙 _) t t (by simp))
      have hh := congrArg Subtype.val (H.law.one_natural (𝟙 _) t t (by simp))
      change (E.law.one t).val ≫ f.map = (H.law.one t).val
      change t ≫ zero E = (E.law.one t).val at he
      change t ≫ zero H = (H.law.one t).val at hh
      rw [← he, Category.assoc, f.zero_eq, hh]
    map_mul' := hf T t }

lemma kills_kernel {n : ℕ} (hn : 0 < n) (P : Cyclic E n)
    (f : Pointed R E H)
    (hf : ∀ i : Fin n, P.point ≫ E.law.schemeNsmul i.val ≫ f.map = zero H) :
    (kernelIdeal E P).subschemeι ≫ f.map =
      (kernelIdeal E P).subschemeι ≫ E.projection ≫ zero H := by
  apply (kernelCover E P).hom_ext
  intro i
  simp only [← Category.assoc]
  rw [kernelCover_component E hn P]
  rw [multiple_over]
  exact (hf i).trans (Category.id_comp _).symm

lemma same_fiber {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P)
    (f : Pointed R E H) (hf : IsHom f)
    (hkill : ∀ i : Fin n, P.point ≫ E.law.schemeNsmul i.val ≫ f.map = zero H)
    {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t E.projection)
    (hxy : x.val ≫ Q.map = y.val ≫ Q.map) : x.val ≫ f.map = y.val ≫ f.map := by
  letI := E.law.pointGroup t
  letI := Q.law.pointGroup t
  letI := H.law.pointGroup t
  let q := pointHom E (Q.arrow E hn P) (Q.arrow_hom E hn P) t
  let a := pointHom E f hf t
  have hq : q x = q y := Subtype.ext hxy
  have hd : q (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨k, hk⟩ := (Q.kernel t (x * y⁻¹)).mp hd
  have ha : a (x * y⁻¹) = 1 := by
    apply Subtype.ext
    change (x * y⁻¹).val ≫ f.map = (H.law.one t).val
    rw [← hk, Category.assoc, kills_kernel E hn P f hkill,
      ← Category.assoc, ← Category.assoc, hk, (x * y⁻¹).property]
    exact congrArg Subtype.val (H.law.one_natural (𝟙 _) t t (Category.comp_id t))
  have hh : a x = a y := mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using ha)
  exact congrArg Subtype.val hh

/-- Faithfully flat descent first constructs the unique actual pointed morphism.
The group-law compatibility is proved separately on a common covering. -/
lemma pointed_factor {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P)
    (f : Pointed R E H) (hf : IsHom f)
    (hkill : ∀ i : Fin n, P.point ≫ E.law.schemeNsmul i.val ≫ f.map = zero H) :
    ∃! g : Pointed R (Q.family E hn P) H, Q.map ≫ g.map = f.map := by
  letI := Q.etale
  letI := Q.surjective
  have hd : ∀ {T : Scheme.{u}} (x y : T ⟶ E.curve),
      x ≫ Q.map = y ≫ Q.map → x ≫ f.map = y ≫ f.map := by
    intro T x y hxy
    have hy : y ≫ E.projection = x ≫ E.projection := by
      rw [← Q.over_eq, ← Category.assoc, ← Category.assoc, hxy]
    exact same_fiber E hn P Q f hf hkill (x ≫ E.projection) ⟨x, rfl⟩ ⟨y, hy⟩ hxy
  let b := EffectiveEpi.desc Q.map f.map hd
  have hb : Q.map ≫ b = f.map := EffectiveEpi.fac _ _ _
  have hover : b ≫ H.projection = Q.structureMap := by
    apply (cancel_epi Q.map).mp
    rw [← Category.assoc, hb, f.over_eq, Q.over_eq]
  have horigin : zero (Q.family E hn P) ≫ b = zero H := by
    rw [← (Q.arrow E hn P).zero_eq, Category.assoc]
    exact (congrArg (fun z => zero E ≫ z) hb).trans f.zero_eq
  refine ⟨⟨b, hover, horigin⟩, hb, ?_⟩
  intro c hc
  have he : c.map = b := (cancel_epi Q.map).mp (hc.trans hb.symm)
  cases c
  subst he
  rfl


/-- Homomorphism identities descend along the actual étale surjection by
lifting both arbitrary test points to one common faithfully flat cover. -/
lemma hom_desc {F H : EllipticFamily R} (q : Pointed R E F)
    (hq : IsHom q) [Etale q.map] [Surjective q.map]
    (f : Pointed R E H) (hf : IsHom f) (g : Pointed R F H)
    (hfg : q.map ≫ g.map = f.map) : IsHom g := by
  intro T t x y
  let e₁ := pullback.snd q.map x.val
  let e₂ := pullback.snd q.map (e₁ ≫ y.val)
  let β := e₂ ≫ e₁
  have hβ : Epi β := inferInstance
  let a : SchemeHomOver (β ≫ t) E.projection := ⟨e₂ ≫ pullback.fst q.map x.val, by
    simp only [← q.over_eq, Category.assoc, pullback.condition_assoc, x.property]
    rfl⟩
  let b : SchemeHomOver (β ≫ t) E.projection := ⟨pullback.fst q.map (e₁ ≫ y.val), by
    rw [← q.over_eq, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, y.property]
    rfl⟩
  have ha : a.val ≫ q.map = β ≫ x.val := by
    change (e₂ ≫ pullback.fst q.map x.val) ≫ q.map = _
    rw [Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm
  have hb : b.val ≫ q.map = β ≫ y.val := by
    change pullback.fst q.map (e₁ ≫ y.val) ≫ q.map = _
    rw [pullback.condition]
    exact (Category.assoc _ _ _).symm
  have hax : imagePoint q (β ≫ t) a = GoodReductionJacobian.schemeHomOverComp β rfl x :=
    Subtype.ext ha
  have hby : imagePoint q (β ≫ t) b = GoodReductionJacobian.schemeHomOverComp β rfl y :=
    Subtype.ext hb
  have hnF := congrArg Subtype.val (F.law.mul_natural t (β ≫ t) β rfl x y)
  have hnH := congrArg Subtype.val (H.law.mul_natural t (β ≫ t) β rfl
    (imagePoint g t x) (imagePoint g t y))
  have habF := congrArg Subtype.val (hq _ (β ≫ t) a b)
  rw [hax, hby] at habF
  change (E.law.mul (β ≫ t) a b).val ≫ q.map = _ at habF
  have haH : imagePoint f (β ≫ t) a =
      GoodReductionJacobian.schemeHomOverComp β rfl (imagePoint g t x) := by
    apply Subtype.ext
    change a.val ≫ f.map = β ≫ (x.val ≫ g.map)
    rw [← hfg, ← Category.assoc, ha, Category.assoc]
  have hbH : imagePoint f (β ≫ t) b =
      GoodReductionJacobian.schemeHomOverComp β rfl (imagePoint g t y) := by
    apply Subtype.ext
    change b.val ≫ f.map = β ≫ (y.val ≫ g.map)
    rw [← hfg, ← Category.assoc, hb, Category.assoc]
  have habH := congrArg Subtype.val (hf _ (β ≫ t) a b)
  rw [haH, hbH] at habH
  change (E.law.mul (β ≫ t) a b).val ≫ f.map = _ at habH
  apply Subtype.ext
  apply (cancel_epi β).mp
  change β ≫ (F.law.mul t x y).val ≫ g.map =
    β ≫ (H.law.mul t (imagePoint g t x) (imagePoint g t y)).val
  change β ≫ (F.law.mul t x y).val = _ at hnF
  change β ≫ (H.law.mul t (imagePoint g t x) (imagePoint g t y)).val = _ at hnH
  calc
    _ = (β ≫ (F.law.mul t x y).val) ≫ g.map := (Category.assoc _ _ _).symm
    _ = ((E.law.mul (β ≫ t) a b).val ≫ q.map) ≫ g.map :=
      congrArg (fun z => z ≫ g.map) (hnF.trans habF.symm)
    _ = (E.law.mul (β ≫ t) a b).val ≫ f.map := by rw [Category.assoc, hfg]
    _ = _ := habH.trans hnH.symm

def completeQuotient {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P) :
    Quotient R E n P.point := by
  refine {
    target := Q.family E hn P
    arrow := Q.arrow E hn P
    hom := Q.arrow_hom E hn P
    finite := Q.finite
    etale := Q.etale
    surjective := Q.surjective
    degree := Q.degree
    kernel := Q.kernel_ideal E hn P
    universal := ?_ }
  intro H f hf hkill
  obtain ⟨g, hg, huniq⟩ := pointed_factor E hn P Q f hf hkill
  letI := Q.etale
  letI := Q.surjective
  have hgh : IsHom g := hom_desc E (Q.arrow E hn P) (Q.arrow_hom E hn P) f hf g hg
  exact ⟨g, ⟨hgh, hg⟩, fun g' hg' => huniq g' hg'.2⟩


lemma quotient_kills {n : ℕ} (hn : 0 < n) (P : Cyclic E n) (Q : SchemeQuotient E P)
    (i : Fin n) : P.point ≫ E.law.schemeNsmul i.val ≫ Q.map = zero (Q.family E hn P) := by
  have h := congrArg (fun f => (kernelCover E P).f i ≫ f) (Q.kernel_square E hn P)
  simp only [← Category.assoc, kernelCover_component E hn P, multiple_over] at h
  change multiple E P i ≫ Q.map = 𝟙 (Base R) ≫ Q.zero E P at h
  rw [Category.id_comp] at h
  exact h

/-- Recover the all-test-schemes kernel functor from the actual ideal equality. -/
def of_kernel {n : ℕ} (hn : 0 < n) (P : Cyclic E n) {H : EllipticFamily R}
    (f : Pointed R E H) (hf : IsHom f) (hfin : IsFinite f.map) (het : Etale f.map)
    (hsurj : Surjective f.map) (hdeg : ∀ y, f.map.finrank y = n)
    (hker : (zero H).ker.comap f.map = kernelIdeal E P)
    (hkill : ∀ i : Fin n, P.point ≫ E.law.schemeNsmul i.val ≫ f.map = zero H) :
    SchemeQuotient E P where
  target := H.curve
  structureMap := H.projection
  law := H.law
  map := f.map
  over_eq := f.over_eq
  geometry := geometry H
  commutative := H.commutative
  finite := hfin
  etale := het
  surjective := hsurj
  degree := hdeg
  preserves_mul := fun t x y => hf _ t x y
  kernel := by
    letI := H.proper
    haveI : IsClosedImmersion (zero H) :=
      ArithmeticThetaRelativeCyclicQuotientR0173.CyclicQuotientArbitraryBaseChangeR0173.section_closed
        H.projection (zero H) (H.law.one (𝟙 _)).property
    have hp := isPullback_of_isClosedImmersion (kernelIdeal E P).subschemeι (zero H)
      ((kernelIdeal E P).subschemeι ≫ E.projection) f.map
      (kills_kernel E hn P f hkill) (by rw [(kernelIdeal E P).ker_subschemeι]; exact hker)
    intro T t x
    have hone : (H.law.one t).val = t ≫ zero H :=
      (congrArg Subtype.val (H.law.one_natural (𝟙 _) t t (Category.comp_id t))).symm
    constructor
    · intro h
      have hx : x.val ≫ f.map = t ≫ zero H := (congrArg Subtype.val h).trans hone
      exact ⟨hp.lift x.val t hx, hp.lift_fst _ _ _⟩
    · rintro ⟨e, he⟩
      apply Subtype.ext
      change x.val ≫ f.map = (H.law.one t).val
      rw [hone, ← he, Category.assoc, hp.w, ← Category.assoc, ← Category.assoc,
        he, x.property]

/-- Uniqueness gives the actual pointed isomorphism between any two constructed
quotients of the same cyclic sections, hence the transition maps and cocycle. -/
lemma quotient_iso {n : ℕ} (hn : 0 < n) (P : Cyclic E n)
    (Q Q' : SchemeQuotient E P) :
    ∃ e : Q.target ≅ Q'.target, Q.map ≫ e.hom = Q'.map ∧
      e.hom ≫ Q'.structureMap = Q.structureMap ∧
      zero (Q.family E hn P) ≫ e.hom = zero (Q'.family E hn P) := by
  obtain ⟨a, ha, _⟩ := pointed_factor E hn P Q (Q'.arrow E hn P)
    (Q'.arrow_hom E hn P) (quotient_kills E hn P Q')
  obtain ⟨b, hb, _⟩ := pointed_factor E hn P Q' (Q.arrow E hn P)
    (Q.arrow_hom E hn P) (quotient_kills E hn P Q)
  letI := Q.etale
  letI := Q.surjective
  letI := Q'.etale
  letI := Q'.surjective
  have hab : a.map ≫ b.map = 𝟙 _ := by
    apply (cancel_epi Q.map).mp
    rw [← Category.assoc, ha, hb, Category.comp_id]
  have hba : b.map ≫ a.map = 𝟙 _ := by
    apply (cancel_epi Q'.map).mp
    rw [← Category.assoc, hb, ha, Category.comp_id]
  exact ⟨⟨a.map, b.map, hab, hba⟩, ha, a.over_eq, a.zero_eq⟩

open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree (toGRJ)

abbrev weierstrassFamily [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : EllipticFamily R where
  curve := Curve R W
  projection := structureMap R W
  law := toGRJ G
  commutative := hG.2
  proper := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  smooth := WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  connected := ⟨by
    intro K _ a V fst snd hpb
    letI : IsIntegral V := (relative_curve_geometry R W).2.2.2.2.2.2.1 a fst snd hpb
    infer_instance⟩

abbrev baseChangeFamily {S : Type u} [CommRing S] (F : EllipticFamily S) (b : Base R ⟶ Base S) :
    EllipticFamily R := by
  letI := F.proper
  letI := F.smooth
  letI := F.connected
  exact {
    curve := pullback F.projection b
    projection := pullback.snd F.projection b
    law := F.law.baseChange b
    commutative := GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange b F.commutative
    proper := inferInstance
    smooth := inferInstance
    connected := inferInstance }

lemma baseChange_zero {S : Type u} [CommRing S] (F : EllipticFamily S) (b : Base R ⟶ Base S) :
    zero (baseChangeFamily F b) ≫ pullback.fst F.projection b = b ≫ zero F := by
  change (pullback.lift (F.law.one (𝟙 _ ≫ b)).val (𝟙 _) _ ≫ pullback.fst F.projection b) = _
  rw [pullback.lift_fst, Category.id_comp]
  exact (congrArg Subtype.val (F.law.one_natural (𝟙 _) b b (by simp))).symm


lemma pointed_hom [IsDomain R] {H : EllipticFamily R} (f : Pointed R E H) : IsHom f := by
  letI := E.smooth
  letI := E.proper
  letI := H.smooth
  letI := H.proper
  letI := (geometry E).geometricallyIntegral_of_commRing
  letI := (geometry H).geometricallyIntegral_of_commRing
  have ho {T : Scheme.{u}} (t : T ⟶ Base R) :
      NeronModelInfra.schemeHomOverComp (E.law.one t) ⟨f.map, f.over_eq⟩ = H.law.one t := by
    apply Subtype.ext
    have he := congrArg Subtype.val (E.law.one_natural (𝟙 _) t t (by simp))
    have hh := congrArg Subtype.val (H.law.one_natural (𝟙 _) t t (by simp))
    change (E.law.one t).val ≫ f.map = (H.law.one t).val
    change t ≫ zero E = (E.law.one t).val at he
    change t ≫ zero H = (H.law.one t).val at hh
    rw [← he, Category.assoc, f.zero_eq, hh]
  intro T t x y
  apply Subtype.ext
  exact ArithmeticThetaRelativeCyclicQuotientR0173.PointedRelativeGroupHom.relative_rigidity
    E.law H.law ⟨f.map, f.over_eq⟩ ho t x y

variable (C : Chart S F) {n : ℕ} (P : Cyclic F n)

abbrev chartFamily := weierstrassFamily C.equation C.law C.originLaw

lemma chart_zero : zero (chartFamily C) = origin C.ring C.equation := by
  exact (C.originLaw.1 (𝟙 _)).trans (Category.id_comp _)

abbrev chartCyclic : Cyclic (chartFamily C) n where
  point := (testCyclic C.comparison P).point
  over_eq := (testCyclic C.comparison P).over_eq
  killed := by
    change (testCyclic C.comparison P).point ≫ C.law.schemeNsmul n = _
    rw [(testCyclic C.comparison P).killed, chart_zero]
  disjoint := (testCyclic C.comparison P).disjoint

/-- The exact r0174 scheme quotient, retaining its map and all group operations. -/
def acceptedChartQuotient (hn : 0 < n) : SchemeQuotient (chartFamily C) (chartCyclic C P) := by
  let Q := Classical.choice
    (ArithmeticThetaRelativeCyclicQuotientR0173.FramedSchemeQuotientR0174.schemeQuotient_nonempty
      C.ring C.equation C.law C.originLaw hn (testCyclic C.comparison P))
  exact {
    target := Q.target
    structureMap := Q.structureMap
    law := Q.law
    map := Q.map
    over_eq := Q.over_eq
    geometry := Q.geometry
    commutative := Q.commutative
    finite := Q.finite
    etale := Q.etale
    surjective := Q.surjective
    degree := Q.degree
    preserves_mul := Q.preserves_mul
    kernel := Q.kernel }


abbrev restrictedArrow (hn : 0 < n) (Q : SchemeQuotient F P) :
    Pointed C.ring (chartFamily C)
      (baseChangeFamily (Q.family F hn P) (baseMap S C.ring C.comparison.scalar)) := by
  let b := baseMap S C.ring C.comparison.scalar
  let q := pullback.lift (f := Q.structureMap) (g := b)
    (C.comparison.map ≫ Q.map) (structureMap C.ring C.equation)
    (by rw [Category.assoc, Q.over_eq]; exact C.comparison.cartesian.w)
  refine ⟨q, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · change (zero (chartFamily C) ≫ q) ≫ pullback.fst Q.structureMap b =
      zero (baseChangeFamily (Q.family F hn P) b) ≫ pullback.fst Q.structureMap b
    rw [Category.assoc, pullback.lift_fst, chart_zero, ← Category.assoc,
      C.comparison.origin_eq, Category.assoc, Q.map_origin F hn P, baseChange_zero]
    rfl
  · rw [Category.assoc, pullback.lift_snd]
    exact (chartFamily C).law.one (𝟙 _) |>.property.trans
      ((baseChangeFamily (Q.family F hn P) b).law.one (𝟙 _)).property.symm

lemma restrictedCartesian (hn : 0 < n) (Q : SchemeQuotient F P) :
    IsPullback C.comparison.map (restrictedArrow C P hn Q).map Q.map
      (pullback.fst Q.structureMap (baseMap S C.ring C.comparison.scalar)) := by
  have houter : IsPullback C.comparison.map
      ((restrictedArrow C P hn Q).map ≫
        pullback.snd Q.structureMap (baseMap S C.ring C.comparison.scalar))
      (Q.map ≫ Q.structureMap) (baseMap S C.ring C.comparison.scalar) := by
    rw [(restrictedArrow C P hn Q).over_eq, Q.over_eq]
    exact C.comparison.cartesian
  exact houter.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

lemma restrictedKernel (hn : 0 < n) (Q : SchemeQuotient F P) :
    (zero (baseChangeFamily (Q.family F hn P) (baseMap S C.ring C.comparison.scalar))).ker.comap
      (restrictedArrow C P hn Q).map = kernelIdeal (chartFamily C) (chartCyclic C P) := by
  let b := baseMap S C.ring C.comparison.scalar
  let H := baseChangeFamily (Q.family F hn P) b
  let f := restrictedArrow C P hn Q
  letI := F.proper
  letI := Q.geometry.proper
  letI : IsClosedImmersion (zero (Q.family F hn P)) :=
    ArithmeticThetaRelativeCyclicQuotientR0173.CyclicQuotientArbitraryBaseChangeR0173.section_closed
      Q.structureMap (zero (Q.family F hn P)) (Q.law.one (𝟙 _)).property
  have ho : (zero (Q.family F hn P)).ker.comap (pullback.fst Q.structureMap b) = (zero H).ker :=
    ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange
      (ArithmeticThetaRelativeCyclicQuotientR0173.CyclicQuotientArbitraryBaseChangeR0173.section_pullback
        (IsPullback.of_hasPullback _ _) (zero (Q.family F hn P)) (zero H)
        (Q.law.one (𝟙 _)).property (H.law.one (𝟙 _)).property (baseChange_zero _ _))
  have hk : (kernelIdeal F P).comap C.comparison.map =
      kernelIdeal (chartFamily C) (chartCyclic C P) := by
    apply ArithmeticThetaRelativeCyclicQuotientR0173.CyclicQuotientArbitraryBaseChangeR0173.union_kernel_pullback
      C.comparison.cartesian (multiple F P) (multiple (chartFamily C) (chartCyclic C P))
      (multiple_over F P) (multiple_over (chartFamily C) (chartCyclic C P))
      (fun i => testCyclic_multiple C.comparison P i) P.disjoint
  change (zero H).ker.comap f.map = _
  have hker : (zero (Q.family F hn P)).ker.comap Q.map = kernelIdeal F P :=
    Q.kernel_ideal F hn P
  rw [← ho, ← Scheme.IdealSheafData.comap_comp, pullback.lift_fst,
    Scheme.IdealSheafData.comap_comp, hker, hk]

/-- The global map restricts to a quotient of precisely the transported local
cyclic section. All maps come from the two specified Cartesian squares. -/
abbrev restrictedQuotient (hn : 0 < n) (Q : SchemeQuotient F P) :
    SchemeQuotient (chartFamily C) (chartCyclic C P) := by
  let f := restrictedArrow C P hn Q
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  have hc := restrictedCartesian C P hn Q
  have hfin : IsFinite f.map := MorphismProperty.of_isPullback hc inferInstance
  have het : Etale f.map := MorphismProperty.of_isPullback hc inferInstance
  have hsurj : Surjective f.map := MorphismProperty.of_isPullback hc inferInstance
  apply of_kernel (chartFamily C) hn (chartCyclic C P) f (pointed_hom _ f) hfin het hsurj
    (fun y => (Scheme.Hom.finrank_of_isPullback _ _ _ _ hc y).trans (Q.degree _))
    (restrictedKernel C P hn Q)
  intro i
  apply pullback.hom_ext
  · change ((testCyclic C.comparison P).point ≫ C.law.schemeNsmul i.val ≫ f.map) ≫
      pullback.fst Q.structureMap (baseMap S C.ring C.comparison.scalar) = _
    calc
      _ = ((testCyclic C.comparison P).point ≫ C.law.schemeNsmul i.val ≫
          C.comparison.map) ≫ Q.map := by
        have hh : f.map ≫ pullback.fst Q.structureMap (baseMap S C.ring C.comparison.scalar) =
            C.comparison.map ≫ Q.map := hc.w.symm
        simp only [Category.assoc]
        rw [hh]
      _ = (baseMap S C.ring C.comparison.scalar ≫ P.point ≫ F.law.schemeNsmul i.val) ≫ Q.map :=
        congrArg (fun z => z ≫ Q.map) (testCyclic_multiple C.comparison P i)
      _ = baseMap S C.ring C.comparison.scalar ≫ zero (Q.family F hn P) := by
        rw [Category.assoc, Category.assoc, quotient_kills F hn P Q]
      _ = _ := (baseChange_zero _ _).symm
  · change ((chartCyclic C P).point ≫ (chartFamily C).law.schemeNsmul i.val ≫ f.map) ≫
      (baseChangeFamily (Q.family F hn P) (baseMap S C.ring C.comparison.scalar)).projection = _
    rw [Category.assoc, Category.assoc, f.over_eq, (chartFamily C).law.schemeNsmul_over,
      (chartCyclic C P).over_eq]
    exact ((baseChangeFamily (Q.family F hn P) (baseMap S C.ring C.comparison.scalar)).law.one (𝟙 _)).property.symm

/-- The actual r0174 quotient target identifies with the restriction of the
constructed global target, intertwining the quotient map, projection, and origin. -/
lemma local_quotient_gluing (hn : 0 < n) (Q : SchemeQuotient F P) :
    ∃ e : (acceptedChartQuotient C P hn).target ≅
        pullback Q.structureMap (baseMap S C.ring C.comparison.scalar),
      (acceptedChartQuotient C P hn).map ≫ e.hom = (restrictedArrow C P hn Q).map ∧
      e.hom ≫ pullback.snd Q.structureMap (baseMap S C.ring C.comparison.scalar) =
        (acceptedChartQuotient C P hn).structureMap ∧
      zero ((acceptedChartQuotient C P hn).family (chartFamily C) hn (chartCyclic C P)) ≫ e.hom =
        zero (baseChangeFamily (Q.family F hn P) (baseMap S C.ring C.comparison.scalar)) :=
  quotient_iso (chartFamily C) hn (chartCyclic C P)
    (acceptedChartQuotient C P hn) (restrictedQuotient C P hn Q)


/-- The r0174 local quotient maps form an actual open cover of the global
quotient, and their maps glue to the constructed global morphism. -/
lemma glued_scheme_quotient (A : Atlas R E) {m : ℕ} (hm : 0 < m) (Z : Cyclic E m) :
    ∃ Q : SchemeQuotient E Z,
      ∃ b : ∀ i : Fin A.count, (acceptedChartQuotient (A.chart i) Z hm).target ⟶ Q.target,
        (∀ i, IsOpenImmersion (b i) ∧
          (acceptedChartQuotient (A.chart i) Z hm).map ≫ b i = (A.chart i).comparison.map ≫ Q.map) ∧
        (∀ y : Q.target, ∃ i x, b i x = y) := by
  classical
  obtain ⟨Q⟩ := schemeQuotient_nonempty E hm Z A
  choose e he hproj hzero using fun i => local_quotient_gluing (A.chart i) Z hm Q
  let b (i : Fin A.count) := (e i).hom ≫
    pullback.fst Q.structureMap (baseMap R (A.chart i).ring (A.chart i).comparison.scalar)
  have hb (i : Fin A.count) :
      (acceptedChartQuotient (A.chart i) Z hm).map ≫ b i = (A.chart i).comparison.map ≫ Q.map := by
    dsimp only [b]
    rw [← Category.assoc, he]
    exact (restrictedCartesian (A.chart i) Z hm Q).w.symm
  refine ⟨Q, b, ?_, ?_⟩
  · intro i
    letI := (A.chart i).openImmersion
    exact ⟨inferInstance, hb i⟩
  · intro y
    letI := Q.surjective
    obtain ⟨x, rfl⟩ := Q.map.surjective y
    obtain ⟨i, z, hz⟩ := A.covers (E.projection x)
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (A.chart i).comparison.cartesian x z hz.symm
    refine ⟨i, (acceptedChartQuotient (A.chart i) Z hm).map w, ?_⟩
    change ((acceptedChartQuotient (A.chart i) Z hm).map ≫ b i) w = Q.map x
    rw [hb]
    exact congrArg Q.map hw

lemma quotient_nonempty (A : Atlas R E) {m : ℕ} (hm : 0 < m) (Z : Cyclic E m) :
    Nonempty (Quotient R E m Z.point) := by
  obtain ⟨Q, _b, _hglue, _hcover⟩ := glued_scheme_quotient E A hm Z
  exact ⟨completeQuotient E hm Z Q⟩

#print axioms local_quotient_gluing
#print axioms glued_scheme_quotient

end GlobalLevelCyclicQuotientR0180
open CategoryTheory AlgebraicGeometry ArithmeticThetaLegendreAtlasR0176

/-- The global cyclic quotient of the actual descended full-level family. -/
theorem global_level_cyclic_quotient
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (_hLeven : Even L)
    (A : LegendreAtlas k L) (m : ℕ) (hm : 0 < m) (hmL : m ∣ L) :
    Nonempty (Quotient A.quotient.ring (levelFamily k L A) m (kernelPoint k L A m)) := by
  obtain ⟨D⟩ := elliptic_family_weierstrass_atlas k A.quotient.ring A.quotient.smooth
    (levelFamily k L A)
  obtain ⟨P, hP⟩ := GlobalLevelCyclicQuotientR0180.cyclic_of_level
    (levelFamily k L A) (by omega : 0 < L) A.marking m hm hmL
  simpa only [hP, kernelPoint] using
    GlobalLevelCyclicQuotientR0180.quotient_nonempty (levelFamily k L A) D hm P

#print axioms global_level_cyclic_quotient
end ArithmeticThetaOpenHodgeR0180
