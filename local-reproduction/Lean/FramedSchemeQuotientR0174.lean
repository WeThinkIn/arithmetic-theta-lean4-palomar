import SplitCyclicKernelR0173
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isImmersion_proj
import CyclicPresentationDefinitionsR0174

/-! Construction of the cyclic scheme quotient and its Hodge frame.
Recovered draft arguments are checked here in a module-specific namespace. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
namespace FramedSchemeQuotientR0174
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeIsogenyHodgeR0172
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

/-- The given generator as a section in the actual relative point group. -/
def generator {n : ℕ} (P : CyclicSection R W G n) :
    SchemeHomOver (𝟙 (Base R)) (structureMap R W) := ⟨P.point, P.over_eq⟩

lemma nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (m : ℕ) :
    letI := G.pointGroup t
    G.nsmul t m x = x ^ m := by
  letI := G.pointGroup t
  induction m with
  | zero => rfl
  | succ m ih => rw [G.nsmul_succ, ih]; exact (pow_succ x m).symm

lemma multiple_over {n : ℕ} (P : CyclicSection R W G n) (i : Fin n) :
    multiple R W G P i ≫ structureMap R W = 𝟙 _ := by
  rw [multiple, Category.assoc, G.schemeNsmul_over, P.over_eq]

lemma multiple_eq_nsmul {n : ℕ} (P : CyclicSection R W G n) (i : Fin n) :
    multiple R W G P i = (G.nsmul (𝟙 _) i.val (generator R W G P)).val :=
  comp_schemeNsmul G (𝟙 _) (generator R W G P) i.val

lemma generator_killed (hG : IsOriginLaw R W G) {n : ℕ}
    (P : CyclicSection R W G n) :
    G.nsmul (𝟙 _) n (generator R W G P) = G.one (𝟙 _) := by
  apply Subtype.ext
  rw [← comp_schemeNsmul, hG.1]
  exact P.killed.trans (Category.id_comp _).symm

lemma nsmul_mod (hG : IsOriginLaw R W G) {n : ℕ}
    (P : CyclicSection R W G n) (m : ℕ) :
    G.nsmul (𝟙 _) (m % n) (generator R W G P) =
      G.nsmul (𝟙 _) m (generator R W G P) := by
  letI := G.pointGroup (𝟙 (Base R))
  have hk : generator R W G P ^ n = 1 := by
    rw [← nsmul_eq_pow]; exact generator_killed R W G hG P
  simp only [nsmul_eq_pow]
  calc generator R W G P ^ (m % n)
      = generator R W G P ^ (m % n) * (generator R W G P ^ n) ^ (m / n) := by
          rw [hk, one_pow, mul_one]
    _ = generator R W G P ^ (m % n + n * (m / n)) := by rw [pow_add, pow_mul]
    _ = generator R W G P ^ m := by rw [Nat.mod_add_div]

/-- Pullback of a section on all scheme-valued points, including nonreduced schemes. -/
def sectionAt {T : Scheme.{u}} (t : T ⟶ Base R)
    (p : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    SchemeHomOver t (structureMap R W) := schemeHomOverComp t (Category.comp_id t) p

/-- The translation isomorphism is constructed by the checked relative group-law theorem. -/
def translation (p : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    Curve R W ≅ Curve R W :=
  (G.exists_iso_comp_eq_and_comp_hom_eq_mul p).choose

lemma translation_over (p : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    (translation R W G p).hom ≫ structureMap R W = structureMap R W :=
  (G.exists_iso_comp_eq_and_comp_hom_eq_mul p).choose_spec.1

lemma comp_translation (p : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    {T : Scheme.{u}} (t : T ⟶ Base R) (x : SchemeHomOver t (structureMap R W)) :
    x.val ≫ (translation R W G p).hom = (G.mul t x (sectionAt R W t p)).val :=
  (G.exists_iso_comp_eq_and_comp_hom_eq_mul p).choose_spec.2 t x

lemma translation_one : (translation R W G (G.one (𝟙 _))).hom = 𝟙 _ := by
  have h := comp_translation R W G (G.one (𝟙 _)) (structureMap R W)
    (RelativeGroupLaw.idPoint (f := structureMap R W))
  simpa only [Category.id_comp, sectionAt, G.one_natural, G.mul_one] using h

lemma translation_mul (p q : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    (translation R W G p).hom ≫ (translation R W G q).hom =
      (translation R W G (G.mul (𝟙 _) p q)).hom := by
  let t := structureMap R W
  let e : SchemeHomOver t t := RelativeGroupLaw.idPoint
  have hp := comp_translation R W G p t e
  have hq := comp_translation R W G q t (G.mul t e (sectionAt R W t p))
  have hpq := comp_translation R W G (G.mul (𝟙 _) p q) t e
  simp only [e, RelativeGroupLaw.idPoint, Category.id_comp] at hp hpq
  rw [hp, hq, G.mul_assoc, hpq]
  congr 2
  exact (G.mul_natural (𝟙 _) t t (Category.comp_id t) p q).symm

/-- The i-th actual cyclic translation. -/
def cyclicTranslation {n : ℕ} (P : CyclicSection R W G n) (i : Fin n) :
    Curve R W ≅ Curve R W :=
  translation R W G (G.nsmul (𝟙 _) i.val (generator R W G P))

lemma cyclicTranslation_comp (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
    (P : CyclicSection R W G n) (i j : Fin n) :
    (cyclicTranslation R W G P i).hom ≫ (cyclicTranslation R W G P j).hom =
      (cyclicTranslation R W G P ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩).hom := by
  unfold cyclicTranslation
  rw [translation_mul, nsmul_mod R W G hG P]
  congr 2
  letI := G.pointGroup (𝟙 (Base R))
  simp only [nsmul_eq_pow]
  exact (pow_add (generator R W G P) i.val j.val).symm

/-- Distinct components remain distinct on every nonempty test scheme. -/
lemma multiples_distinct {n : ℕ} (P : CyclicSection R W G n)
    {T : Scheme.{u}} [Nonempty T] (t : T ⟶ Base R) (i j : Fin n)
    (h : t ≫ multiple R W G P i = t ≫ multiple R W G P j) : i = j := by
  by_contra hij
  obtain ⟨x⟩ := ‹Nonempty T›
  have hx : multiple R W G P i (t x) = multiple R W G P j (t x) :=
    congrArg (fun f : T ⟶ Curve R W => f x) h
  exact Set.disjoint_left.mp (P.disjoint i j hij) ⟨t x, rfl⟩ ⟨t x, hx.symm⟩

/-- Freeness is a statement on actual scheme-valued points, not on the
underlying topological points of the curve. -/
lemma cyclicTranslation_free {n : ℕ} (P : CyclicSection R W G n)
    {T : Scheme.{u}} [Nonempty T] (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (i j : Fin n)
    (h : x.val ≫ (cyclicTranslation R W G P i).hom =
      x.val ≫ (cyclicTranslation R W G P j).hom) : i = j := by
  simp only [cyclicTranslation, comp_translation] at h
  have he := Subtype.ext h
  letI := G.pointGroup t
  have he' : sectionAt R W t (G.nsmul (𝟙 _) i.val (generator R W G P)) =
      sectionAt R W t (G.nsmul (𝟙 _) j.val (generator R W G P)) := mul_left_cancel he
  apply multiples_distinct R W G P t i j
  simpa only [multiple_eq_nsmul, sectionAt, WeierstrassProjModel.schemeHomOverComp_coe] using
    congrArg Subtype.val he'


open CategoryTheory.Limits

/-- Factoring through a monomorphism is local on the source. -/
lemma factor_of_cover {T E X : Scheme.{u}} (ι : E ⟶ X) [Mono ι]
    (f : T ⟶ X) (C : T.OpenCover)
    (h : ∀ i, ∃ g : C.X i ⟶ E, g ≫ ι = C.f i ≫ f) :
    ∃ g : T ⟶ E, g ≫ ι = f := by
  choose g hg using h
  have hc (i j) : pullback.fst (C.f i) (C.f j) ≫ g i =
      pullback.snd (C.f i) (C.f j) ≫ g j := by
    apply (cancel_mono ι).mp
    simp only [Category.assoc, hg]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ f) (pullback.condition (f := C.f i) (g := C.f j))).trans
        (Category.assoc _ _ _))
  refine ⟨C.glueMorphisms g hc, C.hom_ext _ _ fun i => ?_⟩
  rw [← Category.assoc, C.ι_glueMorphisms, hg]

/-- Multiples as relative points on an arbitrary test scheme. -/
def multipleAt {n : ℕ} (P : CyclicSection R W G n) {T : Scheme.{u}}
    (t : T ⟶ Base R) (i : Fin n) : SchemeHomOver t (structureMap R W) :=
  sectionAt R W t (G.nsmul (𝟙 _) i.val (generator R W G P))

lemma multipleAt_val {n : ℕ} (P : CyclicSection R W G n) {T : Scheme.{u}}
    (t : T ⟶ Base R) (i : Fin n) :
    (multipleAt R W G P t i).val = t ≫ multiple R W G P i := by
  rw [multiple_eq_nsmul]; rfl

lemma multipleAt_natural {n : ℕ} (P : CyclicSection R W G n)
    {T U : Scheme.{u}} (t : T ⟶ Base R) (a : U ⟶ T) (i : Fin n) :
    WeierstrassProjModel.schemeHomOverComp a rfl (multipleAt R W G P t i) =
      multipleAt R W G P (a ≫ t) i := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

lemma multipleAt_mul (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
    (P : CyclicSection R W G n) {T : Scheme.{u}} (t : T ⟶ Base R) (i j : Fin n) :
    G.mul t (multipleAt R W G P t i) (multipleAt R W G P t j) =
      multipleAt R W G P t ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ := by
  unfold multipleAt sectionAt
  rw [← G.mul_natural, nsmul_mod R W G hG P]
  congr 1
  letI := G.pointGroup (𝟙 (Base R))
  simp only [nsmul_eq_pow]
  exact (pow_add (generator R W G P) i.val j.val).symm

lemma multipleAt_zero (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
    (P : CyclicSection R W G n) {T : Scheme.{u}} (t : T ⟶ Base R) :
    multipleAt R W G P t ⟨0, hn⟩ = G.one t := by
  exact G.one_natural (𝟙 _) t t (Category.comp_id t)

lemma multipleAt_inv (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
    (P : CyclicSection R W G n) {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n) :
    G.inv t (multipleAt R W G P t i) =
      multipleAt R W G P t ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩ := by
  letI := G.pointGroup t
  apply inv_eq_of_mul_eq_one_right
  change G.mul t _ _ = G.one t
  rw [multipleAt_mul R W G hG hn P]
  have he : (i.val + (n - i.val) % n) % n = 0 := by
    rw [Nat.add_mod_mod, Nat.add_sub_of_le (Nat.le_of_lt i.isLt), Nat.mod_self]
  simpa only [he] using multipleAt_zero R W G hG hn P t

section SplitKernel
variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
variable [W.IsElliptic] (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
variable (P : CyclicSection R W G n)
include hG hn

/-- The accepted split-kernel isomorphism, with no new representability premise. -/
def kernelSplitIso : (kernelIdeal R W G P).subscheme ≅ Spec (CommRingCat.of (Fin n → R)) :=
  (split_cyclic_kernel R W G hG n hn P).2.2.choose

lemma kernelSplitIso_component (i : Fin n) :
    component R n i ≫ (kernelSplitIso R W G hG hn P).inv ≫
      (kernelIdeal R W G P).subschemeι = multiple R W G P i :=
  (split_cyclic_kernel R W G hG n hn P).2.2.choose_spec.2 i

/-- A cover of the actual ideal subscheme by its labeled sections. -/
def kernelCover : (kernelIdeal R W G P).subscheme.OpenCover :=
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
    (sigmaSpec (fun _ : Fin n => CommRingCat.of R) ≫ (kernelSplitIso R W G hG hn P).inv)

lemma kernelCover_component (i : Fin n) :
    (kernelCover R W G hG hn P).f i ≫ (kernelIdeal R W G P).subschemeι =
      multiple R W G P i := by
  change (Sigma.ι (fun _ : Fin n => Base R) i ≫ sigmaSpec _ ≫ _) ≫ _ = _
  rw [← Category.assoc, ι_sigmaSpec]
  exact kernelSplitIso_component R W G hG hn P i

lemma multipleAt_factors {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n) :
    ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = (multipleAt R W G P t i).val := by
  refine ⟨t ≫ (kernelCover R W G hG hn P).f i, ?_⟩
  rw [Category.assoc, kernelCover_component, multipleAt_val]

/-- On the pullback of a labeled kernel chart, a factoring point is exactly
that labeled multiple, with the test scheme's original structural morphism. -/
lemma kernel_local_point {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W))
    (e : T ⟶ (kernelIdeal R W G P).subscheme)
    (he : e ≫ (kernelIdeal R W G P).subschemeι = x.val) (i : Fin n) :
    let C := kernelCover R W G hG hn P
    WeierstrassProjModel.schemeHomOverComp ((C.pullback₁ e).f i)
      (show (C.pullback₁ e).f i ≫ t = (C.pullback₁ e).f i ≫ t from rfl) x =
        multipleAt R W G P ((C.pullback₁ e).f i ≫ t) i := by
  dsimp only
  let C := kernelCover R W G hG hn P
  have hh : (C.pullback₁ e).f i ≫ x.val = C.pullbackHom e i ≫ multiple R W G P i := by
    rw [← he, ← Category.assoc, ← C.pullbackHom_map, Category.assoc,
      kernelCover_component]
  have ht : C.pullbackHom e i = (C.pullback₁ e).f i ≫ t := by
    have z := congrArg (fun f => f ≫ structureMap R W) hh
    simp only [Category.assoc, x.property, multiple_over] at z
    exact (Category.comp_id _).symm.trans z.symm
  apply Subtype.ext
  change (C.pullback₁ e).f i ≫ x.val = _
  rw [multipleAt_val, hh, ht]



lemma kernel_one_closed {T : Scheme.{u}} (t : T ⟶ Base R) :
    ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = (G.one t).val := by
  simpa only [multipleAt_zero R W G hG hn P] using
    multipleAt_factors R W G hG hn P t ⟨0, hn⟩

lemma kernel_mul_multiple {T : Scheme.{u}} (t : T ⟶ Base R) (i : Fin n)
    (y : SchemeHomOver t (structureMap R W))
    (e : T ⟶ (kernelIdeal R W G P).subscheme)
    (he : e ≫ (kernelIdeal R W G P).subschemeι = y.val) :
    ∃ e' : T ⟶ (kernelIdeal R W G P).subscheme,
      e' ≫ (kernelIdeal R W G P).subschemeι =
        (G.mul t (multipleAt R W G P t i) y).val := by
  let C := (kernelCover R W G hG hn P).pullback₁ e
  apply factor_of_cover _ _ C
  intro j
  have hh := G.mul_natural t (C.f j ≫ t) (C.f j) rfl (multipleAt R W G P t i) y
  rw [multipleAt_natural, kernel_local_point R W G hG hn P t y e he j,
    multipleAt_mul R W G hG hn P] at hh
  obtain ⟨z, hz⟩ := multipleAt_factors R W G hG hn P (C.f j ≫ t)
    ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩
  exact ⟨z, hz.trans (congrArg Subtype.val hh).symm⟩

/-- The actual ideal subscheme is closed under the source group operation on
all scheme-valued points. This supplies the subgroup hypothesis for a scheme
quotient theorem, including on disconnected and nonreduced test schemes. -/
lemma kernel_mul_closed {T : Scheme.{u}} (t : T ⟶ Base R)
    (x y : SchemeHomOver t (structureMap R W))
    (hx : ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = x.val)
    (hy : ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = y.val) :
    ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = (G.mul t x y).val := by
  obtain ⟨e, he⟩ := hx
  obtain ⟨d, hd⟩ := hy
  let C := (kernelCover R W G hG hn P).pullback₁ e
  apply factor_of_cover _ _ C
  intro i
  let yi := WeierstrassProjModel.schemeHomOverComp (C.f i) rfl y
  have hh := G.mul_natural t (C.f i ≫ t) (C.f i) rfl x y
  rw [kernel_local_point R W G hG hn P t x e he i] at hh
  obtain ⟨z, hz⟩ := kernel_mul_multiple R W G hG hn P (C.f i ≫ t) i yi (C.f i ≫ d)
    (by change (C.f i ≫ d) ≫ _ = C.f i ≫ y.val; rw [Category.assoc, hd])
  exact ⟨z, hz.trans (congrArg Subtype.val hh).symm⟩

lemma kernel_inv_closed {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W))
    (hx : ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = x.val) :
    ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
      e ≫ (kernelIdeal R W G P).subschemeι = (G.inv t x).val := by
  obtain ⟨e, he⟩ := hx
  let C := (kernelCover R W G hG hn P).pullback₁ e
  apply factor_of_cover _ _ C
  intro i
  let ti := C.f i ≫ t
  let xi := WeierstrassProjModel.schemeHomOverComp (C.f i) rfl x
  have hx' : xi = multipleAt R W G P ti i := kernel_local_point R W G hG hn P t x e he i
  have hinv : WeierstrassProjModel.schemeHomOverComp (C.f i) rfl (G.inv t x) = G.inv ti xi := by
    letI := G.pointGroup ti
    have hh := G.mul_natural t ti (C.f i) rfl (G.inv t x) x
    rw [G.inv_mul_cancel, G.one_natural] at hh
    exact eq_inv_of_mul_eq_one_left hh.symm
  rw [hx', multipleAt_inv R W G hG hn P] at hinv
  obtain ⟨z, hz⟩ := multipleAt_factors R W G hG hn P ti
    ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩
  exact ⟨z, hz.trans (congrArg Subtype.val hinv).symm⟩



open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree (toGRJ)

/-- A finite flat surjective scheme quotient is constructed from the input
cyclic subgroup. The target and its group law are conclusions. -/
theorem scheme_quotient_exists :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Base R) (H : GoodReductionJacobian.RelativeGroupLaw R g)
      (p : Curve R W ⟶ Y) (hp : p ≫ g = structureMap R W)
      (w : pullback.snd ((kernelIdeal R W G P).subschemeι ≫ structureMap R W)
          (structureMap R W) ≫ p =
        (toGRJ G).action (kernelIdeal R W G P).subschemeι ≫ p),
      GoodReductionJacobian.AbelianSchemePropertyBundle R g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t g),
        H.mul t x y = H.mul t y x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t (structureMap R W)),
        (⟨(G.mul t x y).val ≫ p, by rw [Category.assoc, hp, (G.mul t x y).property]⟩ :
          SchemeHomOver t g) = H.mul t
            ⟨x.val ≫ p, by rw [Category.assoc, hp, x.property]⟩
            ⟨y.val ≫ p, by rw [Category.assoc, hp, y.property]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x : SchemeHomOver t (structureMap R W)),
        (⟨x.val ≫ p, by rw [Category.assoc, hp, x.property]⟩ : SchemeHomOver t g) = H.one t ↔
          ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
            e ≫ (kernelIdeal R W G P).subschemeι = x.val) ∧
      IsPullback (pullback.snd ((kernelIdeal R W G P).subschemeι ≫ structureMap R W)
          (structureMap R W))
        ((toGRJ G).action (kernelIdeal R W G P).subschemeι) p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have hgeom := relative_curve_geometry R W
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R W) := hgeom.2.2.2.2.2.2
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hbundle : GoodReductionJacobian.AbelianSchemePropertyBundle R (structureMap R W) :=
    ⟨inferInstance, inferInstance, fun x => by
      rw [← (structureMap R W).range_fiberι, ← Set.image_univ]
      exact isConnected_univ.image _ ((structureMap R W).fiberι x).continuous.continuousOn,
      ⟨toGRJ G⟩⟩
  have hAF : ∀ S : Finset (Curve R W),
      ∃ U : (Curve R W).Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := fun S =>
    exists_isAffineOpen_forall_mem_of_isImmersion_proj
      (WeierstrassProjModel.projModelGradingCR W.toProjective) (𝟙 (Curve R W)) S
  have hk := split_cyclic_kernel R W G hG n hn P
  letI : IsFinite ((kernelIdeal R W G P).subschemeι ≫ structureMap R W) := hk.1
  letI : Etale ((kernelIdeal R W G P).subschemeι ≫ structureMap R W) := hk.2.1
  exact (toGRJ G).exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
    hbundle hG.2 hAF (kernelIdeal R W G P).subschemeι
    (fun t => kernel_one_closed R W G hG hn P t)
    (fun t x y hx hy => kernel_mul_closed R W G hG hn P t x y hx hy)
    (fun t x hx => kernel_inv_closed R W G hG hn P t x hx)



lemma kernel_finrank (x : Base R) :
    ((kernelIdeal R W G P).subschemeι ≫ structureMap R W).finrank x = n := by
  obtain ⟨hf, he, e, hw, _⟩ := split_cyclic_kernel R W G hG n hn P
  letI : IsFinite (splitStructure R n) := SplitCyclicKernelR0173.split_finite R n
  letI : Etale (splitStructure R n) := SplitCyclicKernelR0173.split_etale R n
  rw [← hw, Scheme.Hom.finrank_comp_left_of_isIso]
  change (Spec.map (CommRingCat.ofHom (algebraMap R (Fin n → R)))).finrank x = n
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simp

/-- Every finite-flat quotient with the constructed action relation is étale,
and its rank is exactly the number of labeled kernel components. -/
lemma quotient_etale_finrank {Y : Scheme.{u}} (p : Curve R W ⟶ Y)
    [IsFinite p] [Flat p] [Surjective p]
    (hrel : IsPullback
      (pullback.snd ((kernelIdeal R W G P).subschemeι ≫ structureMap R W) (structureMap R W))
      ((toGRJ G).action (kernelIdeal R W G P).subschemeι) p p) :
    Etale p ∧ ∀ y, p.finrank y = n := by
  have hk := split_cyclic_kernel R W G hG n hn P
  letI : IsFinite ((kernelIdeal R W G P).subschemeι ≫ structureMap R W) := hk.1
  letI : Etale ((kernelIdeal R W G P).subschemeι ≫ structureMap R W) := hk.2.1
  refine ⟨?_, ?_⟩
  · exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hrel ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  · intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hrel.flip,
      Scheme.Hom.finrank_pullback_snd]
    exact kernel_finrank R W G hG hn P _

/-- An intermediate scheme quotient with its exact kernel functor. -/
structure SchemeQuotient where
  target : Scheme.{u}
  structureMap : target ⟶ Base R
  law : GoodReductionJacobian.RelativeGroupLaw R structureMap
  map : Curve R W ⟶ target
  over_eq : map ≫ structureMap = ArithmeticThetaRelativeKatoR0169.structureMap R W
  geometry : GoodReductionJacobian.AbelianSchemePropertyBundle R structureMap
  commutative : ∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t structureMap),
    law.mul t x y = law.mul t y x
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  degree : ∀ y, map.finrank y = n
  preserves_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Base R)
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W)),
    (⟨(G.mul t x y).val ≫ map, by rw [Category.assoc, over_eq, (G.mul t x y).property]⟩ :
      SchemeHomOver t structureMap) = law.mul t
        ⟨x.val ≫ map, by rw [Category.assoc, over_eq, x.property]⟩
        ⟨y.val ≫ map, by rw [Category.assoc, over_eq, y.property]⟩
  kernel : ∀ {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W)),
    (⟨x.val ≫ map, by rw [Category.assoc, over_eq, x.property]⟩ : SchemeHomOver t structureMap) =
      law.one t ↔ ∃ e : T ⟶ (kernelIdeal R W G P).subscheme,
        e ≫ (kernelIdeal R W G P).subschemeι = x.val

/-- No quotient map or target is assumed: all intermediate data are constructed. -/
theorem schemeQuotient_nonempty : Nonempty (SchemeQuotient R W G P) := by
  obtain ⟨Y, g, H, p, hp, w, hg, hcomm, hf, hflat, hfp, hsurj, hmul, hker, hrel, hcoeq⟩ :=
    scheme_quotient_exists R W G hG hn P
  letI := hf
  letI := hflat
  letI := hsurj
  have het := quotient_etale_finrank R W G hG hn P p hrel
  exact ⟨⟨Y, g, H, p, hp, hg, hcomm, hf, het.1, hsurj, het.2, hmul, hker⟩⟩

def constructedSchemeQuotient : SchemeQuotient R W G P :=
  (schemeQuotient_nonempty R W G hG hn P).some


namespace SchemeQuotient
variable (Q : SchemeQuotient R W G P)

/-- The quotient origin is its group identity section. -/
def zero : Base R ⟶ Q.target := (Q.law.one (𝟙 _)).val

lemma zero_over : Q.zero R W G P ≫ Q.structureMap = 𝟙 _ := (Q.law.one (𝟙 _)).property

lemma one_val {T : Scheme.{u}} (t : T ⟶ Base R) :
    (Q.law.one t).val = t ≫ Q.zero R W G P :=
  (congrArg Subtype.val (Q.law.one_natural (𝟙 _) t t (Category.comp_id t))).symm

lemma map_origin : origin R W ≫ Q.map = Q.zero R W G P := by
  have h := (Q.kernel (𝟙 _) (G.one (𝟙 _))).mpr (kernel_one_closed R W G hG hn P (𝟙 _))
  have hv := congrArg Subtype.val h
  simpa only [hG.1, Category.id_comp, zero] using hv

lemma kernel_square : (kernelIdeal R W G P).subschemeι ≫ Q.map =
    ((kernelIdeal R W G P).subschemeι ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W) ≫
      Q.zero R W G P := by
  let t := (kernelIdeal R W G P).subschemeι ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W
  let x : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W) :=
    ⟨(kernelIdeal R W G P).subschemeι, rfl⟩
  have h := (Q.kernel t x).mpr ⟨𝟙 _, Category.id_comp _⟩
  exact (congrArg Subtype.val h).trans (Q.one_val R W G hG hn P t)

lemma kernel_pullback : IsPullback (kernelIdeal R W G P).subschemeι
    ((kernelIdeal R W G P).subschemeι ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W)
    Q.map (Q.zero R W G P) := by
  let ι := (kernelIdeal R W G P).subschemeι
  let π := ArithmeticThetaRelativeKatoR0169.structureMap R W
  have hs (s : PullbackCone Q.map (Q.zero R W G P)) : s.fst ≫ π = s.snd := by
    have h := congrArg (fun f => f ≫ Q.structureMap) s.condition
    simpa only [Category.assoc, Q.over_eq, Q.zero_over R W G hG hn P, Category.comp_id] using h
  have hfac (s : PullbackCone Q.map (Q.zero R W G P)) : ∃ e : s.pt ⟶ _, e ≫ ι = s.fst := by
    apply (Q.kernel s.snd ⟨s.fst, hs s⟩).mp
    apply Subtype.ext
    exact s.condition.trans (Q.one_val R W G hG hn P s.snd).symm
  choose lift hlift using hfac
  apply IsPullback.of_isLimit (c := PullbackCone.mk ι (ι ≫ π) (Q.kernel_square R W G hG hn P))
  refine PullbackCone.IsLimit.mk _ lift hlift ?_ ?_
  · intro s
    rw [← Category.assoc, hlift, hs]
  · intro s m hm _
    exact (cancel_mono ι).mp (hm.trans (hlift s).symm)

/-- Exact equality of ideal sheaves, derived from the actual Cartesian
kernel square rather than only equality of closed-point sets. -/
lemma kernel_ideal : (Q.zero R W G P).ker.comap Q.map = kernelIdeal R W G P := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  have : IsClosedImmersion (Q.zero R W G P) := by
    have : IsClosedImmersion (Q.zero R W G P ≫ Q.structureMap) := by
      rw [Q.zero_over R W G hG hn P]; infer_instance
    exact IsClosedImmersion.of_comp _ Q.structureMap
  let h := Q.kernel_pullback R W G hG hn P
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]
  exact (kernelIdeal R W G P).ker_subschemeι

/-- Relative dimension descends along the actual finite étale quotient map. -/
lemma smooth_dimension_one : SmoothOfRelativeDimension 1 Q.structureMap := by
  letI : Etale Q.map := Q.etale
  letI : Surjective Q.map := Q.surjective
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : Nonempty (Curve R W) := ⟨origin R W (Classical.arbitrary (Base R))⟩
  haveI : SmoothOfRelativeDimension 1 (Q.map ≫ Q.structureMap) := by
    rw [Q.over_eq]
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact (SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
    Q.map Q.structureMap 1 0).1

/-- The constructed origin is an actual relative effective Cartier divisor. -/
lemma zero_ideal_invertible : (Q.zero R W G P).ker.IsInvertible := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one R W G hG hn P
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (Q.zero R W G P)
    (Q.zero_over R W G hG hn P)

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaPullback

/-- The quotient's relative cotangent sheaf pulls back isomorphically by the
constructed quotient morphism, using the existing general étale comparison. -/
def differentialIso :
    (Scheme.Modules.pullback Q.map).obj Q.structureMap.kaehler ≅
      (ArithmeticThetaRelativeKatoR0169.structureMap R W).kaehler := by
  letI : Etale Q.map := Q.etale
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one R W G hG hn P
  let f := differentialMap Q.structureMap
    (ArithmeticThetaRelativeKatoR0169.structureMap R W) Q.map (by simpa using Q.over_eq)
  haveI : IsIso f := EtaleHodgePullbackIsomorphismR0172.differentialMap_isIso_etale
    Q.structureMap (ArithmeticThetaRelativeKatoR0169.structureMap R W) Q.map Q.over_eq
  exact asIso f

/-- The Hodge sheaf at the constructed quotient origin is identified with
the source Hodge sheaf by the actual differential pullback. -/
def hodgeIso :
    (Scheme.Modules.pullback (Q.zero R W G P)).obj Q.structureMap.kaehler ≅ Hodge R W :=
  pullbackEqIso (Q.map_origin R W G hG hn P).symm Q.structureMap.kaehler ≪≫
    ((Scheme.Modules.pullbackComp (origin R W) Q.map).app Q.structureMap.kaehler).symm ≪≫
      (Scheme.Modules.pullback (origin R W)).mapIso (Q.differentialIso R W G hG hn P)

end SchemeQuotient
end SplitKernel

namespace OriginHodge
open scoped TensorProduct
open TensorProduct
lemma tensor_frame {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra A R] [IsScalarTower R A R]
    (x y : A) (d : Derivation R A R) (dx : d x = 1) (dy : d y = 0)
    (hy : (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A y = 0)
    (hext : ∀ D E : Derivation R A (R ⊗[A] Ω[A⁄R]), D x = E x → D y = E y → D = E) :
    ∃ e : R ≃ₗ[R] R ⊗[A] Ω[A⁄R], e 1 = (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A x := by
  let j : Ω[A⁄R] →ₗ[A] R ⊗[A] Ω[A⁄R] := TensorProduct.mk A R Ω[A⁄R] 1
  let L : R ⊗[A] Ω[A⁄R] →ₗ[R] R := d.liftKaehlerDifferential.liftBaseChange R
  let E : R →ₗ[R] R ⊗[A] Ω[A⁄R] := LinearMap.toSpanSingleton R _ (j (KaehlerDifferential.D R A x))
  have Lx : L (j (KaehlerDifferential.D R A x)) = 1 := by
    simpa only [L, j, TensorProduct.mk_apply, LinearMap.liftBaseChange_one_tmul] using
      (d.liftKaehlerDifferential_comp_D x).trans dx
  have Ly : L (j (KaehlerDifferential.D R A y)) = 0 := by
    simpa only [L, j, TensorProduct.mk_apply, LinearMap.liftBaseChange_one_tmul] using
      (d.liftKaehlerDifferential_comp_D y).trans dy
  have hLE : L.comp E = LinearMap.id := by
    apply LinearMap.ext
    intro r
    change L (r • j (KaehlerDifferential.D R A x)) = r
    rw [map_smul, Lx, smul_eq_mul, mul_one]
  have hj : ((E.comp L).restrictScalars A).comp j = j := by
    apply Derivation.liftKaehlerDifferential_unique
    apply hext
    · change E (L (j (KaehlerDifferential.D R A x))) = j (KaehlerDifferential.D R A x)
      rw [Lx]
      exact one_smul R _
    · change E (L (j (KaehlerDifferential.D R A y))) = j (KaehlerDifferential.D R A y)
      rw [Ly, map_zero]
      exact hy.symm
  have hEL : E.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
    | tmul r ω =>
      have h := LinearMap.congr_fun hj ω
      change E (L (1 ⊗ₜ[A] ω)) = 1 ⊗ₜ[A] ω at h
      change E (L (r ⊗ₜ[A] ω)) = r ⊗ₜ[A] ω
      calc
        _ = E (L (r • (1 ⊗ₜ[A] ω))) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = r • (1 ⊗ₜ[A] ω) := by rw [map_smul, map_smul, h]
        _ = r ⊗ₜ[A] ω := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨LinearEquiv.ofLinearMap E L hEL hLE, ?_⟩
  change (1 : R) • j (KaehlerDifferential.D R A x) = _
  rw [one_smul]
  rfl
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open MvPolynomial
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def evalOrigin : OriginQuotient W →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : Fin 2 => (0 : R))) (by
    change Ideal.span {originPolynomial W} ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : R))).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    simp [originPolynomial])

@[simp] lemma evalOrigin_q (p : MvPolynomial (Fin 2) R) :
    evalOrigin W (originQ W p) = aeval (fun _ : Fin 2 => (0 : R)) p := rfl

/-- The evaluation used for the cotangent calculation is exactly the actual
projective origin section under the checked chart presentation. -/
lemma evalOrigin_actual : (evalOrigin W).toRingHom.comp (originEquiv W).toRingHom =
    WeierstrassProjModel.kwYChartEval R W := by
  letI : Algebra R (OriginRing W) := (originScalar W).toAlgebra
  apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
  · intro r
    change evalOrigin W (originEquiv W (algebraMap R (OriginRing W) r)) = _
    rw [(originEquiv W).commutes, (evalOrigin W).commutes]
    exact (RingHom.congr_fun (WeierstrassProjModel.kwYChartEval_section R W) r).symm
  · change evalOrigin W (originToQuotient W (WeierstrassCurve.DrinfeldGlobal.xOverY W)) = _
    rw [originToQuotient_x, evalOrigin_q]
    simp only [aeval_X]
    exact (WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective).2.1.symm
  · change evalOrigin W (originToQuotient W (WeierstrassCurve.DrinfeldGlobal.zOverY W)) = _
    rw [originToQuotient_v, evalOrigin_q]
    simp only [aeval_X]
    exact (WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective).2.2.symm

local instance originResidueAlgebra : Algebra (OriginQuotient W) R :=
  (evalOrigin W).toRingHom.toAlgebra
local instance originResidueTower : IsScalarTower R (OriginQuotient W) R :=
  IsScalarTower.of_algebraMap_eq fun r => ((evalOrigin W).commutes r).symm

lemma origin_linear_coefficient : evalOrigin W (originQ W (originPolyU W)) = -1 := by
  rw [evalOrigin_q]
  simp [originPolyU]
lemma origin_cross_coefficient : evalOrigin W (originQ W (originPolyV W)) = 0 := by
  rw [evalOrigin_q]
  simp [originPolyV]

/-- A genuine global basis of the cotangent module at the Weierstrass origin,
over the original coefficient ring rather than only over its fraction field. -/
theorem origin_cotangent_frame :
    ∃ e : R ≃ₗ[R] R ⊗[OriginQuotient W] Ω[OriginQuotient W⁄R],
      e 1 = (1 : R) ⊗ₜ[OriginQuotient W]
        KaehlerDifferential.D R (OriginQuotient W) (originQ W (X 0)) := by
  let A := OriginQuotient W
  let x := originQ W (X 0)
  let y := originQ W (X 1)
  let d : Derivation R A R := (Algebra.linearMap A R).compDer (-originTangent W)
  have dx : d x = 1 := by
    change evalOrigin W (-(originTangent W x)) = 1
    rw [show originTangent W x = originQ W (originPolyU W) from originTangent_u W,
      map_neg, origin_linear_coefficient, neg_neg]
  have dy : d y = 0 := by
    change evalOrigin W (-(originTangent W y)) = 0
    rw [show originTangent W y = originQ W (originPolyV W) from originTangent_v W,
      map_neg, origin_cross_coefficient, neg_zero]
  have hy : (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A y = 0 := by
    have h := congrArg (fun ω : Ω[A⁄R] => (1 : R) ⊗ₜ[A] ω) (origin_differential_relation W)
    change (1 : R) ⊗ₜ[A] (originQ W (originPolyU W) • KaehlerDifferential.D R A y) =
      (1 : R) ⊗ₜ[A] (originQ W (originPolyV W) • KaehlerDifferential.D R A x) at h
    have hs (a : A) (ω : Ω[A⁄R]) :
        (1 : R) ⊗ₜ[A] (a • ω) = evalOrigin W a ⊗ₜ[A] ω := by
      calc
        _ = (a • (1 : R)) ⊗ₜ[A] ω := TensorProduct.tmul_smul (R := A) a (1 : R) ω
        _ = _ := by change ((evalOrigin W a) * 1) ⊗ₜ[A] ω = _; rw [mul_one]
    rw [hs, hs] at h
    change evalOrigin W (originQ W (originPolyU W)) ⊗ₜ[A] KaehlerDifferential.D R A y =
      evalOrigin W (originQ W (originPolyV W)) ⊗ₜ[A] KaehlerDifferential.D R A x at h
    rw [origin_linear_coefficient, origin_cross_coefficient, TensorProduct.zero_tmul,
      TensorProduct.neg_tmul, neg_eq_zero] at h
    exact h
  exact tensor_frame x y d dx dy hy (origin_derivation_ext W)

def transport_cotangent_frame {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra A R]
    [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower R A R] [IsScalarTower R A B] [IsScalarTower A R C]
    [IsScalarTower A B C] [Algebra.FormallyEtale A B]
    (e : R ≃ₗ[R] R ⊗[A] Ω[A⁄R]) :
    C ≃ₗ[C] C ⊗[B] Ω[B⁄R] :=
  (TensorProduct.AlgebraTensorModule.rid R C C).symm ≪≫ₗ
    LinearEquiv.baseChange R C _ _ e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R C C Ω[A⁄R] ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C Ω[A⁄R]).symm ≪≫ₗ
    LinearEquiv.baseChange B C _ _ (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)

lemma section_chart_evaluation {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (χ : A →+* R) (s : Spec (CommRingCat.of R) ⟶ X)
    (hs : s = Spec.map (CommRingCat.ofHom χ) ≫ ι)
    (h : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ s ⁻¹ᵁ (ι ''ᵁ ⊤))
    (b : Γ(X, ι ''ᵁ ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((s.appLE (ι ''ᵁ ⊤) ⊤ h).hom b) =
      χ (chartRingEquiv ι b) := by
  have he : s.appLE (ι ''ᵁ ⊤) ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      (ι.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom χ := by
    rw [Scheme.Hom.appIso_hom', ← Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc]
    congr 1
    rw [show (Spec.map (CommRingCat.ofHom χ)).appTop =
      (Spec.map (CommRingCat.ofHom χ)).appLE ⊤ ⊤ (by simp) by
        simp [Scheme.Hom.appLE, Scheme.Hom.appTop]]
    rw [Scheme.Hom.appLE_comp_appLE]
    subst s
    rfl
  exact congrArg (fun f => f.hom b) he

theorem source_hodge_trivial (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    Nonempty ((SheafOfModules.unit (Base R).ringCatSheaf : (Base R).Modules) ≅ Hodge R W) := by
  let π := structureMap R W
  let o := origin R W
  let ι := WeierstrassCurve.DrinfeldGlobal.originChartι W.toProjective
  let U := ι ''ᵁ ⊤
  have hU : IsAffineOpen U := by
    change IsAffineOpen (ι ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange ι
  have ho : o = Spec.map (CommRingCat.ofHom (WeierstrassProjModel.kwYChartEval R W)) ≫ ι := rfl
  have hBU : (⊤ : (Base R).Opens) ≤ o ⁻¹ᵁ U := by
    intro x hx
    change o x ∈ Set.image ι.base (Set.univ)
    rw [ho]
    exact ⟨_, Set.mem_univ _, rfl⟩
  let A := OriginQuotient W
  let B := Γ(Curve R W,U)
  let C := Γ(Base R,⊤)
  letI : Algebra R B := π.sectionsAlgebra U
  letI : Algebra R (OriginRing W) := (originScalar W).toAlgebra
  let θ : B ≃ₐ[R] OriginRing W := chartAlgEquiv π ι (origin_structure W)
  let φ : A ≃ₐ[R] B := (θ.trans (originEquiv W)).symm
  let γ := Scheme.ΓSpecIso (CommRingCat.of R)
  letI : Algebra R C := γ.inv.hom.toAlgebra
  letI : Algebra B C := (o.appLE U ⊤ hBU).hom.toAlgebra
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A R := (evalOrigin W).toRingHom.toAlgebra
  letI : Algebra A C := ((o.appLE U ⊤ hBU).hom.comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower R A R :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := R) fun r => ((evalOrigin W).commutes r).symm
  haveI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := B) fun r => (φ.commutes r).symm
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) fun _ => rfl
  haveI : IsScalarTower A R C := by
    apply IsScalarTower.of_algebraMap_eq (R := A) (S := R) (A := C)
    intro a
    change (o.appLE U ⊤ hBU).hom (φ a) = γ.inv.hom (evalOrigin W a)
    apply (ConcreteCategory.bijective_of_isIso γ.hom).injective
    rw [section_chart_evaluation ι _ o ho hBU]
    have he : originEquiv W (chartRingEquiv ι (φ a)) = a :=
      (θ.trans (originEquiv W)).apply_symm_apply a
    have hx := RingHom.congr_fun (evalOrigin_actual W) (chartRingEquiv ι (φ a))
    change evalOrigin W (originEquiv W (chartRingEquiv ι (φ a))) = _ at hx
    rw [he] at hx
    rw [← hx]
    exact (ConcreteCategory.congr_hom γ.inv_hom_id (evalOrigin W a)).symm
  haveI : Algebra.FormallyEtale A B := by
    have h : (algebraMap A B).Etale := RingHom.Etale.of_bijective φ.bijective
    exact (RingHom.etale_algebraMap.mp h).formallyEtale
  obtain ⟨e, he⟩ := origin_cotangent_frame W
  let eC : C ≃ₗ[C] C ⊗[B] Ω[B⁄R] := transport_cotangent_frame e
  haveI : SmoothOfRelativeDimension 1 π :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hΩ : Scheme.Modules.IsInvertible π.kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (π.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  let eΩ := LinearEquiv.ofBijective (π.kaehlerToSectionsₗ U)
    (π.kaehlerToSections_bijective_of_isAffineOpen hU)
  obtain ⟨β, hβ⟩ := hΩ.exists_baseChange_sections_linearEquiv_pullback_of_le
    o U hU ⊤ (isAffineOpen_top _) hBU
  let E : C ≃ₗ[C] Γ(Hodge R W,⊤) := eC ≪≫ₗ LinearEquiv.baseChange B C _ _ eΩ ≪≫ₗ β
  have hspan : Submodule.span C {E 1} = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨c,rfl⟩ := E.surjective z
    rw [show E c = c • E 1 by rw [← map_smul, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hf := (hΩ.pullback o).isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
    (isAffineOpen_top _) (E 1) hspan
  exact ⟨(iso_of_global_frame (E 1) hf).choose⟩

end OriginHodge

namespace SchemeQuotient
variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
variable [W.IsElliptic] (hG : IsOriginLaw R W G) {n : ℕ} (hn : 0 < n)
variable (P : CyclicSection R W G n) (Q : SchemeQuotient R W G P)

include hG hn in
/-- The constructed quotient has a trivial actual Hodge sheaf. Neither a
frame nor a target Weierstrass equation is an input to this result. -/
theorem hodge_trivial :
    Nonempty ((SheafOfModules.unit (Base R).ringCatSheaf : (Base R).Modules) ≅
      (Scheme.Modules.pullback (Q.zero R W G P)).obj Q.structureMap.kaehler) := by
  obtain ⟨e⟩ := OriginHodge.source_hodge_trivial R W
  exact ⟨e ≪≫ (Q.hodgeIso R W G hG hn P).symm⟩

end SchemeQuotient
end FramedSchemeQuotientR0174
end ArithmeticThetaRelativeCyclicQuotientR0173

namespace ArithmeticThetaCyclicPresentationR0174
open ArithmeticThetaRelativeCyclicQuotientR0173.FramedSchemeQuotientR0174

/-- Construct the finite étale cyclic quotient and a frame of its actual Hodge sheaf. -/
theorem framed_scheme_quotient :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G n), Nonempty (ArithmeticThetaCyclicPresentationR0174.FramedQuotient R W G P) := by
  intro R _ _ _ _ _ W _ G hG n hn P
  obtain ⟨Q⟩ := schemeQuotient_nonempty R W G hG hn P
  exact ⟨{
    target := Q.target
    structureMap := Q.structureMap
    law := Q.law
    map := Q.map
    over_eq := Q.over_eq
    geometry := Q.geometry
    dimension := Q.smooth_dimension_one R W G hG hn P
    finite := Q.finite
    etale := Q.etale
    surjective := Q.surjective
    degree := Q.degree
    origin_eq := Q.map_origin R W G hG hn P
    kernel := Q.kernel_ideal R W G hG hn P
    hodge := Q.hodge_trivial R W G hG hn P }⟩

end ArithmeticThetaCyclicPresentationR0174
