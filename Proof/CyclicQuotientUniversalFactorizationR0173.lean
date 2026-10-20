module

public import RelativeCyclicQuotientExistenceR0173
public import SplitCyclicKernelR0173
public import PointedRelativeGroupHomR0173
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

/-! Universal factorization through the actual finite étale cyclic quotient. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeIsogenyHodgeR0172

namespace CyclicQuotientUniversalFactorizationR0173

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)

/- Pointed rigidity gives the homomorphism on every test scheme. -/
def pointHom (V : WeierstrassCurve R) [V.IsElliptic] (H : Law R V)
    (hH : IsOriginLaw R V H) (f : PointedMap R W V)
    {T : Scheme.{u}} (t : T ⟶ Base R) :
    letI := G.pointGroup t
    letI := H.pointGroup t
    SchemeHomOver t (structureMap R W) →* SchemeHomOver t (structureMap R V) := by
  letI := G.pointGroup t
  letI := H.pointGroup t
  exact {
    toFun := mapPoint R W f t
    map_one' := PointedRelativeGroupHom.map_one R W V G H hG hH f t
    map_mul' := (pointed_relative_group_hom R W G hG V H hH f).1 T t }

/- Killing the generator kills each labeled multiple as a scheme morphism. -/
include hG in
lemma kills_multiple {n : ℕ} (P : CyclicSection R W G n)
    (Z : WeierstrassCurve R) [Z.IsElliptic] (J : Law R Z) (hJ : IsOriginLaw R Z J)
    (a : PointedMap R W Z) (ha : P.point ≫ a.map = origin R Z) (i : Fin n) :
    multiple R W G P i ≫ a.map = origin R Z := by
  rw [multiple, Category.assoc,
    (pointed_relative_group_hom R W G hG Z J hJ a).2 i.val,
    ← Category.assoc, ha]
  have he : origin R Z = (J.one (𝟙 (Base R))).val := by
    rw [hJ.1, Category.id_comp]
  rw [he, ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
    J.nsmul_unit]

/- The accepted labeled split presentation detects equality on the entire kernel. -/
include hG in
lemma kills_kernel {n : ℕ} (hn : 0 < n) (P : CyclicSection R W G n)
    (Z : WeierstrassCurve R) [Z.IsElliptic] (J : Law R Z) (hJ : IsOriginLaw R Z J)
    (a : PointedMap R W Z) (ha : P.point ≫ a.map = origin R Z) :
    (kernelIdeal R W G P).subschemeι ≫ a.map =
      (kernelIdeal R W G P).subschemeι ≫ structureMap R W ≫ origin R Z := by
  obtain ⟨e, he, hc⟩ := (split_cyclic_kernel R W G hG n hn P).2.2
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
  apply (cancel_epi e.inv).mp
  apply (cancel_epi (sigmaSpec (fun _ : Fin n => CommRingCat.of R))).mp
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, ι_sigmaSpec]
  change ((component R n i ≫ e.inv) ≫ (kernelIdeal R W G P).subschemeι) ≫ a.map =
    (((component R n i ≫ e.inv) ≫ (kernelIdeal R W G P).subschemeι) ≫
      structureMap R W) ≫ origin R Z
  have hc' : (component R n i ≫ e.inv) ≫ (kernelIdeal R W G P).subschemeι =
      multiple R W G P i := by simpa only [Category.assoc] using hc i
  rw [hc', kills_multiple R W G hG P Z J hJ a ha i]
  have hm : multiple R W G P i ≫ structureMap R W = 𝟙 _ := by
    rw [multiple, Category.assoc, G.schemeNsmul_over, P.over_eq]
  rw [hm, Category.id_comp]

/- Scheme-theoretic kernel equality makes every point killed by f factor through
its actual closed kernel subscheme. -/
lemma factors_kernel {n : ℕ} (P : CyclicSection R W G n)
    (V : WeierstrassCurve R) [V.IsElliptic] (f : PointedMap R W V)
    (hf : IsQuotient R W G P f) {T : Scheme.{u}} (t : T ⟶ Base R)
    (d : SchemeHomOver t (structureMap R W)) (hd : d.val ≫ f.map = t ≫ origin R V) :
    ∃ k : T ⟶ (kernelIdeal R W G P).subscheme,
      k ≫ (kernelIdeal R W G P).subschemeι = d.val := by
  letI : IsProper (structureMap R V) :=
    WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  have ho : origin R V ≫ structureMap R V = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R V).property
  haveI : IsClosedImmersion (origin R V) := by
    haveI : IsClosedImmersion (origin R V ≫ structureMap R V) := by rw [ho]; infer_instance
    exact IsClosedImmersion.of_comp _ (structureMap R V)
  have hk : (kernelIdeal R W G P) ≤ d.val.ker := by
    rw [← hf.2.2.2.2, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hh := (pullback.lift d.val t hd).le_ker_comp (pullback.fst f.map (origin R V))
    simpa only [pullback.lift_fst] using hh
  exact ⟨IsClosedImmersion.lift _ d.val (by simpa using hk),
    IsClosedImmersion.lift_fac _ _ _⟩

/- Two arbitrary scheme-valued points with the same quotient image have the
same image under a pointed map killing the cyclic generator. -/
include hG in
lemma same_fiber {n : ℕ} (hn : 0 < n) (P : CyclicSection R W G n)
    (V : WeierstrassCurve R) [V.IsElliptic] (H : Law R V) (hH : IsOriginLaw R V H)
    (f : PointedMap R W V) (hf : IsQuotient R W G P f)
    (Z : WeierstrassCurve R) [Z.IsElliptic] (J : Law R Z) (hJ : IsOriginLaw R Z J)
    (a : PointedMap R W Z) (ha : P.point ≫ a.map = origin R Z)
    {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t (structureMap R W))
    (hxy : x.val ≫ f.map = y.val ≫ f.map) : x.val ≫ a.map = y.val ≫ a.map := by
  letI := G.pointGroup t
  letI := H.pointGroup t
  letI := J.pointGroup t
  let F := pointHom R W G hG V H hH f t
  let A := pointHom R W G hG Z J hJ a t
  have hF : F x = F y := Subtype.ext hxy
  have hd : (x * y⁻¹).val ≫ f.map = t ≫ origin R V := by
    have hh : F (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hF, mul_inv_cancel]
    exact (congrArg Subtype.val hh).trans (hH.1 t)
  obtain ⟨k, hk⟩ := factors_kernel R W G P V f hf t (x * y⁻¹) hd
  have hA : A (x * y⁻¹) = 1 := by
    apply Subtype.ext
    change (x * y⁻¹).val ≫ a.map = (J.one t).val
    rw [hJ.1, ← hk, Category.assoc, kills_kernel R W G hG hn P Z J hJ a ha,
      ← Category.assoc, ← Category.assoc, hk, (x * y⁻¹).property]
  have hh : A x = A y := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv] using hA
  exact congrArg Subtype.val hh

end CyclicQuotientUniversalFactorizationR0173

/- Faithfully flat descent yields the unique actual pointed factorization. -/
theorem cyclic_quotient_universal_factorization :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G n) (V : WeierstrassCurve R) [V.IsElliptic] (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (hf : ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient R W G P f) (Z : WeierstrassCurve R) [Z.IsElliptic] (J : ArithmeticThetaRelativeKatoR0169.Law R Z) (hJ : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R Z J) (a : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W Z), CategoryTheory.CategoryStruct.comp P.point a.map = ArithmeticThetaRelativeKatoR0169.origin R Z → ∃! u : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R V Z, CategoryTheory.CategoryStruct.comp f.map u.map = a.map := by
  intro R _ _ _ _ _ W _ G hG n hn P V _ H hH f hf Z _ J hJ a ha
  haveI : Etale f.map := hf.2.1
  haveI : Surjective f.map := hf.2.2.1
  have hd : ∀ {T : Scheme.{u}} (x y : T ⟶ Curve R W),
      x ≫ f.map = y ≫ f.map → x ≫ a.map = y ≫ a.map := by
    intro T x y hxy
    have hy : y ≫ structureMap R W = x ≫ structureMap R W := by
      rw [← f.over_eq, ← Category.assoc, ← Category.assoc, hxy]
    exact CyclicQuotientUniversalFactorizationR0173.same_fiber R W G hG hn P V H hH f hf
      Z J hJ a ha (x ≫ structureMap R W) ⟨x, rfl⟩ ⟨y, hy⟩ hxy
  let b := EffectiveEpi.desc f.map a.map hd
  have hb : f.map ≫ b = a.map := EffectiveEpi.fac _ _ _
  have hover : b ≫ structureMap R Z = structureMap R V := by
    apply (cancel_epi f.map).mp
    rw [← Category.assoc, hb, a.over_eq, f.over_eq]
  have horigin : origin R V ≫ b = origin R Z := by
    rw [← f.origin_eq, Category.assoc, hb, a.origin_eq]
  refine ⟨⟨b, hover, horigin⟩, hb, ?_⟩
  intro c hc
  have he : c.map = b := (cancel_epi f.map).mp (hc.trans hb.symm)
  cases c with
  | mk cm co cz =>
    dsimp only at he
    subst cm
    rfl

end ArithmeticThetaRelativeCyclicQuotientR0173
