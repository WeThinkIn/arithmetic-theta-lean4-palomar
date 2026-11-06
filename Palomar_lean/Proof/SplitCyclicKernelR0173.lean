module

public import RelativeCyclicQuotientDefinitionsR0173
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper

@[expose] public section

/-! The actual intersection of the cyclic section ideals is a labeled split
finite étale subscheme of the relative projective Weierstrass curve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeCyclicQuotientR0173
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171

namespace SplitCyclicKernelR0173

lemma split_finite (R : Type u) [CommRing R] (n : ℕ) :
    IsFinite (splitStructure R n) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap R (Fin n → R)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma split_etale (R : Type u) [CommRing R] (n : ℕ) :
    Etale (splitStructure R n) := by
  apply HasRingHomProperty.Spec_iff.mpr
  change (algebraMap R (Fin n → R)).Etale
  exact RingHom.etale_algebraMap.mpr inferInstance

end SplitCyclicKernelR0173

/-- The scheme-theoretic cyclic kernel is split finite étale, with the
prescribed structural map and every prescribed labeled multiple. -/
theorem split_cyclic_kernel :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G n), AlgebraicGeometry.IsFinite (CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeCyclicQuotientR0173.kernelIdeal R W G P).subschemeι (ArithmeticThetaRelativeKatoR0169.structureMap R W)) ∧ AlgebraicGeometry.Etale (CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeCyclicQuotientR0173.kernelIdeal R W G P).subschemeι (ArithmeticThetaRelativeKatoR0169.structureMap R W)) ∧ ∃ e : CategoryTheory.Iso (ArithmeticThetaRelativeCyclicQuotientR0173.kernelIdeal R W G P).subscheme (AlgebraicGeometry.Spec (CommRingCat.of (Fin n → R))), CategoryTheory.CategoryStruct.comp e.hom (ArithmeticThetaRelativeCyclicQuotientR0173.splitStructure R n) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeCyclicQuotientR0173.kernelIdeal R W G P).subschemeι (ArithmeticThetaRelativeKatoR0169.structureMap R W) ∧ ∀ i : Fin n, CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeCyclicQuotientR0173.component R n i) (CategoryTheory.CategoryStruct.comp e.inv (ArithmeticThetaRelativeCyclicQuotientR0173.kernelIdeal R W G P).subschemeι) = ArithmeticThetaRelativeCyclicQuotientR0173.multiple R W G P i := by
  intro R _ _ _ _ _ W _ G _hG n _hn P
  let s (i : Fin n) := multiple R W G P i
  have hs (i : Fin n) : s i ≫ structureMap R W = 𝟙 _ := by
    dsimp [s, multiple]
    rw [Category.assoc, G.schemeNsmul_over, P.over_eq]
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hsc (i : Fin n) : IsClosedImmersion (s i) := by
    have : IsClosedImmersion (s i ≫ structureMap R W) := by rw [hs i]; infer_instance
    exact IsClosedImmersion.of_comp (s i) (structureMap R W)
  let m : (∐ fun _ : Fin n => Base R) ⟶ Curve R W := Sigma.desc s
  have hm : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
      (fun i j hij => P.disjoint i j hij)
  let I := kernelIdeal R W G P
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
  have hq : q ≫ splitStructure R n = m ≫ structureMap R W := by
    apply Sigma.hom_ext
    intro i
    simp only [q, ι_sigmaSpec_assoc, m, Sigma.ι_desc_assoc]
    rw [hs i]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i)) ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi (fun _ : Fin n => RingHom.id (R)))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of (R)) using 1
    congr 1
  have he : e.hom ≫ splitStructure R n = I.subschemeι ≫ structureMap R W := by
    apply (cancel_epi f).mp
    simpa [e, Category.assoc, ← hf] using hq
  have hl (i : Fin n) : component R n i ≫ e.inv ≫ I.subschemeι = s i := by
    rw [show component R n i = Sigma.ι (fun _ : Fin n => Base R) i ≫ q from
      (ι_sigmaSpec (fun _ : Fin n => CommRingCat.of (R)) i).symm]
    simp [e, Category.assoc, hf, m]
  have : IsFinite (splitStructure R n) := SplitCyclicKernelR0173.split_finite R n
  have : Etale (splitStructure R n) := SplitCyclicKernelR0173.split_etale R n
  refine ⟨?_, ?_, e, he, hl⟩
  · change IsFinite (I.subschemeι ≫ structureMap R W)
    rw [← he]
    infer_instance
  · change Etale (I.subschemeι ≫ structureMap R W)
    rw [← he]
    infer_instance

end ArithmeticThetaRelativeCyclicQuotientR0173
