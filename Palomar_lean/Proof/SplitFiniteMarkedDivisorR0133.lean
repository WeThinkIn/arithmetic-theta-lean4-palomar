module

public import PolygonCartierDefinitionsR0133
public import Mathlib.RingTheory.Etale.Pi
public import PolygonCompatibleMarkingsR0131
public import PolygonSmoothMarkedSectionsR0131
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

/-! The split marked divisor, with its prescribed labeled components and base map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace ArithmeticThetaPolygonCartierR0133
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131

namespace SplitFiniteMarkedDivisorR0133

lemma closed_sigma {ι : Type v} [Finite ι] [Small.{u} ι]
    {Z : ι → Scheme.{u}} {X : Scheme.{u}} (s : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (s i)]
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (s i)) (Set.range (s j))) :
    IsClosedImmersion (Sigma.desc s) := by
  have hs : SurjectiveOnStalks (Sigma.desc s) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  have hc : ∀ x : (∐ Z : Scheme.{u}), ∃ i y, Sigma.ι Z i y = x := by
    intro x
    exact ⟨(sigmaOpenCover Z).idx x, (sigmaOpenCover Z).covers x⟩
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (Sigma.desc s).continuous ?_ ?_⟩
  · intro x y h
    obtain ⟨i, x, rfl⟩ := hc x
    obtain ⟨j, y, rfl⟩ := hc y
    have he : s i x = s j y := by simpa [← Scheme.Hom.comp_apply] using h
    by_cases hij : i = j
    · subst j
      exact congrArg (Sigma.ι Z i) ((s i).isClosedEmbedding.injective he)
    · exact False.elim (Set.disjoint_left.mp (hd i j hij) ⟨x, rfl⟩ ⟨y, he.symm⟩)
  · intro C hC
    have he : Sigma.desc s '' C = ⋃ i, s i '' ((Sigma.ι Z i) ⁻¹' C) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y, rfl⟩ := hc x
        exact Set.mem_iUnion.mpr ⟨i, y, hx, by simp [← Scheme.Hom.comp_apply]⟩
      · intro hz
        obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hz
        exact ⟨Sigma.ι Z i y, hy, by simp [← Scheme.Hom.comp_apply]⟩
    rw [he]
    exact isClosed_iUnion_of_finite fun i => (s i).isClosedEmbedding.isClosedMap _
      (hC.preimage (Sigma.ι Z i).continuous)

lemma split_finite (k : Type u) [Field k] [CharZero k] (r n : ℕ) :
    IsFinite (splitStructure k r n) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap (R k n) (Fin r → R k n)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma split_etale (k : Type u) [Field k] [CharZero k] (r n : ℕ) :
    Etale (splitStructure k r n) := by
  apply HasRingHomProperty.Spec_iff.mpr
  change (algebraMap (R k n) (Fin r → R k n)).Etale
  exact RingHom.etale_algebraMap.mpr inferInstance

end SplitFiniteMarkedDivisorR0133
/-- The actual intersection ideal cuts out the prescribed split finite étale divisor. -/
theorem split_finite_marked_divisor :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (E : B k n false ≃+* B k n true), IsAdjacent k n E →
      ∀ (D : Atlas k r n hr E) (a : Fin r → kˣ),
        SplitMarkedDivisor k r n hr D a := by
  intro k _ _ r n hr h3 E hE D a
  let s (i : Fin r) := markedSection k r n hr D i (a i)
  have hs (i : Fin r) : IsClosedImmersion (s i) :=
    (polygon_smooth_marked_sections k r n hr h3 E hE D i (a i)).1
  let m : (∐ fun _ : Fin r => specR k n) ⟶ D.X := Sigma.desc s
  have hm : IsClosedImmersion m :=
    SplitFiniteMarkedDivisorR0133.closed_sigma s (fun i j hij =>
      CompatibleMarkingsR0131.disjoint_markings k r n hr D i j hij (a i) (a j))
  let I := markedIdeal k r n hr D a
  have hker : I = m.ker := by
    rw [← m.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin r => specR k n))]
    change (⨅ i, (s i).ker) = _
    congr 1
    funext i
    congr 1
    exact (Sigma.ι_desc s i).symm
  have hker' : I.subschemeι.ker = m.ker := by
    rw [I.ker_subschemeι, hker]
  let f : (∐ fun _ : Fin r => specR k n) ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι m hker'.le
  have hf : f ≫ I.subschemeι = m := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ hker'
  let q := sigmaSpec (fun _ : Fin r => CommRingCat.of (R k n))
  have : IsOpenImmersion q := by
    classical
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have ht : DFinsupp.single (β := fun _ : Fin r => R k n) j 1 j ∈ y.asIdeal :=
      (PrimeSpectrum.ext_iff.mp heq).le
        (x := DFinsupp.single j 1)
        (show DFinsupp.single (β := fun _ : Fin r => R k n) j 1 i ∈ x.asIdeal by
          simp [hij.symm])
    simp [← Ideal.eq_top_iff_one, y.2.ne_top] at ht
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin r => R k n)).surjective x
    refine ⟨Sigma.ι (fun _ : Fin r => specR k n) i y, ?_⟩
    change (Sigma.ι (fun _ : Fin r => Spec (CommRingCat.of (R k n))) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : Fin r => Spec (CommRingCat.of (R k n))) i ≫ q =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => R k n) i)) from
        ι_sigmaSpec _ i]
    exact hy
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩
  let e : I.subscheme ≅ Spec (CommRingCat.of (Fin r → R k n)) :=
    (asIso f).symm ≪≫ asIso q
  have hq : q ≫ splitStructure k r n = m ≫ D.p := by
    apply Sigma.hom_ext
    intro i
    simp only [q, ι_sigmaSpec_assoc, m, Sigma.ι_desc_assoc]
    rw [SmoothMarkedSections.section_over]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => R k n) i)) ≫
      Spec.map (CommRingCat.ofHom (splitBase k r n)) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of (R k n)) using 1
    congr 1
  have he : e.hom ≫ splitStructure k r n = I.subschemeι ≫ D.p := by
    apply (cancel_epi f).mp
    simpa [e, Category.assoc, ← hf] using hq
  have hl (i : Fin r) : componentMap k r n i ≫ e.inv ≫ I.subschemeι = s i := by
    rw [show componentMap k r n i = Sigma.ι (fun _ : Fin r => specR k n) i ≫ q from
      (ι_sigmaSpec (fun _ : Fin r => CommRingCat.of (R k n)) i).symm]
    simp [e, Category.assoc, hf, m]
  have : IsFinite (splitStructure k r n) := SplitFiniteMarkedDivisorR0133.split_finite k r n
  have : Etale (splitStructure k r n) := SplitFiniteMarkedDivisorR0133.split_etale k r n
  refine ⟨inferInstance, ?_, ?_, e, he, hl⟩
  · change IsFinite (I.subschemeι ≫ D.p)
    rw [← he]
    infer_instance
  · change Etale (I.subschemeι ≫ D.p)
    rw [← he]
    infer_instance

end ArithmeticThetaPolygonCartierR0133
