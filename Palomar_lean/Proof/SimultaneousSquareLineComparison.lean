module

public import FiniteEtaleSelectedComponent
public import FiniteEtaleProductCover
public import SquareIsomorphismTorsor

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaGlobalization
universe u
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaCoverComparison

private lemma local_spec_preconnected (R : Type u) [CommRing R] [IsLocalRing R] :
    _root_.IsPreconnected (Set.univ : Set (AlgebraicGeometry.Spec (CommRingCat.of R))) := by
  have hc : PreconnectedSpace (AlgebraicGeometry.Spec (CommRingCat.of R)) := by
    apply preconnectedSpace_iff_clopen.mpr
    intro s hs
    let c : TopologicalSpace.Clopens (AlgebraicGeometry.Spec (CommRingCat.of R)) := ⟨s, hs⟩
    let e := PrimeSpectrum.isIdempotentElemEquivClopens.symm c
    have he : e.1 = 0 ∨ e.1 = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e.1 with hu | hu
      · exact Or.inr (hu.mul_left_cancel (by simpa [e.2.eq]))
      · exact Or.inl (hu.mul_left_cancel (by
          rw [sub_mul, one_mul, e.2.eq, sub_self, mul_zero]))
    rcases he with he | he
    · left
      have heq : c = ⊥ := by
        apply PrimeSpectrum.isIdempotentElemEquivClopens.symm.injective
        change e = PrimeSpectrum.isIdempotentElemEquivClopens.symm ⊥
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot]
        exact Subtype.ext he
      exact congrArg TopologicalSpace.Clopens.carrier heq
    · right
      have heq : c = ⊤ := by
        apply PrimeSpectrum.isIdempotentElemEquivClopens.symm.injective
        change e = PrimeSpectrum.isIdempotentElemEquivClopens.symm ⊤
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
        exact Subtype.ext he
      exact congrArg TopologicalSpace.Clopens.carrier heq
  exact hc.isPreconnected_univ

private lemma pullback_associativity_hom {S U T X : Scheme.{u}}
    (g : S ⟶ U) (q : U ⟶ T) (p : T ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).hom.app M) ≫
        (Scheme.Modules.pullbackComp g (q ≫ p)).hom.app M =
      (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackComp (g ≫ q) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M := by
  have hunit :
      (Scheme.Modules.pullbackComp g (q ≫ p)).inv.app M ≫
          (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).inv.app M) ≫
          (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback p).obj M) ≫
          (Scheme.Modules.pullbackComp (g ≫ q) p).hom.app M ≫
          (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M = 𝟙 _ := by
    have h := congrArg (fun k => k.app M)
      (Scheme.Modules.pseudofunctor_associativity g q p)
    simpa [NatTrans.comp_app, Scheme.Modules.pullbackCongr] using
      congrArg (fun k => k ≫ (Scheme.Modules.pullbackCongr (Category.assoc g q p)).hom.app M) h
  have h := congrArg (fun k =>
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp q p).hom.app M) ≫
        (Scheme.Modules.pullbackComp g (q ≫ p)).hom.app M ≫ k) hunit
  simpa [Category.assoc, ← Functor.map_comp] using h.symm

private lemma pullback_iso_rfl {S T X : Scheme.{u}} (g : S ⟶ T) (p : T ⟶ X)
    (H J : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J) :
    pullbackIsoOver p (g ≫ p) H J ⟨g, rfl⟩ e =
      ((Scheme.Modules.pullbackComp g p).app H).symm ≪≫
        (Scheme.Modules.pullback g).mapIso e ≪≫ (Scheme.Modules.pullbackComp g p).app J := by
  apply Iso.ext
  simp [pullbackIsoOver, overPullbackIso, Scheme.Modules.pullbackCongr]

private lemma pullback_iso_nested {S U T X : Scheme.{u}}
    (p : T ⟶ X) (p' : U ⟶ X) (f : S ⟶ X)
    (H J : X.Modules) (q : {q : U ⟶ T // q ≫ p = p'})
    (g : {g : S ⟶ U // g ≫ p' = f})
    (e : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J) :
    pullbackIsoOver p' f H J g (pullbackIsoOver p p' H J q e) =
      pullbackIsoOver p f H J
        ⟨g.val ≫ q.val, by rw [Category.assoc, q.property, g.property]⟩ e := by
  rcases q with ⟨q, rfl⟩
  rcases g with ⟨g, rfl⟩
  have hcomp (M : X.Modules) :
      (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp q p).app M) ≪≫
          (Scheme.Modules.pullbackComp g (q ≫ p)).app M =
        (Scheme.Modules.pullbackComp g q).app ((Scheme.Modules.pullback p).obj M) ≪≫
          (Scheme.Modules.pullbackComp (g ≫ q) p).app M ≪≫
          (Scheme.Modules.pullbackCongr (Category.assoc g q p)).app M := by
    apply Iso.ext
    exact pullback_associativity_hom g q p M
  rw [pullback_iso_rfl, pullback_iso_rfl]
  apply Iso.ext
  simp only [pullbackIsoOver, overPullbackIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change (((Scheme.Modules.pullbackComp g (q ≫ p)).app H).symm ≪≫
      (Scheme.Modules.pullback g).mapIso
        (((Scheme.Modules.pullbackComp q p).app H).symm ≪≫
          (Scheme.Modules.pullback q).mapIso e ≪≫ (Scheme.Modules.pullbackComp q p).app J) ≪≫
      (Scheme.Modules.pullbackComp g (q ≫ p)).app J).hom = _
  have hrewrite :
      ((Scheme.Modules.pullbackComp g (q ≫ p)).app H).symm ≪≫
          (Scheme.Modules.pullback g).mapIso
            (((Scheme.Modules.pullbackComp q p).app H).symm ≪≫
              (Scheme.Modules.pullback q).mapIso e ≪≫ (Scheme.Modules.pullbackComp q p).app J) ≪≫
          (Scheme.Modules.pullbackComp g (q ≫ p)).app J =
        ((Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp q p).app H) ≪≫
          (Scheme.Modules.pullbackComp g (q ≫ p)).app H).symm ≪≫
          (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullback q).mapIso e) ≪≫
          ((Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp q p).app J) ≪≫
            (Scheme.Modules.pullbackComp g (q ≫ p)).app J) := by simp
  rw [hrewrite, hcomp H, hcomp J]
  simp [← Functor.comp_map]

private lemma pullback_square_property {X T S : Scheme.{u}} {H J W : X.Modules}
    {a : tensorPower X H 2 ≅ W} {b : tensorPower X J 2 ≅ W} {p : T ⟶ X}
    (g : S ⟶ T) (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J)
    (hW : ArithmeticThetaNormalizedSections.IsLineBundle X W)
    (e : SquareIsos a b p) :
    tensorPowerMap (pullbackIsoOver p (g ≫ p) H J ⟨g, rfl⟩ e.val).hom 2 ≫
        (pullbackPowerIso (g ≫ p) b).hom = (pullbackPowerIso (g ≫ p) a).hom := by
  let C : HomLine.PairFrames X H J := HomLine.pairFrames hH hJ
  have heq : tensorPowerMap e.val.hom 2 =
      HomLine.pullbackPowerMap p (a.hom ≫ b.inv) := by
    apply (cancel_mono (pullbackPowerIso p b).hom).1
    rw [HomLine.pullbackPowerMap_comparison]
    simpa [Category.assoc] using e.property
  have hmap : tensorPowerMap
      (pullbackIsoOver p (g ≫ p) H J ⟨g, rfl⟩ e.val).hom 2 =
      HomLine.pullbackPowerMap (g ≫ p) (a.hom ≫ b.inv) := by
    apply (HomLine.hom_eq_iff_coordinates (HomLine.pullbackHomFrames C (g ≫ p)).opens
      (HomLine.pullbackHomFrames C (g ≫ p)).covers
      (fun i => tensorPowerFrame S ((Scheme.Modules.pullback (g ≫ p)).obj H)
        ((g ≫ p) ⁻¹ᵁ C.opens (p (g i)))
        (HomLine.pulledFrame (g ≫ p) (C.left (p (g i)))) 2)
      (fun i => tensorPowerFrame S ((Scheme.Modules.pullback (g ≫ p)).obj J)
        ((g ≫ p) ⁻¹ᵁ C.opens (p (g i)))
        (HomLine.pulledFrame (g ≫ p) (C.right (p (g i)))) 2)
      (a := tensorPowerMap
        (pullbackIsoOver p (g ≫ p) H J ⟨g, rfl⟩ e.val).hom 2)
      (b := HomLine.pullbackPowerMap (g ≫ p) (a.hom ≫ b.inv))).2
    intro i
    dsimp [HomLine.pullbackHomFrames]
    simp only [← Scheme.Hom.comp_preimage]
    rw [frameHomCoordinate_tensorPowerMap, HomLine.pullbackPowerMap_coordinate]
    have hcoord := HomLine.pullbackIsoOver_coordinate_comp g p
      (C.left (p (g i))) (C.right (p (g i))) e.val
    have hcoord2 := congrArg (fun k => frameHomCoordinate
        (tensorPowerFrame T ((Scheme.Modules.pullback p).obj H)
          (p ⁻¹ᵁ C.opens (p (g i)))
          (HomLine.pulledFrame p (C.left (p (g i)))) 2)
        (tensorPowerFrame T ((Scheme.Modules.pullback p).obj J)
          (p ⁻¹ᵁ C.opens (p (g i)))
          (HomLine.pulledFrame p (C.right (p (g i)))) 2)
        k (p ⁻¹ᵁ C.opens (p (g i))) le_rfl) heq
    rw [frameHomCoordinate_tensorPowerMap, HomLine.pullbackPowerMap_coordinate] at hcoord2
    calc
      _ = (g.app (p ⁻¹ᵁ C.opens (p (g i)))
          (frameHomCoordinate (HomLine.pulledFrame p (C.left (p (g i))))
            (HomLine.pulledFrame p (C.right (p (g i)))) e.val.hom
            (p ⁻¹ᵁ C.opens (p (g i))) le_rfl)) ^ 2 := by
              simpa only [Scheme.Hom.comp_apply] using congrArg (fun z => z ^ 2) hcoord
      _ = g.app (p ⁻¹ᵁ C.opens (p (g i)))
          (frameHomCoordinate (HomLine.pulledFrame p (C.left (p (g i))))
            (HomLine.pulledFrame p (C.right (p (g i)))) e.val.hom
            (p ⁻¹ᵁ C.opens (p (g i))) le_rfl ^ 2) := by rw [map_pow]
      _ = _ := by
        rw [Scheme.Hom.comp_app]
        simp only [ConcreteCategory.comp_apply]
        rw [← hcoord2]
        rfl
  rw [hmap, HomLine.pullbackPowerMap_comparison]
  simp

private lemma pullback_square_over {X T S : Scheme.{u}} {H J W : X.Modules}
    {a : tensorPower X H 2 ≅ W} {b : tensorPower X J 2 ≅ W} {p : T ⟶ X}
    (f : S ⟶ X) (g : {g : S ⟶ T // g ≫ p = f})
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J)
    (hW : ArithmeticThetaNormalizedSections.IsLineBundle X W)
    (e : SquareIsos a b p) :
    tensorPowerMap (pullbackIsoOver p f H J g e.val).hom 2 ≫
        (pullbackPowerIso f b).hom = (pullbackPowerIso f a).hom := by
  rcases g with ⟨g, rfl⟩
  exact pullback_square_property g hH hJ hW e

/-- A finite family of square roots admits one integral finite-etale comparison cover. -/
theorem simultaneous_square_line_comparison
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (h2 : IsUnit (2 : X.presheaf.obj (Opposite.op ⊤)))
    (s : ℕ) (H₀ W : X.Modules) (H : Fin s → X.Modules)
    (hH₀ : ArithmeticThetaNormalizedSections.IsLineBundle X H₀)
    (hW : ArithmeticThetaNormalizedSections.IsLineBundle X W)
    (hH : ∀ i, ArithmeticThetaNormalizedSections.IsLineBundle X (H i))
    (a₀ : CategoryTheory.Iso (tensorPower X H₀ 2) W)
    (a : ∀ i, CategoryTheory.Iso (tensorPower X (H i) 2) W)
    (R : Type u) [CommRing R] [IsLocalRing R] [Nontrivial R]
    (f : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of R)) X)
    (w : ∀ i, SquareIsos a₀ (a i) f) :
    ∃ (Y : AlgebraicGeometry.Scheme.{u}) (p : Quiver.Hom Y X),
      AlgebraicGeometry.IsIntegral Y ∧ AlgebraicGeometry.IsFinite p ∧
      AlgebraicGeometry.Etale p ∧ AlgebraicGeometry.Surjective p ∧
      (∀ x : X, 0 < AlgebraicGeometry.Scheme.Hom.finrank p x ∧
        AlgebraicGeometry.Scheme.Hom.finrank p x ≤ 2 ^ s) ∧
      ∃ (e : ∀ i, SquareIsos a₀ (a i) p)
        (g : {g : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of R)) Y //
          CategoryTheory.CategoryStruct.comp g p = f}),
        ∀ i, pullbackIsoOver p f H₀ (H i) g (e i).val = (w i).val := by
  classical
  have each : ∀ i : Fin s,
      ∃ (T : Scheme) (p : T ⟶ X) (e : SquareIsos a₀ (a i) p),
        IsFinite p ∧ Etale p ∧ Surjective p ∧
          (∀ x : X, Scheme.Hom.finrank p x = 2) ∧
          ∀ (S : Scheme) (f' : S ⟶ X) (w' : SquareIsos a₀ (a i) f'),
            ∃! g' : {g' : S ⟶ T // g' ≫ p = f'},
              pullbackIsoOver p f' H₀ (H i) g' e.val = w'.val := by
    intro i
    exact square_isomorphism_torsor X h2 H₀ (H i) W hH₀ (hH i) hW a₀ (a i)
  choose T p e hfin heta hsurj hdegree huniv using each
  letI : ∀ i, IsFinite (p i) := hfin
  letI : ∀ i, Etale (p i) := heta
  letI : ∀ i, Surjective (p i) := hsurj
  obtain ⟨Tprod, pprod, vprod, hpfin, hpeta, hpsurj, hprank, hvprod, hUprod⟩ :=
    finite_etale_product_cover X s T p
  letI : IsFinite pprod := hpfin
  letI : Etale pprod := hpeta
  letI : Surjective pprod := hpsurj
  let Z : Scheme := Spec (CommRingCat.of R)
  letI : PreconnectedSpace Z := ⟨local_spec_preconnected R⟩
  let z : Z := Classical.choice (inferInstance : Nonempty Z)
  have branches : ∀ i : Fin s, ∃ gi : {gi : Z ⟶ T i // gi ≫ p i = f},
      pullbackIsoOver (p i) f H₀ (H i) gi (e i).val = (w i).val := by
    intro i
    obtain ⟨gi, hgi, -⟩ := huniv i Z f (w i)
    exact ⟨gi, hgi⟩
  choose gi hgi using branches
  obtain ⟨gprod, hgprod, hgproj⟩ := hUprod Z f (fun i => (gi i).val)
    (fun i => (gi i).property)
  let y : Tprod := gprod z
  obtain ⟨U, hUeq, hUint, hUfin, hUeta, hUsurj, hUrank⟩ :=
    ArithmeticThetaGlobalization.finite_etale_selected_component X Tprod hnormal pprod y
  let pU : (U : Scheme) ⟶ X := U.ι ≫ pprod
  have himage : Set.range gprod.base ⊆ connectedComponent y := by
    have hc : _root_.IsPreconnected (Set.range gprod.base) := by
      simpa only [Set.image_univ] using
        (isPreconnected_univ.image gprod.base gprod.continuous.continuousOn)
    exact hc.subset_connectedComponent ⟨z, rfl⟩
  let gU : {g : Z ⟶ (U : Scheme) // g ≫ pU = f} := by
    have hsub : Set.range gprod.base ⊆ Set.range U.ι := by
      intro q hq
      rw [Scheme.Opens.range_ι, hUeq]
      exact himage hq
    let gu : Z ⟶ (U : Scheme) := IsOpenImmersion.lift U.ι gprod hsub
    refine ⟨gu, ?_⟩
    change (gu ≫ U.ι) ≫ pprod = f
    rw [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    exact hgprod.1
  let eU : ∀ i, SquareIsos a₀ (a i) pU := fun i => by
    let qi : (U : Scheme) ⟶ T i := U.ι ≫ vprod i
    have hqi : qi ≫ p i = pU := by
      dsimp [qi, pU]
      rw [Category.assoc, hvprod i]
    refine ⟨pullbackIsoOver (p i) pU H₀ (H i) ⟨qi, hqi⟩ (e i).val, ?_⟩
    exact pullback_square_over pU ⟨qi, hqi⟩ hH₀ (hH i) hW (e i)
  refine ⟨(U : Scheme), pU, hUint, hUfin, hUeta, hUsurj, ?_, ?_⟩
  · intro x
    have hr := hUrank x
    constructor
    · exact hr.1
    · calc
        pU.finrank x ≤ pprod.finrank x := hr.2
        _ = ∏ i : Fin s, (p i).finrank x := hprank x
        _ = ∏ i : Fin s, 2 := by simp [hdegree]
        _ = 2 ^ s := by simp
  · refine ⟨eU, gU, ?_⟩
    intro i
    let qi : (U : Scheme) ⟶ T i := U.ι ≫ vprod i
    let gi' : {g : Z ⟶ T i // g ≫ p i = f} :=
      ⟨gU.val ≫ qi, by
        calc
          gU.val ≫ qi ≫ p i = gU.val ≫ U.ι ≫ (vprod i ≫ p i) := by
            simp [qi, Category.assoc]
          _ = gU.val ≫ U.ι ≫ pprod := by rw [hvprod i]
          _ = f := by rw [gU.property]⟩
    have heq : gi'.val = (gi i).val := by
      have hfac : gU.val ≫ U.ι = gprod := by
        exact AlgebraicGeometry.IsOpenImmersion.lift_fac U.ι gprod _
      calc
        gi'.val = gU.val ≫ U.ι ≫ vprod i := by rfl
        _ = gprod ≫ vprod i := by simpa only [Category.assoc] using congrArg (fun k => k ≫ vprod i) hfac
        _ = (gi i).val := hgprod.2 i
    have hsub : gi' = gi i := Subtype.ext heq
    rw [← hgi i, ← hsub]
    exact pullback_iso_nested (p i) pU f H₀ (H i)
      ⟨qi, by dsimp [qi, pU]; rw [Category.assoc, hvprod i]⟩ gU (e i).val

end ArithmeticThetaCoverComparison
