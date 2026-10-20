module

public import TateCuspDiskExtensionR0181
public import TateFullLevelMarkingR0181
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import SmoothProjectiveLevelCompletionR0179
public import CompactifiedLevelForgettingR0179
public import Theorems.Thm_AlgebraicGeometry_exists_isProper_twoAffineLineCover

@[expose] public section

/-! Specialization tools for coverage of the actual compactified level base.
The universal boundary-coverage theorem is proved using the finite flat
compactified j-map, actual marked Tate fibers and proper specialization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
namespace EveryGeometricBoundaryTateDisk
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaCompatibleLevelR0178

/-- A full marking over a characteristic-zero field accounts for every killed
point over every field extension, as an equality of scheme morphisms. This
retains the actual torsion subscheme and both coefficient maps. -/
lemma killed_point_coordinates
    (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G) (L : ℕ) (hL : 0 < L)
    (A : FullLevel F W G L (𝟙 (Base F)))
    (K : Type u) [Field K] (t : Base K ⟶ Base F)
    (x : SchemeHomOver t (structureMap F W))
    (hx : G.nsmul t L x = G.one t) :
    ∃ i j : Fin L, t ≫ coordinatePoint F W G A i j = x.val := by
  let η : Base K := IsLocalRing.closedPoint K
  have hk : x.val ≫ G.schemeNsmul L = t ≫ origin F W := by
    rw [← FullLevelTorsionSplittingR0175.nsmul_val G, hx, hG.1]
  haveI : IsProper (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  haveI : IsClosedImmersion (origin F W) := by
    haveI : IsClosedImmersion (origin F W ≫ structureMap F W) := by
      rw [BaseChange.origin_over]; infer_instance
    exact IsClosedImmersion.of_comp _ (structureMap F W)
  have hmem : x.val η ∈ (torsionIdeal F W G L).support := by
    rw [torsionIdeal, Scheme.IdealSheafData.support_comap]
    change G.schemeNsmul L (x.val η) ∈ (origin F W).ker.support
    apply (origin F W).range_subset_ker_support
    exact ⟨t η, (congrArg (fun f : Base K ⟶ Curve F W => f η) hk).symm⟩
  change x.val η ∈ ((torsionIdeal F W G L).support : Set _) at hmem
  rw [CoverGeometryR0175.torsion_support_eq_marked_union F W G hG L hL A] at hmem
  obtain ⟨i, hmem⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨j, β, hβ⟩ := Set.mem_iUnion.mp hmem
  let c := coordinatePoint F W G A i j
  have hc : c ≫ structureMap F W = 𝟙 _ :=
    FullLevelTorsionSplittingR0175.coordinate_over G A i j
  haveI : IsClosedImmersion c := by
    haveI : IsClosedImmersion (c ≫ structureMap F W) := hc.symm ▸ inferInstance
    exact IsClosedImmersion.of_comp c (structureMap F W)
  let p := pullback.fst x.val c
  let q := pullback.snd x.val c
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := x.val) (g := c)
    η β hβ.symm
  haveI : Nonempty ↥(pullback x.val c) := ⟨z⟩
  haveI : Surjective p := ⟨Function.surjective_to_subsingleton p⟩
  haveI : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  have hq : p ≫ t = q := by
    have h := congrArg (fun f => f ≫ structureMap F W)
      (pullback.condition (f := x.val) (g := c))
    simpa only [Category.assoc, x.property, hc, Category.comp_id] using h
  refine ⟨i, j, ?_⟩
  apply (cancel_epi p).mp
  rw [← Category.assoc, hq]
  exact (pullback.condition (f := x.val) (g := c)).symm

/-- Once one full marking is rational, every full marking of the same curve
over an extension field descends, preserving both labeled section maps. -/
lemma full_marking_descends
    (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G) (L : ℕ) (hL : 0 < L)
    (A : FullLevel F W G L (𝟙 (Base F)))
    (K : Type u) [Field K] (t : Base K ⟶ Base F)
    (M : FullLevel F W G L t) :
    ∃ B : FullLevel F W G L (𝟙 (Base F)),
      t ≫ B.x.val = M.x.val ∧ t ≫ B.y.val = M.y.val := by
  obtain ⟨i, j, hx⟩ := killed_point_coordinates F W G hG L hL A K t M.x M.killed_x
  obtain ⟨a, b, hy⟩ := killed_point_coordinates F W G hG L hL A K t M.y M.killed_y
  let c (i j : Fin L) : SchemeHomOver (𝟙 (Base F)) (structureMap F W) :=
    G.mul _ (G.nsmul _ i.val A.x) (G.nsmul _ j.val A.y)
  have hc (i j : Fin L) : G.nsmul (𝟙 (Base F)) L (c i j) = G.one _ := by
    apply Subtype.ext
    rw [FullLevelTorsionSplittingR0175.nsmul_val G, hG.1, Category.id_comp]
    exact FullLevelTorsionSplittingR0175.coordinate_killed G hG A i j
  have hav : ∀ r s : Fin L, r.val ≠ 0 ∨ s.val ≠ 0 →
      Disjoint (Set.range (G.mul _ (G.nsmul _ r.val (c i j))
        (G.nsmul _ s.val (c a b))).val) (Set.range (origin F W)) := by
    intro r s hrs
    have hn := Representability.combination_comp F W G (𝟙 (Base F)) t t
      (Category.comp_id t) (c i j) (c a b) M.x M.y hx hy r.val s.val
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ hz
    obtain ⟨w, hw⟩ := Function.surjective_to_subsingleton t z
    apply Set.disjoint_left.mp (M.avoids r s hrs) (Set.mem_range_self w)
    rw [← congrArg (fun f : Base K ⟶ Curve F W => f w) hn]
    simpa only [Scheme.Hom.comp_apply, hw] using hz
  exact ⟨⟨c i j, c a b, hc i j, hc a b, hav⟩, hx, hy⟩

/-- The actual scheme representing full markings on an already fully marked
elliptic curve is covered by rational sections. This assertion is about the
representing scheme and its universal sections, rather than an abstract set
of bases. -/
lemma level_cover_points_rational
    (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G) (L : ℕ) (hL : 0 < L)
    (A : FullLevel F W G L (𝟙 (Base F)))
    (Z : LevelScheme F W G L) (hZ : Represents F W G Z) (z : Z.space) :
    ∃ s : Base F ⟶ Z.space,
      s ≫ Z.projection = 𝟙 (Base F) ∧ s (IsLocalRing.closedPoint F) = z := by
  let K := Z.space.residueField z
  let q : Base K ⟶ Z.space := Z.space.fromSpecResidueField z
  let t : Base K ⟶ Base F := q ≫ Z.projection
  let M : FullLevel F W G L t := CoverGeometryR0175.pullMark q rfl Z.level
  obtain ⟨B, hx, hy⟩ := full_marking_descends F W G hG L hL A K t M
  obtain ⟨s, hs, _⟩ := hZ (Base F) (𝟙 (Base F)) B
  have hsq : t ≫ s.val = q := by
    let a : SchemeHomOver t Z.projection :=
      ⟨t ≫ s.val, by rw [Category.assoc, s.property, Category.comp_id]⟩
    let b : SchemeHomOver t Z.projection := ⟨q, rfl⟩
    have ha : a.val ≫ Z.level.x.val = M.x.val ∧
        a.val ≫ Z.level.y.val = M.y.val := by
      constructor
      · change (t ≫ s.val) ≫ Z.level.x.val = _
        rw [Category.assoc, hs.1, hx]
      · change (t ≫ s.val) ≫ Z.level.y.val = _
        rw [Category.assoc, hs.2, hy]
    exact congrArg Subtype.val
      (CoverGeometryR0175.representing_ext Z hZ M a b ha ⟨rfl, rfl⟩)
  refine ⟨s.val, s.property, ?_⟩
  let η : Base K := IsLocalRing.closedPoint K
  calc
    s.val (IsLocalRing.closedPoint F) = s.val (t η) :=
      congrArg s.val (Subsingleton.elim _ _)
    _ = q η := congrArg (fun f : Base K ⟶ Z.space => f η) hsq
    _ = z := Z.space.fromSpecResidueField_apply z η

/-- A classified marking of a coefficient extension of the fixed Tate curve
already comes from a marking over the original Laurent-series field. The
comparison is with the actual compatible quotient, using its uniqueness
theorem and both original labels. -/
lemma classifying_map_descends
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (σ : LaurentSeries k →+* K)
    (hσ : σ.comp (algebraMap k (LaurentSeries k)) = algebraMap k K)
    (V : WeierstrassCurve K) [V.IsElliptic] (H : Law K V)
    (hH : IsOriginLaw K V H)
    (c : Curve K V ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hc : IsBaseChange (LaurentSeries k) (TateCurve k L) E.law K V H σ c)
    (M : FullLevel K V H L (𝟙 (Base K)))
    (a : Base K ⟶ OpenBase k L D) (g : Curve K V ⟶ D.atlas.descent.family.curve)
    (ha : Classifies k L D.atlas D.two D.cover D.quotient K V H M a g) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E' b ∧ Spec.map (CommRingCat.ofHom σ) ≫ b = a := by
  letI := E.elliptic
  letI : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
  let M' := BaseChange.down hc E.originLaw hH M
  obtain ⟨B, hx, hy⟩ := full_marking_descends (LaurentSeries k) (TateCurve k L)
    E.law E.originLaw L (by omega) E.marking K
    ((𝟙 (Base K)) ≫ baseMap (LaurentSeries k) K σ) M'
  have hx' : baseMap (LaurentSeries k) K σ ≫ B.x.val = M.x.val ≫ c := by
    simpa only [Category.id_comp, M', BaseChange.down, BaseChange.point] using hx
  have hy' : baseMap (LaurentSeries k) K σ ≫ B.y.val = M.y.val ≫ c := by
    simpa only [Category.id_comp, M', BaseChange.down, BaseChange.point] using hy
  let E' : TateLevel k L := ⟨E.elliptic, E.law, E.originLaw, B⟩
  obtain ⟨b, hb, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E'
  obtain ⟨f, hf⟩ := hb
  have hcf : Classifies k L D.atlas D.two D.cover D.quotient K V H M
      (Spec.map (CommRingCat.ofHom σ) ≫ b) (c ≫ f) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hf.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
    · simpa only [Category.assoc] using hc.1.paste_horiz hf.2.1
    · rw [← Category.assoc, hc.2.1, Category.assoc, hf.2.2.1]
      rfl
    · rw [← Category.assoc, ← hx', Category.assoc, hf.2.2.2.1]
      rfl
    · rw [← Category.assoc, ← hy', Category.assoc, hf.2.2.2.2]
      rfl
  refine ⟨E', b, ⟨f, hf⟩, ?_⟩
  exact (compatible_classifying_uniqueness k L hL heven D.atlas D.two D.canonical
    D.cover D.quotient K V H hH M _ a (c ≫ f) g hcf ha).1

/-- In a flat separated family, sections covering the fiber at a generization
cover every fiber specializing from it. This uses the actual section maps. -/
lemma sections_cover_specialization
    {S Y : Scheme.{u}} (f : Y ⟶ S) [Flat f] [IsSeparated f]
    {I : Type*} (s : I → (S ⟶ Y)) (hs : ∀ i, s i ≫ f = 𝟙 S)
    (η z : S) (hηz : η ⤳ z)
    (hη : ∀ y : Y, f y = η → ∃ i, s i η = y)
    (y : Y) (hy : f y = z) : ∃ i, s i z = y := by
  obtain ⟨w, hwy, hw⟩ := Flat.generalizingMap f (a := y) (b := η) (hy ▸ hηz)
  obtain ⟨i, hi⟩ := hη w hw
  haveI : IsClosedImmersion (s i ≫ f) := (hs i).symm ▸ inferInstance
  haveI : IsClosedImmersion (s i) := IsClosedImmersion.of_comp (s i) f
  have hyrange : y ∈ Set.range (s i) :=
    hwy.mem_closed (s i).isClosedEmbedding.isClosed_range ⟨η, hi⟩
  obtain ⟨a, ha⟩ := hyrange
  have haz : a = z := by
    calc
      a = f (s i a) := (congrArg (fun g : S ⟶ S => g a) (hs i)).symm
      _ = z := (congrArg f ha).trans hy
  exact ⟨i, haz ▸ ha⟩

/-- Properness extends a specified family of punctured sections. Flatness then
shows that generic-fiber coverage by this same family gives closed-fiber
coverage. No rationality or splitting of the generic fiber is inferred from
properness: it is the explicit `hcover` input to this general lemma. -/
lemma proper_flat_coverage
    (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (f : Y ⟶ Disk k) [IsProper f] [Flat f]
    {I : Type*} (b : I → (Puncture k ⟶ Y))
    (hb : ∀ i, b i ≫ f = genericInclusion k)
    (η : Puncture k)
    (hcover : ∀ y : Y, f y = genericInclusion k η → ∃ i, b i η = y)
    (y : Y) (hy : f y = closedPoint k) :
    ∃ (i : I) (d : Disk k ⟶ Y), d ≫ f = 𝟙 (Disk k) ∧
      genericInclusion k ≫ d = b i ∧ d (closedPoint k) = y := by
  classical
  have hext : ∀ i, ∃ d : Disk k ⟶ Y,
      d ≫ f = 𝟙 (Disk k) ∧ genericInclusion k ≫ d = b i := by
    intro i
    let S : ValuativeCommSq f :=
      { R := PowerSeries k
        K := LaurentSeries k
        i₁ := b i
        i₂ := 𝟙 (Disk k)
        commSq := ⟨by simpa only [Category.comp_id, genericInclusion] using hb i⟩ }
    have hv : ValuativeCriterion f := by
      have h : IsProper f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1
    obtain ⟨U⟩ := hv S
    exact ⟨U.default.l, U.default.fac_right, U.default.fac_left⟩
  choose d hd hdb using hext
  have hcov : ∀ w : Y, f w = genericInclusion k η →
      ∃ i, d i (genericInclusion k η) = w := by
    intro w hw
    obtain ⟨i, hi⟩ := hcover w hw
    exact ⟨i, (congrArg (fun g : Puncture k ⟶ Y => g η) (hdb i)).trans hi⟩
  obtain ⟨i, hi⟩ := sections_cover_specialization f d hd
    (genericInclusion k η) (closedPoint k)
    (IsLocalRing.specializes_closedPoint _) hcov y hy
  exact ⟨i, d i, hd i, hdb i, hi⟩

/-- The generic point of the actual boundary DVR maps into the given open
level base. The factorization retains the canonical map from the stalk. -/
lemma boundary_fraction_field_lift
    (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space)
    [IsDomain (X.space.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.space.presheaf.stalk x)] :
    ∃ b : Base (FractionRing (X.space.presheaf.stalk x)) ⟶ OpenBase k L D,
      b ≫ X.inclusion =
        Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
          (FractionRing (X.space.presheaf.stalk x)))) ≫ X.space.fromSpecStalk x := by
  let R := X.space.presheaf.stalk x
  let K := FractionRing R
  let g : Base K ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f := X.space.fromSpecStalk x
  have hr : Set.range (g ≫ f) ⊆ Set.range X.inclusion := by
    rintro _ ⟨η, rfl⟩
    by_contra h
    have hc := BoundaryGeometry.boundary_point_closed k L D X ((g ≫ f) η) h
    have hs : (g ≫ f) η ⤳ x := by
      exact ((IsLocalRing.specializes_closedPoint (g η)).map f.continuous).trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
    have he : (g ≫ f) η = x :=
      (Set.mem_singleton_iff.mp (hs.mem_closed hc (Set.mem_singleton _))).symm
    have hlocal : g η = IsLocalRing.closedPoint R := f.isEmbedding.injective
      (he.trans Scheme.fromSpecStalk_closedPoint.symm)
    have hη : η.asIdeal = ⊥ := by
      exact congrArg PrimeSpectrum.asIdeal
        (Subsingleton.elim η (⟨⊥, inferInstance⟩ : PrimeSpectrum K))
    have hz : (g η).asIdeal = ⊥ := by
      change Ideal.comap (algebraMap R K) η.asIdeal = ⊥
      rw [hη]
      change RingHom.ker (algebraMap R K) = ⊥
      exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)
    exact IsDiscreteValuationRing.not_a_field R
      ((congrArg PrimeSpectrum.asIdeal hlocal).symm.trans hz)
  letI := X.openImmersion
  exact ⟨IsOpenImmersion.lift X.inclusion (g ≫ f) hr,
    IsOpenImmersion.lift_fac X.inclusion (g ≫ f) hr⟩

/-- The residue identification uses the actual structural scalar map at the
specified boundary point, rather than an unrelated field structure. -/
lemma boundary_residue_bijective
    (k : Type u) [Field k] [IsAlgClosed k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X) :
    Function.Bijective (ArithmeticThetaCurveDegree.baseToResidue k X.projection x) := by
  letI := X.proper
  have hf := ArithmeticThetaCurveDegree.baseToResidue_finite_of_closed
    X.space k X.projection x (BoundaryGeometry.boundary_point_closed k L D X x hx)
  letI : Algebra k (X.space.residueField x) :=
    (ArithmeticThetaCurveDegree.baseToResidue k X.projection x).toAlgebra
  letI : Module.Finite k (X.space.residueField x) := hf
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Every prescribed geometric boundary point is an actual rational section
over the structural base, using its residue-field morphism. -/
lemma boundary_rational_section
    (k : Type u) [Field k] [IsAlgClosed k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X) :
    ∃ s : Base k ⟶ X.space,
      s ≫ X.projection = 𝟙 (Base k) ∧ s (IsLocalRing.closedPoint k) = x := by
  let e : k ≃+* X.space.residueField x := RingEquiv.ofBijective
    (ArithmeticThetaCurveDegree.baseToResidue k X.projection x)
    (boundary_residue_bijective k L D X x hx)
  let a := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  refine ⟨a ≫ X.space.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← ArithmeticThetaCurveDegree.specMap_baseToResidue,
      ← Spec.map_comp]
    have he : CommRingCat.ofHom (ArithmeticThetaCurveDegree.baseToResidue
        k X.projection x) ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 (CommRingCat.of k) := by
      ext z
      exact e.symm_apply_apply z
    rw [he, Spec.map_id]
  · exact X.space.fromSpecResidueField_apply x _

/-- The accepted boundary geometry supplies the DVR instances needed for the
canonical fraction-field factorization, at every boundary point. -/
lemma boundary_local_trait
    (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X) :
    ∃ hdom : IsDomain (X.space.presheaf.stalk x),
      letI := hdom
      IsDiscreteValuationRing (X.space.presheaf.stalk x) ∧
      ∃ b : Base (FractionRing (X.space.presheaf.stalk x)) ⟶ OpenBase k L D,
        b ≫ X.inclusion =
          Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
            (FractionRing (X.space.presheaf.stalk x)))) ≫ X.space.fromSpecStalk x := by
  letI := X.smooth
  obtain ⟨hdom, hdvr⟩ := BoundaryGeometry.dvr_of_closed X.projection x
    (BoundaryGeometry.boundary_point_closed k L D X x hx)
  letI := hdom
  letI := hdvr
  exact ⟨hdom, hdvr, boundary_fraction_field_lift k L D X x⟩

/-- A boundary trait cannot have its descended parameter extend to the open
Legendre base. Properness of that parameter would extend the generic level
point itself, contradicting the specified boundary center. -/
lemma boundary_parameter_no_extension
    (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X)
    [IsDomain (X.space.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.space.presheaf.stalk x)]
    (p : OpenBase k L D ⟶ Base (ArithmeticThetaLegendreAtlasR0176.LegendreRing k))
    (hp : IsParameter k L D p) [IsProper p]
    (b : Base (FractionRing (X.space.presheaf.stalk x)) ⟶ OpenBase k L D)
    (hb : b ≫ X.inclusion =
      Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
        (FractionRing (X.space.presheaf.stalk x)))) ≫ X.space.fromSpecStalk x) :
    ¬ ∃ a : Spec (X.space.presheaf.stalk x) ⟶
        Base (ArithmeticThetaLegendreAtlasR0176.LegendreRing k),
      Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
        (FractionRing (X.space.presheaf.stalk x)))) ≫ a = b ≫ p ∧
      a ≫ ArithmeticThetaLegendreAtlasR0176.legendreBaseMap k =
        X.space.fromSpecStalk x ≫ X.projection := by
  rintro ⟨a, ha, hak⟩
  let R := X.space.presheaf.stalk x
  letI : ValuationRing R :=
    of_isDiscreteValuationRing (X.space.presheaf.stalk x)
  let K := FractionRing R
  let g : Base K ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f := X.space.fromSpecStalk x
  let S : ValuativeCommSq p :=
    { R := R
      K := K
      i₁ := b
      i₂ := a
      commSq := ⟨ha.symm⟩ }
  have hpv : ValuativeCriterion p := by
    have h : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨U⟩ := hpv S
  let c := U.default.l
  have hc : c ≫ p = a := U.default.fac_right
  have hgc : g ≫ c = b := U.default.fac_left
  have hck : (c ≫ X.inclusion) ≫ X.projection = f ≫ X.projection := by
    rw [Category.assoc, X.over_eq, ← hp.2, ← Category.assoc, hc]
    exact hak
  have hgen : g ≫ (c ≫ X.inclusion) = g ≫ f := by
    rw [← Category.assoc, hgc, hb]
  let T : ValuativeCommSq X.projection :=
    { R := R
      K := K
      i₁ := g ≫ f
      i₂ := f ≫ X.projection
      commSq := ⟨Category.assoc _ _ _⟩ }
  have hv : ValuativeCriterion X.projection := by
    have h := X.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨V⟩ := hv T
  have he : c ≫ X.inclusion = f := congrArg CommSq.LiftStruct.l
    ((V.uniq ⟨c ≫ X.inclusion, hgen, hck⟩).trans
      (V.uniq ⟨f, rfl, rfl⟩).symm)
  apply hx
  refine ⟨c (IsLocalRing.closedPoint R), ?_⟩
  exact (congrArg (fun m : Spec R ⟶ X.space => m (IsLocalRing.closedPoint R)) he).trans
    Scheme.fromSpecStalk_closedPoint

open Polynomial
lemma integral_of_legendre_equation
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (a : K) (c : R)
    (h : (1-a+a^2)^3 = algebraMap R K c * (a^2*(1-a)^2)) : IsIntegral R a := by
  let p : R[X] := (X^2-X+1)^3 - C c * (X^2*(1-X)^2)
  have hp : p.Monic := by dsimp [p]; monicity!
  refine ⟨p, hp, ?_⟩
  change Polynomial.eval₂ (algebraMap R K) a p = 0
  simp only [p, eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul, eval₂_X, eval₂_one, eval₂_C]
  rw [show a^2-a+1 = 1-a+a^2 by ring, h, sub_self]

lemma legendre_integral_elements
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (a : K) (c : R) (h0 : a ≠ 0) (h1 : 1-a ≠ 0)
    (h : (1-a+a^2)^3 = algebraMap R K c * (a^2*(1-a)^2)) :
    IsIntegral R a ∧ IsIntegral R a⁻¹ ∧ IsIntegral R (1-a)⁻¹ := by
  have hi : (1-a⁻¹+(a⁻¹)^2)^3 = algebraMap R K c * ((a⁻¹)^2*(1-a⁻¹)^2) := by
    field_simp
    linear_combination h
  have hs : (1-(1-a)+(1-a)^2)^3 =
      algebraMap R K c * ((1-a)^2*(1-(1-a))^2) := by
    linear_combination h
  have his : (1-(1-a)⁻¹+((1-a)⁻¹)^2)^3 =
      algebraMap R K c * (((1-a)⁻¹)^2*(1-(1-a)⁻¹)^2) := by
    field_simp
    linear_combination h
  exact ⟨integral_of_legendre_equation R K a c h,
    integral_of_legendre_equation R K a⁻¹ c hi,
    integral_of_legendre_equation R K (1-a)⁻¹ c his⟩
lemma integral_legendre_parameter_units
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (a : K) (c : R) (h0 : a ≠ 0) (h1 : 1-a ≠ 0)
    (h : (1-a+a^2)^3 = algebraMap R K c * (a^2*(1-a)^2)) :
    ∃ r : R, algebraMap R K r = a ∧ IsUnit (r*(r-1)) := by
  obtain ⟨hi, hii, hsi⟩ := legendre_integral_elements R K a c h0 h1 h
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hii
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hsi
  have hunit : r*s = 1 := IsFractionRing.injective R K (by
    rw [map_mul, hr, hs, mul_inv_cancel₀ h0, map_one])
  have hunit' : (1-r)*t = 1 := IsFractionRing.injective R K (by
    rw [map_mul, map_sub, map_one, hr, ht, mul_inv_cancel₀ h1])
  refine ⟨r, hr, (isUnit_iff_exists_inv.mpr ⟨s, hunit⟩).mul ?_⟩
  have hu : IsUnit (1-r) := isUnit_iff_exists_inv.mpr ⟨t, hunit'⟩
  convert hu.neg using 1; ring
open ArithmeticThetaLegendreAtlasR0176
lemma integral_legendre_parameter_lift
    (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    [IsFractionRing R K]
    (α : LegendreRing k →ₐ[k] K) (c : R)
    (h0 : α (parameter k) ≠ 0) (h1 : 1-α (parameter k) ≠ 0)
    (h : (1-α (parameter k)+(α (parameter k))^2)^3 =
      algebraMap R K c * ((α (parameter k))^2*(1-α (parameter k))^2)) :
    ∃ β : LegendreRing k →ₐ[k] R, (IsScalarTower.toAlgHom k R K).comp β = α := by
  obtain ⟨r, hr, hu⟩ := integral_legendre_parameter_units R K _ c h0 h1 h
  obtain ⟨β, hβ⟩ := ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.exists_parameterMap
    k R r hu
  refine ⟨β, ?_⟩
  have he : ((IsScalarTower.toAlgHom k R K).comp β).toRingHom = α.toRingHom := by
    apply ArithmeticThetaCompatibleLevelR0178.CompatibleClassifyingUniqueness.parameter_hom_ext
    · ext z
      simp
    · change algebraMap R K (β (parameter k)) = α (parameter k)
      rw [hβ, hr]
  exact AlgHom.ext (fun z => RingHom.congr_fun he z)

lemma integral_j_parameter_lift
    (k R K : Type u) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [CharZero K] [Algebra k R] [Algebra R K] [Algebra k K]
    [IsScalarTower k R K] [IsFractionRing R K]
    (α : LegendreRing k →ₐ[k] K) (j : R)
    (hj : algebraMap R K j = 256 * (1-α (parameter k)+(α (parameter k))^2)^3 /
      ((α (parameter k))^2*(1-α (parameter k))^2)) :
    ∃ β : LegendreRing k →ₐ[k] R, (IsScalarTower.toAlgHom k R K).comp β = α := by
  let a := α (parameter k)
  have hu : IsUnit (a*(a-1)) := by
    have hu := IsLocalization.Away.algebraMap_isUnit
      (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
    simpa only [map_mul, map_sub, map_one, parameter, a] using hu.map α
  have h0 : a ≠ 0 := (IsUnit.mul_iff.mp hu).1.ne_zero
  have h1 : 1-a ≠ 0 := by
    intro hh
    apply (IsUnit.mul_iff.mp hu).2.ne_zero
    linear_combination -hh
  let c : R := algebraMap k R ((256 : k)⁻¹) * j
  have hc : algebraMap R K c = (256 : K)⁻¹ * algebraMap R K j := by
    dsimp only [c]
    rw [map_mul, ← IsScalarTower.algebraMap_apply k R K, map_inv₀, map_ofNat]
  apply integral_legendre_parameter_lift k R K α c h0 h1
  change (1-a+a^2)^3 = algebraMap R K c * (a^2*(1-a)^2)
  rw [hc, hj]
  change (1-a+a^2)^3 = (256 : K)⁻¹ *
    (256 * (1-a+a^2)^3 / (a^2*(1-a)^2)) * (a^2*(1-a)^2)
  field_simp [h0, h1]
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179
set_option backward.isDefEq.respectTransparency false in
lemma boundary_j_not_integral
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (x : X.space) (hx : x ∈ boundary k L D X)
    [IsDomain (X.space.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.space.presheaf.stalk x)]
    (p : OpenBase k L D ⟶ Base (LegendreRing k))
    (hp : IsParameter k L D p) [IsProper p]
    (b : Base (FractionRing (X.space.presheaf.stalk x)) ⟶ OpenBase k L D)
    (hb : b ≫ X.inclusion =
      Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
        (FractionRing (X.space.presheaf.stalk x)))) ≫ X.space.fromSpecStalk x) :
    let a := (Spec.preimage (b ≫ p)).hom (parameter k)
    ¬ ∃ j : X.space.presheaf.stalk x,
      algebraMap (X.space.presheaf.stalk x) (FractionRing (X.space.presheaf.stalk x)) j =
        256*(1-a+a^2)^3/(a^2*(1-a)^2) := by
  let R := X.space.presheaf.stalk x
  let K := FractionRing R
  let f := X.space.fromSpecStalk x
  let σ : k →+* R := (Spec.preimage (f ≫ X.projection)).hom
  letI : Algebra k R := σ.toAlgebra
  letI : CharZero K := charZero_of_injective_ringHom (algebraMap k K).injective
  let g : Base K ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let α₀ : LegendreRing k →+* K := (Spec.preimage (b ≫ p)).hom
  have hs : α₀.comp (algebraMap k (LegendreRing k)) = algebraMap k K := by
    have he : CommRingCat.ofHom (α₀.comp (algebraMap k (LegendreRing k))) =
        CommRingCat.ofHom (algebraMap k K) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      change Spec.map (CommRingCat.ofHom α₀) ≫ legendreBaseMap k = _
      rw [show Spec.map (CommRingCat.ofHom α₀) = b ≫ p from Spec.map_preimage _]
      rw [Category.assoc, hp.2, ← X.over_eq, ← Category.assoc, hb, Category.assoc]
      change g ≫ f ≫ X.projection = Spec.map (CommRingCat.ofHom ((algebraMap R K).comp σ))
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      rw [show Spec.map (CommRingCat.ofHom σ) = f ≫ X.projection from Spec.map_preimage _]
    exact congrArg CommRingCat.Hom.hom he
  let α : LegendreRing k →ₐ[k] K :=
    { __ := α₀
      commutes' := RingHom.congr_fun hs }
  change ¬ ∃ j : R, algebraMap R K j =
    256*(1-α (parameter k)+(α (parameter k))^2)^3 /
      ((α (parameter k))^2*(1-α (parameter k))^2)
  rintro ⟨j, hj⟩
  obtain ⟨β, hβ⟩ := integral_j_parameter_lift k R K α j hj
  let a : Spec R ⟶ Base (LegendreRing k) := Spec.map (CommRingCat.ofHom β.toRingHom)
  apply boundary_parameter_no_extension k L D X x hx p hp b hb
  refine ⟨a, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      Spec.map (CommRingCat.ofHom β.toRingHom) = b ≫ p
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hh : (algebraMap R K).comp β.toRingHom = α₀ := congrArg AlgHom.toRingHom hβ
    rw [hh]
    exact Spec.map_preimage _
  · change Spec.map (CommRingCat.ofHom β.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (LegendreRing k))) = f ≫ X.projection
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hh : β.toRingHom.comp (algebraMap k (LegendreRing k)) = σ := by
      ext z
      exact β.commutes z
    rw [hh]
    exact Spec.map_preimage _
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179
set_option backward.isDefEq.respectTransparency false in
lemma every_boundary_has_j_pole
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D)
    (x : X.space) (hx : x ∈ boundary k L D X) :
    ∃ hdom : IsDomain (X.space.presheaf.stalk x),
      letI := hdom
      IsDiscreteValuationRing (X.space.presheaf.stalk x) ∧
      ∃ (p : OpenBase k L D ⟶ Base (LegendreRing k))
        (b : Base (FractionRing (X.space.presheaf.stalk x)) ⟶ OpenBase k L D),
        IsParameter k L D p ∧ IsFinite p ∧
        b ≫ X.inclusion =
          Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
            (FractionRing (X.space.presheaf.stalk x)))) ≫ X.space.fromSpecStalk x ∧
        let a := (Spec.preimage (b ≫ p)).hom (parameter k)
        ¬ ∃ j : X.space.presheaf.stalk x,
          algebraMap (X.space.presheaf.stalk x) (FractionRing (X.space.presheaf.stalk x)) j =
            256*(1-a+a^2)^3/(a^2*(1-a)^2) := by
  obtain ⟨hdom, hdvr, b, hb⟩ := boundary_local_trait k L D X x hx
  letI := hdom
  letI := hdvr
  obtain ⟨p, hp, _⟩ := descended_legendre_parameter k L hL heven D
  letI := hp.2.1
  exact ⟨hdom, hdvr, p, b, hp.1, hp.2.1, hb,
    boundary_j_not_integral k L D X x hx p hp.1 b hb⟩

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreComparisonR0177
lemma pointed_coefficient_comparison_of_j_eq
    (F K : Type u) [Field F] [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (G : Law F W) (hG : IsOriginLaw F W G)
    (σ : F →+* K) (V : WeierstrassCurve K) [V.IsElliptic]
    (H : Law K V) (hH : IsOriginLaw K V H)
    (hj : V.j = σ W.j) :
    ∃ c : Curve K V ⟶ Curve F W, IsBaseChange F W G K V H σ c := by
  letI : Algebra F K := σ.toAlgebra
  haveI : (W.map σ).IsElliptic := inferInstance
  have hj' : (W.map σ).j = V.j := (WeierstrassCurve.map_j W σ).trans hj.symm
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (W.map σ) V hj'
  have hvar : ∃ e : Curve K V ⟶ Curve K (W.map σ), IsIso e ∧
      e ≫ structureMap K (W.map σ) = structureMap K V ∧
      origin K V ≫ e = origin K (W.map σ) := by
    rw [← hC]
    obtain ⟨e, _, hi, he, ho, _⟩ := NormalFormConstruction.variable_comparison (W.map σ) C
    exact ⟨e, hi, he, ho⟩
  obtain ⟨e, hi, he, ho⟩ := hvar
  letI := hi
  obtain ⟨c, _, hc, hco, _⟩ := NormalFormConstruction.coefficient_comparison W σ
  have hepb : IsPullback e (structureMap K V) (structureMap K (W.map σ)) (𝟙 (Base K)) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  have hpb : IsPullback (e ≫ c) (structureMap K V) (structureMap F W)
      (baseMap F K σ) := by
    simpa only [Category.id_comp, baseMap] using hepb.paste_horiz hc
  have hpo : origin K V ≫ (e ≫ c) = baseMap F K σ ≫ origin F W := by
    rw [← Category.assoc, ho, hco]
    rfl
  exact ⟨e ≫ c, MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change G H hG hH σ _ hpb hpo⟩
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLevelCompactificationR0179
lemma classifying_map_descends_of_j_eq
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra k K]
    (σ : LaurentSeries k →+* K)
    (hσ : σ.comp (algebraMap k (LaurentSeries k)) = algebraMap k K)
    (V : WeierstrassCurve K) [V.IsElliptic] (H : Law K V)
    (hH : IsOriginLaw K V H) (hj : V.j = σ (tateJ k L))
    (M : FullLevel K V H L (𝟙 (Base K)))
    (a : Base K ⟶ OpenBase k L D) (g : Curve K V ⟶ D.atlas.descent.family.curve)
    (ha : Classifies k L D.atlas D.two D.cover D.quotient K V H M a g) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E' b ∧ Spec.map (CommRingCat.ofHom σ) ≫ b = a := by
  letI := E.elliptic
  have htj : (TateCurve k L).j = tateJ k L := by
    simp only [WeierstrassCurve.j, tateJ, Units.val_inv_eq_inv_val,
      WeierstrassCurve.coe_Δ', div_eq_mul_inv, mul_comm]
  obtain ⟨c, hc⟩ := pointed_coefficient_comparison_of_j_eq
    (LaurentSeries k) K (TateCurve k L) E.law E.originLaw σ V H hH (hj.trans (congrArg σ htj).symm)
  exact classifying_map_descends k L hL heven D E K σ hσ V H hH c hc M a g ha
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaLegendreComparisonR0177
open CompatibleClassifyingUniqueness
lemma tate_j_fiber_geometric_descent
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra k K]
    (σ : LaurentSeries k →+* K)
    (hσ : σ.comp (algebraMap k (LaurentSeries k)) = algebraMap k K)
    (a : Base K ⟶ OpenBase k L D)
    (ha : a ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hj : let z := (Spec.preimage (a ≫ p)).hom (parameter k)
      256*(1-z+z^2)^3/(z^2*(1-z)^2) = σ (tateJ k L)) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E' b ∧ Spec.map (CommRingCat.ofHom σ) ≫ b = a := by
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨w, hw⟩ := lift_geometric_point D.quotient.quotient.q a
  let q := w ≫ D.cover.inclusion
  let α := (Spec.preimage (a ≫ p)).hom
  have hq : q ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α) := by
    rw [show Spec.map (CommRingCat.ofHom α) = a ≫ p from Spec.map_preimage _]
    change (w ≫ D.cover.inclusion) ≫ D.atlas.level.projection = _
    rw [Category.assoc, ← hp.1, ← Category.assoc, hw]
  obtain ⟨P⟩ := presentation_exists k L D.atlas K α q hq
  have hqa : q ≫ D.atlas.quotient.q = a ≫ D.quotient.inclusion := by
    change (w ≫ D.cover.inclusion) ≫ D.atlas.quotient.q = _
    rw [Category.assoc, D.quotient.cartesian.w, ← Category.assoc, hw]
  let V := (legendre k).map α
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.toAlgebra
  letI : V.IsElliptic := inferInstance
  have hc : Classifies k L D.atlas D.two D.cover D.quotient K V P.law P.marking a
      P.comparison := by
    refine ⟨ha, ?_, ?_, ?_, ?_⟩
    · rw [← hqa]; exact P.cartesian
    · rw [← hqa]; exact P.origin_eq
    · rw [← hqa]; exact P.x_eq
    · rw [← hqa]; exact P.y_eq
  have hleg : V = legendreAt K (α (parameter k)) := by
    ext <;> simp [V, legendre, legendreAt]
  have hjV : V.j = σ (tateJ k L) := by
    calc
      V.j = V.c₄^3/V.Δ := by
        simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
          WeierstrassCurve.coe_Δ', div_eq_mul_inv, mul_comm]
      _ = 256*(1-α (parameter k)+(α (parameter k))^2)^3 /
          ((α (parameter k))^2*(1-α (parameter k))^2) := by
        rw [hleg, TateLevelClassifyingParameter.legendre_invariant]
      _ = σ (tateJ k L) := hj
  exact classifying_map_descends_of_j_eq k L hL heven D E K σ hσ V P.law P.originLaw
    hjV P.marking a P.comparison hc
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaLevelCompactificationR0179
lemma tate_j_fiber_descent
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (σ : LaurentSeries k →+* K)
    (hσ : σ.comp (algebraMap k (LaurentSeries k)) = algebraMap k K)
    (a : Base K ⟶ OpenBase k L D)
    (ha : a ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hj : let z := (Spec.preimage (a ≫ p)).hom (parameter k)
      256*(1-z+z^2)^3/(z^2*(1-z)^2) = σ (tateJ k L)) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E' b ∧ Spec.map (CommRingCat.ofHom σ) ≫ b = a := by
  let K' := AlgebraicClosure K
  let γ := algebraMap K K'
  let σ' := γ.comp σ
  let a' := Spec.map (CommRingCat.ofHom γ) ≫ a
  have hs : σ'.comp (algebraMap k (LaurentSeries k)) = algebraMap k K' := by
    rw [show σ' = γ.comp σ from rfl, RingHom.comp_assoc, hσ]
    exact (IsScalarTower.algebraMap_eq k K K').symm
  have ha' : a' ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K')) := by
    rw [show a' = Spec.map (CommRingCat.ofHom γ) ≫ a from rfl,
      Category.assoc, ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq k K K']
  have hα : (Spec.preimage (a' ≫ p)).hom = γ.comp (Spec.preimage (a ≫ p)).hom := by
    have he : CommRingCat.ofHom (Spec.preimage (a' ≫ p)).hom =
        CommRingCat.ofHom (γ.comp (Spec.preimage (a ≫ p)).hom) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, CommRingCat.ofHom_comp,
        Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
      exact Category.assoc _ _ _
    exact congrArg CommRingCat.Hom.hom he
  have hj' : let z := (Spec.preimage (a' ≫ p)).hom (parameter k)
      256*(1-z+z^2)^3/(z^2*(1-z)^2) = σ' (tateJ k L) := by
    dsimp only
    rw [hα]
    simpa only [σ', RingHom.comp_apply, map_div₀, map_mul, map_pow, map_add,
      map_sub, map_one, map_ofNat] using congrArg γ hj
  obtain ⟨E', b, hb, he⟩ := tate_j_fiber_geometric_descent k L hL heven D E p hp
    K' σ' hs a' ha' hj'
  refine ⟨E', b, hb, ?_⟩
  apply CompatibleClassifyingUniqueness.affine_ext γ γ.injective
  simpa only [σ', a', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using he

/-- Over an algebraically closed coefficient field the accepted marking and
extension providers construct at least one actual boundary-centered Tate disk.
This does not assert coverage of an arbitrarily prescribed boundary point. -/
lemma exists_canonical_disk
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) :
    ∃ (ζ : k) (E : TateLevel k L)
      (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space),
      IsPrimitiveRoot ζ L ∧ CanonicalMarking k L ζ E ∧
      ClassifiesTate k L D E b ∧ Extends k L D X b d := by
  haveI : NeZero L := ⟨by omega⟩
  haveI : NeZero (L : k) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne L)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k L
  obtain ⟨E, hE⟩ := tate_full_level_marking k L hL heven ζ hζ
  obtain ⟨b, hb, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E
  obtain ⟨d, hd, _⟩ := tate_cusp_disk_extension k L hL heven D E X b hb
  exact ⟨ζ, E, b, d, hζ, hE, hb, hd⟩

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177

def legendreJSection (k : Type u) [Field k] [CharZero k] : LegendreRing k :=
  letI := (legendre_family_geometry k).2.2.2.1
  (legendre k).j

def jPolynomialMap (k : Type u) [Field k] [CharZero k] :
    Polynomial k →ₐ[k] LegendreRing k := Polynomial.aeval (legendreJSection k)

def legendreJMap (k : Type u) [Field k] [CharZero k] :
    Base (LegendreRing k) ⟶ Base (Polynomial k) :=
  Spec.map (CommRingCat.ofHom (jPolynomialMap k).toRingHom)

lemma legendreJMap_over (k : Type u) [Field k] [CharZero k] :
    legendreJMap k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) =
      legendreBaseMap k := by
  rw [legendreJMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : (jPolynomialMap k).toRingHom.comp (algebraMap k (Polynomial k)) =
      algebraMap k (LegendreRing k) := by ext z; exact (jPolynomialMap k).commutes z
  rw [he]
  rfl

lemma map_legendreJSection
    (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    (α : LegendreRing k →+* K) :
    α (legendreJSection k) = 256*(1-α (parameter k)+(α (parameter k))^2)^3 /
      ((α (parameter k))^2*(1-α (parameter k))^2) := by
  letI := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.toAlgebra
  letI : ((legendre k).map α).IsElliptic := inferInstance
  have he : (legendre k).map α = legendreAt K (α (parameter k)) := by
    ext <;> simp [legendre, legendreAt]
  change α (legendre k).j = _
  rw [← WeierstrassCurve.map_j]
  calc
    ((legendre k).map α).j = ((legendre k).map α).c₄^3 / ((legendre k).map α).Δ := by
      simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
        WeierstrassCurve.coe_Δ', div_eq_mul_inv, mul_comm]
    _ = _ := by rw [he, TateLevelClassifyingParameter.legendre_invariant]

lemma legendreJMap_valuative_existence
    (k : Type u) [Field k] [CharZero k] :
    ValuativeCriterion.Existence (legendreJMap k) := by
  intro T
  let R := T.R
  let K := T.K
  let ι := algebraMap R K
  let α₀ := (Spec.preimage T.i₁).hom
  let β₀ := (Spec.preimage T.i₂).hom
  have hring : α₀.comp (jPolynomialMap k).toRingHom = ι.comp β₀ := by
    have he : CommRingCat.ofHom (α₀.comp (jPolynomialMap k).toRingHom) =
        CommRingCat.ofHom (ι.comp β₀) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
      rw [show Spec.map (CommRingCat.ofHom α₀) = T.i₁ from Spec.map_preimage _,
        show Spec.map (CommRingCat.ofHom β₀) = T.i₂ from Spec.map_preimage _]
      exact T.commSq.w
    exact congrArg CommRingCat.Hom.hom he
  let σ := β₀.comp (algebraMap k (Polynomial k))
  letI : Algebra k R := σ.toAlgebra
  letI : Algebra k K := (ι.comp σ).toAlgebra
  letI : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : CharZero K := charZero_of_injective_ringHom (algebraMap k K).injective
  let α : LegendreRing k →ₐ[k] K :=
    { __ := α₀
      commutes' := by
        intro z
        have hz := RingHom.congr_fun hring (algebraMap k (Polynomial k) z)
        change α₀ (algebraMap k (LegendreRing k) z) = ι (β₀ (algebraMap k (Polynomial k) z))
        change α₀ ((jPolynomialMap k) (algebraMap k (Polynomial k) z)) =
          ι (β₀ (algebraMap k (Polynomial k) z)) at hz
        rw [(jPolynomialMap k).commutes] at hz
        exact hz }
  have hj : ι (β₀ Polynomial.X) =
      256*(1-α (parameter k)+(α (parameter k))^2)^3 /
        ((α (parameter k))^2*(1-α (parameter k))^2) := by
    calc
      ι (β₀ Polynomial.X) = α₀ (legendreJSection k) := by
        have hx := RingHom.congr_fun hring Polynomial.X
        change α₀ (Polynomial.aeval (legendreJSection k) Polynomial.X) = ι (β₀ Polynomial.X) at hx
        rw [Polynomial.aeval_X] at hx
        exact hx.symm
      _ = _ := map_legendreJSection k K α₀
  obtain ⟨β, hβ⟩ := integral_j_parameter_lift k R K α (β₀ Polynomial.X) hj
  let d : Base R ⟶ Base (LegendreRing k) := Spec.map (CommRingCat.ofHom β.toRingHom)
  have hβ' : ι.comp β.toRingHom = α₀ := congrArg AlgHom.toRingHom hβ
  have hleft : Spec.map (CommRingCat.ofHom ι) ≫ d = T.i₁ := by
    rw [show d = Spec.map (CommRingCat.ofHom β.toRingHom) from rfl,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hβ']
    exact Spec.map_preimage _
  have hright : d ≫ legendreJMap k = T.i₂ := by
    have he : β.toRingHom.comp (jPolynomialMap k).toRingHom = β₀ := by
      apply RingHom.ext
      intro z
      apply IsFractionRing.injective R K
      have h := RingHom.congr_fun hring z
      have hb := RingHom.congr_fun hβ' ((jPolynomialMap k) z)
      exact hb.trans h
    change Spec.map (CommRingCat.ofHom β.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (jPolynomialMap k).toRingHom) = T.i₂
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]
    exact Spec.map_preimage _
  exact ⟨⟨d, hleft, hright⟩⟩

lemma legendreJMap_finite (k : Type u) [Field k] [CharZero k] :
    IsFinite (legendreJMap k) := by
  letI := (legendre_family_geometry k).2.2.2.2.1
  letI : LocallyOfFiniteType (legendreJMap k ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
    rw [legendreJMap_over]; infer_instance
  letI : LocallyOfFiniteType (legendreJMap k) := locallyOfFiniteType_of_comp (legendreJMap k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  letI : IsAffineHom (legendreJMap k) := isAffineHom_of_isAffine _
  letI : IsProper (legendreJMap k) := IsProper.of_valuativeCriterion _
    (ValuativeCriterion.iff.mpr ⟨legendreJMap_valuative_existence k,
      IsSeparated.valuativeCriterion _⟩)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179
open SmoothProjectiveLevelCompletionR0179

lemma smooth_curve_closed_or_field
    (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Base k) [SmoothOfRelativeDimension 1 p] (y : Y) :
    IsClosed ({y} : Set Y) ∨ IsField (Y.presheaf.stalk y) := by
  letI : IsReduced Y := isReduced_of_smooth_over_field (g := p) inferInstance
  let C : IrreducibleCloseds Y := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  rcases Order.krullDim_le_one_iff.mp
    (SmoothOfRelativeDimension.topologicalKrullDim_le p 1) C with hmin | hmax
  · left
    apply isClosed_of_closure_subset
    intro z hz
    let E : IrreducibleCloseds Y := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hEC : E ≤ C := isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz)
    have he : closure ({y} : Set Y) = closure {z} := SetLike.ext'_iff.mp
      (le_antisymm (hmin hEC) hEC : C = E)
    exact Set.mem_singleton_iff.mpr ((isGenericPoint_closure (x := y)).eq
      (show IsGenericPoint z (closure {y}) by rw [he]; exact isGenericPoint_closure)).symm
  · right
    apply isField_stalk_of_closure_mem_irreducibleComponents Y y
    rw [irreducibleComponents_eq_maximals_closed]
    refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
    intro S hS hCS
    exact hmax (b := ⟨S, hS.2, hS.1⟩) hCS

lemma closed_of_finite_image_closed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (x : X) (hx : IsClosed ({f x} : Set Y)) :
    IsClosed ({x} : Set X) := by
  have hcf : IsClosed (f ⁻¹' {f x}) := hx.preimage f.continuous
  have hp : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) :=
    (f.quasiFiniteAt x).isClopen_singleton_asFiber.1
  have hh := (f.fiberHomeo (f x)).isClosedMap _ hp
  have hc := hcf.isClosedEmbedding_subtypeVal.isClosedMap _ hh
  simpa [Scheme.Hom.asFiber] using hc

lemma finite_smooth_curves_flat
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Base k) (q : Y ⟶ Base k)
    [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension 1 q]
    (f : X ⟶ Y) [IsFinite f] : Flat f := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  apply Flat.of_stalkMap
  intro x
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  rcases smooth_curve_closed_or_field k q (f x) with hc | hf
  · have hcx := closed_of_finite_image_closed f x hc
    letI := Smooth.isRegularLocalRing_stalk (f := p) x
    letI := Smooth.isRegularLocalRing_stalk (f := q) (f x)
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero f x)
      ((SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed k p 1 x hcx).trans
        (SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed k q 1 (f x) hc).symm)
  · letI := hf.toField
    change Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    infer_instance

abbrev JLine (k : Type u) [Field k] := Base (Polynomial k)
def jLineStructure (k : Type u) [Field k] : JLine k ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
abbrev JCompletion (k : Type u) [Field k] := CurveCompletion k (JLine k) (jLineStructure k)

lemma jLine_smooth (k : Type u) [Field k] : SmoothOfRelativeDimension 1 (jLineStructure k) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{1} k) := by
    simpa using P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr.SplitTorusSmoothEngine.isStandardSmoothOfRelativeDimension_mvPolynomial k PUnit.{1}
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv k PUnit.{1})
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance)

lemma jCompletion_exists (k : Type u) [Field k] [CharZero k] : Nonempty (JCompletion k) := by
  letI := jLine_smooth k
  exact integral_completion k (JLine k) (jLineStructure k)

lemma extension_to_proper
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D)
    {Y : Scheme.{u}} (q : Y ⟶ Base k) [IsProper q]
    (b : OpenBase k L D ⟶ Y) (hb : b ≫ q = openStructure k L D) :
    ∃ F : X.space ⟶ Y, F ≫ q = X.projection ∧ X.inclusion ≫ F = b := by
  letI := X.openImmersion
  letI := X.proper
  letI := CompactifiedLevelForgetting.reduced k D X
  letI : IsLocallyNoetherian X.space := LocallyOfFiniteType.isLocallyNoetherian X.projection
  let U := X.inclusion.opensRange
  let e : OpenBase k L D ≅ (U : Scheme.{u}) :=
    IsOpenImmersion.isoOfRangeEq X.inclusion U.ι (by simp [U])
  have hei : e.inv ≫ X.inclusion = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have heh : e.hom ≫ U.ι = X.inclusion := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hval : ∀ x : X.space, x ∉ U →
      (∃ _ : IsDomain (X.space.presheaf.stalk x), IsDiscreteValuationRing (X.space.presheaf.stalk x)) ∧
        ∃ y : X.space, y ∈ U ∧ y ⤳ x := by
    intro x hx
    obtain ⟨hdom, hdvr, a, ha⟩ := boundary_local_trait k L D X x hx
    letI := hdom
    letI := hdvr
    let η := IsLocalRing.closedPoint (FractionRing (X.space.presheaf.stalk x))
    let g := Spec.map (CommRingCat.ofHom (algebraMap (X.space.presheaf.stalk x)
      (FractionRing (X.space.presheaf.stalk x))))
    refine ⟨⟨hdom, hdvr⟩, X.inclusion (a η), ⟨a η, rfl⟩, ?_⟩
    have he : X.inclusion (a η) = X.space.fromSpecStalk x (g η) :=
      congrArg (fun m => m η) ha
    rw [he]
    exact ((IsLocalRing.specializes_closedPoint (g η)).map
      (X.space.fromSpecStalk x).continuous).trans (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
  obtain ⟨F, hF, hFi⟩ :=
    exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
      X.projection q U (e.inv ≫ b) (by
        rw [Category.assoc, hb, ← X.over_eq, ← Category.assoc, hei]) hval
  refine ⟨F, hF, ?_⟩
  rw [← heh, Category.assoc, hFi]
  simp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179

lemma extension_finite_to_jCompletion
    (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (Y : JCompletion k)
    (f : OpenBase k L D ⟶ JLine k) [IsFinite f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) : IsFinite F := by
  letI := X.proper
  letI := Y.proper
  letI := Y.openImmersion
  letI : IsProper (F ≫ Y.projection) := hF.symm ▸ X.proper
  letI : IsProper F := IsProper.of_comp F Y.projection
  letI : LocallyQuasiFinite F := LocallyQuasiFinite.of_finite_preimage_singleton F fun y => by
    have hfin := f.finite_preimage ((Set.finite_singleton y).preimage
      Y.inclusion.isOpenEmbedding.injective.injOn)
    apply ((hfin.image X.inclusion.base).union (BoundaryGeometry.boundary_finite k L D X)).subset
    intro x hx
    by_cases hxi : x ∈ Set.range X.inclusion.base
    · obtain ⟨z, rfl⟩ := hxi
      apply Or.inl
      refine ⟨z, ?_, rfl⟩
      change (f ≫ Y.inclusion) z = y
      rw [← hi]
      exact hx
    · exact Or.inr hxi
  exact IsFinite.of_isProper_of_locallyQuasiFinite F

lemma extension_j_cartesian
    (k : Type u) [Field k] (L : ℕ) (D : LevelData k L)
    (X : Compactification k L D) (Y : JCompletion k)
    (f : OpenBase k L D ⟶ JLine k) [IsFinite f]
    (F : X.space ⟶ Y.space) (hF : F ≫ Y.projection = X.projection)
    (hi : X.inclusion ≫ F = f ≫ Y.inclusion) :
    IsPullback X.inclusion f F Y.inclusion := by
  letI := X.openImmersion
  letI := Y.openImmersion
  letI := extension_finite_to_jCompletion k L D X Y f F hF hi
  let a : OpenBase k L D ⟶ pullback F Y.inclusion := pullback.lift X.inclusion f hi
  have ha : a ≫ pullback.fst F Y.inclusion = X.inclusion := pullback.lift_fst _ _ _
  have hb : a ≫ pullback.snd F Y.inclusion = f := pullback.lift_snd _ _ _
  letI : IsOpenImmersion (a ≫ pullback.fst F Y.inclusion) := ha.symm ▸ X.openImmersion
  letI : IsOpenImmersion a := IsOpenImmersion.of_comp a (pullback.fst F Y.inclusion)
  letI : IsProper (a ≫ pullback.snd F Y.inclusion) := by rw [hb]; infer_instance
  letI : IsProper a := IsProper.of_comp a (pullback.snd F Y.inclusion)
  letI : IsDominant a := ⟨by
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    have ho := (pullback.fst F Y.inclusion).isOpenEmbedding.isOpenMap O hO
    obtain ⟨x, ⟨z, hzO, hzx⟩, w, hwx⟩ :=
      X.dense.inter_open_nonempty _ ho (hOne.image (pullback.fst F Y.inclusion))
    refine ⟨z, hzO, w, ?_⟩
    apply (pullback.fst F Y.inclusion).isOpenEmbedding.injective
    exact (congrArg (fun m => m w) ha).trans (hwx.trans hzx.symm)⟩
  letI : Surjective a := inferInstance
  letI : IsIso a := (isIso_iff_isOpenImmersion_and_surjective a).mpr ⟨inferInstance, inferInstance⟩
  exact IsPullback.of_iso_pullback ⟨hi⟩ (asIso a) ha hb

lemma compactified_j_exists
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (X : Compactification k L D) (Y : JCompletion k) :
    ∃ (p : OpenBase k L D ⟶ Base (LegendreRing k)) (F : X.space ⟶ Y.space),
      IsParameter k L D p ∧
      F ≫ Y.projection = X.projection ∧
      X.inclusion ≫ F = (p ≫ legendreJMap k) ≫ Y.inclusion ∧
      IsPullback X.inclusion (p ≫ legendreJMap k) F Y.inclusion ∧
      IsFinite F ∧ Flat F := by
  obtain ⟨p, hp, _⟩ := descended_legendre_parameter k L hL heven D
  letI := hp.2.1
  letI := legendreJMap_finite k
  letI := Y.proper
  letI := X.smooth
  letI := Y.smooth
  have hover : ((p ≫ legendreJMap k) ≫ Y.inclusion) ≫ Y.projection =
      openStructure k L D := by
    rw [Category.assoc, Y.over_eq, Category.assoc]
    change p ≫ (legendreJMap k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) = _
    rw [legendreJMap_over, hp.1.2]
  obtain ⟨F, hF, hi⟩ := extension_to_proper k L D X Y.projection
    ((p ≫ legendreJMap k) ≫ Y.inclusion) hover
  letI := extension_finite_to_jCompletion k L D X Y (p ≫ legendreJMap k) F hF hi
  exact ⟨p, F, hp.1, hF, hi, extension_j_cartesian k L D X Y _ F hF hi,
    inferInstance, finite_smooth_curves_flat k X.projection Y.projection F⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179.SmoothProjectiveLevelCompletionR0179

lemma polynomial_zero_unique (k : Type u) [Field k]
    (x y : JLine k) (hx : Polynomial.X ∈ x.asIdeal) (hy : Polynomial.X ∈ y.asIdeal) : x = y := by
  have hm : (Ideal.span ({Polynomial.X} : Set (Polynomial k))).IsMaximal :=
    (Ideal.irreducible_iff_isMaximal_span_singleton Polynomial.X_ne_zero).mp Polynomial.irreducible_X
  have hxi : Ideal.span ({Polynomial.X} : Set (Polynomial k)) ≤ x.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hyi : Ideal.span ({Polynomial.X} : Set (Polynomial k)) ≤ y.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)
  apply PrimeSpectrum.ext
  exact (hm.eq_of_le x.isPrime.ne_top hxi).symm.trans (hm.eq_of_le y.isPrime.ne_top hyi)

lemma toLaurent_range (k : Type u) [Field k] :
    Set.range (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))) =
      {z : JLine k | Polynomial.X ∉ z.asIdeal} := by
  have he : (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k) =
      algebraMap (Polynomial k) (LaurentPolynomial k) :=
    RingHom.ext (fun z => (LaurentPolynomial.algebraMap_eq_toLaurent z).symm)
  rw [he]
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k) Polynomial.X

lemma compact_j_line_two_charts (k : Type u) [Field k] [CharZero k] :
    ∃ (Y : JCompletion k) (i : JLine k ⟶ Y.space),
      IsOpenImmersion i ∧ i ≫ Y.projection = jLineStructure k ∧
      Set.range Y.inclusion ∪ Set.range i = Set.univ ∧
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)) ≫
          Y.inclusion =
        Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := k)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))) ≫ i ∧
      (Set.range Y.inclusion)ᶜ.Subsingleton := by
  obtain ⟨P, p, i₀, i₁, hp, h0, h1, h0p, h1p, hcov, hglue, hpb, hint⟩ :=
    exists_isProper_twoAffineLineCover k
  letI := hp
  letI := h0
  letI := h1
  letI : IsIntegral P := hint inferInstance
  let ch : Bool → (JLine k ⟶ P) := fun b => if b then i₁ else i₀
  haveI : ∀ b, IsOpenImmersion (ch b) := by intro b; cases b <;> dsimp [ch] <;> infer_instance
  let U : P.OpenCover := Scheme.Cover.mkOfCovers Bool (fun _ => JLine k) ch (fun x => by
    rcases (Set.eq_univ_iff_forall.mp hcov x) with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have hs : SmoothOfRelativeDimension 1 p := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1) U
    intro b
    cases b
    · change SmoothOfRelativeDimension 1 (i₀ ≫ p)
      rw [h0p]; exact jLine_smooth k
    · change SmoothOfRelativeDimension 1 (i₁ ≫ p)
      rw [h1p]; exact jLine_smooth k
  letI := hs
  obtain ⟨n, e, he, hep⟩ := Projectivity.exists_embedding k P p
  let Y : JCompletion k :=
    { space := P
      projection := p
      inclusion := i₀
      over_eq := h0p
      openImmersion := h0
      dense := i₀.isOpenMap.denseRange_of_isPreirreducibleSpace _
      proper := hp
      smooth := hs
      dimension := n
      embedding := e
      closedImmersion := he
      embedding_over := hep }
  refine ⟨Y, i₁, h1, h1p, hcov, hglue, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ : x ∈ Set.range i₁ := by
    exact (Set.eq_univ_iff_forall.mp hcov x).resolve_left hx
  obtain ⟨b, rfl⟩ : y ∈ Set.range i₁ := by
    exact (Set.eq_univ_iff_forall.mp hcov y).resolve_left hy
  have hzero : ∀ z : JLine k, i₁ z ∉ Set.range i₀ → Polynomial.X ∈ z.asIdeal := by
    intro z hz
    by_contra hn
    have hr : z ∈ Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))) := by
      rw [toLaurent_range]; exact hn
    obtain ⟨w, hw⟩ := hr
    let v := (LaurentPolynomial.invert (R := k)).toRingEquiv
    have hvinv : (CommRingCat.ofHom v.toRingHom) ≫ CommRingCat.ofHom v.toRingHom =
        𝟙 (CommRingCat.of (LaurentPolynomial k)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro t
      exact LaurentPolynomial.involutive_invert t
    let q := Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))
    let r := Spec.map (CommRingCat.ofHom (v.toRingHom.comp
      (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)))
    have hrq : Spec.map (CommRingCat.ofHom v.toRingHom) ≫ r = q := by
      rw [show r = Spec.map (CommRingCat.ofHom (v.toRingHom.comp
        (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))) from rfl,
        CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hvinv,
        Spec.map_id, Category.id_comp]
    let w' := Spec.map (CommRingCat.ofHom v.toRingHom) w
    have hw' : r w' = z := (congrArg (fun f => f w) hrq).trans hw
    apply hz
    refine ⟨q w', ?_⟩
    exact (congrArg (fun f => f w') hglue).trans (congrArg i₁ hw')
  exact congrArg i₁ (polynomial_zero_unique k a b (hzero a hx) (hzero b hy))

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179

def tateJPoint (k : Type u) [Field k] [CharZero k] (L : ℕ) : Puncture k ⟶ JLine k :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (tateJ k L)).toRingHom)

lemma classifying_j_map
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    b ≫ p ≫ legendreJMap k = tateJPoint k L := by
  let α := (Spec.preimage (b ≫ p)).hom
  have hα : α.comp (algebraMap k (LegendreRing k)) = algebraMap k (LaurentSeries k) := by
    have hh : CommRingCat.ofHom (α.comp (algebraMap k (LegendreRing k))) =
        CommRingCat.ofHom (algebraMap k (LaurentSeries k)) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      change Spec.map (CommRingCat.ofHom α) ≫ legendreBaseMap k = _
      rw [show Spec.map (CommRingCat.ofHom α) = b ≫ p from Spec.map_preimage _,
        Category.assoc, hp.2]
      exact hb.choose_spec.1
    exact congrArg CommRingCat.Hom.hom hh
  have hj : α (legendreJSection k) = tateJ k L := by
    letI : CharZero (LaurentSeries k) := charZero_of_injective_ringHom (algebraMap k (LaurentSeries k)).injective
    rw [map_legendreJSection]
    exact TateLevelClassifyingParameter.classifying_j k L D E p hp b hb
  have he : α.comp (jPolynomialMap k).toRingHom = (Polynomial.aeval (tateJ k L)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      change α ((jPolynomialMap k) (Polynomial.C c)) = _
      change α ((jPolynomialMap k) (algebraMap k (Polynomial k) c)) =
        Polynomial.aeval (tateJ k L) (algebraMap k (Polynomial k) c)
      rw [AlgHom.commutes, AlgHom.commutes]
      exact RingHom.congr_fun hα c
    · change α ((jPolynomialMap k) Polynomial.X) = Polynomial.aeval (tateJ k L) Polynomial.X
      simpa only [jPolynomialMap, Polynomial.aeval_X] using hj
  rw [← Category.assoc]
  rw [show b ≫ p = Spec.map (CommRingCat.ofHom α) from (Spec.map_preimage _).symm]
  change Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom (jPolynomialMap k).toRingHom) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]
  rfl

lemma tateJPoint_over (k : Type u) [Field k] [CharZero k] (L : ℕ) :
    tateJPoint k L ≫ jLineStructure k = genericInclusion k ≫ diskStructure k := by
  change Spec.map (CommRingCat.ofHom (Polynomial.aeval (tateJ k L)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : (Polynomial.aeval (tateJ k L)).toRingHom.comp (algebraMap k (Polynomial k)) =
      algebraMap k (LaurentSeries k) := by
    apply RingHom.ext
    intro z
    exact (Polynomial.aeval (tateJ k L)).commutes z
  rw [he]
  simp only [genericInclusion, diskStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

lemma tate_j_disk_extension
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (Y : JCompletion k) :
    ∃! d : Disk k ⟶ Y.space, d ≫ Y.projection = diskStructure k ∧
      genericInclusion k ≫ d = tateJPoint k L ≫ Y.inclusion := by
  let T : ValuativeCommSq Y.projection :=
    { R := PowerSeries k
      K := LaurentSeries k
      i₁ := tateJPoint k L ≫ Y.inclusion
      i₂ := diskStructure k
      commSq := ⟨by rw [Category.assoc, Y.over_eq, tateJPoint_over]; rfl⟩ }
  have hv : ValuativeCriterion Y.projection := by
    have h := Y.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨U⟩ := hv T
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, ?_⟩
  intro e he
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨e, he.2, he.1⟩)

lemma tate_j_not_powerSeries
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) :
    ¬ ∃ a : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) a = tateJ k L := by
  rintro ⟨a, ha⟩
  obtain ⟨v, _, hv, h⟩ := (tate_j_pole k L hL heven).2
  rw [← ha, ← map_pow, ← map_mul] at h
  have he := IsFractionRing.injective (PowerSeries k) (LaurentSeries k) h
  have hc := congrArg PowerSeries.constantCoeff he
  have hc' : (0 : k) = 1 := by
    simpa only [map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (by omega : L ≠ 0), mul_zero, hv] using hc
  exact zero_ne_one hc'

lemma tate_j_disk_center_outside
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (Y : JCompletion k) (d : Disk k ⟶ Y.space)
    (hd : genericInclusion k ≫ d = tateJPoint k L ≫ Y.inclusion) :
    d (closedPoint k) ∉ Set.range Y.inclusion := by
  letI := Y.openImmersion
  intro h
  have hr : Set.range d ⊆ Set.range Y.inclusion := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map d.continuous).mem_open
      Y.inclusion.isOpenEmbedding.isOpen_range h
  let a := IsOpenImmersion.lift Y.inclusion d hr
  have hai : a ≫ Y.inclusion = d := IsOpenImmersion.lift_fac _ _ _
  have hgen : genericInclusion k ≫ a = tateJPoint k L := by
    apply (cancel_mono Y.inclusion).mp
    rw [Category.assoc, hai, hd]
  let α := (Spec.preimage a).hom
  have he : (algebraMap (PowerSeries k) (LaurentSeries k)).comp α =
      (Polynomial.aeval (tateJ k L)).toRingHom := by
    have hh : CommRingCat.ofHom ((algebraMap (PowerSeries k) (LaurentSeries k)).comp α) =
        CommRingCat.ofHom (Polynomial.aeval (tateJ k L)).toRingHom := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      rw [show Spec.map (CommRingCat.ofHom α) = a from Spec.map_preimage _]
      exact hgen
    exact congrArg CommRingCat.Hom.hom hh
  apply tate_j_not_powerSeries k L hL heven
  refine ⟨α Polynomial.X, ?_⟩
  have hh := RingHom.congr_fun he Polynomial.X
  change algebraMap (PowerSeries k) (LaurentSeries k) (α Polynomial.X) =
    Polynomial.aeval (tateJ k L) Polynomial.X at hh
  simpa only [Polynomial.aeval_X] using hh

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179

lemma j_fiber_descends_map
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (K : Type u) [Field K] (t : Base K ⟶ Puncture k) (a : Base K ⟶ OpenBase k L D)
    (haj : a ≫ p ≫ legendreJMap k = t ≫ tateJPoint k L) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
      ClassifiesTate k L D E' b ∧ t ≫ b = a := by
  let σ := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom σ) = t := Spec.map_preimage _
  letI : Algebra k K := (σ.comp (algebraMap k (LaurentSeries k))).toAlgebra
  letI : CharZero K := charZero_of_injective_ringHom (algebraMap k K).injective
  have ha : a ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← hp.2, ← legendreJMap_over, ← Category.assoc, ← Category.assoc]
    rw [Category.assoc a p (legendreJMap k), haj]
    change (t ≫ tateJPoint k L) ≫ jLineStructure k = _
    rw [Category.assoc, tateJPoint_over]
    change t ≫ Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hh : (algebraMap (PowerSeries k) (LaurentSeries k)).comp (algebraMap k (PowerSeries k)) =
        algebraMap k (LaurentSeries k) := rfl
    rw [hh, ← ht, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let α := (Spec.preimage (a ≫ p)).hom
  have he : α.comp (jPolynomialMap k).toRingHom = σ.comp (Polynomial.aeval (tateJ k L)).toRingHom := by
    have hh : CommRingCat.ofHom (α.comp (jPolynomialMap k).toRingHom) =
        CommRingCat.ofHom (σ.comp (Polynomial.aeval (tateJ k L)).toRingHom) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        show Spec.map (CommRingCat.ofHom α) = a ≫ p from Spec.map_preimage _, ht]
      exact (Category.assoc _ _ _).trans haj
    exact congrArg CommRingCat.Hom.hom hh
  have hj : let z := α (parameter k);
      256*(1-z+z^2)^3/(z^2*(1-z)^2) = σ (tateJ k L) := by
    have hh := RingHom.congr_fun he Polynomial.X
    change α (Polynomial.aeval (legendreJSection k) Polynomial.X) =
      σ (Polynomial.aeval (tateJ k L) Polynomial.X) at hh
    rw [Polynomial.aeval_X, Polynomial.aeval_X, map_legendreJSection] at hh
    exact hh
  obtain ⟨E', b, hb, heq⟩ := tate_j_fiber_descent k L hL heven D E p hp K σ rfl a ha hj
  exact ⟨E', b, hb, ht ▸ heq⟩

lemma pullback_generic_coverage
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L) (X : Compactification k L D)
    (Y : JCompletion k)
    (p : OpenBase k L D ⟶ Base (LegendreRing k)) (hp : IsParameter k L D p)
    (F : X.space ⟶ Y.space)
    (hcart : IsPullback X.inclusion (p ≫ legendreJMap k) F Y.inclusion)
    (d : Disk k ⟶ Y.space)
    (hd : genericInclusion k ≫ d = tateJPoint k L ≫ Y.inclusion)
    (η : Puncture k) (y : ↥(pullback F d))
    (hy : pullback.snd F d y = genericInclusion k η) :
    ∃ (E' : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D)
      (s : Puncture k ⟶ pullback F d),
      ClassifiesTate k L D E' b ∧ s ≫ pullback.snd F d = genericInclusion k ∧
      s ≫ pullback.fst F d = b ≫ X.inclusion ∧ s η = y := by
  let Z := pullback F d
  let r : Z ⟶ X.space := pullback.fst F d
  let f : Z ⟶ Disk k := pullback.snd F d
  let K := Z.residueField y
  let q : Base K ⟶ Z := Z.fromSpecResidueField y
  letI : IsOpenImmersion (genericInclusion k) :=
    IsOpenImmersion.of_isLocalization (S := LaurentSeries k) (PowerSeries.X : PowerSeries k)
  have hqr : Set.range (q ≫ f) ⊆ Set.range (genericInclusion k) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨η, ?_⟩
    change genericInclusion k η = f (q z)
    rw [show q z = y from Z.fromSpecResidueField_apply y z]
    exact hy.symm
  let t := IsOpenImmersion.lift (genericInclusion k) (q ≫ f) hqr
  have ht : t ≫ genericInclusion k = q ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hsq : (q ≫ r) ≫ F = (t ≫ tateJPoint k L) ≫ Y.inclusion := by
    rw [Category.assoc, show r ≫ F = f ≫ d from pullback.condition,
      ← Category.assoc, ← ht, Category.assoc, hd, Category.assoc]
  let a := hcart.lift (q ≫ r) (t ≫ tateJPoint k L) hsq
  have hai : a ≫ X.inclusion = q ≫ r := hcart.lift_fst _ _ _
  have haj : a ≫ p ≫ legendreJMap k = t ≫ tateJPoint k L := hcart.lift_snd _ _ _
  obtain ⟨E', b, hb, he⟩ := j_fiber_descends_map k L hL heven D E p hp K t a haj
  have hbi : (b ≫ X.inclusion) ≫ F = genericInclusion k ≫ d := by
    rw [Category.assoc, hcart.w, ← Category.assoc, ← Category.assoc,
      Category.assoc b p (legendreJMap k),
      classifying_j_map k L D E' p hp b hb, ← hd]
  let s : Puncture k ⟶ Z := pullback.lift (b ≫ X.inclusion) (genericInclusion k) hbi
  have hsr : s ≫ r = b ≫ X.inclusion := pullback.lift_fst _ _ _
  have hsf : s ≫ f = genericInclusion k := pullback.lift_snd _ _ _
  have hts : t ≫ s = q := by
    apply pullback.hom_ext
    · rw [Category.assoc, hsr, ← Category.assoc, he, hai]
    · rw [Category.assoc, hsf, ht]
  refine ⟨E', b, s, hb, hsf, hsr, ?_⟩
  let z := IsLocalRing.closedPoint K
  calc
    s η = s (t z) := congrArg s (Subsingleton.elim _ _)
    _ = q z := congrArg (fun m => m z) hts
    _ = y := Z.fromSpecResidueField_apply y z

#print axioms killed_point_coordinates
#print axioms full_marking_descends
#print axioms level_cover_points_rational
#print axioms classifying_map_descends
#print axioms sections_cover_specialization
#print axioms proper_flat_coverage
#print axioms exists_canonical_disk
#print axioms boundary_fraction_field_lift
#print axioms boundary_residue_bijective
#print axioms boundary_rational_section
#print axioms boundary_local_trait
#print axioms boundary_parameter_no_extension
#print axioms integral_of_legendre_equation
#print axioms legendre_integral_elements
#print axioms integral_legendre_parameter_units
#print axioms integral_legendre_parameter_lift
#print axioms integral_j_parameter_lift
#print axioms boundary_j_not_integral
#print axioms every_boundary_has_j_pole
#print axioms pointed_coefficient_comparison_of_j_eq
#print axioms classifying_map_descends_of_j_eq
#print axioms tate_j_fiber_geometric_descent
#print axioms tate_j_fiber_descent

end EveryGeometricBoundaryTateDisk

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179 EveryGeometricBoundaryTateDisk

theorem every_geometric_boundary_tate_disk :
    ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L)
      (heven : Even L) (D : LevelData k L) (X : Compactification k L D) (x : X.space),
      x ∈ boundary k L D X →
      ∃ (E : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space),
        ClassifiesTate k L D E b ∧ Extends k L D X b d ∧ d (closedPoint k) = x := by
  intro k _ _ _ L hL heven D X x hx
  classical
  obtain ⟨_, E, _, _, _, _, _, _⟩ := exists_canonical_disk k L hL heven D X
  obtain ⟨Y, _, _, _, _, _, hboundary⟩ := compact_j_line_two_charts k
  obtain ⟨p, F, hp, hF, hi, hcart, hfin, hflat⟩ := compactified_j_exists k L hL heven D X Y
  letI := hfin
  letI := hflat
  obtain ⟨d, hd, _⟩ := tate_j_disk_extension k L Y
  have hdx := tate_j_disk_center_outside k L hL heven Y d hd.2
  have hFx : F x ∉ Set.range Y.inclusion := by
    rintro ⟨a, ha⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hcart x a ha.symm
    exact hx ⟨z, hz⟩
  have hcenter : F x = d (closedPoint k) := hboundary hFx hdx
  obtain ⟨y, hyx, hyd⟩ := Scheme.Pullback.exists_preimage_pullback (f := F) (g := d)
    x (closedPoint k) hcenter
  let Z := pullback F d
  let r : Z ⟶ X.space := pullback.fst F d
  let f : Z ⟶ Disk k := pullback.snd F d
  let I := { i : TateLevel k L × (Puncture k ⟶ OpenBase k L D) × (Puncture k ⟶ Z) //
    ClassifiesTate k L D i.1 i.2.1 ∧ i.2.2 ≫ f = genericInclusion k ∧
      i.2.2 ≫ r = i.2.1 ≫ X.inclusion }
  let s : I → (Puncture k ⟶ Z) := fun i => i.val.2.2
  let η := IsLocalRing.closedPoint (LaurentSeries k)
  have hcover : ∀ z : Z, f z = genericInclusion k η → ∃ i, s i η = z := by
    intro z hz
    obtain ⟨E', b, a, hb, haf, har, haz⟩ :=
      pullback_generic_coverage k L hL heven D E X Y p hp F hcart d hd.2 η z hz
    exact ⟨⟨⟨E', b, a⟩, hb, haf, har⟩, haz⟩
  obtain ⟨i, u, huf, hgu, huy⟩ := proper_flat_coverage k f s
    (fun i => i.property.2.1) η hcover y hyd
  let δ := u ≫ r
  have hδx : δ (closedPoint k) = x := by
    change r (u (closedPoint k)) = x
    rw [huy]
    exact hyx
  have hδ : δ ≫ X.projection = diskStructure k := by
    change (u ≫ r) ≫ X.projection = _
    calc
      (u ≫ r) ≫ X.projection = u ≫ (r ≫ F) ≫ Y.projection := by
        rw [Category.assoc, Category.assoc, hF]
      _ = u ≫ (f ≫ d) ≫ Y.projection := by rw [pullback.condition]
      _ = (u ≫ f) ≫ d ≫ Y.projection := by simp only [Category.assoc]
      _ = diskStructure k := by rw [huf, Category.id_comp, hd.1]
  have hδgen : genericInclusion k ≫ δ = i.val.2.1 ≫ X.inclusion := by
    rw [show δ = u ≫ r from rfl, ← Category.assoc, hgu]
    exact i.property.2.2
  exact ⟨i.val.1, i.val.2.1, δ, i.property.1,
    ⟨hδ, hδgen, hδx.symm ▸ hx⟩, hδx⟩
#print axioms every_geometric_boundary_tate_disk

end ArithmeticThetaTateCuspsR0181
