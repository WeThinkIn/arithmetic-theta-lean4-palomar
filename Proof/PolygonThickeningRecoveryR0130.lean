module

public import InfinitesimalPolygonAtlasR0129
public import PolygonProvidersRecoveryR0130
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section

/-! Reduction maps for arbitrary realizations of the explicit infinitesimal atlas. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

lemma truncReduce_surjective (S : Type u) [CommRing S] (t : S)
    (n N : ℕ) (h : n ≤ N) : Function.Surjective (truncReduce S t n N h) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨trunc S t N a, rfl⟩

lemma truncReduce_natural {S U : Type u} [CommRing S] [CommRing U]
    (f : S →+* U) (t : S) (s : U) (hf : f t = s)
    (n N : ℕ) (h : n ≤ N) :
    (truncReduce U s n N h).comp (truncMap f t s hf N) =
      (truncMap f t s hf n).comp (truncReduce S t n N h) := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

variable (k : Type u) [Field k] [CharZero k]

def overlapReduction (n N : ℕ) (h : n ≤ N) (side : Bool) :
    specB k n side ⟶ specB k N side :=
  Spec.map (CommRingCat.ofHom (truncReduce (RawOpen k side) (openParameter k side) n N h))

lemma chartReduction_over (n N : ℕ) (h : n ≤ N) :
    chartReduction k n N h ≫ structureMap k N =
      structureMap k n ≫ baseReduction k n N h := by
  simp only [chartReduction, structureMap, baseReduction, ← Spec.map_comp]
  apply congrArg Spec.map
  exact congrArg CommRingCat.ofHom (truncReduce_natural _ _ _ rfl n N h)

lemma rightLeg_reduction (n N : ℕ) (h : n ≤ N) :
    rightLeg k n ≫ chartReduction k n N h =
      overlapReduction k n N h true ≫ rightLeg k N := by
  simp only [rightLeg, chartReduction, overlapReduction, ← Spec.map_comp]
  apply congrArg Spec.map
  exact congrArg CommRingCat.ofHom (truncReduce_natural _ _ _ rfl n N h).symm

/-- The defining raw-coordinate squares force compatibility at different orders. -/
lemma adjacent_reduction (n N : ℕ) (h : n ≤ N)
    (E : B k n false ≃+* B k n true) (F : B k N false ≃+* B k N true)
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F) :
    E.toRingHom.comp (truncReduce (RawOpen k false) (openParameter k false) n N h) =
      (truncReduce (RawOpen k true) (openParameter k true) n N h).comp F.toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hn := congrArg (fun f => f a) hE
  have hN := congrArg (fun f => f a) hF
  change E (trunc (RawOpen k false) (openParameter k false) n a) = _
  change E (trunc (RawOpen k false) (openParameter k false) n a) =
    truncReduce _ _ n N h (F (Ideal.Quotient.mk _ a))
  rw [show F (Ideal.Quotient.mk _ a) =
      trunc (RawOpen k true) (openParameter k true) N (rawAdjacent k a) from hN]
  exact hn

lemma leftLeg_reduction (n N : ℕ) (h : n ≤ N)
    (E : B k n false ≃+* B k n true) (F : B k N false ≃+* B k N true)
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F) :
    leftLeg k n E ≫ chartReduction k n N h =
      overlapReduction k n N h true ≫ leftLeg k N F := by
  simp only [leftLeg, chartReduction, overlapReduction, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (E.toRingHom.comp (restriction k n false)).comp
      (truncReduce _ _ n N h) =
    (truncReduce _ _ n N h).comp (F.toRingHom.comp (restriction k N false))
  have q := truncReduce_natural (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false))
    (ArithmeticThetaNodeCharts.t k) (openParameter k false) rfl n N h
  change (truncReduce _ _ n N h).comp (restriction k N false) =
    (restriction k n false).comp (truncReduce _ _ n N h) at q
  rw [RingHom.comp_assoc, ← q,
    ← RingHom.comp_assoc, adjacent_reduction k n N h E F hE hF, RingHom.comp_assoc]

namespace Atlas
variable {k} {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}

def thickeningOpenCoverR0130 (D : Atlas k r n hr E) : D.X.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin r) (fun _ => specA k n) D.chart D.covers D.chart_open

lemma hom_ext (D : Atlas k r n hr E) {Y : Scheme.{u}} (f g : D.X ⟶ Y)
    (h : ∀ j, D.chart j ≫ f = D.chart j ≫ g) : f = g :=
  D.thickeningOpenCoverR0130.hom_ext f g h

/-- Compatibility on the prescribed adjacent opens suffices: other intersections
are either diagonal or empty. This applies to any realization of the atlas. -/
lemma compatible (D : Atlas k r n hr E) {Y : Scheme.{u}}
    (f : Fin r → (specA k n ⟶ Y))
    (hf : ∀ j, leftLeg k n E ≫ f j = rightLeg k n ≫ f (next r hr j)) :
    ∀ i j, pullback.fst (D.chart i) (D.chart j) ≫ f i =
      pullback.snd (D.chart i) (D.chart j) ≫ f j := by
  intro i j
  letI := D.chart_open i
  letI := D.chart_open j
  by_cases hij : i = j
  · subst j
    congr 1
    exact (cancel_mono (D.chart i)).mp pullback.condition
  by_cases hn : next r hr i = j
  · subst j
    rw [← cancel_epi (D.adjacent i).isoPullback.hom]
    simpa using hf i
  by_cases hp : next r hr j = i
  · subst i
    rw [← cancel_epi (D.adjacent j).flip.isoPullback.hom]
    simpa using (hf j).symm
  · letI := Scheme.isEmpty_pullback _ _ (D.disjoint i j hij hn hp)
    exact isInitialOfIsEmpty.hom_ext _ _

def desc (D : Atlas k r n hr E) {Y : Scheme.{u}}
    (f : Fin r → (specA k n ⟶ Y))
    (hf : ∀ j, leftLeg k n E ≫ f j = rightLeg k n ≫ f (next r hr j)) : D.X ⟶ Y :=
  D.thickeningOpenCoverR0130.glueMorphisms f (D.compatible f hf)

@[reassoc (attr := simp)]
lemma chart_desc (D : Atlas k r n hr E) {Y : Scheme.{u}}
    (f : Fin r → (specA k n ⟶ Y))
    (hf : ∀ j, leftLeg k n E ≫ f j = rightLeg k n ≫ f (next r hr j)) (j : Fin r) :
    D.chart j ≫ D.desc f hf = f j := D.thickeningOpenCoverR0130.ι_glueMorphisms f _ j
end Atlas

/-- Glue the actual quotient reductions on all charts, including the cyclic seam. -/
def reduction (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F)
    (D : Atlas k r n hr E) (T : Atlas k r N hr F) : D.X ⟶ T.X :=
  D.desc (fun j => chartReduction k n N h ≫ T.chart j) (by
    intro j
    rw [← Category.assoc, leftLeg_reduction k n N h E F hE hF,
      Category.assoc, (T.adjacent j).w, ← Category.assoc,
      ← rightLeg_reduction, Category.assoc])

lemma reduction_spec (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F)
    (D : Atlas k r n hr E) (T : Atlas k r N hr F) :
    IsReduction k r n N hr h D T (reduction k r n N hr h hE hF D T) := by
  constructor
  · apply D.hom_ext
    intro j
    rw [reduction, Atlas.chart_desc_assoc, Category.assoc, T.chart_over,
      chartReduction_over, ← Category.assoc, D.chart_over]
  · intro j
    exact D.chart_desc _ _ j

lemma reduction_unique (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i j : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i)
    (hj : IsReduction k r n N hr h D T j) : i = j :=
  D.hom_ext i j (fun a => (hi.2 a).trans (hj.2 a).symm)

lemma trunc_parameter_zero (S : Type u) [CommRing S] (t : S) (n : ℕ) :
    trunc S t n (t ^ (n+1)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _

/-- Parameter-power reduction commutes with arbitrary parameter-preserving scalar maps.
The universal map is obtained by killing the lower parameter power. -/
lemma trunc_pushout {S U : Type u} [CommRing S] [CommRing U]
    (f : S →+* U) (t : S) (s : U) (hf : f t = s)
    (n N : ℕ) (h : n ≤ N) :
    IsPushout (CommRingCat.ofHom (truncMap f t s hf N))
      (CommRingCat.ofHom (truncReduce S t n N h))
      (CommRingCat.ofHom (truncReduce U s n N h))
      (CommRingCat.ofHom (truncMap f t s hf n)) := by
  have w : CommRingCat.ofHom (truncMap f t s hf N) ≫
      CommRingCat.ofHom (truncReduce U s n N h) =
      CommRingCat.ofHom (truncReduce S t n N h) ≫
      CommRingCat.ofHom (truncMap f t s hf n) :=
    congrArg CommRingCat.ofHom (truncReduce_natural f t s hf n N h)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  apply PushoutCocone.isColimitAux'
  intro c
  have hc (a : S) :
      c.inl.hom (trunc U s N (f a)) = c.inr.hom (trunc S t n a) :=
    congrArg (fun q => q.hom (trunc S t N a)) c.condition
  have hz : (c.inl.hom.comp (trunc U s N)) (s ^ (n+1)) = 0 := by
    change c.inl.hom (trunc U s N (s ^ (n+1))) = 0
    rw [show s ^ (n+1) = f (t ^ (n+1)) by rw [map_pow, hf],
      hc, trunc_parameter_zero, map_zero]
  have hk : (Ideal.span {s}) ^ (n+1) ≤ RingHom.ker
      (c.inl.hom.comp (trunc U s N)) := by
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact hz
  let d : CommRingCat.of (Trunc U s n) ⟶ c.pt :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ (c.inl.hom.comp (trunc U s N)) hk)
  have hd : CommRingCat.ofHom (truncReduce U s n N h) ≫ d = c.inl := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  refine ⟨d, hd, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hc a
  · intro m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := truncReduce_surjective U s n N h a
    exact congrArg (fun q => q.hom a) (hm.trans hd.symm)

lemma chartReduction_pullback (n N : ℕ) (h : n ≤ N) :
    IsPullback (chartReduction k n N h) (structureMap k n)
      (structureMap k N) (baseReduction k n N h) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (trunc_pushout (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
      PowerSeries.X (ArithmeticThetaNodeCharts.t k) rfl n N h)

lemma baseReduction_closed (n N : ℕ) (h : n ≤ N) :
    IsClosedImmersion (baseReduction k n N h) :=
  IsClosedImmersion.spec_of_surjective _ (truncReduce_surjective _ _ n N h)

lemma chartReduction_closed (n N : ℕ) (h : n ≤ N) :
    IsClosedImmersion (chartReduction k n N h) :=
  IsClosedImmersion.spec_of_surjective _ (truncReduce_surjective _ _ n N h)

/-- Every prime contains the nilpotent parameter, so reduction loses no points. -/
lemma truncReduce_spec_surjective (S : Type u) [CommRing S] (t : S)
    (n N : ℕ) (h : n ≤ N) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (truncReduce S t n N h))) := by
  change Function.Surjective (PrimeSpectrum.comap (truncReduce S t n N h))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (truncReduce_surjective S t n N h)]
  apply Set.eq_univ_of_forall
  intro q
  change RingHom.ker (truncReduce S t n N h) ≤ q.asIdeal
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha' : a ∈ (Ideal.span {t}) ^ (n+1) :=
    Ideal.Quotient.eq_zero_iff_mem.mp ha
  have ht : trunc S t N t ∈ q.asIdeal := by
    apply q.isPrime.mem_of_pow_mem (N+1)
    rw [← map_pow, trunc_parameter_zero]
    exact q.asIdeal.zero_mem
  have hi : Ideal.span {t} ≤ Ideal.comap (trunc S t N) q.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht
  exact hi (Ideal.pow_le_self (by omega) ha')

lemma reduction_surjective (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i) :
    Function.Surjective i := by
  intro x
  obtain ⟨j, a, rfl⟩ := T.covers x
  obtain ⟨b, hb⟩ := truncReduce_spec_surjective (ArithmeticThetaNodeCharts.Node k)
    (ArithmeticThetaNodeCharts.t k) n N h a
  refine ⟨D.chart j b, ?_⟩
  rw [← Scheme.Hom.comp_apply, hi.2 j, Scheme.Hom.comp_apply]
  exact congrArg (T.chart j) hb

/-- A point identification upstairs comes from a specified adjacent intersection;
its overlap point lifts through nilpotent reduction and gives the same identification downstairs. -/
lemma reduction_injective (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F)
    (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i) :
    Function.Injective i := by
  have hc : Function.Injective (chartReduction k n N h) :=
    (chartReduction_closed k n N h).isClosedEmbedding.injective
  have hadj (a b : Fin r) (hab : next r hr a = b)
      (x y : specA k n)
      (heq : T.chart a (chartReduction k n N h x) =
        T.chart b (chartReduction k n N h y)) : D.chart a x = D.chart b y := by
    subst b
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback (T.adjacent a) _ _ heq
    obtain ⟨w, hw⟩ := truncReduce_spec_surjective (RawOpen k true)
      (openParameter k true) n N h z
    have hx : leftLeg k n E w = x := by
      apply hc
      rw [← Scheme.Hom.comp_apply, leftLeg_reduction k n N h E F hE hF,
        Scheme.Hom.comp_apply]
      exact (congrArg (leftLeg k N F) hw).trans hz₁
    have hy : rightLeg k n w = y := by
      apply hc
      rw [← Scheme.Hom.comp_apply, rightLeg_reduction, Scheme.Hom.comp_apply]
      exact (congrArg (rightLeg k N) hw).trans hz₂
    rw [← hx, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (D.adjacent a).w]
  intro x y hxy
  obtain ⟨a, x, rfl⟩ := D.covers x
  obtain ⟨b, y, rfl⟩ := D.covers y
  have heq : T.chart a (chartReduction k n N h x) =
      T.chart b (chartReduction k n N h y) := by
    simpa only [← Scheme.Hom.comp_apply, hi.2] using hxy
  by_cases hab : a = b
  · subst b
    have ht := T.chart_open a
    exact congrArg (D.chart a) (hc ((T.chart a).isOpenEmbedding.injective heq))
  by_cases hn : next r hr a = b
  · exact hadj a b hn x y heq
  by_cases hp : next r hr b = a
  · exact (hadj b a hp y x heq.symm).symm
  · exact False.elim (Set.disjoint_left.mp (T.disjoint a b hab hn hp)
      ⟨_, rfl⟩ ⟨_, heq.symm⟩)

/-- The comparison with the base change is a bijective open immersion.
Its chart restrictions are open immersions by the affine pullback calculation. -/
lemma reduction_pullback (r n N : ℕ) (hr : 0 < r) (h : n ≤ N)
    {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true}
    (hE : IsAdjacent k n E) (hF : IsAdjacent k N F)
    (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i) :
    IsPullback i D.p T.p (baseReduction k n N h) := by
  let l : D.X ⟶ pullback T.p (baseReduction k n N h) :=
    pullback.lift i D.p hi.1
  have hl₁ : l ≫ pullback.fst _ _ = i := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd _ _ = D.p := pullback.lift_snd _ _ _
  have hli : Function.Injective l := by
    intro x y hxy
    apply reduction_injective k r n N hr h hE hF D T i hi
    simpa only [← Scheme.Hom.comp_apply, hl₁] using
      congrArg (pullback.fst T.p (baseReduction k n N h)) hxy
  have hb := baseReduction_closed k n N h
  have hp : IsClosedImmersion (pullback.fst T.p (baseReduction k n N h)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip hb
  have hls : Function.Surjective l := by
    intro y
    obtain ⟨x, hx⟩ := reduction_surjective k r n N hr h D T i hi
      (pullback.fst T.p (baseReduction k n N h) y)
    refine ⟨x, hp.isClosedEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, hl₁] using hx
  have hlo : IsOpenImmersion l := by
    apply IsOpenImmersion.of_openCover_source l D.thickeningOpenCoverR0130 hli
    intro j
    change IsOpenImmersion (D.chart j ≫ l)
    have hout : IsPullback (chartReduction k n N h)
        ((D.chart j ≫ l) ≫ pullback.snd T.p (baseReduction k n N h))
        (T.chart j ≫ T.p) (baseReduction k n N h) := by
      simpa only [Category.assoc, hl₂, D.chart_over, T.chart_over] using
        chartReduction_pullback k n N h
    have hs : IsPullback (chartReduction k n N h) (D.chart j ≫ l)
        (T.chart j) (pullback.fst T.p (baseReduction k n N h)) :=
      hout.of_bot (by rw [Category.assoc, hl₁, hi.2 j])
        (IsPullback.of_hasPullback _ _)
    exact MorphismProperty.of_isPullback hs (T.chart_open j)
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).mpr
    ⟨hlo, (surjective_iff l).mpr hls⟩
  exact IsPullback.of_iso_pullback ⟨hi.1⟩ (asIso l) hl₁ hl₂

/-- The exact frozen transition statement, for every field, cycle and pair of orders. -/
theorem polygon_thickening_transition :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (n N : ℕ) (h : n ≤ N)
        (E : B k n false ≃+* B k n true) (F : B k N false ≃+* B k N true),
        IsAdjacent k n E → IsAdjacent k N F →
        ∀ (D : Atlas k r n hr E) (T : Atlas k r N hr F),
        ∃! i : Quiver.Hom D.X T.X,
          IsReduction k r n N hr h D T i ∧ IsClosedImmersion i ∧
            IsPullback i D.p T.p (baseReduction k n N h) := by
  intro k _ _ r hr _ n N h E F hE hF D T
  let i := reduction k r n N hr h hE hF D T
  have hi := reduction_spec k r n N hr h hE hF D T
  have hp := reduction_pullback k r n N hr h hE hF D T i hi
  refine ⟨i, ⟨hi, ?_, hp⟩, ?_⟩
  · exact MorphismProperty.of_isPullback hp.flip (baseReduction_closed k n N h)
  · intro j hj
    exact reduction_unique k r n N hr h D T j i hj.1 hi

end ArithmeticThetaInfinitesimalPolygonR0129
