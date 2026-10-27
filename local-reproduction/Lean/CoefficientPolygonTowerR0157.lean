import CoefficientCompletedMapsR0157

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
namespace CoefficientPolygonTowerR0157
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaRamifiedPeriodR0154.RamifiedPolygonTower
variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable (ι : k →+* l)

def coefficientMap (n : ℕ) : R k n →+* R l n :=
  truncMap (baseMap k l ι) PowerSeries.X PowerSeries.X (PowerSeries.map_X ι) n

lemma coefficientMap_trunc (n : ℕ) :
    (coefficientMap k l ι n).comp (trunc _ PowerSeries.X n) =
      (trunc _ PowerSeries.X n).comp (baseMap k l ι) := rfl

lemma coefficientMap_parameter (n : ℕ) :
    coefficientMap k l ι n (parameter k n) = parameter l n := by
  change trunc _ PowerSeries.X n (PowerSeries.map ι PowerSeries.X) = _
  rw [PowerSeries.map_X]
  rfl

variable (ρ : Chart k →+* Chart l) (hρ : IsChartMap k l ι ρ)

include hρ in
lemma reduction_kernel_le (n : ℕ) :
    RingHom.ker (ArithmeticThetaKatoAnnularR0152.reduction k n) ≤
      RingHom.ker ((ArithmeticThetaKatoAnnularR0152.reduction l n).comp ρ) := by
  rw [← RingHom.comap_ker, CompletedChartFieldMaps.reduction_kernel,
    CompletedChartFieldMaps.reduction_kernel]
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  have ht := hρ.1 PowerSeries.X
  have ht' : ρ (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau l := by
    simpa only [baseMap, PowerSeries.map_X, ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau, ArithmeticThetaAnnularTorsionPrereqR0053.base] using ht
  rw [ht']

def nodeMap (n : ℕ) : A k n →+* A l n :=
  (ArithmeticThetaKatoAnnularR0152.reduction k n).liftOfSurjective
    (CompletedChartFieldMaps.reduction_surjective k n)
    ⟨(ArithmeticThetaKatoAnnularR0152.reduction l n).comp ρ,
      reduction_kernel_le k l ι ρ hρ n⟩

lemma nodeMap_reduction (n : ℕ) :
    (nodeMap k l ι ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n) =
      (ArithmeticThetaKatoAnnularR0152.reduction l n).comp ρ :=
  RingHom.liftOfSurjective_comp ..

lemma nodeMap_base (n : ℕ) (b : R k n) :
    nodeMap k l ι ρ hρ n (base k n b) = base l n (coefficientMap k l ι n b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change nodeMap k l ι ρ hρ n (base k n (trunc _ _ n b)) = _
  rw [← reduction_base]
  change ((nodeMap k l ι ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction l n
    (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) = _
  rw [hρ.1, reduction_base]
  rfl

lemma nodeMap_x (n : ℕ) : nodeMap k l ι ρ hρ n (coordX k n) = coordX l n := by
  rw [← reduction_x]
  change ((nodeMap k l ι ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction l n
    (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = _
  rw [hρ.2.1, reduction_x]

lemma nodeMap_y (n : ℕ) : nodeMap k l ι ρ hρ n (coordY k n) = coordY l n := by
  rw [← reduction_y]
  change ((nodeMap k l ι ρ hρ n).comp (ArithmeticThetaKatoAnnularR0152.reduction k n)) _ = _
  rw [nodeMap_reduction]
  change ArithmeticThetaKatoAnnularR0152.reduction l n
    (ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = _
  rw [hρ.2.2.1, reduction_y]

lemma nodeMap_unique (n : ℕ) (η : A k n →+* A l n)
    (hη : η.comp (ArithmeticThetaKatoAnnularR0152.reduction k n) =
      (ArithmeticThetaKatoAnnularR0152.reduction l n).comp ρ) :
    η = nodeMap k l ι ρ hρ n := by
  apply RingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := CompletedChartFieldMaps.reduction_surjective k n z
  exact RingHom.congr_fun (hη.trans (nodeMap_reduction k l ι ρ hρ n).symm) z

lemma nodeMap_reduce (n N : ℕ) (h : n ≤ N) :
    (truncReduce _ (ArithmeticThetaNodeCharts.t l) n N h).comp (nodeMap k l ι ρ hρ N) =
      (nodeMap k l ι ρ hρ n).comp (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h) := by
  apply point_ext
  · apply Ideal.Quotient.ringHom_ext
    ext b
    change truncReduce _ _ n N h (nodeMap k l ι ρ hρ N (base k N (trunc _ _ N b))) =
      nodeMap k l ι ρ hρ n (base k n (trunc _ _ n b))
    rw [nodeMap_base, nodeMap_base]
    rfl
  · change truncReduce _ _ n N h (nodeMap k l ι ρ hρ N (coordX k N)) =
      nodeMap k l ι ρ hρ n (coordX k n)
    rw [nodeMap_x, nodeMap_x]
    rfl
  · change truncReduce _ _ n N h (nodeMap k l ι ρ hρ N (coordY k N)) =
      nodeMap k l ι ρ hρ n (coordY k n)
    rw [nodeMap_y, nodeMap_y]
    rfl

lemma nodeMap_pushout (n : ℕ) :
    IsPushout (CommRingCat.ofHom (base k n)) (CommRingCat.ofHom (coefficientMap k l ι n))
      (CommRingCat.ofHom (nodeMap k l ι ρ hρ n)) (CommRingCat.ofHom (base l n)) := by
  have w : CommRingCat.ofHom (base k n) ≫ CommRingCat.ofHom (nodeMap k l ι ρ hρ n) =
      CommRingCat.ofHom (coefficientMap k l ι n) ≫ CommRingCat.ofHom (base l n) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (nodeMap_base k l ι ρ hρ n)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  apply PushoutCocone.isColimitAux'
  intro c
  have hc (b : R k n) : c.inl.hom (base k n b) =
      c.inr.hom (coefficientMap k l ι n b) := congrArg (fun q => q.hom b) c.condition
  have hxy : c.inl.hom (coordX k n) * c.inl.hom (coordY k n) =
      c.inr.hom (parameter l n) := by
    rw [← map_mul, coordX_mul_coordY, hc, coefficientMap_parameter]
  let d := mkPoint c.inr.hom (c.inl.hom (coordX k n)) (c.inl.hom (coordY k n)) hxy
  have hd : d.comp (base l n) = c.inr.hom := mkPoint_base ..
  have hd' : d.comp (nodeMap k l ι ρ hρ n) = c.inl.hom := by
    apply point_ext
    · apply RingHom.ext
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, nodeMap_base]
      exact (RingHom.congr_fun hd _).trans (hc b).symm
    · simp only [RingHom.comp_apply, nodeMap_x, d, mkPoint_x]
    · simp only [RingHom.comp_apply, nodeMap_y, d, mkPoint_y]
  refine ⟨CommRingCat.ofHom d, CommRingCat.hom_ext hd', CommRingCat.hom_ext hd, ?_⟩
  intro m hm₁ hm₂
  apply CommRingCat.hom_ext
  apply point_ext
  · exact (congrArg CommRingCat.Hom.hom hm₂).trans hd.symm
  · have hh := congrArg (fun q => q.hom (coordX k n)) hm₁
    change m.hom (nodeMap k l ι ρ hρ n (coordX k n)) = _ at hh
    change m.hom (coordX l n) = d (coordX l n)
    rw [show d (coordX l n) = c.inl.hom (coordX k n) from mkPoint_x ..]
    exact (congrArg m.hom (nodeMap_x k l ι ρ hρ n)).symm.trans hh
  · have hh := congrArg (fun q => q.hom (coordY k n)) hm₁
    change m.hom (nodeMap k l ι ρ hρ n (coordY k n)) = _ at hh
    change m.hom (coordY l n) = d (coordY l n)
    rw [show d (coordY l n) = c.inl.hom (coordY k n) from mkPoint_y ..]
    exact (congrArg m.hom (nodeMap_y k l ι ρ hρ n)).symm.trans hh

lemma nodeMap_pullback (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n))) (structureMap l n)
      (structureMap k n) (Spec.map (CommRingCat.ofHom (coefficientMap k l ι n))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (nodeMap_pushout k l ι ρ hρ n)

section Gluing
variable {r n : ℕ} {hr : 0 < r}
variable {E : B k n false ≃+* B k n true} {El : B l n false ≃+* B l n true}
variable (D : Atlas k r n hr E) (Dl : Atlas l r n hr El)
variable (hE : IsAdjacent k n E) (hEl : IsAdjacent l n El)

def localMap (i : Fin r) : specA l n ⟶ D.X :=
  Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n)) ≫ D.chart i

include hE hEl in
lemma localMap_compatible (i : Fin r) :
    leftLeg l n El ≫ localMap k l ι ρ hρ D i =
      rightLeg l n ≫ localMap k l ι ρ hρ D (next r hr i) := by
  let L := El.toRingHom.comp (restriction l n false)
  let R := restriction l n true
  let f := L.comp (nodeMap k l ι ρ hρ n)
  let g := R.comp (nodeMap k l ι ρ hρ n)
  have hb : f.comp (base k n) = g.comp (base k n) := by
    apply RingHom.ext
    intro b
    change L (nodeMap k l ι ρ hρ n (base k n b)) =
      R (nodeMap k l ι ρ hρ n (base k n b))
    rw [nodeMap_base]
    exact RingHom.congr_fun (adjacent_base hEl) _
  dsimp only [localMap]
  rw [← Category.assoc, ← Category.assoc, leftLeg, rightLeg,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply adjacent_points D hE i f g hb
  change L (nodeMap k l ι ρ hρ n (coordY k n)) *
    R (nodeMap k l ι ρ hρ n (coordX k n)) = 1
  rw [nodeMap_y, nodeMap_x]
  exact adjacent_y_mul_x hEl

def stageHom : Dl.X ⟶ D.X :=
  Dl.desc (localMap k l ι ρ hρ D) (localMap_compatible k l ι ρ hρ D hE hEl)

@[reassoc (attr := simp)] lemma stageHom_chart (i : Fin r) :
    Dl.chart i ≫ stageHom k l ι ρ hρ D Dl hE hEl = localMap k l ι ρ hρ D i :=
  Dl.chart_desc _ _ i

lemma stageHom_over :
    stageHom k l ι ρ hρ D Dl hE hEl ≫ D.p =
      Dl.p ≫ Spec.map (CommRingCat.ofHom (coefficientMap k l ι n)) := by
  apply Dl.hom_ext
  intro i
  rw [stageHom_chart_assoc, ← Category.assoc, Dl.chart_over]
  dsimp only [localMap]
  rw [Category.assoc, D.chart_over]
  exact (nodeMap_pullback k l ι ρ hρ n).w
lemma stageHom_preimage (j : Fin r) :
    (stageHom k l ι ρ hρ D Dl hE hEl) ⁻¹' Set.range (D.chart j) =
      Set.range (Dl.chart j) := by
  let f := stageHom k l ι ρ hρ D Dl hE hEl
  let a := Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n))
  have hc (i : Fin r) (x : specA l n) : f (Dl.chart i x) = D.chart i (a x) := by
    rw [← Scheme.Hom.comp_apply, stageHom_chart]
    rfl
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, x, rfl⟩ := Dl.covers x
    have he : D.chart i (a x) = D.chart j y := (hc i x).symm.trans hy.symm
    by_cases hij : i = j
    · subst j
      exact ⟨x, rfl⟩
    by_cases hn : next r hr i = j
    · subst j
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i) _ _ he
      have hx : x ∈ Set.range (leftLeg l n El) := by
        rw [ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.leftLeg_range]
        have hh : a x ∈ Set.range (leftLeg k n E) := ⟨z, hz⟩
        rw [ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.leftLeg_range] at hh
        change nodeMap k l ι ρ hρ n (coordY k n) ∉ x.asIdeal at hh
        apply (PrimeSpectrum.mem_basicOpen _ _).mpr
        rwa [nodeMap_y] at hh
      obtain ⟨z, rfl⟩ := hx
      refine ⟨rightLeg l n z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (Dl.adjacent i).w]
    by_cases hp : next r hr j = i
    · subst i
      obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j) _ _ he.symm
      have hx : x ∈ Set.range (rightLeg l n) := by
        rw [ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.rightLeg_range]
        have hh : a x ∈ Set.range (rightLeg k n) := ⟨z, hz⟩
        rw [ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.rightLeg_range] at hh
        change nodeMap k l ι ρ hρ n (coordX k n) ∉ x.asIdeal at hh
        apply (PrimeSpectrum.mem_basicOpen _ _).mpr
        rwa [nodeMap_x] at hh
      obtain ⟨z, rfl⟩ := hx
      refine ⟨leftLeg l n El z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (Dl.adjacent j).w]
    · exact False.elim (Set.disjoint_left.mp (D.disjoint i j hij hn hp)
        ⟨a x, rfl⟩ ⟨y, he.symm⟩)
  · rintro ⟨x, rfl⟩
    exact ⟨a x, (hc j x).symm⟩

lemma stageHom_pullback :
    IsPullback (stageHom k l ι ρ hρ D Dl hE hEl) Dl.p D.p
      (Spec.map (CommRingCat.ofHom (coefficientMap k l ι n))) := by
  let f := stageHom k l ι ρ hρ D Dl hE hEl
  let b := Spec.map (CommRingCat.ofHom (coefficientMap k l ι n))
  let a := Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n))
  let g : Dl.X ⟶ pullback D.p b := pullback.lift f Dl.p (stageHom_over k l ι ρ hρ D Dl hE hEl)
  have hg₁ : g ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd _ _ = Dl.p := pullback.lift_snd _ _ _
  have hcharts (j : Fin r) : IsPullback a (Dl.chart j ≫ g) (D.chart j) (pullback.fst D.p b) := by
    have hout : IsPullback a ((Dl.chart j ≫ g) ≫ pullback.snd D.p b)
        (D.chart j ≫ D.p) b := by
      simpa only [Category.assoc, hg₂, Dl.chart_over, D.chart_over] using
        nodeMap_pullback k l ι ρ hρ n
    apply hout.of_bot _ (IsPullback.of_hasPullback _ _)
    rw [Category.assoc, hg₁]
    exact (stageHom_chart k l ι ρ hρ D Dl hE hEl j).symm
  have hopen (j : Fin r) : IsOpenImmersion (Dl.chart j ≫ g) :=
    MorphismProperty.of_isPullback (hcharts j) (D.chart_open j)
  have hinj : Function.Injective g := by
    intro x y hxy
    obtain ⟨j, z, rfl⟩ := Dl.covers x
    have hy : y ∈ Set.range (Dl.chart j) := by
      rw [← stageHom_preimage k l ι ρ hρ D Dl hE hEl j]
      have he : f y = f (Dl.chart j z) := by
        simpa only [← Scheme.Hom.comp_apply, Category.assoc, hg₁] using
          congrArg (pullback.fst D.p b) hxy.symm
      rw [Set.mem_preimage, he]
      refine ⟨a z, ?_⟩
      rw [← Scheme.Hom.comp_apply, stageHom_chart]
      rfl
    obtain ⟨w, rfl⟩ := hy
    letI := hopen j
    have hz : z = w := (Dl.chart j ≫ g).isOpenEmbedding.injective (by
      simpa only [Scheme.Hom.comp_apply] using hxy)
    exact congrArg (Dl.chart j) hz
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨j, z, hz⟩ := D.covers (pullback.fst D.p b x)
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback (hcharts j) z x hz
    refine ⟨Dl.chart j w, ?_⟩
    change (Dl.chart j ≫ g) w = x
    exact hw
  have hgo : IsOpenImmersion g :=
    IsOpenImmersion.of_openCover_source g Dl.thickeningOpenCoverR0130 hinj hopen
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr
    ⟨hgo, (surjective_iff g).mpr hsurj⟩
  exact IsPullback.of_iso_pullback ⟨stageHom_over k l ι ρ hρ D Dl hE hEl⟩ (asIso g) hg₁ hg₂
end Gluing

section Towers
variable {r : ℕ} {hr : 0 < r}
variable (T : Tower k r hr) (Tl : Tower l r hr)

def towerHom (n : ℕ) : (Tl.atlas n).X ⟶ (T.atlas n).X :=
  stageHom k l ι ρ hρ (T.atlas n) (Tl.atlas n) (T.overlap_spec n) (Tl.overlap_spec n)

lemma chartMap_reduce (n N : ℕ) (h : n ≤ N) :
    chartReduction l n N h ≫ Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ N)) =
      Spec.map (CommRingCat.ofHom (nodeMap k l ι ρ hρ n)) ≫ chartReduction k n N h := by
  simp only [chartReduction, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (nodeMap_reduce k l ι ρ hρ n N h)

lemma towerHom_transition (n N : ℕ) (h : n ≤ N) :
    Tl.transition n N h ≫ towerHom k l ι ρ hρ T Tl N =
      towerHom k l ι ρ hρ T Tl n ≫ T.transition n N h := by
  apply (Tl.atlas n).hom_ext
  intro i
  dsimp only [towerHom]
  rw [← Category.assoc, (Tl.transition_spec n N h).2 i, Category.assoc,
    stageHom_chart, stageHom_chart_assoc]
  dsimp only [localMap]
  rw [Category.assoc, (T.transition_spec n N h).2,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun z : specA l n ⟶ specA k N => z ≫ (T.atlas N).chart i)
    (chartMap_reduce k l ι ρ hρ n N h)

lemma towerHom_spec : IsTowerMap k l ι T Tl ρ (towerHom k l ι ρ hρ T Tl) := by
  refine ⟨fun n => ?_, towerHom_transition k l ι ρ hρ T Tl⟩
  refine ⟨coefficientMap k l ι n, coefficientMap_trunc k l ι n,
    stageHom_pullback k l ι ρ hρ (T.atlas n) (Tl.atlas n)
      (T.overlap_spec n) (Tl.overlap_spec n), ?_⟩
  intro i
  exact ⟨nodeMap k l ι ρ hρ n, nodeMap_reduction k l ι ρ hρ n,
    stageHom_chart k l ι ρ hρ (T.atlas n) (Tl.atlas n)
      (T.overlap_spec n) (Tl.overlap_spec n) i⟩

lemma towerHom_unique (f : ∀ n, (Tl.atlas n).X ⟶ (T.atlas n).X)
    (hf : IsTowerMap k l ι T Tl ρ f) : f = towerHom k l ι ρ hρ T Tl := by
  funext n
  apply (Tl.atlas n).hom_ext
  intro i
  obtain ⟨β, _, _, hcharts⟩ := hf.1 n
  obtain ⟨η, hη, hi⟩ := hcharts i
  rw [hi, nodeMap_unique k l ι ρ hρ n η hη]
  exact (stageHom_chart k l ι ρ hρ (T.atlas n) (Tl.atlas n)
    (T.overlap_spec n) (Tl.overlap_spec n) i).symm
end Towers

end CoefficientPolygonTowerR0157

theorem coefficient_polygon_tower :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l)
      (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (Tl : ArithmeticThetaInfinitesimalPolygonR0129.Tower l r hr)
      (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l)
      (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ),
      ∃! f : (∀ n, Quiver.Hom (Tl.atlas n).X (T.atlas n).X),
        ArithmeticThetaCoefficientNormDescentR0157.IsTowerMap k l ι T Tl ρ f := by
  intro k l _ _ _ _ ι r hr _ T Tl ρ hρ
  exact ⟨CoefficientPolygonTowerR0157.towerHom k l ι ρ hρ T Tl,
    CoefficientPolygonTowerR0157.towerHom_spec k l ι ρ hρ T Tl,
    CoefficientPolygonTowerR0157.towerHom_unique k l ι ρ hρ T Tl⟩

end ArithmeticThetaCoefficientNormDescentR0157

#print axioms ArithmeticThetaCoefficientNormDescentR0157.coefficient_polygon_tower
