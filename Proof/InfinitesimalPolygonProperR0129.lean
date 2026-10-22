module

public import InfinitesimalPolygonAtlasR0129
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine

@[expose] public section

/-! Finiteness and valuative geometry of the specified infinitesimal polygons. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (k : Type u) [Field k] [CharZero k]

lemma base_finiteType (n : ℕ) : (base k n).FiniteType := by
  apply RingHom.FiniteType.of_comp_finiteType
    (f := trunc (PowerSeries k) PowerSeries.X n)
  change ((trunc _ (ArithmeticThetaNodeCharts.t k) n).comp
    (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))).FiniteType
  apply RingHom.FiniteType.comp_surjective
  · exact RingHom.finiteType_algebraMap.mpr inferInstance
  · exact Ideal.Quotient.mk_surjective

instance structureMap_finiteType (n : ℕ) : LocallyOfFiniteType (structureMap k n) :=
  HasRingHomProperty.Spec_iff.mpr (base_finiteType k n)

variable {k} {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}

/-- The given finite chart family, with its specified joint surjectivity. -/
def Atlas.openCover (D : Atlas k r n hr E) : D.X.OpenCover where
  I₀ := Fin r
  X _ := specA k n
  f := D.chart
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨D.covers, D.chart_open⟩

instance Atlas.locallyOfFiniteType (D : Atlas k r n hr E) : LocallyOfFiniteType D.p := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) D.openCover
  intro i
  change LocallyOfFiniteType (D.chart i ≫ D.p)
  rw [D.chart_over]
  infer_instance

instance Atlas.compactSpace (D : Atlas k r n hr E) : CompactSpace D.X := by
  let : Finite D.openCover.I₀ := inferInstanceAs (Finite (Fin r))
  let : ∀ i, CompactSpace (D.openCover.X i) := fun _ =>
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (A k n))))
  exact D.openCover.compactSpace

instance Atlas.locallyNoetherian (D : Atlas k r n hr E) : IsLocallyNoetherian D.X := by
  apply (isLocallyNoetherian_iff_openCover D.openCover).mpr
  intro i
  change IsLocallyNoetherian (Spec (CommRingCat.of (A k n)))
  infer_instance

instance Atlas.noetherian (D : Atlas k r n hr E) : IsNoetherian D.X where

instance Atlas.quasiCompact (D : Atlas k r n hr E) : QuasiCompact D.p := by
  infer_instance

instance Atlas.quasiSeparated (D : Atlas k r n hr E) : QuasiSeparated D.p := by
  infer_instance

variable (k n)

def coordX : A k n := trunc _ (ArithmeticThetaNodeCharts.t k) n
  (ArithmeticThetaNodeCharts.x k)
def coordY : A k n := trunc _ (ArithmeticThetaNodeCharts.t k) n
  (ArithmeticThetaNodeCharts.y k)
def parameter : R k n := trunc _ PowerSeries.X n PowerSeries.X

lemma parameter_pow : parameter k n ^ (n+1) = 0 := by
  rw [parameter, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _

lemma coordX_mul_coordY : coordX k n * coordY k n = base k n (parameter k n) := by
  change trunc _ _ n (ArithmeticThetaNodeCharts.x k) *
    trunc _ _ n (ArithmeticThetaNodeCharts.y k) =
    trunc _ _ n (ArithmeticThetaNodeCharts.t k)
  rw [← map_mul, ArithmeticThetaNodeCharts.node_xy]

variable {k n}

lemma parameter_map_eq_zero {S : Type u} [CommRing S] [IsReduced S]
    (b : R k n →+* S) : b (parameter k n) = 0 := by
  apply IsNilpotent.eq_zero
  exact ⟨n+1, by rw [← map_pow, parameter_pow, map_zero]⟩

/-- Any map from a local affine scheme into the polygon lies in one specified chart. -/
lemma Atlas.local_factor (D : Atlas k r n hr E) {S : Type u} [CommRing S]
    [IsLocalRing S] (f : Spec (CommRingCat.of S) ⟶ D.X) :
    ∃ (i : Fin r) (a : Spec (CommRingCat.of S) ⟶ specA k n), a ≫ D.chart i = f := by
  obtain ⟨i, a, ha⟩ := D.covers (f (IsLocalRing.closedPoint S))
  let : IsOpenImmersion (D.chart i) := D.chart_open i
  have h : Set.range f ⊆ Set.range (D.chart i) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open
      (IsOpenImmersion.isOpen_range (D.chart i)) ⟨a, ha⟩
  exact ⟨i, IsOpenImmersion.lift (D.chart i) f h, IsOpenImmersion.lift_fac _ _ _⟩

/-- A truncated nodal point is determined by its base and its two coordinates. -/
lemma point_ext {S : Type u} [CommRing S] {f g : A k n →+* S}
    (hb : f.comp (base k n) = g.comp (base k n))
    (hx : f (coordX k n) = g (coordX k n))
    (hy : f (coordY k n) = g (coordY k n)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    exact RingHom.congr_fun hb (trunc _ PowerSeries.X n z)
  · intro j
    fin_cases j
    · exact hx
    · exact hy

/-- The explicit universal property of the two successive nodal quotients. -/
def mkPoint {S : Type u} [CommRing S] (b : R k n →+* S) (x y : S)
    (hxy : x * y = b (parameter k n)) : A k n →+* S := by
  let f : ArithmeticThetaNodeCharts.PolynomialChart k →+* S :=
    MvPolynomial.eval₂Hom (b.comp (trunc _ PowerSeries.X n))
      (fun j => if j = 0 then x else y)
  have hf : ArithmeticThetaNodeCharts.relationIdeal k ≤ RingHom.ker f := by
    rw [ArithmeticThetaNodeCharts.relationIdeal, Ideal.span_singleton_le_iff_mem]
    change f (ArithmeticThetaNodeCharts.relation k) = 0
    simpa [f, ArithmeticThetaNodeCharts.relation, ArithmeticThetaNodeCharts.parameter,
      parameter] using sub_eq_zero.mpr hxy
  let g : ArithmeticThetaNodeCharts.Node k →+* S :=
    Ideal.Quotient.lift _ f (fun a ha => hf ha)
  have hg : (Ideal.span {ArithmeticThetaNodeCharts.t k}) ^ (n+1) ≤ RingHom.ker g := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    change g (ArithmeticThetaNodeCharts.t k ^ (n+1)) = 0
    rw [map_pow]
    have ht : g (ArithmeticThetaNodeCharts.t k) = b (parameter k n) := by
      change f (MvPolynomial.C PowerSeries.X) = _
      simp [f, parameter]
    rw [ht, ← map_pow, parameter_pow, map_zero]
  exact Ideal.Quotient.lift _ g (fun a ha => hg ha)

@[simp] lemma mkPoint_x {S : Type u} [CommRing S] (b : R k n →+* S) (x y : S)
    (hxy : x * y = b (parameter k n)) : mkPoint b x y hxy (coordX k n) = x := by
  simp [mkPoint, coordX, trunc, ArithmeticThetaNodeCharts.x,
    ArithmeticThetaNodeCharts.quotientMap]

@[simp] lemma mkPoint_y {S : Type u} [CommRing S] (b : R k n →+* S) (x y : S)
    (hxy : x * y = b (parameter k n)) : mkPoint b x y hxy (coordY k n) = y := by
  simp [mkPoint, coordY, trunc, ArithmeticThetaNodeCharts.y,
    ArithmeticThetaNodeCharts.quotientMap]

@[simp] lemma mkPoint_base {S : Type u} [CommRing S] (b : R k n →+* S) (x y : S)
    (hxy : x * y = b (parameter k n)) : (mkPoint b x y hxy).comp (base k n) = b := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro z
  change MvPolynomial.eval₂Hom (b.comp (trunc _ PowerSeries.X n))
    (fun j : Fin 2 => if j = 0 then x else y) (MvPolynomial.C z) = _
  simp [trunc]

lemma point_coordinates_mul_eq_zero {S : Type u} [CommRing S] [IsReduced S]
    (f : A k n →+* S) : f (coordX k n) * f (coordY k n) = 0 := by
  rw [← map_mul, coordX_mul_coordY]
  exact parameter_map_eq_zero (f.comp (base k n))

/-- Extend a nodal point to either specified principal coordinate open. -/
def openPoint {S : Type u} [CommRing S] (f : A k n →+* S) (side : Bool)
    (hu : IsUnit (f (if side then coordX k n else coordY k n))) : B k n side →+* S := by
  let g : ArithmeticThetaNodeCharts.Node k →+* S :=
    f.comp (trunc _ (ArithmeticThetaNodeCharts.t k) n)
  have hu' : IsUnit (g (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side)) := by
    cases side <;> exact hu
  let l : RawOpen k side →+* S := IsLocalization.Away.lift _ hu'
  have hkill : (Ideal.span {openParameter k side}) ^ (n+1) ≤ RingHom.ker l := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    change l (openParameter k side ^ (n+1)) = 0
    rw [map_pow]
    change l (algebraMap _ _ (ArithmeticThetaNodeCharts.t k)) ^ (n+1) = 0
    rw [IsLocalization.Away.lift_eq]
    change f (base k n (parameter k n)) ^ (n+1) = 0
    rw [← map_pow, ← map_pow, parameter_pow, map_zero, map_zero]
  exact Ideal.Quotient.lift _ l (fun a ha => hkill ha)

@[simp] lemma openPoint_restriction {S : Type u} [CommRing S] (f : A k n →+* S)
    (side : Bool) (hu : IsUnit (f (if side then coordX k n else coordY k n))) :
    (openPoint f side hu).comp (restriction k n side) = f := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro z
  exact IsLocalization.Away.lift_eq _ (by cases side <;> exact hu) z

lemma adjacent_base (hE : IsAdjacent k n E) :
    E.toRingHom.comp ((restriction k n false).comp (base k n)) =
      (restriction k n true).comp (base k n) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro z
  have hn : ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k z) =
      algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z := by
    unfold ArithmeticThetaIndexedOverlapsR0058.nodeEquiv
      ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase
    exact AlgEquiv.commutes _ _
  have ha := congrArg (fun f => f z)
    (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates k 1 0
      (by decide) (by decide)).1
  have hb := congrArg (fun f => f
    (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false)
      (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z))) hE
  change E (trunc _ (openParameter k false) n
      (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false)
        (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) z))) = _
  dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hb
  rw [hb]
  apply congrArg (trunc _ (openParameter k true) n)
  simpa [rawAdjacent, ArithmeticThetaIndexedOverlapsR0058.openBase,
    ArithmeticThetaIndexedOverlapsR0058.openMap, hn] using ha

lemma adjacent_y_mul_x (hE : IsAdjacent k n E) :
    E (restriction k n false (coordY k n)) * restriction k n true (coordX k n) = 1 := by
  have he := RingHom.congr_fun hE
    (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k false)
      (ArithmeticThetaNodeCharts.y k))
  change E (trunc _ _ n _) * trunc _ _ n _ = 1
  rw [show E (trunc _ _ n _) = trunc _ _ n ((rawAdjacent k)
      (ArithmeticThetaIndexedOverlapsR0058.oy k 0 false)) from he]
  have hy := (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates k 1 0
    (by decide) (by decide)).2.1
  change trunc _ _ n ((rawAdjacent k) _) * trunc _ _ n _ = 1
  rw [show rawAdjacent k (ArithmeticThetaIndexedOverlapsR0058.oy k 0 false) =
      ↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k 0)⁻¹) from hy]
  have hx : (ArithmeticThetaIndexedOverlapsR0058.xUnit k 0 : RawOpen k true) =
      algebraMap _ _ (ArithmeticThetaNodeCharts.x k) := IsUnit.unit_spec _
  rw [← hx, ← map_mul, Units.inv_mul, map_one]

lemma specMap_injective_ringHom {S T : Type u} [CommRing S] [CommRing T]
    {f g : S →+* T}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

lemma specMap_cancel_of_injective {V F T : Type u} [CommRing V] [CommRing F]
    [CommRing T] (a : V →+* F) (ha : Function.Injective a)
    (f g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of T))
    (h : Spec.map (CommRingCat.ofHom a) ≫ f = Spec.map (CommRingCat.ofHom a) ≫ g) :
    f = g := by
  obtain ⟨f, rfl⟩ := Spec.homEquiv.symm.surjective f
  obtain ⟨g, rfl⟩ := Spec.homEquiv.symm.surjective g
  change Spec.map (CommRingCat.ofHom a) ≫ Spec.map f =
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map g at h
  change Spec.map f = Spec.map g
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply ha
  exact congrArg (fun q : CommRingCat.of T ⟶ CommRingCat.of F => q z) h'

lemma Atlas.local_ring_factor (D : Atlas k r n hr E) {S : Type u} [CommRing S]
    [IsLocalRing S] (f : Spec (CommRingCat.of S) ⟶ D.X) :
    ∃ (i : Fin r) (a : A k n →+* S), Spec.map (CommRingCat.ofHom a) ≫ D.chart i = f := by
  obtain ⟨i, a, ha⟩ := D.local_factor f
  obtain ⟨a, rfl⟩ := Spec.homEquiv.symm.surjective a
  exact ⟨i, a.hom, ha⟩

/-- Integrality of two adjacent coordinates forces them to be units,
so two integral extensions glue on the actual overlap. -/
lemma Atlas.adjacent_cancel (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    {V F : Type u} [CommRing V] [CommRing F]
    (a : V →+* F) (ha : Function.Injective a) (i : Fin r)
    (f g : A k n →+* V)
    (h : Spec.map (CommRingCat.ofHom (a.comp f)) ≫ D.chart i =
      Spec.map (CommRingCat.ofHom (a.comp g)) ≫ D.chart (next r hr i)) :
    Spec.map (CommRingCat.ofHom f) ≫ D.chart i =
      Spec.map (CommRingCat.ofHom g) ≫ D.chart (next r hr i) := by
  let t := (D.adjacent i).lift (Spec.map (CommRingCat.ofHom (a.comp f)))
    (Spec.map (CommRingCat.ofHom (a.comp g))) h
  have htf : t ≫ leftLeg k n E = Spec.map (CommRingCat.ofHom (a.comp f)) :=
    (D.adjacent i).lift_fst _ _ h
  have htg : t ≫ rightLeg k n = Spec.map (CommRingCat.ofHom (a.comp g)) :=
    (D.adjacent i).lift_snd _ _ h
  obtain ⟨q, hq⟩ := Spec.homEquiv.symm.surjective t
  change Spec.map q = t at hq
  have hqf : q.hom.comp (E.toRingHom.comp (restriction k n false)) = a.comp f := by
    apply specMap_injective_ringHom
    simpa [CommRingCat.ofHom_comp, Spec.map_comp, ← hq, leftLeg] using htf
  have hqg : q.hom.comp (restriction k n true) = a.comp g := by
    apply specMap_injective_ringHom
    simpa [CommRingCat.ofHom_comp, Spec.map_comp, ← hq, rightLeg] using htg
  have hu : f (coordY k n) * g (coordX k n) = 1 := by
    apply ha
    rw [map_mul, map_one]
    have hy := RingHom.congr_fun hqf (coordY k n)
    have hx := RingHom.congr_fun hqg (coordX k n)
    change q.hom (E (restriction k n false (coordY k n))) = a (f (coordY k n)) at hy
    change q.hom (restriction k n true (coordX k n)) = a (g (coordX k n)) at hx
    rw [← hy, ← hx, ← map_mul, adjacent_y_mul_x hE, map_one]
  have hy : IsUnit (f (coordY k n)) := isUnit_iff_exists_inv.mpr ⟨_, hu⟩
  let l := (openPoint f false hy).comp E.symm.toRingHom
  have hlf : l.comp (E.toRingHom.comp (restriction k n false)) = f := by
    apply RingHom.ext
    intro z
    change openPoint f false hy (E.symm (E (restriction k n false z))) = f z
    rw [E.symm_apply_apply]
    exact RingHom.congr_fun (openPoint_restriction f false hy) z
  have hl : Spec.map (CommRingCat.ofHom l) ≫ leftLeg k n E =
      Spec.map (CommRingCat.ofHom f) := by
    rw [leftLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlf]
  have ht : Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom l) = t := by
    have : IsOpenImmersion (leftLeg k n E) := leftLeg_open k n E
    apply (cancel_mono (leftLeg k n E)).mp
    rw [Category.assoc, hl, htf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hlg : Spec.map (CommRingCat.ofHom l) ≫ rightLeg k n =
      Spec.map (CommRingCat.ofHom g) := by
    apply specMap_cancel_of_injective a ha
    rw [← Category.assoc, ht, htg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← hl, Category.assoc, (D.adjacent i).w, ← Category.assoc, hlg]

/-- Uniqueness of valuation extensions, proved from the exact intersection data. -/
lemma Atlas.valuative_uniqueness (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    ValuativeCriterion.Uniqueness D.p := by
  intro S
  constructor
  rintro ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
  ext : 1
  change f = g
  obtain ⟨i, a, ha⟩ := D.local_ring_factor f
  obtain ⟨j, b, hb⟩ := D.local_ring_factor g
  let α := algebraMap S.R S.K
  have hinj : Function.Injective α := IsFractionRing.injective S.R S.K
  have heq : Spec.map (CommRingCat.ofHom (α.comp a)) ≫ D.chart i =
      Spec.map (CommRingCat.ofHom (α.comp b)) ≫ D.chart j := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hb]
    exact hf.trans hg.symm
  have : ∀ i, IsOpenImmersion (D.chart i) := D.chart_open
  by_cases hij : i = j
  · subst j
    have h := (cancel_mono (D.chart i)).mp heq
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp] at h
    have hab := specMap_cancel_of_injective α hinj _ _ h
    rw [← ha, ← hb, hab]
  · by_cases hnext : next r hr i = j
    · subst j
      exact ha.symm.trans ((D.adjacent_cancel hE α hinj i a b heq).trans hb)
    · by_cases hprev : next r hr j = i
      · subst i
        exact ha.symm.trans ((D.adjacent_cancel hE α hinj j b a heq.symm).symm.trans hb)
      · have h := congrArg (fun f : Spec (CommRingCat.of S.K) ⟶ D.X =>
          f (IsLocalRing.closedPoint S.K)) heq
        exact False.elim (Set.disjoint_left.mp (D.disjoint i j hij hnext hprev)
          ⟨_, rfl⟩ ⟨_, h.symm⟩)

lemma Atlas.isSeparated (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    IsSeparated D.p := IsSeparated.of_valuativeCriterion D.p (D.valuative_uniqueness hE)

lemma integral_point {V F : Type u} [CommRing V] [CommRing F]
    (α : V →+* F) (hinj : Function.Injective α) (b : R k n →+* V)
    (f : A k n →+* F) (hb : f.comp (base k n) = α.comp b)
    (hx : ∃ x, α x = f (coordX k n)) (hy : ∃ y, α y = f (coordY k n)) :
    ∃ g : A k n →+* V, α.comp g = f ∧ g.comp (base k n) = b := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x * y = b (parameter k n) := by
    apply hinj
    rw [map_mul, hx, hy, ← map_mul, coordX_mul_coordY]
    exact RingHom.congr_fun hb (parameter k n)
  refine ⟨mkPoint b x y hxy, ?_, mkPoint_base b x y hxy⟩
  apply point_ext
  · rw [RingHom.comp_assoc, mkPoint_base, hb]
  · simpa using hx
  · simpa using hy

lemma overlap_coordinates {F : Type u} [Field F] (hE : IsAdjacent k n E)
    (q : B k n true →+* F) :
    q (E (restriction k n false (coordY k n))) *
      q (restriction k n true (coordX k n)) = 1 := by
  rw [← map_mul, adjacent_y_mul_x hE, map_one]

lemma Atlas.shift_forward (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    {F : Type u} [Field F] (i : Fin r) (f : A k n →+* F)
    (hy : f (coordY k n) ≠ 0) :
    ∃ g : A k n →+* F,
      g.comp (base k n) = f.comp (base k n) ∧
      g (coordX k n) = (f (coordY k n))⁻¹ ∧ g (coordY k n) = 0 ∧
      Spec.map (CommRingCat.ofHom g) ≫ D.chart (next r hr i) =
        Spec.map (CommRingCat.ofHom f) ≫ D.chart i := by
  let l := openPoint f false (isUnit_iff_ne_zero.mpr hy)
  let q := l.comp E.symm.toRingHom
  have hq : q.comp (E.toRingHom.comp (restriction k n false)) = f := by
    apply RingHom.ext
    intro z
    change l (E.symm (E (restriction k n false z))) = f z
    rw [E.symm_apply_apply]
    exact RingHom.congr_fun (openPoint_restriction f false (isUnit_iff_ne_zero.mpr hy)) z
  let g := q.comp (restriction k n true)
  have hxy : f (coordY k n) * g (coordX k n) = 1 := by
    rw [← RingHom.congr_fun hq (coordY k n)]
    exact overlap_coordinates hE q
  have hx : g (coordX k n) = (f (coordY k n))⁻¹ := eq_inv_of_mul_eq_one_right hxy
  have hz : g (coordY k n) = 0 := by
    exact (mul_eq_zero.mp (point_coordinates_mul_eq_zero g)).resolve_left
      (by rw [hx]; exact inv_ne_zero hy)
  refine ⟨g, ?_, hx, hz, ?_⟩
  · change (q.comp (restriction k n true)).comp (base k n) = _
    apply RingHom.ext
    intro z
    change q (restriction k n true (base k n z)) = f (base k n z)
    have hh := RingHom.congr_fun (adjacent_base hE) z
    change E (restriction k n false (base k n z)) = restriction k n true (base k n z) at hh
    rw [← hh]
    exact RingHom.congr_fun hq (base k n z)
  · have hgeom : Spec.map (CommRingCat.ofHom q) ≫ leftLeg k n E =
        Spec.map (CommRingCat.ofHom f) := by
      rw [leftLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hq]
    change Spec.map (CommRingCat.ofHom (q.comp (restriction k n true))) ≫ _ = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change (Spec.map (CommRingCat.ofHom q) ≫ rightLeg k n) ≫ _ = _
    rw [Category.assoc, ← (D.adjacent i).w, ← Category.assoc, hgeom]

lemma Atlas.shift_backward (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    {F : Type u} [Field F] (i : Fin r) (f : A k n →+* F)
    (hx : f (coordX k n) ≠ 0) :
    ∃ g : A k n →+* F,
      g.comp (base k n) = f.comp (base k n) ∧
      g (coordX k n) = 0 ∧ g (coordY k n) = (f (coordX k n))⁻¹ ∧
      Spec.map (CommRingCat.ofHom g) ≫ D.chart i =
        Spec.map (CommRingCat.ofHom f) ≫ D.chart (next r hr i) := by
  let q := openPoint f true (isUnit_iff_ne_zero.mpr hx)
  have hq : q.comp (restriction k n true) = f := openPoint_restriction f true _
  let g := q.comp (E.toRingHom.comp (restriction k n false))
  have hxy : g (coordY k n) * f (coordX k n) = 1 := by
    rw [← RingHom.congr_fun hq (coordX k n)]
    exact overlap_coordinates hE q
  have hy : g (coordY k n) = (f (coordX k n))⁻¹ := eq_inv_of_mul_eq_one_left hxy
  have hz : g (coordX k n) = 0 := by
    exact (mul_eq_zero.mp (point_coordinates_mul_eq_zero g)).resolve_right
      (by rw [hy]; exact inv_ne_zero hx)
  refine ⟨g, ?_, hz, hy, ?_⟩
  · change (q.comp (E.toRingHom.comp (restriction k n false))).comp (base k n) = _
    rw [RingHom.comp_assoc, RingHom.comp_assoc, adjacent_base hE,
      ← RingHom.comp_assoc, hq]
  · have hgeom : Spec.map (CommRingCat.ofHom q) ≫ rightLeg k n =
        Spec.map (CommRingCat.ofHom f) := by
      rw [rightLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hq]
    change Spec.map (CommRingCat.ofHom (q.comp (E.toRingHom.comp (restriction k n false)))) ≫ _ = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change (Spec.map (CommRingCat.ofHom q) ≫ leftLeg k n E) ≫ _ = _
    rw [Category.assoc, (D.adjacent i).w, ← Category.assoc, hgeom]

lemma next_surjective (r : ℕ) (hr : 0 < r) : Function.Surjective (next r hr) := by
  apply Finite.surjective_of_injective
  intro i j h
  have h' : (i.val+1)%r = (j.val+1)%r := congrArg Fin.val h
  apply Fin.ext
  by_cases hi : i.val+1 < r <;> by_cases hj : j.val+1 < r
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
    omega
  · have hjr : j.val+1 = r := by omega
    rw [Nat.mod_eq_of_lt hi, hjr, Nat.mod_self] at h'
    omega
  · have hir : i.val+1 = r := by omega
    rw [hir, Nat.mod_self, Nat.mod_eq_of_lt hj] at h'
    omega
  · omega

/-- A field-valued point can be moved to a neighboring chart with integral coordinates. -/
lemma Atlas.integral_chart (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    {V F : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field F] [Algebra V F] [IsFractionRing V F]
    (b : R k n →+* V) (i : Fin r) (f : A k n →+* F)
    (hb : f.comp (base k n) = (algebraMap V F).comp b) :
    ∃ (j : Fin r) (g : A k n →+* V), g.comp (base k n) = b ∧
      Spec.map (CommRingCat.ofHom ((algebraMap V F).comp g)) ≫ D.chart j =
        Spec.map (CommRingCat.ofHom f) ≫ D.chart i := by
  let α := algebraMap V F
  have hi : Function.Injective α := IsFractionRing.injective V F
  have finish (j : Fin r) (f' : A k n →+* F)
      (hb' : f'.comp (base k n) = α.comp b)
      (hx : IsLocalization.IsInteger V (f' (coordX k n)))
      (hy : IsLocalization.IsInteger V (f' (coordY k n)))
      (he : Spec.map (CommRingCat.ofHom f') ≫ D.chart j =
        Spec.map (CommRingCat.ofHom f) ≫ D.chart i) :
      ∃ (j : Fin r) (g : A k n →+* V), g.comp (base k n) = b ∧
        Spec.map (CommRingCat.ofHom (α.comp g)) ≫ D.chart j =
          Spec.map (CommRingCat.ofHom f) ≫ D.chart i := by
    obtain ⟨g, hg, hgb⟩ := integral_point α hi b f' hb' hx hy
    exact ⟨j, g, hgb, by rw [hg]; exact he⟩
  by_cases hx : IsLocalization.IsInteger V (f (coordX k n))
  · by_cases hy : IsLocalization.IsInteger V (f (coordY k n))
    · exact finish i f hb hx hy rfl
    · have hy0 : f (coordY k n) ≠ 0 := by
        intro h
        exact hy (h ▸ IsLocalization.isInteger_zero)
      obtain ⟨g, hgb, hgx, hgy, hgeom⟩ := D.shift_forward hE i f hy0
      apply finish (next r hr i) g (hgb.trans hb) _ _ hgeom
      · rw [hgx]
        exact (ValuationRing.isInteger_or_isInteger V (f (coordY k n))).resolve_left hy
      · rw [hgy]
        exact IsLocalization.isInteger_zero
  · have hx0 : f (coordX k n) ≠ 0 := by
      intro h
      exact hx (h ▸ IsLocalization.isInteger_zero)
    obtain ⟨j, hj⟩ := next_surjective r hr i
    obtain ⟨g, hgb, hgx, hgy, hgeom⟩ := D.shift_backward hE j f hx0
    apply finish j g (hgb.trans hb) _ _ (by simpa [hj] using hgeom)
    · rw [hgx]
      exact IsLocalization.isInteger_zero
    · rw [hgy]
      exact (ValuationRing.isInteger_or_isInteger V (f (coordX k n))).resolve_left hx

/-- Existence uses nilpotence of the base parameter and valuation-ring totality. -/
lemma Atlas.valuative_existence (D : Atlas k r n hr E) (hE : IsAdjacent k n E) :
    ValuativeCriterion.Existence D.p := by
  intro S
  obtain ⟨i, f, hf⟩ := D.local_ring_factor S.i₁
  obtain ⟨b, hb⟩ := Spec.homEquiv.symm.surjective S.i₂
  change Spec.map b = S.i₂ at hb
  have hbase : f.comp (base k n) = (algebraMap S.R S.K).comp b.hom := by
    apply specMap_injective_ringHom
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    change Spec.map (CommRingCat.ofHom f) ≫ structureMap k n =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map b
    rw [← D.chart_over i, ← Category.assoc, hf, hb]
    exact S.commSq.w
  obtain ⟨j, g, hgb, hgf⟩ := D.integral_chart hE b.hom i f hbase
  refine ⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ D.chart j, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hgf, hf]
  · rw [Category.assoc, D.chart_over]
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (base k n)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgb]
    exact hb

/-- Properness of every realization of the specified finite-stage cyclic atlas. -/
theorem infinitesimal_polygon_proper :
    ∀ (k : Type u) [Field k] [CharZero k],
      ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (n : ℕ) (E : B k n false ≃+* B k n true),
      IsAdjacent k n E → ∀ D : Atlas k r n hr E, IsProper D.p := by
  intro k _ _ r hr _ n E hE D
  apply IsProper.of_valuativeCriterion
  exact ValuativeCriterion.iff.mpr ⟨D.valuative_existence hE, D.valuative_uniqueness hE⟩

end ArithmeticThetaInfinitesimalPolygonR0129
