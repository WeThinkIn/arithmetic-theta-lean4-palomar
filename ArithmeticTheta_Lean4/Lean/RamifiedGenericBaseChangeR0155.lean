import RamifiedLaurentExtensionR0155
import RamifiedAcceptedLeavesR0155

/-! The generic lift of the specified integral ramification map. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155
namespace RamifiedGenericBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaRamifiedPeriodR0154

/-- Laurent polynomial maps are determined by coefficients and the invertible variable. -/
private lemma laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

private def laurentUnit (R : Type*) [CommRing R] : (LaurentPolynomial R)ˣ :=
  (LaurentPolynomial.isUnit_T 1).unit

private lemma laurentUnit_val (R : Type*) [CommRing R] :
    (laurentUnit R : LaurentPolynomial R) = LaurentPolynomial.T 1 :=
  (LaurentPolynomial.isUnit_T 1).unit_spec

/-- Coefficient extension on Laurent polynomials, fixing the variable. -/
private def laurentMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp φ) (laurentUnit S)

private lemma laurentMap_C {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) :
    laurentMap φ (LaurentPolynomial.C a) = LaurentPolynomial.C (φ a) :=
  LaurentPolynomial.eval₂_C ..

private lemma laurentMap_T {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) :
    laurentMap φ (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  simp [laurentMap, laurentUnit_val]

/-- A Laurent torus commutes with the specified coefficient base change. -/
private lemma laurent_pushout {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    IsPushout (CommRingCat.ofHom (LaurentPolynomial.C (R := R)))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (laurentMap φ))
      (CommRingCat.ofHom (LaurentPolynomial.C (R := S))) := by
  have w : CommRingCat.ofHom (LaurentPolynomial.C (R := R)) ≫
      CommRingCat.ofHom (laurentMap φ) = CommRingCat.ofHom φ ≫
      CommRingCat.ofHom (LaurentPolynomial.C (R := S)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact laurentMap_C φ a
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  apply PushoutCocone.isColimitAux'
  intro c
  let U := Units.map c.inl.hom.toMonoidHom (laurentUnit R)
  let ψ : LaurentPolynomial S →+* c.pt := LaurentPolynomial.eval₂ c.inr.hom U
  have hψC a : ψ (LaurentPolynomial.C a) = c.inr.hom a := LaurentPolynomial.eval₂_C ..
  have hψT : ψ (LaurentPolynomial.T 1) = c.inl.hom (LaurentPolynomial.T 1) := by
    simp [ψ, U, laurentUnit_val]
  refine ⟨CommRingCat.ofHom ψ, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro a
      change ψ (laurentMap φ (LaurentPolynomial.C a)) = c.inl.hom (LaurentPolynomial.C a)
      rw [laurentMap_C, hψC]
      exact (congrArg (fun z => z.hom a) c.condition).symm
    · change ψ (laurentMap φ (LaurentPolynomial.T 1)) = c.inl.hom (LaurentPolynomial.T 1)
      rw [laurentMap_T, hψT]
  · ext a
    exact hψC a
  · intro q hq₁ hq₂
    apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro a
      change q.hom (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a)
      rw [hψC]
      exact congrArg (fun z => z.hom a) hq₂
    · change q.hom (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)
      rw [hψT]
      have h := congrArg (fun z => z.hom (LaurentPolynomial.T 1)) hq₁
      change q.hom (laurentMap φ (LaurentPolynomial.T 1)) = _ at h
      rwa [laurentMap_T] at h

variable (k : Type u) [Field k] [CharZero k]

lemma base_square (d : ℕ) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : IsLaurentExtension k d hd ell) :
    Spec.map (CommRingCat.ofHom ell) ≫ genericBase k =
      genericBase k ≫ baseMorphism k d hd := by
  simp only [genericBase, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (fun b => hell b)

/-- Inverting a positive power inverts the original element. -/
private lemma localization_away_pow {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (x : R) [IsLocalization.Away x S] (d : ℕ) (hd : 0 < d) :
    IsLocalization.Away (x ^ d) S := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (Submonoid.powers (x ^ d)) (Submonoid.powers x) ?_ ?_).mpr inferInstance
  · rintro z ⟨n, rfl⟩
    exact ⟨d*n, pow_mul x d n⟩
  · rintro z ⟨n, rfl⟩
    refine ⟨(x ^ d) ^ n, ⟨n, rfl⟩, ?_⟩
    rw [← pow_mul]
    exact pow_dvd_pow x (Nat.le_mul_of_pos_left n hd)

/-- The scalar square itself is cartesian, by localization at the parameter. -/
lemma base_cartesian (d : ℕ) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : IsLaurentExtension k d hd ell) :
    IsPullback (Spec.map (CommRingCat.ofHom ell)) (genericBase k)
      (genericBase k) (baseMorphism k d hd) := by
  letI : IsLocalization
      ((Submonoid.powers (PowerSeries.X : PowerSeries k)).map (baseMap k d hd))
      (LaurentSeries k) := by
    rw [Submonoid.map_powers]
    simp only [baseMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.expand_X]
    change IsLocalization.Away ((PowerSeries.X : PowerSeries k) ^ d) (LaurentSeries k)
    exact localization_away_pow PowerSeries.X d hd
  exact (AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (baseMap k d hd) ell
      (RingHom.ext hell) (Submonoid.powers (PowerSeries.X : PowerSeries k)))).flip

variable {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
variable (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
variable (M : Model k T) (Mb : Model k Tb)
variable (F : Mb.X ⟶ M.X)
    (hF : F ≫ M.p = Mb.p ≫ baseMorphism k d hd)
variable (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : IsLaurentExtension k d hd ell)

/-- Base change of the integral morphism along the specified Laurent extension. -/
def lift : genericScheme k Mb ⟶ genericScheme k M :=
  pullback.lift (genericInclusion k Mb ≫ F)
    (genericStructure k Mb ≫ Spec.map (CommRingCat.ofHom ell)) (by
      rw [Category.assoc, hF, ← Category.assoc]
      change (pullback.fst Mb.p (genericBase k) ≫ Mb.p) ≫ _ = _
      rw [pullback.condition, Category.assoc, Category.assoc, base_square k d hd ell hell]
      rfl)

lemma lift_inclusion : IsGenericLift k T Tb M Mb F (lift k T Tb M Mb F hF ell hell) :=
  pullback.lift_fst ..

lemma lift_structure :
    lift k T Tb M Mb F hF ell hell ≫ genericStructure k M =
      genericStructure k Mb ≫ Spec.map (CommRingCat.ofHom ell) :=
  pullback.lift_snd ..

/-- The open generic inclusion makes a lift of the integral map unique. -/
lemma lift_unique (f : genericScheme k Mb ⟶ genericScheme k M)
    (hf : IsGenericLift k T Tb M Mb F f) :
    f = lift k T Tb M Mb F hF ell hell := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  exact hf.trans (lift_inclusion k T Tb M Mb F hF ell hell).symm

/-- Restricting the integral ramification to the generic fibers is a base change
of the integral morphism, because the scalar localization square is cartesian. -/
lemma lift_cartesian_over_models :
    IsPullback (lift k T Tb M Mb F hF ell hell) (genericInclusion k Mb)
      (genericInclusion k M) F := by
  have hs := (IsPullback.of_hasPullback Mb.p (genericBase k)).paste_vert
    (base_cartesian k d hd ell hell).flip
  have hs' : IsPullback (genericInclusion k Mb)
      (lift k T Tb M Mb F hF ell hell ≫ genericStructure k M)
      (F ≫ M.p) (genericBase k) := by
    rw [lift_structure, hF]
    exact hs
  exact (hs'.of_bot (lift_inclusion k T Tb M Mb F hF ell hell).symm
    (IsPullback.of_hasPullback M.p (genericBase k))).flip

/-- The concrete comparison with the required field base change. -/
def comparison : genericScheme k Mb ⟶
    pullback (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)) :=
  pullback.lift (lift k T Tb M Mb F hF ell hell) (genericStructure k Mb)
    (lift_structure k T Tb M Mb F hF ell hell)

lemma comparison_fst : comparison k T Tb M Mb F hF ell hell ≫
    pullback.fst (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)) =
      lift k T Tb M Mb F hF ell hell := pullback.lift_fst ..

lemma comparison_snd : comparison k T Tb M Mb F hF ell hell ≫
    pullback.snd (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)) =
      genericStructure k Mb := pullback.lift_snd ..

lemma cartesian_of_comparison_isIso
    [IsIso (comparison k T Tb M Mb F hF ell hell)] :
    IsPullback (lift k T Tb M Mb F hF ell hell) (genericStructure k Mb)
      (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)) :=
  IsPullback.of_iso_pullback ⟨lift_structure k T Tb M Mb F hF ell hell⟩
    (asIso (comparison k T Tb M Mb F hF ell hell))
    (comparison_fst k T Tb M Mb F hF ell hell)
    (comparison_snd k T Tb M Mb F hF ell hell)

/-- The comparison is proper over the new Laurent field. -/
lemma comparison_proper (hM : IsModel k T M) (hMb : IsModel k Tb Mb) :
    IsProper (comparison k T Tb M Mb F hF ell hell) := by
  letI : IsProper (genericStructure k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI : IsProper (genericStructure k Mb) :=
    AlgebraizedGenericSmoothnessR0135.generic_proper k Mb hMb
  haveI : IsProper (comparison k T Tb M Mb F hF ell hell ≫
      pullback.snd (genericStructure k M) (Spec.map (CommRingCat.ofHom ell))) := by
    rw [comparison_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd (genericStructure k M) _)

/-- This equivalence retains the entire desired conclusion, including uniqueness.
It does not assert that the comparison is an isomorphism. -/
lemma target_iff_comparison_isIso :
    (∃! f : genericScheme k Mb ⟶ genericScheme k M,
      IsGenericLift k T Tb M Mb F f ∧
      IsPullback f (genericStructure k Mb) (genericStructure k M)
        (Spec.map (CommRingCat.ofHom ell))) ↔
      IsIso (comparison k T Tb M Mb F hF ell hell) := by
  constructor
  · rintro ⟨f, ⟨hf, hc⟩, _⟩
    have he : f = lift k T Tb M Mb F hF ell hell :=
      lift_unique k T Tb M Mb F hF ell hell f hf
    subst f
    have hq : comparison k T Tb M Mb F hF ell hell = hc.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [comparison_fst, hc.isoPullback_hom_fst]
      · rw [comparison_snd, hc.isoPullback_hom_snd]
    rw [hq]
    infer_instance
  · intro hq
    letI := hq
    exact ⟨lift k T Tb M Mb F hF ell hell,
      ⟨lift_inclusion k T Tb M Mb F hF ell hell,
        cartesian_of_comparison_isIso k T Tb M Mb F hF ell hell⟩,
      fun f hf => lift_unique k T Tb M Mb F hF ell hell f hf.1⟩

open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

/-- The lift retains each specified chart equation when passing to chart fields. -/
lemma lift_chart
    (ρ : Fin d → (Chart k →+* Chart k))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X))
    (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (hcharts : ∀ i : Fin (r*d), χb i ≫ F =
      Spec.map (CommRingCat.ofHom (ρ (residueIndex r d hd i))) ≫ χ (coarseIndex r d hd i))
    (i : Fin (r*d)) (E : ChartField k →+* ChartField k)
    (hE : ExtendsChart k (ρ (residueIndex r d hd i)) E) :
    genericChart k Mb (χb i) (hχb i).1 ≫ lift k T Tb M Mb F hF ell hell =
      Spec.map (CommRingCat.ofHom E) ≫
        genericChart k M (χ (coarseIndex r d hd i)) (hχ _).1 := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  apply (cancel_mono (genericInclusion k M)).mp
  rw [Category.assoc, lift_inclusion, ← Category.assoc, genericChart_inclusion,
    Category.assoc, hcharts, Category.assoc, genericChart_inclusion]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom z)) (RingHom.ext (fun a => (hE a).symm))

section SmoothCharts
open ArithmeticThetaPolygonCohomologyR0131

private def smoothPresentation (n : ℕ) : B k n true ≃+* LaurentPolynomial (R k n) :=
  Classical.choose (truncated_laurent_presentation k n)

private lemma smoothPresentation_spec (n : ℕ) :
    LaurentPresentation k n (smoothPresentation k n) :=
  (Classical.choose_spec (truncated_laurent_presentation k n)).1

private lemma smoothPresentation_inv_C (n : ℕ) (a : R k n) :
    (smoothPresentation k n).symm (LaurentPolynomial.C a) =
      restriction k n true (base k n a) := by
  apply (smoothPresentation k n).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (smoothPresentation_spec k n).1 a).symm

/-- The finite-stage map on the noncontracted smooth torus. -/
def smoothMap (d : ℕ) (hd : 0 < d) (n : ℕ) : B k n true →+* B k n true :=
  (smoothPresentation k n).symm.toRingHom.comp
    ((laurentMap (RamifiedPolygonTower.coefficientMap k d hd n)).comp
      (smoothPresentation k n).toRingHom)

lemma smoothMap_base (d : ℕ) (hd : 0 < d) (n : ℕ) (a : R k n) :
    smoothMap k d hd n (restriction k n true (base k n a)) =
      restriction k n true (base k n (RamifiedPolygonTower.coefficientMap k d hd n a)) := by
  change (smoothPresentation k n).symm
    (laurentMap _ (smoothPresentation k n (restriction k n true (base k n a)))) = _
  have ha : smoothPresentation k n (restriction k n true (base k n a)) =
      LaurentPolynomial.C a := RingHom.congr_fun (smoothPresentation_spec k n).1 a
  rw [ha, laurentMap_C, smoothPresentation_inv_C]

lemma smoothMap_x (d : ℕ) (hd : 0 < d) (n : ℕ) :
    smoothMap k d hd n (restriction k n true (coordX k n)) =
      restriction k n true (coordX k n) := by
  change (smoothPresentation k n).symm
    (laurentMap _ (smoothPresentation k n (restriction k n true (coordX k n)))) = _
  rw [(smoothPresentation_spec k n).2, laurentMap_T,
    ← (smoothPresentation_spec k n).2, RingEquiv.symm_apply_apply]

/-- The smooth torus square is cartesian at every infinitesimal thickness. -/
lemma smoothMap_cartesian (d : ℕ) (hd : 0 < d) (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (smoothMap k d hd n)))
      (Spec.map (CommRingCat.ofHom ((restriction k n true).comp (base k n))))
      (Spec.map (CommRingCat.ofHom ((restriction k n true).comp (base k n))))
      (Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n))) := by
  apply AlgebraicGeometry.isPullback_SpecMap_of_isPushout
  apply (laurent_pushout (RamifiedPolygonTower.coefficientMap k d hd n)).of_iso
    (Iso.refl _) (smoothPresentation k n).symm.toCommRingCatIso
    (Iso.refl _) (smoothPresentation k n).symm.toCommRingCatIso
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact smoothPresentation_inv_C k n a
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (smoothPresentation k n).symm (laurentMap _ a) =
      (smoothPresentation k n).symm
        (laurentMap _ (smoothPresentation k n ((smoothPresentation k n).symm a)))
    rw [RingEquiv.apply_symm_apply]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact smoothPresentation_inv_C k n a

/-- The torus map is the restriction of the given completed-chart map on the
zero residue chart. It is not merely an abstract isomorphism of Laurent rings. -/
lemma smoothMap_nodeMap (d : ℕ) (hd : 0 < d) (n : ℕ) (q : Fin d) (hq : q.val = 0)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    (smoothMap k d hd n).comp (restriction k n true) =
      (restriction k n true).comp (RamifiedPolygonTower.nodeMap k ρ hρ n) := by
  let f := (smoothMap k d hd n).comp (restriction k n true)
  let g := (restriction k n true).comp (RamifiedPolygonTower.nodeMap k ρ hρ n)
  have hb : f.comp (base k n) = g.comp (base k n) := by
    ext a
    change smoothMap k d hd n (restriction k n true (base k n a)) =
      restriction k n true (RamifiedPolygonTower.nodeMap k ρ hρ n (base k n a))
    rw [smoothMap_base, RamifiedPolygonTower.nodeMap_base]
  have hx : f (coordX k n) = g (coordX k n) := by
    change smoothMap k d hd n (restriction k n true (coordX k n)) =
      restriction k n true (RamifiedPolygonTower.nodeMap k ρ hρ n (coordX k n))
    rw [smoothMap_x, RamifiedPolygonTower.nodeMap_x, hq, pow_zero, one_mul]
  apply point_ext hb hx
  have hu : IsUnit (f (coordX k n)) := by
    change IsUnit (smoothMap k d hd n (restriction k n true (coordX k n)))
    rw [smoothMap_x]
    have he : (smoothPresentation k n).symm (LaurentPolynomial.T 1) =
        restriction k n true (coordX k n) := by
      rw [← (smoothPresentation_spec k n).2, RingEquiv.symm_apply_apply]
    rw [← he]
    exact (LaurentPolynomial.isUnit_T 1).map (smoothPresentation k n).symm.toRingHom
  apply hu.mul_left_cancel
  calc
    f (coordX k n) * f (coordY k n) = f (base k n (parameter k n)) := by
      rw [← map_mul, coordX_mul_coordY]
    _ = g (base k n (parameter k n)) := RingHom.congr_fun hb (parameter k n)
    _ = f (coordX k n) * g (coordY k n) := by
      rw [hx, ← map_mul, coordX_mul_coordY]

/-- On every other refined chart the target x coordinate is nilpotent.
Consequently such a chart has no point above the target x-open. -/
lemma nodeMap_x_nilpotent (d : ℕ) (hd : 0 < d) (n : ℕ) (q : Fin d) (hq : 0 < q.val)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    IsNilpotent (RamifiedPolygonTower.nodeMap k ρ hρ n (coordX k n)) := by
  rw [RamifiedPolygonTower.nodeMap_x]
  refine ⟨n+1, ?_⟩
  rw [mul_pow, ← pow_mul, Nat.mul_comm q.val (n+1), pow_mul]
  have ht : RamifiedPolygonTower.tau k n ^ (n+1) = 0 := by
    rw [← map_pow, parameter_pow, map_zero]
  rw [ht, zero_pow (Nat.ne_of_gt hq), zero_mul]

/-- Exact inverse image of the target x-open on each refined affine chart. -/
lemma nodeMap_preimage_x (d : ℕ) (hd : 0 < d) (n : ℕ) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    TopologicalSpace.Opens.comap
      ⟨PrimeSpectrum.comap (RamifiedPolygonTower.nodeMap k ρ hρ n),
        PrimeSpectrum.continuous_comap _⟩ (PrimeSpectrum.basicOpen (coordX k n)) =
      if q.val = 0 then PrimeSpectrum.basicOpen (coordX k n) else ⊥ := by
  rw [PrimeSpectrum.comap_basicOpen]
  split_ifs with hq
  · rw [RamifiedPolygonTower.nodeMap_x, hq, pow_zero, one_mul]
  · exact (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr
      (nodeMap_x_nilpotent k d hd n q (Nat.pos_of_ne_zero hq) ρ hρ)

/-- The specified coordinate-open map has exactly the expected principal-open range. -/
lemma restriction_range (n : ℕ) (side : Bool) :
    Set.range (PrimeSpectrum.comap (restriction k n side)) =
      (PrimeSpectrum.basicOpen (if side then coordX k n else coordY k n) : Set _) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    apply (PrimeSpectrum.mem_basicOpen _ _).mpr
    have hu : IsUnit (restriction k n side (if side then coordX k n else coordY k n)) := by
      have h := (IsLocalization.Away.algebraMap_isUnit
        (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k side)).map
        (trunc (RawOpen k side) (openParameter k side) n)
      cases side <;> exact h
    exact fun hz => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
  · intro hp
    let f := algebraMap (A k n) p.asIdeal.ResidueField
    have hu : IsUnit (f (if side then coordX k n else coordY k n)) := by
      rw [isUnit_iff_ne_zero]
      exact fun hz => (PrimeSpectrum.mem_basicOpen _ _).mp hp
        (Ideal.algebraMap_residueField_eq_zero.mp hz)
    let g := openPoint f side hu
    obtain ⟨z, hz⟩ := (PrimeSpectrum.residueField_comap p).symm ▸
      (show p ∈ ({p} : Set (PrimeSpectrum (A k n))) from rfl)
    refine ⟨PrimeSpectrum.comap g z, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, openPoint_restriction]
    exact hz

lemma rightLeg_range (n : ℕ) : Set.range (rightLeg k n) =
    (PrimeSpectrum.basicOpen (coordX k n) : Set (PrimeSpectrum (A k n))) :=
  restriction_range k n true

lemma leftLeg_range (n : ℕ) (E : B k n false ≃+* B k n true) :
    Set.range (leftLeg k n E) =
      (PrimeSpectrum.basicOpen (coordY k n) : Set (PrimeSpectrum (A k n))) := by
  change Set.range (PrimeSpectrum.comap (E.toRingHom.comp (restriction k n false))) = _
  rw [PrimeSpectrum.comap_comp, Set.range_comp]
  have hsur : Function.Surjective (PrimeSpectrum.comap E.toRingHom) := by
    intro z
    refine ⟨PrimeSpectrum.comap E.symm.toRingHom z, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    simp
  rw [hsur.range_eq, Set.image_univ]
  exact restriction_range k n false

/-- The smooth torus of a component, as its actual open immersion into the atlas. -/
def smoothChart {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : specB k n true ⟶ D.X :=
  rightLeg k n ≫ D.chart i

instance smoothChart_open {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : IsOpenImmersion (smoothChart k D i) := by
  letI := D.chart_open i
  unfold smoothChart
  infer_instance

/-- The smooth tori in distinct components are disjoint, including the cyclic seam. -/
lemma smoothChart_disjoint {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i j : Fin r) (hij : i ≠ j) :
    Disjoint (Set.range (smoothChart k D i)) (Set.range (smoothChart k D j)) := by
  have hadj (i : Fin r) (p q : specB k n true)
      (heq : smoothChart k D i p = smoothChart k D (next r hr i) q) : False := by
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i)
      (rightLeg k n p) (rightLeg k n q) heq
    exact Set.disjoint_left.mp (legs_disjoint k n E) ⟨z, hz⟩ ⟨p, rfl⟩
  rw [Set.disjoint_left]
  rintro x ⟨p, rfl⟩ ⟨q, hq⟩
  by_cases hn : next r hr i = j
  · subst j
    exact hadj i p q hq.symm
  by_cases hp : next r hr j = i
  · subst i
    exact hadj j q p hq
  · exact Set.disjoint_left.mp (D.disjoint i j hij hn hp)
      ⟨rightLeg k n p, rfl⟩ ⟨rightLeg k n q, hq⟩

/-- A point in chart i mapping to component j's smooth torus lies either in
its own right open or in the left overlap with the next chart. -/
lemma chart_mem_smoothChart {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (i j : Fin r) (a : specA k n) :
    D.chart i a ∈ Set.range (smoothChart k D j) ↔
      (i = j ∧ a ∈ Set.range (rightLeg k n)) ∨
      (next r hr i = j ∧ a ∈ Set.range (leftLeg k n E)) := by
  constructor
  · rintro ⟨b, hb⟩
    by_cases hij : i = j
    · subst j
      left
      refine ⟨rfl, b, ?_⟩
      letI := D.chart_open i
      exact (D.chart i).isOpenEmbedding.injective hb
    by_cases hn : next r hr i = j
    · subst j
      right
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i)
        a (rightLeg k n b) hb.symm
      exact ⟨rfl, z, hz⟩
    by_cases hp : next r hr j = i
    · subst i
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j)
        (rightLeg k n b) a hb
      exact False.elim (Set.disjoint_left.mp (legs_disjoint k n E) ⟨z, hz⟩ ⟨b, rfl⟩)
    · exact False.elim (Set.disjoint_left.mp (D.disjoint i j hij hn hp)
        ⟨a, rfl⟩ ⟨rightLeg k n b, hb⟩)
  · rintro (⟨rfl, b, rfl⟩ | ⟨rfl, b, rfl⟩)
    · exact ⟨b, rfl⟩
    · exact ⟨b, (congrArg (fun f => f b) (D.adjacent i).w).symm⟩

lemma nodeMap_mem_right_iff (d : ℕ) (hd : 0 < d) (n : ℕ) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) (a : specA k n) :
    Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.nodeMap k ρ hρ n)) a ∈
      Set.range (rightLeg k n) ↔ q.val = 0 ∧ a ∈ Set.range (rightLeg k n) := by
  rw [rightLeg_range]
  change RamifiedPolygonTower.nodeMap k ρ hρ n (coordX k n) ∉ a.asIdeal ↔
    q.val = 0 ∧ coordX k n ∉ a.asIdeal
  by_cases hq : q.val = 0
  · rw [RamifiedPolygonTower.nodeMap_x, hq, pow_zero, one_mul]
    simp
  · obtain ⟨m, hm⟩ := nodeMap_x_nilpotent k d hd n q (Nat.pos_of_ne_zero hq) ρ hρ
    have hh := a.isPrime.mem_of_pow_mem m (hm ▸ Ideal.zero_mem a.asIdeal)
    simp [hq, hh]

lemma nodeMap_mem_left_iff (d : ℕ) (hd : 0 < d) (n : ℕ) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)
    (E Eb : B k n false ≃+* B k n true) (a : specA k n) :
    Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.nodeMap k ρ hρ n)) a ∈
      Set.range (leftLeg k n E) ↔ q.val+1 = d ∧ a ∈ Set.range (leftLeg k n Eb) := by
  rw [leftLeg_range, leftLeg_range]
  change RamifiedPolygonTower.nodeMap k ρ hρ n (coordY k n) ∉ a.asIdeal ↔
    q.val+1 = d ∧ coordY k n ∉ a.asIdeal
  rw [RamifiedPolygonTower.nodeMap_y]
  by_cases hq : q.val+1 = d
  · rw [show d-q.val-1 = 0 by omega, pow_zero, one_mul]
    simp [hq]
  · have hpos : 0 < d-q.val-1 := by have := q.isLt; omega
    have ht : RamifiedPolygonTower.tau k n ^ (n+1) = 0 := by
      rw [← map_pow, parameter_pow, map_zero]
    have hm : (RamifiedPolygonTower.tau k n ^ (d-q.val-1) * coordY k n) ^ (n+1) = 0 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (d-q.val-1) (n+1), pow_mul,
        ht, zero_pow (Nat.ne_of_gt hpos), zero_mul]
    have hh := a.isPrime.mem_of_pow_mem (n+1) (hm ▸ Ideal.zero_mem a.asIdeal)
    simp [hq, hh]

private lemma index_eq_marked {r d : ℕ} (hd : 0 < d) (i : Fin (r*d))
    (hq : (residueIndex r d hd i).val = 0) :
    i = markedIndex r d hd (coarseIndex r d hd i) := by
  apply Fin.ext
  change i.val = i.val/d*d
  have h := Nat.mod_add_div i.val d
  change i.val % d = 0 at hq
  rw [hq, zero_add, Nat.mul_comm] at h
  exact h.symm

lemma stage_smoothChart {r d n : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    {E Eb : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (Db : Atlas k (r*d) n hrd Eb)
    (hE : IsAdjacent k n E) (hEb : IsAdjacent k n Eb) (j : Fin r) :
    smoothChart k Db (markedIndex r d hd j) ≫
      RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb =
      Spec.map (CommRingCat.ofHom (smoothMap k d hd n)) ≫ smoothChart k D j := by
  unfold smoothChart
  rw [Category.assoc, RamifiedPolygonTower.stageHom_chart]
  unfold RamifiedPolygonTower.localMap
  rw [RamifiedMarkedSections.coarse_marked, ← Category.assoc, ← Category.assoc,
    rightLeg, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  exact (smoothMap_nodeMap k d hd n _
    (congrArg Fin.val (RamifiedMarkedSections.residue_marked r d hd j)) _ (hρ _)).symm

/-- The complete inverse image of the smooth torus is its marked refined torus.
The atlas overlap equations account for both endpoints and the cyclic seam. -/
lemma stage_preimage_smoothChart {r d n : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    {E Eb : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (Db : Atlas k (r*d) n hrd Eb)
    (hE : IsAdjacent k n E) (hEb : IsAdjacent k n Eb) (j : Fin r) :
    (RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb) ⁻¹'
      Set.range (smoothChart k D j) = Set.range (smoothChart k Db (markedIndex r d hd j)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, a, rfl⟩ := Db.covers x
    have hi := congrArg (fun f => f a)
      (RamifiedPolygonTower.stageHom_chart k ρ hρ D Db hE hEb i)
    change RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb (Db.chart i a) ∈ Set.range (smoothChart k D j) at hx
    change (Db.chart i ≫ RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb) a ∈ Set.range (smoothChart k D j) at hx
    rw [hi] at hx
    change D.chart (coarseIndex r d hd i)
      (Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.nodeMap k _ (hρ _) n)) a) ∈ Set.range (smoothChart k D j) at hx
    rcases (chart_mem_smoothChart k D _ j _).mp hx with ⟨hj, ha⟩ | ⟨hj, ha⟩
    · obtain ⟨hq, ha⟩ := (nodeMap_mem_right_iff k d hd n _ _ (hρ _) a).mp ha
      have he := index_eq_marked hd i hq
      rw [hj] at he
      exact (chart_mem_smoothChart k Db i _ a).mpr (Or.inl ⟨he, ha⟩)
    · obtain ⟨hq, ha⟩ := (nodeMap_mem_left_iff k d hd n _ _ (hρ _) E Eb a).mp ha
      have hb := RamifiedPolygonTower.indices_boundary hr hd hrd i hq
      have he := index_eq_marked hd (next (r*d) hrd i) hb.2
      rw [hb.1, hj] at he
      exact (chart_mem_smoothChart k Db i _ a).mpr (Or.inr ⟨he, ha⟩)
  · rintro ⟨a, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (smoothMap k d hd n)) a,
      (congrArg (fun f => f a) (stage_smoothChart k ρ hρ D Db hE hEb j)).symm⟩

/-- The finite-stage contraction square is cartesian above each actual smooth torus. -/
lemma stage_smooth_cartesian {r d n : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    {E Eb : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (Db : Atlas k (r*d) n hrd Eb)
    (hE : IsAdjacent k n E) (hEb : IsAdjacent k n Eb) (j : Fin r) :
    IsPullback (Spec.map (CommRingCat.ofHom (smoothMap k d hd n)))
      (smoothChart k Db (markedIndex r d hd j)) (smoothChart k D j)
      (RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (stage_smoothChart k ρ hρ D Db hE hEb j)
  apply TopologicalSpace.Opens.ext
  exact stage_preimage_smoothChart k ρ hρ D Db hE hEb j

/-- A categorical cancellation lemma retaining the actual maps to a base change. -/
private lemma comparison_square {U V X Y S Sb : Scheme.{u}}
    (u : U ⟶ V) (a : U ⟶ X) (b : V ⟶ Y) (F : X ⟶ Y)
    (pU : U ⟶ Sb) (pV : V ⟶ S) (pX : X ⟶ Sb) (pY : Y ⟶ S) (β : Sb ⟶ S)
    (hs : IsPullback u a b F) (hb : IsPullback u pU pV β)
    (ha : a ≫ pX = pU) (hv : b ≫ pY = pV) (hF : F ≫ pY = pX ≫ β) :
    IsPullback (𝟙 U) a
      (pullback.lift (u ≫ b) pU (by rw [Category.assoc, hv]; exact hb.w))
      (pullback.lift F pX hF) := by
  let B := pullback.lift (u ≫ b) pU (by rw [Category.assoc, hv]; exact hb.w)
  let G := pullback.lift F pX hF
  have hB₁ : B ≫ pullback.fst pY β = u ≫ b := pullback.lift_fst ..
  have hB₂ : B ≫ pullback.snd pY β = pU := pullback.lift_snd ..
  have hG₁ : G ≫ pullback.fst pY β = F := pullback.lift_fst ..
  have hG₂ : G ≫ pullback.snd pY β = pX := pullback.lift_snd ..
  have hc : IsPullback u B b (pullback.fst pY β) := by
    have hbig : IsPullback u (B ≫ pullback.snd pY β) (b ≫ pY) β := by
      rw [hB₂, hv]
      exact hb
    exact hbig.of_bot hB₁.symm (IsPullback.of_hasPullback pY β)
  have hw : (𝟙 U) ≫ B = a ≫ G := by
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [hB₁, Category.assoc, hG₁, hs.w]
    · rw [hB₂, Category.assoc, hG₂, ha]
  have hbig : IsPullback ((𝟙 U) ≫ u) a b (G ≫ pullback.fst pY β) := by
    rw [Category.id_comp, hG₁]
    exact hs
  exact hbig.of_right hw hc

lemma stage_smooth_over (n : ℕ) {r : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E) (i : Fin r) :
    smoothChart k D i ≫ D.p =
      Spec.map (CommRingCat.ofHom ((restriction k n true).comp (base k n))) := by
  rw [smoothChart, Category.assoc, D.chart_over, rightLeg, structureMap,
    ← Spec.map_comp]
  rfl

/-- The stage comparison becomes the identity after pullback to a smooth torus
of the actual base-changed target. -/
lemma stage_comparison_smooth_cartesian {r d n : ℕ} {hr : 0 < r}
    {hd : 0 < d} {hrd : 0 < r*d}
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    {E Eb : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (Db : Atlas k (r*d) n hrd Eb)
    (hE : IsAdjacent k n E) (hEb : IsAdjacent k n Eb) (j : Fin r) :
    let u := Spec.map (CommRingCat.ofHom (smoothMap k d hd n))
    let p := Spec.map (CommRingCat.ofHom ((restriction k n true).comp (base k n)))
    let β := Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n))
    let B := pullback.lift (u ≫ smoothChart k D j) p
      (by rw [Category.assoc, stage_smooth_over]; exact (smoothMap_cartesian k d hd n).w)
    let G := pullback.lift (RamifiedPolygonTower.stageHom k ρ hρ D Db hE hEb) Db.p
      (RamifiedPolygonTower.stageHom_over k ρ hρ D Db hE hEb)
    IsPullback (𝟙 (specB k n true)) (smoothChart k Db (markedIndex r d hd j)) B G := by
  apply comparison_square
  · exact stage_smooth_cartesian k ρ hρ D Db hE hEb j
  · exact smoothMap_cartesian k d hd n
  · exact stage_smooth_over k n Db _
  · exact stage_smooth_over k n D j

end SmoothCharts

section FormalComparison

/-- Detect an isomorphism to a complete affine base on all its infinitesimal fibers. -/
private lemma proper_iso_of_truncations (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of R)) [IsProper h]
    (hn : ∀ n : ℕ, IsIso (pullback.snd h
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^(n+1))))))) : IsIso h := by
  apply AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
    R I (𝟙 (Spec (.of R))) h
    (fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^(n+1))))) (fun _ => rfl)
  intro n
  let s := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^(n+1))))
  haveI : IsIso (pullback.snd h s) := hn n
  haveI : IsIso (pullback.snd (h ≫ 𝟙 _) s) := by
    rw [Category.comp_id]
    exact hn n
  let e := pullbackRightPullbackFstIso (𝟙 (Spec (.of R))) s h
  have he : pullback.snd h (pullback.fst (𝟙 _) s) =
      e.hom ≫ pullback.snd (h ≫ 𝟙 _) s ≫ inv (pullback.snd (𝟙 _) s) := by
    apply (cancel_mono (pullback.snd (𝟙 _) s)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (pullbackRightPullbackFstIso_hom_snd (𝟙 _) s h).symm
  rw [he]
  infer_instance

/-- A proper map which is the identity after every truncation of a complete
local test scheme is the identity after pullback to that whole test scheme. -/
lemma formal_cartesian (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X Y : Scheme.{u}}
    (G : X ⟶ Y) [IsProper G] (a : Spec (.of R) ⟶ X) (b : Spec (.of R) ⟶ Y)
    (hab : a ≫ G = b)
    (hn : ∀ n : ℕ, let s := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^(n+1))))
      IsPullback (𝟙 _) (s ≫ a) (s ≫ b) G) :
    IsPullback (𝟙 _) a b G := by
  let j := pullback.lift a (𝟙 _) (by simpa using hab)
  have hj₁ : j ≫ pullback.fst G b = a := pullback.lift_fst ..
  have hj₂ : j ≫ pullback.snd G b = 𝟙 _ := pullback.lift_snd ..
  haveI : IsIso (pullback.snd G b) := by
    apply proper_iso_of_truncations R I
    intro n
    let s := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^(n+1))))
    have hbig : IsPullback ((s ≫ j) ≫ pullback.fst G b) (𝟙 _)
        G (s ≫ b) := by
      rw [Category.assoc, hj₁]
      exact (hn n).flip
    have hp : IsPullback (s ≫ j) (𝟙 _) (pullback.snd G b) s :=
      hbig.of_right (by simp only [Category.assoc, hj₂, Category.comp_id, Category.id_comp])
        (IsPullback.of_hasPullback G b)
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have hj : j = inv (pullback.snd G b) := by
    apply (cancel_mono (pullback.snd G b)).mp
    rw [hj₂, IsIso.inv_hom_id]
  haveI : IsIso j := by rw [hj]; infer_instance
  exact (IsPullback.of_iso_pullback ⟨by simpa using hab⟩ (asIso j) hj₁ hj₂).flip

/-- Formation of the concrete comparison commutes with a compatible change of
base, even when the scalar square itself is not cartesian. -/
private lemma comparison_reduction_cartesian
    {X Y S Sb Xn Yn Sn Sbn : Scheme.{u}}
    (pX : X ⟶ Sb) (pY : Y ⟶ S) (β : Sb ⟶ S)
    (pXn : Xn ⟶ Sbn) (pYn : Yn ⟶ Sn) (βn : Sbn ⟶ Sn)
    (iX : Xn ⟶ X) (iY : Yn ⟶ Y) (σ : Sn ⟶ S) (σb : Sbn ⟶ Sb)
    (hX : IsPullback iX pXn pX σb) (hY : IsPullback iY pYn pY σ)
    (hβ : σb ≫ β = βn ≫ σ)
    (F : X ⟶ Y) (Fn : Xn ⟶ Yn)
    (hF : F ≫ pY = pX ≫ β) (hFn : Fn ≫ pYn = pXn ≫ βn)
    (hiF : iX ≫ F = Fn ≫ iY) :
    let G := pullback.lift F pX hF
    let Gn := pullback.lift Fn pXn hFn
    let iz := pullback.lift (pullback.fst pYn βn ≫ iY)
      (pullback.snd pYn βn ≫ σb) (by
        rw [Category.assoc, hY.w, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc, hβ])
    IsPullback Gn iX iz G := by
  intro G Gn iz
  have hiz₁ : iz ≫ pullback.fst pY β = pullback.fst pYn βn ≫ iY := pullback.lift_fst ..
  have hiz₂ : iz ≫ pullback.snd pY β = pullback.snd pYn βn ≫ σb := pullback.lift_snd ..
  have hG₁ : G ≫ pullback.fst pY β = F := pullback.lift_fst ..
  have hG₂ : G ≫ pullback.snd pY β = pX := pullback.lift_snd ..
  have hGn₁ : Gn ≫ pullback.fst pYn βn = Fn := pullback.lift_fst ..
  have hGn₂ : Gn ≫ pullback.snd pYn βn = pXn := pullback.lift_snd ..
  have hz : IsPullback iz (pullback.snd pYn βn) (pullback.snd pY β) σb := by
    have hb : IsPullback (iz ≫ pullback.fst pY β) (pullback.snd pYn βn) pY (σb ≫ β) := by
      rw [hiz₁, hβ]
      exact (IsPullback.of_hasPullback pYn βn).paste_horiz hY
    exact hb.of_right hiz₂ (IsPullback.of_hasPullback pY β)
  have hw : Gn ≫ iz = iX ≫ G := by
    apply pullback.hom_ext
    · rw [Category.assoc, hiz₁, ← Category.assoc, hGn₁, Category.assoc, hG₁, hiF]
    · rw [Category.assoc, hiz₂, ← Category.assoc, hGn₂, Category.assoc, hG₂, hX.w]
  have hb : IsPullback (Gn ≫ pullback.snd pYn βn) iX σb (G ≫ pullback.snd pY β) := by
    rw [hGn₂, hG₂]
    exact hX.flip
  exact hb.of_right hw hz.flip

lemma model_reduction {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (T : Tower k r hr) (Tb : Tower k (r*d) hrd) (M : Model k T) (Mb : Model k Tb)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (n : ℕ) :
    Mb.inclusion n ≫ F = RamifiedPolygonTower.towerHom k T Tb ρ hρ n ≫ M.inclusion n := by
  apply (Tb.atlas n).hom_ext
  intro i
  rw [← Category.assoc, ← (hχb i).2, Category.assoc, hF.2]
  rw [RamifiedPolygonTower.towerHom, ← Category.assoc ((Tb.atlas n).chart i), RamifiedPolygonTower.stageHom_chart]
  unfold RamifiedPolygonTower.localMap
  rw [Category.assoc, ← (hχ _).2]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom z) ≫ χ (coarseIndex r d hd i))
    (RamifiedPolygonTower.nodeMap_reduction k _ (hρ _) n).symm

/-- The integral comparison with the actual ramified base change. -/
def integralComparison {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    {T : Tower k r hr} {Tb : Tower k (r*d) hrd} (M : Model k T) (Mb : Model k Tb)
    (F : Mb.X ⟶ M.X) (hF : F ≫ M.p = Mb.p ≫ baseMorphism k d hd) :
    Mb.X ⟶ pullback M.p (baseMorphism k d hd) := pullback.lift F Mb.p hF

lemma integralComparison_proper {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    {T : Tower k r hr} {Tb : Tower k (r*d) hrd} (M : Model k T) (Mb : Model k Tb)
    (hM : IsModel k T M) (hMb : IsModel k Tb Mb)
    (F : Mb.X ⟶ M.X) (hF : F ≫ M.p = Mb.p ≫ baseMorphism k d hd) :
    IsProper (integralComparison k M Mb F hF) := by
  letI : IsProper M.p := hM.1
  letI : IsProper Mb.p := hMb.1
  haveI : IsProper (integralComparison k M Mb F hF ≫ pullback.snd M.p (baseMorphism k d hd)) := by
    change IsProper (pullback.lift F Mb.p hF ≫ _)
    rw [pullback.lift_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd M.p (baseMorphism k d hd))

end FormalComparison

section CompletedSmooth

abbrev SmoothRing := HatOpen k true

def smoothRestriction : Chart k →+* SmoothRing k :=
  Classical.choose (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions k 0 true)

lemma smoothRestriction_spec :
    ArithmeticThetaIndexedOverlapsR0058.IsRestriction k 0 true (smoothRestriction k) :=
  (Classical.choose_spec
    (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions k 0 true)).1

instance smoothRing_domain : IsDomain (SmoothRing k) :=
  ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.open_hat_domain k 0 true

instance smoothRing_noetherian : IsNoetherianRing (SmoothRing k) := by
  letI : IsNoetherianRing (RawOpen k true) :=
    (ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.open_algebra_data k 0 true).2.1
  exact ArithmeticThetaFractionalCharts.noetherian_adic_completion _ _

lemma smoothRestriction_injective : Function.Injective (smoothRestriction k) :=
  ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.restriction_injective_of_spec
    k 0 true _ (smoothRestriction_spec k)

def smoothParameter : SmoothRing k :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 true (openParameter k true)

def smoothIdeal : Ideal (SmoothRing k) := Ideal.span {smoothParameter k}

private lemma principal_completion_complete {A : Type*} [CommRing A] (t : A) :
    IsAdicComplete
      ((Ideal.span {t}).map (algebraMap A (AdicCompletion (Ideal.span {t}) A)))
      (AdicCompletion (Ideal.span {t}) A) :=
  AdicCompletion.isAdicComplete_self (Ideal.span {t})
    (Submodule.fg_span (Set.finite_singleton t))

instance smoothRing_complete : IsAdicComplete (smoothIdeal k) (SmoothRing k) := by
  have he : (ArithmeticThetaIndexedOverlapsR0058.openIdeal k 0 true).map
      (algebraMap (RawOpen k true) (SmoothRing k)) = smoothIdeal k := by
    change (Ideal.span {ArithmeticThetaIndexedOverlapsR0058.ot k 0 true}).map
      (algebraMap (RawOpen k true) (SmoothRing k)) = _
    rw [Ideal.map_span, Set.image_singleton]
    unfold smoothIdeal smoothParameter
    rw [ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.ot_eq]
    rfl
  have h := principal_completion_complete (ArithmeticThetaIndexedOverlapsR0058.ot k 0 true)
  change IsAdicComplete ((ArithmeticThetaIndexedOverlapsR0058.openIdeal k 0 true).map
    (algebraMap (RawOpen k true) (SmoothRing k))) (SmoothRing k) at h
  rw [he] at h
  exact h

private def smoothReductionEquiv (n : ℕ) : HatB k n true ≃+* B k n true :=
  Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) true

private lemma smoothReductionEquiv_spec (n : ℕ) :
    CompletionComparison k n (Classical.choose (finite_stage_completion_comparison k n))
      (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n))) :=
  Classical.choose_spec (Classical.choose_spec (finite_stage_completion_comparison k n))

def smoothReduction (n : ℕ) : SmoothRing k →+* B k n true :=
  (smoothReductionEquiv k n).toRingHom.comp (trunc (SmoothRing k) (smoothParameter k) n)

lemma smoothReduction_surjective (n : ℕ) : Function.Surjective (smoothReduction k n) :=
  (smoothReductionEquiv k n).surjective.comp Ideal.Quotient.mk_surjective

lemma smoothReduction_kernel (n : ℕ) :
    RingHom.ker (smoothReduction k n) = smoothIdeal k ^ (n+1) := by
  rw [smoothReduction, RingHom.ker_comp_of_injective _ (smoothReductionEquiv k n).injective]
  exact Ideal.mk_ker

lemma smoothReduction_restriction (n : ℕ) :
    (smoothReduction k n).comp (smoothRestriction k) =
      (restriction k n true).comp (ArithmeticThetaKatoAnnularR0152.reduction k n) := by
  apply RingHom.ext
  exact (smoothReductionEquiv_spec k n).2.2 true

/-- The completed smooth chart is mapped to the actual model by its fixed node chart. -/
def completedSmoothChart {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (χ : chartScheme k ⟶ M.X) : Spec (.of (SmoothRing k)) ⟶ M.X :=
  Spec.map (CommRingCat.ofHom (smoothRestriction k)) ≫ χ

lemma completedSmoothChart_reduction {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (j : Fin r) (χ : chartScheme k ⟶ M.X)
    (hχ : IsChartMap k M j χ) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (smoothReduction k n)) ≫ completedSmoothChart k M χ =
      smoothChart k (T.atlas n) j ≫ M.inclusion n := by
  rw [completedSmoothChart, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    smoothReduction_restriction, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hχ.2]
  rfl

lemma completedSmoothChart_dominant {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) [IsIntegral (genericScheme k M)] (j : Fin r)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M j χ) :
    IsDominant (completedSmoothChart k M χ) := by
  letI : IsDominant χ := CompletedChartFieldMaps.chart_dominant k M hM j χ hχ
  letI : IsDominant (Spec.map (CommRingCat.ofHom (smoothRestriction k))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (smoothRestriction k))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (smoothRestriction_injective k)]
    exact bot_le
  unfold completedSmoothChart
  infer_instance

/-- Above a completed smooth component chart the integral comparison is an
isomorphism. This only asserts a pullback over that chart, not a global integral
isomorphism of the contraction. -/
lemma completedSmoothChart_cartesian {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (T : Tower k r hr) (Tb : Tower k (r*d) hrd) (M : Model k T) (Mb : Model k Tb)
    (hM : IsModel k T M) (hMb : IsModel k Tb Mb)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (j : Fin r) :
    let a := completedSmoothChart k Mb (χb (markedIndex r d hd j))
    let G := integralComparison k M Mb F hF.1
    IsPullback (𝟙 _) a (a ≫ G) G := by
  intro a G
  letI : IsProper G := integralComparison_proper k M Mb hM hMb F hF.1
  apply formal_cartesian (SmoothRing k) (smoothIdeal k) G a (a ≫ G) rfl
  intro n
  have hβ : baseInclusion k n ≫ baseMorphism k d hd =
      Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n)) ≫
        baseInclusion k n := by
    simp only [baseInclusion, baseMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hp := comparison_reduction_cartesian Mb.p M.p (baseMorphism k d hd)
    (Tb.atlas n).p (T.atlas n).p
    (Spec.map (CommRingCat.ofHom (RamifiedPolygonTower.coefficientMap k d hd n)))
    (Mb.inclusion n) (M.inclusion n) (baseInclusion k n) (baseInclusion k n)
    (hMb.2.2.1 n) (hM.2.2.1 n) hβ F (RamifiedPolygonTower.towerHom k T Tb ρ hρ n)
    hF.1 (RamifiedPolygonTower.stageHom_over k ρ hρ (T.atlas n) (Tb.atlas n)
      (T.overlap_spec n) (Tb.overlap_spec n))
    (model_reduction k T Tb M Mb ρ hρ χ hχ χb hχb F hF n)
  have hs := stage_comparison_smooth_cartesian k ρ hρ (T.atlas n) (Tb.atlas n)
    (T.overlap_spec n) (Tb.overlap_spec n) j
  dsimp only at hp hs
  have hc := hs.paste_vert hp
  have hw := hc.w
  simp only [Category.id_comp] at hw
  rw [hw, ← completedSmoothChart_reduction k Mb _ _ (hχb _) n] at hc
  change IsPullback (𝟙 _) (Spec.map (CommRingCat.ofHom (smoothReduction k n)) ≫ a)
    ((Spec.map (CommRingCat.ofHom (smoothReduction k n)) ≫ a) ≫ G) G at hc
  let E : (SmoothRing k ⧸ (smoothIdeal k)^(n+1)) ≃+* B k n true := smoothReductionEquiv k n
  let e : Spec (.of (B k n true)) ≅ Spec (.of (SmoothRing k ⧸ (smoothIdeal k)^(n+1))) :=
    Scheme.Spec.mapIso E.toCommRingCatIso.op
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((smoothIdeal k)^(n+1)))) =
      Spec.map (CommRingCat.ofHom (smoothReduction k n)) := by
    change Spec.map (CommRingCat.ofHom E.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    rfl
  apply hc.of_iso e e (Iso.refl _) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, ← Category.assoc] using congrArg (· ≫ a) he.symm
  · simpa only [Iso.refl_hom, Category.comp_id, ← Category.assoc] using
      congrArg (fun z => (z ≫ a) ≫ G) he.symm
  · simp

/-- A dominant field-valued point factors through every nonempty open subscheme. -/
private lemma dominant_field_lift {K : Type u} [Field K] {X U : Scheme.{u}}
    (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
    (f : Spec (.of K) ⟶ X) [IsDominant f] :
    ∃ g : Spec (.of K) ⟶ U, g ≫ i = f ∧ IsDominant g := by
  have hi : Set.range f ⊆ Set.range i := by
    obtain ⟨z, hz⟩ := f.denseRange.exists_mem_open i.isOpenEmbedding.isOpen_range
      (Set.range_nonempty i)
    rintro _ ⟨w, rfl⟩
    simpa only [Subsingleton.elim w z] using hz
  let g := IsOpenImmersion.lift i f hi
  have hg : g ≫ i = f := IsOpenImmersion.lift_fac i f hi
  refine ⟨g, hg, ?_⟩
  haveI : IsDominant (g ≫ i) := by rw [hg]; infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion g i

/-- The generic comparison becomes the identity over a dominant field-valued
point of the refined generic curve. All maps are restrictions of the integral
comparison and the specified completed chart. -/
lemma exists_generic_test {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (h3 : 3 ≤ r) (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
    (M : Model k T) (Mb : Model k Tb) (hM : IsModel k T M) (hMb : IsModel k Tb Mb)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k d hd ell) :
    ∃ a : Spec (.of (FractionRing (SmoothRing k))) ⟶ genericScheme k Mb,
      IsDominant a ∧ IsPullback (𝟙 _) a
        (a ≫ comparison k T Tb M Mb F hF.1 ell hell)
        (comparison k T Tb M Mb F hF.1 ell hell) := by
  let j : Fin r := ⟨0, hr⟩
  let c := completedSmoothChart k Mb (χb (markedIndex r d hd j))
  let s := Spec.map (CommRingCat.ofHom (algebraMap (SmoothRing k) (FractionRing (SmoothRing k))))
  let G := integralComparison k M Mb F hF.1
  let C := comparison k T Tb M Mb F hF.1 ell hell
  have h3b : 3 ≤ r*d := h3.trans (Nat.le_mul_of_pos_right r hd)
  letI : IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3b Mb hMb
  letI : IsDominant c := completedSmoothChart_dominant k Mb hMb _ _ (hχb _)
  letI : IsDominant s := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap (SmoothRing k) (FractionRing (SmoothRing k))))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (SmoothRing k) (FractionRing (SmoothRing k)))]
    exact bot_le
  letI : IsDominant (s ≫ c) := inferInstance
  letI : IsOpenImmersion (genericInclusion k Mb) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k Mb
  obtain ⟨a, ha, hda⟩ := dominant_field_lift (genericInclusion k Mb) (s ≫ c)
  refine ⟨a, hda, ?_⟩
  have hs : IsPullback (𝟙 _) (s ≫ c) ((s ≫ c) ≫ G) G := by
    have h := (IsPullback.of_id_fst (f := s)).paste_vert
      (completedSmoothChart_cartesian k T Tb M Mb hM hMb ρ hρ χ hχ χb hχb F hF j)
    simpa only [Category.assoc] using h
  have hp := comparison_reduction_cartesian Mb.p M.p (baseMorphism k d hd)
    (genericStructure k Mb) (genericStructure k M) (Spec.map (CommRingCat.ofHom ell))
    (genericInclusion k Mb) (genericInclusion k M) (genericBase k) (genericBase k)
    (IsPullback.of_hasPullback Mb.p (genericBase k))
    (IsPullback.of_hasPullback M.p (genericBase k))
    (base_square k d hd ell hell).symm F (lift k T Tb M Mb F hF.1 ell hell)
    hF.1 (lift_structure k T Tb M Mb F hF.1 ell hell)
    (lift_inclusion k T Tb M Mb F hF.1 ell hell).symm
  dsimp only at hp
  have hw := hp.w
  rw [← ha, Category.assoc] at hs
  change IsPullback (𝟙 _) (a ≫ genericInclusion k Mb)
    (a ≫ (genericInclusion k Mb ≫ pullback.lift F Mb.p hF.1)) (pullback.lift F Mb.p hF.1) at hs
  rw [← hw, ← Category.assoc] at hs
  exact hs.of_bot (by simp only [Category.id_comp]; rfl) hp

end CompletedSmooth

section GenericDominance

/-- The chart predicate determines the homomorphism, without assuming its
injectivity or fraction-field extension as an additional hypothesis. -/
lemma chartRamification_unique (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ ψ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ)
    (hψ : IsChartRamification k d hd q ψ) : ρ = ψ := by
  let J : Ideal (Chart k) := Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k}
  have he : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k)) = J := by
    simp only [ArithmeticThetaScaledTateBridgeR0046.nodeIdeal, Ideal.map_span, Set.image_singleton]
    apply congrArg (fun z : Chart k => Ideal.span {z})
    change ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 = _
    simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  letI : IsAdicComplete J (Chart k) := by
    rw [← he]
    exact AdicCompletion.isAdicComplete_self _ (Submodule.fg_span_singleton _)
  have hn (n : ℕ) : RamifiedPolygonTower.nodeMap k ρ hρ n = RamifiedPolygonTower.nodeMap k ψ hψ n := by
    apply point_ext
    · ext b
      exact (RamifiedPolygonTower.nodeMap_base k ρ hρ n b).trans
        (RamifiedPolygonTower.nodeMap_base k ψ hψ n b).symm
    · rw [RamifiedPolygonTower.nodeMap_x, RamifiedPolygonTower.nodeMap_x]
    · rw [RamifiedPolygonTower.nodeMap_y, RamifiedPolygonTower.nodeMap_y]
  apply RingHom.ext
  intro z
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := J)
  intro n
  apply SModEq.zero.mpr
  cases n with
  | zero => simp
  | succ n =>
    change ρ z - ψ z ∈ (J^(n+1) * ⊤ : Ideal (Chart k))
    rw [Ideal.mul_top, ← CompletedChartFieldMaps.reduction_kernel k n]
    change ArithmeticThetaKatoAnnularR0152.reduction k n (ρ z - ψ z) = 0
    rw [map_sub, sub_eq_zero]
    have h₁ := RingHom.congr_fun (RamifiedPolygonTower.nodeMap_reduction k ρ hρ n) z
    have h₂ := RingHom.congr_fun (RamifiedPolygonTower.nodeMap_reduction k ψ hψ n) z
    rw [hn n] at h₁
    exact h₁.symm.trans h₂

lemma chartRamification_field (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) (hρ : IsChartRamification k d hd q ρ) :
    Function.Injective ρ ∧ ∃ E : ChartField k →+* ChartField k, ExtendsChart k ρ E := by
  obtain ⟨ψ, hψ, _⟩ := completed_chart_ramification k d hd q
  have h := chartRamification_unique k d hd q ρ ψ hρ hψ.1
  subst ρ
  exact ⟨hψ.2.1, hψ.2.2.exists⟩

set_option synthInstance.maxHeartbeats 100000 in
lemma lift_dominant {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (h3 : 3 ≤ r) (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
    (M : Model k T) (Mb : Model k Tb) (hM : IsModel k T M)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k d hd ell) :
    IsDominant (lift k T Tb M Mb F hF.1 ell hell) := by
  let i : Fin (r*d) := ⟨0, hrd⟩
  obtain ⟨_, E, hE⟩ := chartRamification_field k d hd (residueIndex r d hd i) _ (hρ _)
  letI : IsIntegral (genericScheme k M) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI : IsDominant (genericChart k M (χ (coarseIndex r d hd i)) (hχ _).1) :=
    genericChart_dominant k M hM _ _ (hχ _)
  letI : IsDominant (Spec.map (CommRingCat.ofHom E)) := by
    constructor
    change DenseRange (PrimeSpectrum.comap E)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp E.injective]
    exact bot_le
  haveI : IsDominant (genericChart k Mb (χb i) (hχb i).1 ≫ lift k T Tb M Mb F hF.1 ell hell) := by
    rw [lift_chart k T Tb M Mb F hF.1 ell hell ρ χ hχ χb hχb hF.2 i E hE]
    infer_instance
  exact IsDominant.of_comp (genericChart k Mb (χb i) (hχb i).1) _

private lemma dominant_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (_root_.genericPoint X) = _root_.genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  have h := (genericPoint_spec X).image f.continuous
  simpa only [Set.image_univ, f.denseRange.closure_range] using h

/-- A discrete-fiber projection cannot hide a failure of dominance between
integral schemes. -/
private lemma dominant_of_comp_quasiFinite {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite g] [IsDominant (f ≫ g)] : IsDominant f := by
  letI : IsDominant g := IsDominant.of_comp f g
  have hg : g (_root_.genericPoint Y) = _root_.genericPoint Z := dominant_genericPoint g
  have hfg : g (f (_root_.genericPoint X)) = _root_.genericPoint Z := dominant_genericPoint (f ≫ g)
  have he : _root_.genericPoint Y = f (_root_.genericPoint X) :=
    (g.isDiscrete_preimage_singleton (_root_.genericPoint Z)).eq_of_specializes
      ((genericPoint_spec Y).specializes trivial) hg hfg
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨_root_.genericPoint X, he.symm⟩

lemma laurent_spec_finite (d : ℕ) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k d hd ell) :
    IsFinite (Spec.map (CommRingCat.ofHom ell)) := by
  obtain ⟨e, he, _⟩ := ramified_laurent_extension k d hd
  have heq : ell = e := IsFractionRing.ringHom_ext (fun x => (hell x).trans (he.1 x).symm)
  have hdeg : LaurentDegree k d ell := heq ▸ he.2
  apply (IsFinite.SpecMap_iff _).mpr
  exact hdeg.1

lemma comparison_target_integral {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (ell : LaurentSeries k →+* LaurentSeries k) :
    IsIntegral (pullback (genericStructure k M) (Spec.map (CommRingCat.ofHom ell))) := by
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_geometricallyIntegral k h3 M hM
  exact GeometricallyIntegral.isIntegral_of_subsingleton
    (pullback.snd (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)))

lemma comparison_dominant {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (h3 : 3 ≤ r) (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
    (M : Model k T) (Mb : Model k Tb) (hM : IsModel k T M) (hMb : IsModel k Tb Mb)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k d hd ell) :
    IsDominant (comparison k T Tb M Mb F hF.1 ell hell) := by
  letI : IsIntegral (genericScheme k M) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI : IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k
      (h3.trans (Nat.le_mul_of_pos_right r hd)) Mb hMb
  letI := comparison_target_integral k h3 M hM ell
  letI := laurent_spec_finite k d hd ell hell
  haveI : IsDominant (comparison k T Tb M Mb F hF.1 ell hell ≫
      pullback.fst (genericStructure k M) (Spec.map (CommRingCat.ofHom ell))) := by
    rw [comparison_fst]
    exact lift_dominant k h3 T Tb M Mb hM ρ hρ χ hχ χb hχb F hF ell hell
  letI : IsIntegral (pullback M.p (genericBase k)) :=
    inferInstanceAs (IsIntegral (genericScheme k M))
  exact dominant_of_comp_quasiFinite _
    (pullback.fst (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)))

private lemma field_point_factor {K : Type u} [Field K] {Y : Scheme.{u}}
    (b : Spec (.of K) ⟶ Y) (y : Y) (hy : b (IsLocalRing.closedPoint K) = y) :
    ∃ φ : Y.presheaf.stalk y →+* K, Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y = b := by
  subst y
  exact ⟨(Scheme.stalkClosedPointTo b).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk b⟩

/-- Faithfully flat field descent turns a dominant test isomorphism into a
section over the target's actual generic point. -/
lemma generic_section_of_field_test {K : Type u} [Field K] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (a : Spec (.of K) ⟶ X) [IsDominant a]
    (H : IsPullback (𝟙 _) a (a ≫ f) f) :
    ∃ t : Spec (.of Y.functionField) ⟶ X,
      t ≫ f = Y.fromSpecStalk (_root_.genericPoint Y) ∧ IsDominant t := by
  let η := Y.fromSpecStalk (_root_.genericPoint Y)
  have hy : (a ≫ f) (IsLocalRing.closedPoint K) = _root_.genericPoint Y := by
    simpa only [Subsingleton.elim (IsLocalRing.closedPoint K) (_root_.genericPoint (Spec (.of K)))]
      using dominant_genericPoint (a ≫ f)
  obtain ⟨φ, hφ⟩ := field_point_factor (a ≫ f) (_root_.genericPoint Y) hy
  let s : Spec (.of K) ⟶ Spec (.of Y.functionField) := Spec.map (CommRingCat.ofHom φ)
  have hsη : s ≫ η = a ≫ f := hφ
  let u := pullback.lift a s hsη.symm
  have hu₁ : u ≫ pullback.fst f η = a := pullback.lift_fst ..
  have hu₂ : u ≫ pullback.snd f η = s := pullback.lift_snd ..
  have hb : IsPullback (u ≫ pullback.fst f η) (𝟙 _) f (s ≫ η) := by
    rw [hu₁, hsη]
    exact H.flip
  have hp : IsPullback u (𝟙 _) (pullback.snd f η) s :=
    hb.of_right (by simp only [hu₂, Category.id_comp]) (IsPullback.of_hasPullback f η)
  haveI : Surjective s := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  haveI : Flat s := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField Y.functionField) φ)
  haveI : IsIso (pullback.snd f η) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let t := inv (pullback.snd f η) ≫ pullback.fst f η
  have htf : t ≫ f = η := by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have hst : s ≫ t = a := by
    rw [← hu₂, Category.assoc, IsIso.hom_inv_id_assoc, hu₁]
  refine ⟨t, htf, ?_⟩
  haveI : IsDominant (s ≫ t) := by rw [hst]; infer_instance
  exact IsDominant.of_comp s t

/-- A proper dominant map to a smooth integral curve is an isomorphism if it
becomes the identity over a dominant field-valued test point. The inverse is
extended using the actual valuation stalks of the target curve. -/
lemma iso_of_dominant_field_test {κ K : Type u} [Field κ] [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (pX : X ⟶ Spec (.of κ)) (pY : Y ⟶ Spec (.of κ))
    [IsProper pX] [IsSeparated pY] [SmoothOfRelativeDimension 1 pY]
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ pY = pX)
    (a : Spec (.of K) ⟶ X) [IsDominant a]
    (H : IsPullback (𝟙 _) a (a ≫ f) f) : IsIso f := by
  obtain ⟨t, ht, hdt⟩ := generic_section_of_field_test f a H
  letI : IsDominant t := hdt
  let η := Y.fromSpecStalk (_root_.genericPoint Y)
  have htp : t ≫ pX = η ≫ pY := by rw [← hf, ← Category.assoc, ht]
  obtain ⟨V, hV, g₀, a₀, hg₀, ha₀, hat⟩ :=
    ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.ValuationExtension.exists_valuation_chart
      pY pX t htp (_root_.genericPoint Y)
      (valuationRing_stalk_of_smoothOfRelativeDimension_one pY _)
  letI : Nonempty (V : Scheme) := ⟨⟨_root_.genericPoint Y, hV⟩⟩
  obtain ⟨g, hg, hVg⟩ :=
    ArithmeticThetaCompactifiedDifferentialR0145.CompactifiedCoordinateIsomorphism.ValuationExtension.exists_valuation_extension
      pY V.ι (fun x _ => valuationRing_stalk_of_smoothOfRelativeDimension_one pY x) pX g₀ hg₀
  change a₀ ≫ V.ι = η at ha₀
  have hηg : η ≫ g = t := by
    rw [← ha₀, Category.assoc, hVg, hat]
  letI : IsDominant η := by
    constructor
    change Dense (Set.range (Y.fromSpecStalk (_root_.genericPoint Y)))
    apply Dense.mono (s₁ := {_root_.genericPoint Y})
    · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
      exact (genericPoint_spec Y).specializes trivial
    · rw [dense_iff_closure_eq]
      exact genericPoint_spec Y
  have hgf : g ≫ f = 𝟙 Y := by
    apply ext_of_isDominant_of_isSeparated pY
      (by rw [Category.assoc, hf, hg, Category.id_comp]) η
    rw [← Category.assoc, hηg, ht, Category.comp_id]
  have hfg : f ≫ g = 𝟙 X := by
    apply ext_of_isDominant_of_isSeparated pX
      (by rw [Category.assoc, hg, hf, Category.id_comp]) t
    rw [← Category.assoc, ht, hηg, Category.comp_id]
  exact ⟨⟨g, hfg, hgf⟩⟩

lemma comparison_isIso {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
    (h3 : 3 ≤ r) (T : Tower k r hr) (Tb : Tower k (r*d) hrd)
    (M : Model k T) (Mb : Model k Tb) (hM : IsModel k T M) (hMb : IsModel k Tb Mb)
    (ρ : Fin d → (Chart k →+* Chart k)) (hρ : ∀ q, IsChartRamification k d hd q (ρ q))
    (χ : Fin r → (chartScheme k ⟶ M.X)) (hχ : ∀ j, IsChartMap k M j (χ j))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (hχb : ∀ j, IsChartMap k Mb j (χb j))
    (F : Mb.X ⟶ M.X) (hF : IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k) (hell : IsLaurentExtension k d hd ell) :
    IsIso (comparison k T Tb M Mb F hF.1 ell hell) := by
  letI : IsIntegral (genericScheme k Mb) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k
      (h3.trans (Nat.le_mul_of_pos_right r hd)) Mb hMb
  letI := comparison_target_integral k h3 M hM ell
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k Mb hMb
  obtain ⟨s, hs, _⟩ := ArithmeticThetaAlgebraizedMarkedLineR0136.marked_section_algebraization
    k r hr h3 T M hM (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one k h3 M hM s hs
  letI := comparison_dominant k h3 T Tb M Mb hM hMb ρ hρ χ hχ χb hχb F hF ell hell
  obtain ⟨a, hda, ha⟩ := exists_generic_test k h3 T Tb M Mb hM hMb ρ hρ χ hχ χb hχb F hF ell hell
  letI := hda
  letI : IsIntegral (pullback Mb.p (genericBase k)) :=
    inferInstanceAs (IsIntegral (genericScheme k Mb))
  exact iso_of_dominant_field_test (genericStructure k Mb)
    (pullback.snd (genericStructure k M) (Spec.map (CommRingCat.ofHom ell)))
    (comparison k T Tb M Mb F hF.1 ell hell) (comparison_snd k T Tb M Mb F hF.1 ell hell) a ha

end GenericDominance

end RamifiedGenericBaseChange

/-- The actual generic fibre of the refined polygon is the base change along
its prescribed Laurent map, uniquely compatibly with the integral contraction. -/
theorem ramified_generic_base_change :
  ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ)
    (hd : 0 < d)
    (r : ℕ)
    (hr : 0 < r)
    (h3 : 3 ≤ r)
    (hrd : 0 < r*d)
    (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
    (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd)
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model k Tb)
    (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel k Tb Mb)
    (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k))
    (hρ : ∀ q, ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q (ρ q))
    (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k)
    (M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (χb : Fin (r*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k)
    (Mb.X))
    (hχb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j (χb j))
    (F : Quiver.Hom (Mb.X)
    (M.X))
    (hF : ArithmeticThetaRamifiedPeriodR0154.IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell), ∃! f : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb)
    (ArithmeticThetaGenericEvaluationR0140.genericScheme k M), ArithmeticThetaRamifiedPeriodR0154.IsGenericLift k T Tb M Mb F f ∧ CategoryTheory.IsPullback f (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k Mb)
    (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ell)) := by
  intro k _ _ d hd r hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF ell hell
  apply (RamifiedGenericBaseChange.target_iff_comparison_isIso k T Tb M Mb F hF.1 ell hell).mpr
  exact RamifiedGenericBaseChange.comparison_isIso k h3 T Tb M Mb hM hMb ρ hρ χ hχ χb hχb F hF ell hell

end ArithmeticThetaRamifiedPeriodR0155

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.base_cartesian
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.lift_unique
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.lift_cartesian_over_models
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.comparison_proper
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.target_iff_comparison_isIso
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.lift_chart

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.smoothMap_cartesian
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.smoothMap_nodeMap
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.nodeMap_x_nilpotent

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.nodeMap_preimage_x

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.formal_cartesian
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.model_reduction
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.completedSmoothChart_cartesian
#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.exists_generic_test

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.stage_smooth_cartesian

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.stage_comparison_smooth_cartesian

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.smoothReduction_kernel

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.completedSmoothChart_dominant

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.chartRamification_unique

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.lift_dominant

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.comparison_dominant

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.generic_section_of_field_test

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.iso_of_dominant_field_test

#print axioms ArithmeticThetaRamifiedPeriodR0155.RamifiedGenericBaseChange.comparison_isIso

#print axioms ArithmeticThetaRamifiedPeriodR0155.ramified_generic_base_change
