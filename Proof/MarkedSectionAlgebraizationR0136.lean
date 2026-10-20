module

public import AlgebraizedMarkedLineDefinitionsR0136
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

/-! Algebraization of the compatible marked points by an affine neighborhood
and completeness of the actual power-series quotients. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedSectionAlgebraizationR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPositiveLineR0134.CompatibleFormalSectionBasisR0134
variable (k : Type u) [Field k] [CharZero k]

lemma series_ext {f g : PowerSeries k}
    (h : ∀ n, trunc (PowerSeries k) PowerSeries.X n f =
      trunc (PowerSeries k) PowerSeries.X n g) : f = g := by
  obtain ⟨v, hv, hu⟩ := powerSeries_limit k
    (fun n => trunc (PowerSeries k) PowerSeries.X n g) (fun _ _ _ => rfl)
  exact (hu f h).trans (hu g (fun _ => rfl)).symm

lemma ring_limit {S : Type u} [CommRing S] (f : ∀ n, S →+* R k n)
    (hf : ∀ n N (h : n ≤ N),
      (truncReduce (PowerSeries k) PowerSeries.X n N h).comp (f N) = f n) :
    ∃ F : S →+* PowerSeries k, ∀ n,
      (trunc (PowerSeries k) PowerSeries.X n).comp F = f n := by
  choose g hg hu using fun x => powerSeries_limit k (fun n => f n x)
    (fun n N h => RingHom.congr_fun (hf n N h) x)
  let F : S →+* PowerSeries k :=
    { toFun := g
      map_one' := series_ext k (fun n => by rw [hg]; simp)
      map_zero' := series_ext k (fun n => by rw [hg]; simp)
      map_add' := fun x y => series_ext k (fun n => by simp only [hg, map_add])
      map_mul' := fun x y => series_ext k (fun n => by simp only [hg, map_mul]) }
  exact ⟨F, fun n => RingHom.ext (fun x => hg x n)⟩

local instance quotient_nontrivial (n : ℕ) : Nontrivial (R k n) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)).ne_top
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.pow_le_self (by omega)

local instance quotient_local (n : ℕ) : IsLocalRing (R k n) :=
  IsLocalRing.of_surjective' (trunc (PowerSeries k) PowerSeries.X n)
    Ideal.Quotient.mk_surjective

local instance trunc_local (n : ℕ) :
    IsLocalHom (trunc (PowerSeries k) PowerSeries.X n) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

local instance reduction_local (n N : ℕ) (h : n ≤ N) :
    IsLocalHom (truncReduce (PowerSeries k) PowerSeries.X n N h) :=
  IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective _)

lemma base_closed (n : ℕ) :
    baseInclusion k n (IsLocalRing.closedPoint (R k n)) =
      IsLocalRing.closedPoint (PowerSeries k) :=
  @Spec_closedPoint _ _ _ _ _ (trunc_local k n)

lemma reduction_closed (n N : ℕ) (h : n ≤ N) :
    baseReduction k n N h (IsLocalRing.closedPoint (R k n)) =
      IsLocalRing.closedPoint (R k N) :=
  @Spec_closedPoint _ _ _ _ _ (reduction_local k n N h)

lemma affine_lift {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {S : Type u} [CommRing S] [IsLocalRing S] (f : Spec (.of S) ⟶ X)
    (hf : f (IsLocalRing.closedPoint S) ∈ U) :
    ∃ g : Spec (.of S) ⟶ Spec Γ(X, U), g ≫ hU.fromSpec = f := by
  have hr : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem f hf).ge (Set.mem_univ x)
  exact ⟨IsOpenImmersion.lift hU.fromSpec f hr, IsOpenImmersion.lift_fac _ _ _⟩

lemma affine_hom_ext {S : CommRingCat.{u}}
    {f g : baseScheme k ⟶ Spec S}
    (h : ∀ n, baseInclusion k n ≫ f = baseInclusion k n ≫ g) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply series_ext k
  intro n
  have hh := h n
  rw [← Spec.map_preimage f, ← Spec.map_preimage g, baseInclusion,
    ← Spec.map_comp, ← Spec.map_comp] at hh
  exact congrArg (fun q => q.hom x) (Spec.map_injective hh)

lemma hom_ext {X : Scheme.{u}} {f g : baseScheme k ⟶ X}
    (h : ∀ n, baseInclusion k n ≫ f = baseInclusion k n ≫ g) : f = g := by
  have he : f (IsLocalRing.closedPoint (PowerSeries k)) =
      g (IsLocalRing.closedPoint (PowerSeries k)) := by
    have hh := congrArg (fun q : specR k 0 ⟶ X => q (IsLocalRing.closedPoint (R k 0))) (h 0)
    simpa only [Scheme.Hom.comp_apply, base_closed] using! hh
  obtain ⟨U, hU, hf, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := f (IsLocalRing.closedPoint (PowerSeries k))) (U := ⊤) trivial
  obtain ⟨f', hf'⟩ := affine_lift hU f hf
  obtain ⟨g', hg'⟩ := affine_lift hU g (he ▸ hf)
  rw [← hf', ← hg']
  congr 1
  apply affine_hom_ext k
  intro n
  apply (cancel_mono hU.fromSpec).mp
  simpa only [Category.assoc, hf', hg'] using h n

lemma point_algebraization {X : Scheme.{u}} (s : ∀ n, specR k n ⟶ X)
    (hs : ∀ n N (h : n ≤ N), baseReduction k n N h ≫ s N = s n) :
    ∃! f : baseScheme k ⟶ X, ∀ n, baseInclusion k n ≫ f = s n := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := s 0 (IsLocalRing.closedPoint (R k 0))) (U := ⊤) trivial
  have hn (n : ℕ) : s n (IsLocalRing.closedPoint (R k n)) ∈ U := by
    have hh := congrArg (fun q : specR k 0 ⟶ X => q (IsLocalRing.closedPoint (R k 0)))
      (hs 0 n (Nat.zero_le n))
    rw [Scheme.Hom.comp_apply, reduction_closed] at hh
    exact hh.symm ▸ hx
  choose g hg using fun n => affine_lift hU (s n) (hn n)
  let q (n : ℕ) : Γ(X, U) →+* R k n := (Spec.preimage (g n)).hom
  have hq (n N : ℕ) (h : n ≤ N) :
      (truncReduce (PowerSeries k) PowerSeries.X n N h).comp (q N) = q n := by
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (Spec.preimage (g N) ≫ CommRingCat.ofHom
      (truncReduce (PowerSeries k) PowerSeries.X n N h)) = Spec.map (Spec.preimage (g n))
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    apply (cancel_mono hU.fromSpec).mp
    simpa only [Category.assoc, hg] using! hs n N h
  obtain ⟨F, hF⟩ := ring_limit k q hq
  let f : baseScheme k ⟶ X := Spec.map (CommRingCat.ofHom F) ≫ hU.fromSpec
  have hf (n : ℕ) : baseInclusion k n ≫ f = s n := by
    dsimp [f, baseInclusion]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((trunc (PowerSeries k) PowerSeries.X n).comp F)) ≫ _ = _
    rw [hF]
    change Spec.map (Spec.preimage (g n)) ≫ _ = _
    rw [Spec.map_preimage, hg]
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  exact hom_ext k (fun n => (hf' n).trans (hf n).symm)

end ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedSectionAlgebraizationR0136

namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCohomologyR0131
open MarkedSectionAlgebraizationR0136

theorem marked_section_algebraization :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : Tower k r hr) (M : Model k T), IsModel k T M → ∀ (i : Fin r) (a : kˣ),
    ∃! s : baseScheme k ⟶ M.X, MarkedLift k M i a s := by
  intro k _ _ r hr _ T M hM i a
  let s (n : ℕ) := markedSection k r n hr (T.atlas n) i a ≫ M.inclusion n
  have hs (n N : ℕ) (h : n ≤ N) : baseReduction k n N h ≫ s N = s n := by
    dsimp [s]
    rw [← Category.assoc, ← CompatibleMarkingsR0131.section_reduction,
      Category.assoc, hM.2.2.2 n N h]
  obtain ⟨f, hf, hu⟩ := point_algebraization k s hs
  refine ⟨f, ⟨?_, hf⟩, fun g hg => hu g hg.2⟩
  change f ≫ M.p = 𝟙 (Spec (.of (PowerSeries k)))
  apply affine_hom_ext k
  intro n
  change baseInclusion k n ≫ (f ≫ M.p) = baseInclusion k n ≫ 𝟙 _
  rw [Category.comp_id, ← Category.assoc, hf]
  dsimp [s]
  rw [Category.assoc, (hM.2.2.1 n).w, ← Category.assoc,
    SmoothMarkedSections.section_over, Category.id_comp]

end ArithmeticThetaAlgebraizedMarkedLineR0136
#print axioms ArithmeticThetaAlgebraizedMarkedLineR0136.marked_section_algebraization
