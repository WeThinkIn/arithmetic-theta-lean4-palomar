module

public import InfinitesimalPolygonAtlasR0129
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

/-! Flatness for the specified infinitesimal polygon structural morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- Truncation of both rings is the actual pushout along the base quotient. -/
lemma trunc_isPushout {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (t : S) (s : T) (h : f t = s) (n : ℕ) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (trunc S t n))
      (CommRingCat.ofHom (trunc T s n)) (CommRingCat.ofHom (truncMap f t s h n)) := by
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom (trunc T s n) =
      CommRingCat.ofHom (trunc S t n) ≫ CommRingCat.ofHom (truncMap f t s h n) := by
    ext x
    rfl
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  apply PushoutCocone.isColimitAux'
  intro c
  have hk : (Ideal.span {s}) ^ (n+1) ≤ RingHom.ker c.inl.hom := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    change c.inl.hom (s ^ (n+1)) = 0
    have hw := congrArg (fun g => g (t ^ (n+1))) c.condition
    change c.inl.hom (f (t ^ (n+1))) = c.inr.hom (trunc S t n (t ^ (n+1))) at hw
    rw [map_pow, h] at hw
    rw [hw]
    have hz : trunc S t n (t ^ (n+1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
    rw [hz, map_zero]
  let g : Trunc T s n →+* c.pt := Ideal.Quotient.lift _ c.inl.hom (fun x hx => hk hx)
  refine ⟨CommRingCat.ofHom g, ?_, ?_, ?_⟩
  · ext x
    rfl
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact congrArg (fun q => q x) c.condition
  · intro q hq _
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom hq

lemma structureMap_flat (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    Flat (structureMap k n) := by
  rw [structureMap, Flat.SpecMap_iff]
  have hf : (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (ArithmeticThetaNodeCharts.node_flat_domain_parameter k).2.1
  exact MorphismProperty.of_isPushout (P := CommRingCat.flat) (trunc_isPushout
    (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
    PowerSeries.X (ArithmeticThetaNodeCharts.t k) rfl n).flip hf

/-- Every realization of the fixed atlas is flat over its truncated base. -/
theorem infinitesimal_polygon_flat :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (n : ℕ) (E : B k n false ≃+* B k n true), IsAdjacent k n E →
        ∀ D : Atlas k r n hr E, AlgebraicGeometry.Flat D.p := by
  intro k _ _ r hr _ n E _ D
  let U : D.X.OpenCover :=
    { I₀ := Fin r
      X := fun _ => specA k n
      f := D.chart
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨D.covers, D.chart_open⟩ }
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat) U
  intro i
  change Flat (D.chart i ≫ D.p)
  rw [D.chart_over]
  exact structureMap_flat k n

end ArithmeticThetaInfinitesimalPolygonR0129
