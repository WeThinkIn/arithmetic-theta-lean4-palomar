import SectionDivisorComparison
import CompletedSectionOrder
import CompletedSectionInjective
import CuspOrder

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree

universe u v w
noncomputable section

namespace ArithmeticThetaSectionCompletion

private theorem scaledSeries_injective
    {R : Type u} [Semiring R] (L : ℕ) (hL : 0 < L) :
    Function.Injective (scaledSeries L : PowerSeries R → PowerSeries R) := by
  intro F G h
  apply PowerSeries.ext
  intro n
  have hc := congrArg (PowerSeries.coeff (L * n)) h
  change PowerSeries.coeff n F = PowerSeries.coeff n G
  simpa [scaledSeries, Nat.dvd_mul_right, Nat.mul_div_right n hL] using hc

private theorem order_toNat_ge_of_q_order
    {R : Type u} [Field R] (P : PowerSeries R) (m : ℕ)
    (hP : P ≠ 0) (hdiv : HasQOrderAtLeast P m) :
    (m : ℤ) ≤ (P.order.toNat : ℤ) := by
  obtain ⟨G, hG⟩ := hdiv
  have hcoeff : ∀ n : ℕ, n < m → PowerSeries.coeff n P = 0 := by
    intro n hn
    have hdvd : (PowerSeries.X : PowerSeries R) ^ m ∣ P := by
      refine ⟨G, ?_⟩
      exact hG
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) n hn
  by_contra hlt
  have hlt' : P.order.toNat < m := Nat.lt_of_not_ge (by
    intro hm
    exact hlt (by exact_mod_cast hm))
  exact (PowerSeries.coeff_order hP) (hcoeff _ hlt')

private theorem section_zero_of_expansion_order
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (H : X.Modules) (hH : IsLineBundle X H)
    (ι : Type v) (C : NormalFrameCover X H ι)
    (i : ι) (x : X) (hx : x ∈ C.opens i)
    (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (hc : Order.coheight x = 1)
    (s : Γ(H, ⊤)) (G : PowerSeries κ) (m : ℕ)
    (hG : completedSection X H C s i x hx κ e = G)
    (hGne : G ≠ 0) (hm : (m : ℤ) ≤ (G.order.toNat : ℤ))
    (d : ℤ)
    (hbound : ArithmeticThetaSectionOrder.localOrder X H C s i x ≤ d)
    (hstrict : d < m) :
    s = 0 := by
  by_contra hs
  have hco := completed_section_order X hN H hH ι C s i x hx κ e hc hs
  have hlocal : ArithmeticThetaSectionOrder.localOrder X H C s i x =
      ((G.order.toNat : ℕ) : ℤ) := by
    rw [hco]
    simpa [hG]
  omega

theorem fixed_line_finite_jet_vanishing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X)
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s₀ : Γ(H, ⊤)) (D₀ : X →₀ ℤ)
    (s : Γ(H, ⊤)) (i : ι) (x : X) (hx : x ∈ C.opens i)
    (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (F : PowerSeries κ) (L B : ℕ) :
    s₀ ≠ 0 → MatchesSectionOrder X H C s₀ D₀ → Order.coheight x = 1 →
    0 < L →
    completedSection X H C s i x hx κ e = scaledSeries L F →
    VanishesThrough F B →
    weightedDegree k f D₀ < (L * (B + 1) : ℕ) → s = 0 := by
  intro hs₀ hD₀ hc hL hexpand hvan hdeg
  by_contra hs
  have hq := scaled_series_has_q_order F L B hL hvan
  have hscaledne : scaledSeries L F ≠ 0 := by
    intro hz
    have hz' : completedSection X H C s i x hx κ e =
        completedSection X H C 0 i x hx κ e := by
      rw [hexpand, hz]
      simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
    exact hs ((completed_section_injective X hN H hH ι C i x hx κ e hc) hz')
  have hm := order_toNat_ge_of_q_order (scaledSeries L F) (L * (B + 1))
    hscaledne hq
  have hbound := section_fixed_degree_order_bound X k f hcurve H hH ι C s s₀ D₀ i x
    hs hs₀ hD₀ hx
  exact hs (section_zero_of_expansion_order X hN H hH ι C i x hx κ e hc s
    (scaledSeries L F) (L * (B + 1)) hexpand hscaledne hm
    (weightedDegree k f D₀) hbound (by exact_mod_cast hdeg))

theorem fixed_line_expansion_vanishing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X)
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s₀ : Γ(H, ⊤)) (D₀ : X →₀ ℤ)
    (s : Γ(H, ⊤)) (i : ι) (x : X) (hx : x ∈ C.opens i)
    (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (F : PowerSeries κ) (L B : ℕ) :
    s₀ ≠ 0 → MatchesSectionOrder X H C s₀ D₀ → Order.coheight x = 1 →
    0 < L →
    completedSection X H C s i x hx κ e = scaledSeries L F →
    VanishesThrough F B →
    weightedDegree k f D₀ < (L * (B + 1) : ℕ) → F = 0 := by
  intro hs₀ hD₀ hc hL hexpand hvan hdeg
  have hs := fixed_line_finite_jet_vanishing X k f hcurve hN H hH ι C s₀ D₀ s i x hx κ e F L B
    hs₀ hD₀ hc hL hexpand hvan hdeg
  have hz : scaledSeries L F = 0 := by
    rw [← hexpand, hs]
    simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
  exact (scaledSeries_injective L hL) (by simpa [scaledSeries, hz])

theorem unit_frame_finite_jet_vanishing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X)
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s₀ : Γ(H, ⊤)) (D₀ : X →₀ ℤ)
    (s : Γ(H, ⊤)) (i : ι) (x : X) (hx : x ∈ C.opens i)
    (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (F : PowerSeries κ) (a : (PowerSeries κ)ˣ) (L B : ℕ) :
    s₀ ≠ 0 → MatchesSectionOrder X H C s₀ D₀ → Order.coheight x = 1 →
    0 < L →
    completedSection X H C s i x hx κ e =
      (a : PowerSeries κ) * scaledSeries L F →
    VanishesThrough F B →
    weightedDegree k f D₀ < (L * (B + 1) : ℕ) → s = 0 ∧ F = 0 := by
  intro hs₀ hD₀ hc hL hexpand hvan hdeg
  have hs : s = 0 := by
    by_contra hs
    have hq := scaled_series_has_q_order F L B hL hvan
    have hscaledne : scaledSeries L F ≠ 0 := by
      intro hz
      have hz' : completedSection X H C s i x hx κ e =
          completedSection X H C 0 i x hx κ e := by
        rw [hexpand, hz]
        simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
      exact hs ((completed_section_injective X hN H hH ι C i x hx κ e hc) hz')
    have hprodne : (a : PowerSeries κ) * scaledSeries L F ≠ 0 :=
      mul_ne_zero a.ne_zero hscaledne
    have hm0 := order_toNat_ge_of_q_order (scaledSeries L F) (L * (B + 1))
      hscaledne hq
    have hm : ((L * (B + 1) : ℕ) : ℤ) ≤
        (((a : PowerSeries κ) * scaledSeries L F).order.toNat : ℤ) := by
      simpa [PowerSeries.order_mul, PowerSeries.order_zero_of_unit a.isUnit] using hm0
    have hbound := section_fixed_degree_order_bound X k f hcurve H hH ι C s s₀ D₀ i x
      hs hs₀ hD₀ hx
    exact hs (section_zero_of_expansion_order X hN H hH ι C i x hx κ e hc s
      ((a : PowerSeries κ) * scaledSeries L F) (L * (B + 1)) hexpand hprodne hm
      (weightedDegree k f D₀) hbound (by exact_mod_cast hdeg))
  refine ⟨hs, ?_⟩
  have hzprod : (a : PowerSeries κ) * scaledSeries L F = 0 := by
    rw [← hexpand, hs]
    simp [completedSection, sectionGerm, completionExpansion, sectionCoordinate]
  have hzscaled : scaledSeries L F = 0 :=
    (mul_eq_zero.mp hzprod).resolve_left a.ne_zero
  apply (scaledSeries_injective L hL)
  calc
    scaledSeries L F = 0 := hzscaled
    _ = scaledSeries L 0 := by
      ext n
      simp [scaledSeries]

end ArithmeticThetaSectionCompletion

#print axioms ArithmeticThetaSectionCompletion.fixed_line_finite_jet_vanishing
#print axioms ArithmeticThetaSectionCompletion.fixed_line_expansion_vanishing
#print axioms ArithmeticThetaSectionCompletion.unit_frame_finite_jet_vanishing
