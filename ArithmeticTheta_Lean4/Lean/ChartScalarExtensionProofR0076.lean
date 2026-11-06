import Mathlib

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaFractionLiftBridgeR0076

/-- The fraction field of an actual parameter-localized chart carrier. -/
abbrev ChartFraction (S : Type u) [CommRing S] [IsDomain S] := FractionRing S

/-- The structural ring map from the base carrier into the localized chart. -/
def chartBaseMap {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra A S] (f : R →+* A) : R →+* S := (algebraMap A S).comp f

/-- The canonical injective fraction-field extension of the chart map. -/
theorem canonical_chart_scalar_extension
    {R A K S : Type u} [CommRing R] [CommRing A] [IsDomain A]
    [CommRing S] [IsDomain S] [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra A S] (t : R) (f : R →+* A)
    (ht : f t ≠ 0) (hf : Function.Injective f)
    [IsLocalization.Away (f t) S]
    (hstruct : Function.Injective ((algebraMap A S).comp f)) :
    ∃! F : K →+* ChartFraction S,
      Function.Injective F ∧
        ∀ a : R,
          F (algebraMap R K a) =
            algebraMap S (ChartFraction S) (chartBaseMap f a) := by
  let g : R →+* ChartFraction S :=
    (algebraMap S (ChartFraction S)).comp (chartBaseMap f)
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (ChartFraction S)).comp hstruct
  let F : K →+* ChartFraction S :=
    IsFractionRing.lift (K := K) (g := g) hg
  have hF : Function.Injective F := F.injective
  have hbase : ∀ a : R, F (algebraMap R K a) = g a := by
    intro a
    exact IsFractionRing.lift_algebraMap hg a
  have hext : ∀ a : R,
      F (algebraMap R K a) =
        algebraMap S (ChartFraction S) (chartBaseMap f a) := by
    intro a
    exact hbase a
  refine ⟨F, ⟨hF, hext⟩, ?_⟩
  intro G hG
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  apply RingHom.ext
  intro a
  calc
    (G.comp (algebraMap R K)) a =
        algebraMap S (ChartFraction S) (chartBaseMap f a) := hG.2 a
    _ = (F.comp (algebraMap R K)) a := (hext a).symm

end ArithmeticThetaFractionLiftBridgeR0076
