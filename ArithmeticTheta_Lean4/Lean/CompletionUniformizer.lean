import SectionCompletionDefinitions
import LocalExpansionOrder
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Inverse

universe u w
noncomputable section
namespace ArithmeticThetaSectionCompletion

/-- A uniformizer of the DVR remains a uniformizer after passing to the
maximal-ideal completion.  The chosen coordinate identifies that completed
uniformizer with a unit multiple of the power-series parameter. -/
theorem completion_uniformizer_order
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (κ : Type w) [Field κ]
    (e : completedLocalRing R ≃+* PowerSeries κ) (π : R)
    (hπ : Irreducible π) :
    (completionExpansion R κ e π).order = 1 := by
  let q : completedLocalRing R := algebraMap R (completedLocalRing R) π
  letI : IsDomain (completedLocalRing R) := e.toMulEquiv.isDomain (PowerSeries κ)
  letI : IsDiscreteValuationRing (completedLocalRing R) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  have hmax : IsLocalRing.maximalIdeal (completedLocalRing R) =
      Ideal.map (algebraMap R (completedLocalRing R)) (IsLocalRing.maximalIdeal R) := by
    exact AdicCompletion.maximalIdeal_eq_map_of_fg
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have hmapspan : Ideal.map (algebraMap R (completedLocalRing R))
      (IsLocalRing.maximalIdeal R) =
      Ideal.span ({q} : Set (completedLocalRing R)) := by
    calc
      Ideal.map (algebraMap R (completedLocalRing R)) (IsLocalRing.maximalIdeal R) =
          Ideal.map (algebraMap R (completedLocalRing R)) (Ideal.span ({π} : Set R)) :=
        congrArg (Ideal.map (algebraMap R (completedLocalRing R))) hπ.maximalIdeal_eq
      _ = Ideal.span ({q} : Set (completedLocalRing R)) := by
        rw [Ideal.map_span]
        simp [q]
  have hqspan : IsLocalRing.maximalIdeal (completedLocalRing R) =
      Ideal.span ({q} : Set (completedLocalRing R)) := hmax.trans hmapspan
  have hq : Irreducible q :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer q).2 hqspan
  have hy : Irreducible (e q) := hq.map e
  have hyspan : IsLocalRing.maximalIdeal (PowerSeries κ) =
      Ideal.span ({e q} : Set (PowerSeries κ)) := hy.maximalIdeal_eq
  have hassoc : Associated (e q) (PowerSeries.X : PowerSeries κ) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    exact hyspan.symm.trans PowerSeries.maximalIdeal_eq_span_X
  rcases hassoc with ⟨u, hu⟩
  have horder := congrArg PowerSeries.order hu
  simpa [completionExpansion, q, PowerSeries.order_mul,
    PowerSeries.order_zero_of_unit u.isUnit] using horder

/-- The canonical completion-coordinate expansion is injective. -/
theorem completion_expansion_injective
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (κ : Type w) [Field κ]
    (e : completedLocalRing R ≃+* PowerSeries κ) :
    Function.Injective (completionExpansion R κ e) := by
  have hq : Irreducible (Classical.choose (IsDiscreteValuationRing.exists_irreducible R)) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible R)
  have horder : (completionExpansion R κ e
      (Classical.choose (IsDiscreteValuationRing.exists_irreducible R))).order = 1 :=
    completion_uniformizer_order R κ e _ hq
  exact ArithmeticThetaFormalOrder.expansion_injective R κ
    (completionExpansion R κ e)
    (Classical.choose (IsDiscreteValuationRing.exists_irreducible R)) hq horder

end ArithmeticThetaSectionCompletion
