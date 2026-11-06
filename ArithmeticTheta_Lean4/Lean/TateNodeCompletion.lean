import TateNodeNormalForm
import TateNodeFiniteType
import NoetherianAdicCompletion

/-! The canonical completion of the algebraic node: separatedness, Noetherianity,
base flatness, and regularity of the actual structural parameter. -/

set_option autoImplicit false
universe u

namespace ArithmeticThetaNodeCharts

/-- The completion map is an embedding, and the completed node is Noetherian
and flat over the power-series base. Its structural parameter stays nonzero
and acts injectively. No domain or faithful-flatness claim is made here. -/
theorem node_completion_embedding_flat :
    ∀ (k : Type u) [Field k] [CharZero k],
      Function.Injective (ArithmeticThetaNodeCharts.toCompleted k) ∧
      IsNoetherianRing (ArithmeticThetaNodeCharts.CompletedNode k) ∧
      Module.Flat (ArithmeticThetaNodeCharts.Base k)
        (ArithmeticThetaNodeCharts.CompletedNode k) ∧
      ArithmeticThetaNodeCharts.toCompleted k (ArithmeticThetaNodeCharts.t k) ≠ 0 ∧
      Function.Injective (fun a : ArithmeticThetaNodeCharts.CompletedNode k =>
        ArithmeticThetaNodeCharts.toCompleted k (ArithmeticThetaNodeCharts.t k) * a) := by
  intro k _ _
  obtain ⟨hdom, hflat, ht, hnu, _⟩ := node_flat_domain_parameter k
  let : IsDomain (Node k) := hdom
  let : Module.Flat (Base k) (Node k) := hflat
  let : IsNoetherianRing (Node k) := (node_noetherian_finite_type k).1
  have hproper : nodeIdeal k ≠ ⊤ := by
    simpa [nodeIdeal, Ideal.span_singleton_eq_top] using hnu
  let : IsHausdorff (nodeIdeal k) (Node k) :=
    IsHausdorff.of_isDomain (nodeIdeal k) hproper
  have hinj : Function.Injective (toCompleted k) :=
    AdicCompletion.of_injective (nodeIdeal k) (Node k)
  have hnoeth : IsNoetherianRing (CompletedNode k) :=
    ArithmeticThetaFractionalCharts.noetherian_adic_completion (Node k) (nodeIdeal k)
  have hbase : Module.Flat (Base k) (CompletedNode k) :=
    Module.Flat.trans (Base k) (Node k) (CompletedNode k)
  refine ⟨hinj, hnoeth, hbase, ?_, ?_⟩
  · exact fun h => ht (hinj (h.trans (map_zero (toCompleted k)).symm))
  · simpa only [Algebra.smul_def, toCompleted] using
      (smul_right_injective (M := CompletedNode k) ht)

end ArithmeticThetaNodeCharts
