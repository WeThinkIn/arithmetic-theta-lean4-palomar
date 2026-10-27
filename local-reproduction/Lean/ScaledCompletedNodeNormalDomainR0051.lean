import ScaledCompletedSplitLawsR0051
import SplitNormalDescentR0051

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050

open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaNodeCharts
open ArithmeticThetaScaledNormalRecoveryR0051

/-- Normality of the completed scaled node, obtained by the concrete split into
the accepted unit-thickness completed node.  The singular cases `r > 1` are
handled by descent and are not treated as regular rings. -/
theorem completed_node_normal_domain :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      IsDomain (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r) ∧
      IsIntegrallyClosed (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r) := by
  intro k _ _ r hr
  obtain ⟨f, p, hsplit⟩ := algebraic_split_exists k r hr
  obtain ⟨F, hF⟩ := ring_extension_exists k r hr f hsplit.2.2.2.2.2.1
  obtain ⟨P, hP⟩ := additive_extension_exists k r hr p hsplit.2.2.2.2.2.2.1
  have hcompleted := completed_split_laws k r hr f p F P hsplit hF hP
  have hunit := ArithmeticThetaAnnularGeometry.completed_node_normal_domain k
  letI : IsDomain (ArithmeticThetaNodeCharts.CompletedNode k) := hunit.2.1
  letI : IsIntegrallyClosed (ArithmeticThetaNodeCharts.CompletedNode k) := hunit.2.2.1
  exact normal_domain_of_split
    (ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r)
    (ArithmeticThetaNodeCharts.CompletedNode k) F P hcompleted.1 hcompleted.2

end ArithmeticThetaScaledAnnularR0050
