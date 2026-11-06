import RelativeRootTestFiberR0196

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSquareLinesR0192

/-- Every square-root test fiber of a finite étale surjective level is finite
étale surjective, with twice the pointwise rank of the original level map. -/
theorem finite_metaplectic_test_level
    (B Y : Scheme.{0}) (W : B.Modules) (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W))
    (h2 : IsUnit (2 : B.presheaf.obj (Opposite.op ⊤)))
    (hfin : IsFinite p) (het : Etale p) (hsur : Surjective p) :
    FiniteRootLevel p H := by
  letI := hfin
  letI := het
  letI := hsur
  intro T R
  obtain ⟨F, hrep, hpair⟩ := relative_root_test_fiber B Y W p H h2 T R
  obtain ⟨a, haY, haT, hafin, haet, hasur, harank⟩ := hpair
  letI := hafin
  letI := haet
  letI := hasur
  refine ⟨F, hrep, ⟨a, haY, haT, hafin, haet, hasur, harank⟩, ?_⟩
  rw [← haT]
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro t
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const a (Limits.pullback.snd p R.map)
    2 harank, Scheme.Hom.finrank_pullback_snd]

#print axioms finite_metaplectic_test_level
end ArithmeticThetaMetaplecticTestsR0196
