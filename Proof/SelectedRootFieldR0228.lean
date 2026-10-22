module

public import FramedRootCoefficientR0228
public import KummerDegree
public import AmbientCompletedRootsDefinitionsR0227

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaAmbientCompletedRootsR0227
open AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Sections)
open ArithmeticThetaTensorPower (tensorPower)
open ArithmeticThetaRelativeDiscriminantR0171 (IsFrame)
open ArithmeticThetaAlgebraicBranchesR0226 (Equation seriesMap)

/-- The prescribed roots generate a finite field of the stated degree, and
satisfy the original full section equations over this exact field. -/
theorem selected_root_field :
    ∀ (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E]
      (Z : AlgebraicGeometry.Scheme.{0})
      (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z)
      (J : Z.Modules) (n s : ℕ), 0 < n →
      ∀ (F : Fin s → Sections (tensorPower Z J n))
        (h : Sections ((Scheme.Modules.pullback f).obj J)),
      IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ h →
      ∀ (r : Fin s → E), (∀ j, Equation f J n (F j) h (r j)) →
      FiniteDimensional (LaurentSeries k) (selectedField k E s r) ∧
      Module.finrank (LaurentSeries k) (selectedField k E s r) ≤ n ^ s ∧
      ∃ r0 : Fin s → selectedField k E s r,
        (∀ j, (selectedField k E s r).subtype (r0 j) = r j) ∧
        ∀ j, Equation f J n (F j) h (r0 j) := by
  intro k E _ _ _ Z f J n s hn F h hh r hr
  classical
  have hc := fun j => (framed_root_coefficient k Z f J n (F j) h hh).exists
  choose a ha using hc
  have he : ∀ j, r j ^ n = algebraMap (LaurentSeries k) E
      (algebraMap (PowerSeries k) (LaurentSeries k) (a j)) := by
    intro j
    exact (ha j).2 E (r j) |>.mp (hr j)
  obtain ⟨hfinite, hdegree⟩ := ArithmeticThetaKummer.family_root_degree
    (LaurentSeries k) E n s hn r
    (fun j => algebraMap (PowerSeries k) (LaurentSeries k) (a j)) he
  refine ⟨hfinite, hdegree, ?_⟩
  let r0 : Fin s → selectedField k E s r := fun j =>
    ⟨r j, IntermediateField.subset_adjoin (LaurentSeries k) (Set.range r) (Set.mem_range_self j)⟩
  refine ⟨r0, fun j => rfl, ?_⟩
  intro j
  apply ((ha j).2 (selectedField k E s r) (r0 j)).mpr
  apply (selectedField k E s r).subtype.injective
  rw [map_pow]
  change r j ^ n = (selectedField k E s r).subtype
    (algebraMap (LaurentSeries k) (selectedField k E s r)
      (algebraMap (PowerSeries k) (LaurentSeries k) (a j)))
  exact he j

#print axioms selected_root_field
end ArithmeticThetaAmbientCompletedRootsR0227
