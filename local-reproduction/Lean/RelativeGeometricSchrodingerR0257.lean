import RelativeThetaSectionsCohomologyR0257
import RelativeSchrodingerModuleR0257

/-! The geometric comparison on the actual theta sections, with no chosen frame. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeSchrodingerR0257
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256

namespace RelativeGeometricSchrodinger
open RelativePrimitiveThetaCommutator
variable {R : Type u} [CommRing R] (E : EllipticFamily R)

/-- The sheaf addition and period laws give the order law on genuine sections. -/
lemma cyclic_order (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (F : ∀ n : ℕ, Lift E m (translation E (multiple E P n)))
    (hF : CyclicSystem E m P ι F) :
    letI := sectionModule E m
    thetaAct E m (multiple E P 1) (F 1) ^ m = 1 := by
  letI := sectionModule E m
  let T (n : ℕ) : Module.End R (sections E m) := thetaAct E m (multiple E P n) (F n)
  have hadd (a b : ℕ) : T (a+b) = T a * T b := by
    obtain ⟨h, hh⟩ := hF.2.2.1 a b
    ext s
    change Sections.act _ (F (a+b)) s = Sections.act _ (F a) (Sections.act _ (F b) s)
    rw [← Sections.act_comp]
    change Sections.act _ (F (a+b)) s = Sections.act _ (compose E m _ _ (F a) (F b)) s
    rw [hh]
    exact (Sections.act_changeMap h (F (a+b)) s).symm
  have hz : T 0 = 1 := by
    haveI : IsIso (translation E (multiple E P 0)) := by
      rw [RelativeCyclicThetaSplittingR0256.translation_multiple_zero]
      infer_instance
    have hi : Function.Injective (T 0) := (Sections.act_bijective _ (F 0)).1
    ext s
    apply hi
    exact (congrArg (fun t : Module.End R (sections E m) => t s) (hadd 0 0)).symm
  have hp (n : ℕ) : T 1 ^ n = T n := by
    induction n with
    | zero => simpa only [pow_zero] using hz.symm
    | succ n ih => rw [pow_succ, ih, ← hadd]
  have hm : T m = T 0 := by
    have hperiod := hF.2.2.2 0
    rw [Nat.zero_add] at hperiod
    obtain ⟨h, hh⟩ := hperiod
    ext s
    change Sections.act _ (F m) s = Sections.act _ (F 0) s
    rw [hh]
    exact Sections.act_changeMap h (F 0) s
  exact (hp m).trans (hm.trans hz)

/-- Choose the accepted normalized cyclic lift and transport its first term. -/
lemma normalized_order [Algebra ℚ R] [IsNoetherianRing R]
    (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : P.val ≫ E.law.schemeNsmul (2*m) = zero E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    ∃ α : Lift E m (translation E P),
      MidpointNormalized E m P ι α ∧ Symmetric E m P ι α ∧
      (letI := sectionModule E m; thetaAct E m P α ^ m = 1) := by
  obtain ⟨F, hF, _⟩ := relative_cyclic_theta_splitting R E m hm he P hP ι hι
  have H : ∃ α : Lift E m (translation E (multiple E P 1)),
      MidpointNormalized E m (multiple E P 1) ι α ∧
      Symmetric E m (multiple E P 1) ι α ∧
      (letI := sectionModule E m; thetaAct E m (multiple E P 1) α ^ m = 1) :=
    ⟨F 1, (hF.1 1).1, (hF.1 1).2, cyclic_order E m P ι F hF⟩
  rw [RelativeCyclicThetaSplittingR0256.multiple_one] at H
  exact H

end RelativeGeometricSchrodinger

/-- Relative Schrodinger comparison for the normalized geometric theta lifts. -/
theorem relative_geometric_schrodinger :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) (m : ℕ),
      0 < m → Even m → ∀ M : ArithmeticThetaLegendreAtlasR0176.FamilyLevel R E (2*m),
      GeometricComparison E m M := by
  intro R _ _ _ E m hm he M
  obtain ⟨ι, hι, _⟩ := (relative_normalized_theta_inversion R E m).2
  obtain ⟨α, hα, hsα, hoα⟩ :=
    RelativeGeometricSchrodinger.normalized_order E m hm he M.x M.killed_x ι hι
  obtain ⟨β, hβ, hsβ, hoβ⟩ :=
    RelativeGeometricSchrodinger.normalized_order E m hm he M.y M.killed_y ι hι
  obtain ⟨c, ⟨hc, hp⟩, _⟩ := relative_primitive_theta_commutator R E m hm he M α β
  refine ⟨ι, α, β, c, hι, hα, hsα, hβ, hsβ, hc, hp, hoα, hoβ, ?_⟩
  letI := sectionModule E m
  exact relative_schrodinger_module R (sections E m) m hm
    (relative_theta_sections_cohomology R E m hm).1 _ _ c hoα hoβ
    (RelativePrimitiveThetaCommutator.thetaAct_relation E m M.x M.y α β c hc) hp

#print axioms relative_geometric_schrodinger
end ArithmeticThetaRelativeSchrodingerR0257
