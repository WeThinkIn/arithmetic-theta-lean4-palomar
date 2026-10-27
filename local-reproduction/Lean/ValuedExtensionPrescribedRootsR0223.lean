import ValuativeRootIntegralityR0223
import ValuativeSimultaneousSectionsR0223

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaValuativeRootsR0223
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185

namespace ValuedExtensionPrescribedRootsR0223

/-- Compatibility of rho identifies the actual generic extended disk map. -/
lemma generic_extended_disk (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra (LaurentSeries k) Ω] (A : ValuationSubring Ω)
    (ρ : PowerSeries k →+* A)
    (hρ : ∀ t : PowerSeries k, algebraMap A Ω (ρ t) =
      algebraMap (LaurentSeries k) Ω (algebraMap (PowerSeries k) (LaurentSeries k) t))
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) :
    genericInclusion Ω A ≫ extendedDisk k Ω A ρ f =
      Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) Ω)) ≫
        (ArithmeticThetaTateCuspsR0181.genericInclusion k ≫ f) := by
  have he : (algebraMap A Ω).comp ρ =
      (algebraMap (LaurentSeries k) Ω).comp
        (algebraMap (PowerSeries k) (LaurentSeries k)) := by
    ext t
    exact hρ t
  unfold genericInclusion extendedDisk ArithmeticThetaTateCuspsR0181.genericInclusion
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((algebraMap A Ω).comp ρ)) ≫ f =
    Spec.map (CommRingCat.ofHom ((algebraMap (LaurentSeries k) Ω).comp
      (algebraMap (PowerSeries k) (LaurentSeries k)))) ≫ f
  rw [he]

/-- Extending a dominant punctured disk along its specified field inclusion
preserves dominance. -/
lemma extended_disk_dominant (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra (LaurentSeries k) Ω] (A : ValuationSubring Ω)
    (ρ : PowerSeries k →+* A)
    (hρ : ∀ t : PowerSeries k, algebraMap A Ω (ρ t) =
      algebraMap (LaurentSeries k) Ω (algebraMap (PowerSeries k) (LaurentSeries k) t))
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z)
    (hf : IsDominant (ArithmeticThetaTateCuspsR0181.genericInclusion k ≫ f)) :
    IsDominant (genericInclusion Ω A ≫ extendedDisk k Ω A ρ f) := by
  rw [generic_extended_disk k Ω A ρ hρ f]
  let q := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) Ω))
  have hq : Function.Surjective q := fun y =>
    ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ y⟩
  letI : IsDominant q := ⟨hq.denseRange⟩
  letI := hf
  exact inferInstanceAs (IsDominant (q ≫
    (ArithmeticThetaTateCuspsR0181.genericInclusion k ≫ f)))

/-- The extended frame is the transport of the original frame through exactly
Spec(rho) and the pullback-composition isomorphism. -/
lemma extended_frame_isFrame (k : Type) [Field k] (Ω : Type) [Field Ω]
    (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A)
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules)
    (h : Sections (ArithmeticThetaTateCuspsR0181.Disk k)
      ((Scheme.Modules.pullback f).obj J))
    (hh : IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ h) :
    IsFrame ((Scheme.Modules.pullback (extendedDisk k Ω A ρ f)).obj J) ⊤
      (extendedFrame k Ω A ρ f J h) := by
  have ht := transport_frame (Spec.map (CommRingCat.ofHom ρ))
    ((Scheme.Modules.pullback f).obj J) _
    ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom ρ)) f).app J) h hh
  rw [transport_as_app] at ht
  exact ht

end ValuedExtensionPrescribedRootsR0223

/-- Prescribed field roots over the same extended disk and frame are realized
by integral coefficients and one smooth proper finite flat cover. -/
theorem valued_extension_prescribed_roots :
∀ (k : Type) [Field k] [CharZero k] (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (b : Quiver.Hom Z (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.IsProper b] [AlgebraicGeometry.SmoothOfRelativeDimension 1 b] (J : Z.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (K s : ℕ), 0 < K → ∀ (F : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections Z (ArithmeticThetaTensorPower.tensorPower Z J K)), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) Z), CategoryTheory.CategoryStruct.comp f b = ArithmeticThetaTateCuspsR0181.diskStructure k → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion k) f) → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (Ω : Type) [Field Ω] [Algebra (LaurentSeries k) Ω] (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A), (∀ t : PowerSeries k, algebraMap A Ω (ρ t) = algebraMap (LaurentSeries k) Ω (algebraMap (PowerSeries k) (LaurentSeries k) t)) → ∀ (r : Fin s → Ω), (∀ j, ArithmeticThetaValuativeRootsR0223.FieldEquation Ω A (ArithmeticThetaValuativeRootsR0223.extendedDisk k Ω A ρ f) J K (F j) (ArithmeticThetaValuativeRootsR0223.extendedFrame k Ω A ρ f J h) (r j)) → ∃ R : ArithmeticThetaSimultaneousUnaryR0187.RootCover k Z b (K^s), ArithmeticThetaValuativeRootsR0223.PrescribedFieldRoots k R Ω A J K s F (ArithmeticThetaValuativeRootsR0223.extendedDisk k Ω A ρ f) (ArithmeticThetaValuativeRootsR0223.extendedFrame k Ω A ρ f J h) r := by
  intro k _ _ Z _ b _ _ J hJ K s hK F hF f hf hdom h hh Ω _ _ A ρ hρ r hr
  have hh' := ValuedExtensionPrescribedRootsR0223.extended_frame_isFrame k Ω A ρ f J h hh
  have hd := ValuedExtensionPrescribedRootsR0223.extended_disk_dominant k Ω A ρ hρ f hdom
  have hi : ∀ j, ∃ a : A, algebraMap A Ω a = r j ∧
      IntegralEquation Ω A (extendedDisk k Ω A ρ f) J K (F j)
        (extendedFrame k Ω A ρ f J h) a := by
    intro j
    exact (valuative_root_integrality Ω A Z (extendedDisk k Ω A ρ f) J K hK
      (F j) (extendedFrame k Ω A ρ f J h) hh' (r j) (hr j)).exists
  choose a ha using hi
  obtain ⟨R, hR⟩ := valuative_simultaneous_sections k Z b J hJ K s hK F hF Ω A
    (extendedDisk k Ω A ρ f) hd (extendedFrame k Ω A ρ f J h) hh' a (fun j => (ha j).2)
  exact ⟨R, a, fun j => (ha j).1, hR⟩

#print axioms valued_extension_prescribed_roots
end ArithmeticThetaValuativeRootsR0223
