import LocalizedRingModuleNaturality
import LocalizedModuleFamilyConstant

open AlgebraicGeometry CategoryTheory
open ArithmeticThetaCompletedCharts
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaFormalConstants

/-- The comparison takes an actual structural numerator to its completed
global restriction. -/
lemma localized_structural_numerator (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) (t : R)
    (e : CompletionEquivalences R X f t) (he : MatchesCompletion R X f t e)
    (ell : LocalizedEquivalences R X f t) (hell : MatchesLocalization R X f t e ell)
    (U : X.Opens) (r : R) :
    ell U (localizedOf R X f t U (ringOf R X f t U (structuralMap R X f U r))) =
      toLocalized R X f t U (globalToCompleted R X f t U (structuralMap R X f ⊤ r)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
  rw [hell, he]
  congr 1
  change AdicCompletion.of _ _ (structuralMap R X f U r) =
    AdicCompletion.of _ _ ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
      (structuralMap R X f ⊤ r))
  congr 1
  exact ((Scheme.TwoAffineOpenCover.restrictAlgHom f (show U ≤ ⊤ from le_top)).commutes r).symm

/-- Multiplication by the localized structural parameter is the prescribed
base scalar action, including on empty opens. -/
lemma localized_parameter_pow_smul (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) (t : R) (U : X.Opens)
    (n : ℕ) (z : LocalizedRing R X f t U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    (localizedOf R X f t U (ringParameter R X f t U)) ^ n * z = t ^ n • z := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  rw [Algebra.smul_def, map_pow]
  congr 2

/-- The precise ring and module numerator predicates agree through the
constructed comparison; the Laurent-field equation is preserved verbatim. -/
lemma ring_laurent_constant_iff (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))
    (e : CompletionEquivalences (PowerSeries k) X f PowerSeries.X)
    (he : MatchesCompletion (PowerSeries k) X f PowerSeries.X e)
    (ell : LocalizedEquivalences (PowerSeries k) X f PowerSeries.X)
    (hell : MatchesLocalization (PowerSeries k) X f PowerSeries.X e ell)
    (C : X.OrderedAffineCover) (z : RingFamily (PowerSeries k) X f PowerSeries.X C)
    (c : LaurentSeries k) :
    IsRingLaurentConstant k X f C z c ↔
      IsLaurentConstant k X f C (fun i => ell (C.U i) (z i)) c := by
  constructor
  · rintro ⟨n, r, hc, h⟩
    refine ⟨n, r, hc, fun i => ?_⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (C.U i)
    have hi := congrArg (ell (C.U i)) (h i)
    rw [localized_structural_numerator _ _ _ _ e he ell hell,
      localized_parameter_pow_smul, map_smul] at hi
    exact hi
  · rintro ⟨n, r, hc, h⟩
    refine ⟨n, r, hc, fun i => ?_⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (C.U i)
    apply (ell (C.U i)).injective
    rw [localized_structural_numerator _ _ _ _ e he ell hell,
      localized_parameter_pow_smul, map_smul]
    exact h i

/-- Every compatible family in the actual localized completed coordinate rings
has a unique structural Laurent scalar. The overlap extensions are instantiated
before the compatibility hypothesis is used. -/
theorem localized_ring_family_constant
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))
    [Flat f] [IsProper f] [Smooth (genericStructure k X f)]
    [GeometricallyConnected (genericStructure k X f)]
    (C : X.OrderedAffineCover)
    (z : RingFamily (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C)
    (hz : RingCompatible (PowerSeries k) X f (PowerSeries.X : PowerSeries k) C z) :
    ∃! c : LaurentSeries k, IsRingLaurentConstant k X f C z c := by
  obtain ⟨e, he, _⟩ := completed_ring_module_comparison (PowerSeries k) X f PowerSeries.X
  obtain ⟨ell, ⟨hell, hmaps⟩, _⟩ :=
    localized_ring_module_naturality (PowerSeries k) X f PowerSeries.X e he
  let w : LocalizedFamily (PowerSeries k) X f PowerSeries.X C := fun i => ell (C.U i) (z i)
  have hw : LocalizedCompatible (PowerSeries k) X f PowerSeries.X C w := by
    intro i j
    obtain ⟨phi, ⟨hphi, psi, ⟨hpsi, hsquare⟩, _⟩, _⟩ :=
      hmaps (C.U i) (C.U i ⊓ C.U j) inf_le_left
    obtain ⟨phi', ⟨hphi', psi', ⟨hpsi', hsquare'⟩, _⟩, _⟩ :=
      hmaps (C.U j) (C.U i ⊓ C.U j) inf_le_right
    exact (hsquare (z i)).symm.trans
      ((congrArg (ell (C.U i ⊓ C.U j))
        (hz i j phi phi' psi psi' hphi hphi' hpsi hpsi')).trans (hsquare' (z j)))
  obtain ⟨c, hc, hu⟩ := localized_module_family_constant k X f C w hw
  have hiff := ring_laurent_constant_iff k X f e he ell hell C z
  exact ⟨c, (hiff c).mpr hc, fun d hd => hu d ((hiff d).mp hd)⟩

#print axioms localized_ring_family_constant
end ArithmeticThetaFormalConstants
