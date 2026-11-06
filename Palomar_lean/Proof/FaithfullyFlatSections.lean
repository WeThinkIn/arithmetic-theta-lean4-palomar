module

public import ConstantDescentDefinitions
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ArithmeticThetaConstantDescent

/-- Pullback along a flat surjection is faithful on actual global functions. -/
theorem flat_surjective_global_sections_injective
    (X Y : Scheme.{u}) (f : X ⟶ Y) [Flat f] [Surjective f] :
    Function.Injective f.appTop.hom := by
  have : Epi f := Flat.epi_of_flat_of_surjective f
  let e := fun (Z : Scheme.{u}) =>
    @AffineSpace.toSpecMvPolyIntEquiv (PUnit.{u + 1}) Z
  intro s t h
  have he : f ≫ (e Y).symm (fun _ => s) = f ≫ (e Y).symm (fun _ => t) := by
    apply (e X).injective
    funext i
    simpa only [e, AffineSpace.toSpecMvPolyIntEquiv_comp,
      Equiv.apply_symm_apply] using h
  have he' := (cancel_epi f).mp he
  have hv := congrArg (fun g => e Y g PUnit.unit) he'
  simpa only [Equiv.apply_symm_apply] using hv

/-- The actual global-section equalizer for a single fpqc covering morphism. -/
theorem fpqc_global_sections_equalizer
    (X Y : Scheme.{u}) (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] (s : X.presheaf.obj (Opposite.op ⊤)) :
    leftOverlapMap X Y f s = rightOverlapMap X Y f s ↔
      ∃! t : Y.presheaf.obj (Opposite.op ⊤), f.appTop.hom t = s := by
  let e := fun (Z : Scheme.{u}) =>
    @AffineSpace.toSpecMvPolyIntEquiv (PUnit.{u + 1}) Z
  constructor
  · intro hs
    let g := (e X).symm (fun _ => s)
    have hg : pullback.fst f f ≫ g = pullback.snd f f ≫ g := by
      apply (e (pullback f f)).injective
      funext i
      simpa only [e, g, AffineSpace.toSpecMvPolyIntEquiv_comp,
        Equiv.apply_symm_apply] using hs
    obtain ⟨k, hk⟩ := (regularEpiOfEffectiveEpi f).desc' g hg
    refine ⟨e Y k PUnit.unit, ?_, ?_⟩
    · have hv := congrArg (fun q => e X q PUnit.unit) hk
      simpa only [e, g, AffineSpace.toSpecMvPolyIntEquiv_comp,
        Equiv.apply_symm_apply] using hv
    · intro t ht
      apply flat_surjective_global_sections_injective X Y f
      have hv := congrArg (fun q => e X q PUnit.unit) hk
      have ht' : f.appTop.hom (e Y k PUnit.unit) = s := by
        simpa only [e, g, AffineSpace.toSpecMvPolyIntEquiv_comp,
          Equiv.apply_symm_apply] using hv
      exact ht.trans ht'.symm
  · rintro ⟨t, ht, _⟩
    rw [← ht]
    change (pullback.fst f f).appTop (f.appTop t) =
      (pullback.snd f f).appTop (f.appTop t)
    change (pullback.fst f f ≫ f).appTop t = (pullback.snd f f ≫ f).appTop t
    rw [pullback.condition]

end ArithmeticThetaConstantDescent
