module
public import RelativeKatoDefinitionsR0169
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PalomarZero694
/-- The homogeneous coordinate map of the zero section is uniquely specified by
evaluation at the projective point [0:1:0], on every polynomial representative. -/
theorem normalized_iff_original (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (q : ProjModelRingCR W.toProjective →+* R) :
    (∀ p : MvPolynomial (Fin 3) R,
      q (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal p) =
        MvPolynomial.eval ![(0 : R), 1, 0] p) ↔
      q = kwYEvalRingHom R W := by
  constructor
  · intro h
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact h p
  · rintro rfl
    intro p
    rfl
end PalomarZero694
