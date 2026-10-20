module

public import PolygonCohomologyDefinitionsR0131

@[expose] public section

/-! The coordinate-normalized Laurent presentation of the actual truncated x-open. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
namespace TruncatedLaurentPresentationR0131
open ArithmeticThetaInfinitesimalPolygonR0129

private lemma laurent_hom_ext {S T : Type*} [CommRing S] [CommRing T]
    {f g : LaurentPolynomial S →+* T}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

private def xUnit : (B k n true)ˣ :=
  Units.map (trunc (RawOpen k true) (openParameter k true) n)
    (ArithmeticThetaIndexedOverlapsR0058.xUnit k 0)

omit [CharZero k] in
private lemma xUnit_val : (xUnit k n : B k n true) =
    restriction k n true (coordX k n) := by
  change trunc _ _ n (ArithmeticThetaIndexedOverlapsR0058.xUnit k 0 : RawOpen k true) = _
  rw [show (ArithmeticThetaIndexedOverlapsR0058.xUnit k 0 : RawOpen k true) =
      algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k true)
        (ArithmeticThetaNodeCharts.x k) from IsUnit.unit_spec _]
  rfl

/-- Base coefficients and the invertible x coordinate determine maps from the actual open. -/
private lemma open_hom_ext {S : Type u} [CommRing S] {f g : B k n true →+* S}
    (hb : f.comp ((restriction k n true).comp (base k n)) =
      g.comp ((restriction k n true).comp (base k n)))
    (hx : f (restriction k n true (coordX k n)) =
      g (restriction k n true (coordX k n))) : f = g := by
  have hp : f.comp (restriction k n true) = g.comp (restriction k n true) := by
    apply point_ext
    · exact hb
    · exact hx
    · have hu : IsUnit (f (restriction k n true (coordX k n))) := by
        rw [← xUnit_val]
        exact (xUnit k n).isUnit.map f
      apply hu.mul_left_cancel
      calc
        f (restriction k n true (coordX k n)) * f (restriction k n true (coordY k n)) =
            f (restriction k n true (base k n (parameter k n))) := by
          rw [← map_mul, ← map_mul, coordX_mul_coordY]
        _ = g (restriction k n true (base k n (parameter k n))) :=
          RingHom.congr_fun hb (parameter k n)
        _ = g (restriction k n true (coordX k n)) *
            g (restriction k n true (coordY k n)) := by
          rw [← map_mul, ← map_mul, coordX_mul_coordY]
        _ = f (restriction k n true (coordX k n)) *
            g (restriction k n true (coordY k n)) := by rw [hx]
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k true))
  apply RingHom.ext
  intro a
  exact RingHom.congr_fun hp (trunc _ (ArithmeticThetaNodeCharts.t k) n a)

private def forward : B k n true →+* LaurentPolynomial (R k n) :=
  openPoint (mkPoint LaurentPolynomial.C (LaurentPolynomial.T 1)
    (LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T (-1)) (by
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      simp)) true (by simp; exact LaurentPolynomial.isUnit_T 1)

private lemma forward_base :
    (forward k n).comp ((restriction k n true).comp (base k n)) =
      LaurentPolynomial.C := by
  unfold forward
  rw [← RingHom.comp_assoc, openPoint_restriction, mkPoint_base]

private lemma forward_base_apply (a : R k n) :
    forward k n (restriction k n true (base k n a)) = LaurentPolynomial.C a :=
  RingHom.congr_fun (forward_base k n) a

private lemma forward_x : forward k n (restriction k n true (coordX k n)) =
    LaurentPolynomial.T 1 := by
  have h := RingHom.congr_fun (openPoint_restriction
    (mkPoint LaurentPolynomial.C (LaurentPolynomial.T 1)
      (LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T (-1)) (by
        rw [mul_left_comm, ← LaurentPolynomial.T_add]; simp)) true
      (by simp; exact LaurentPolynomial.isUnit_T 1)) (coordX k n)
  simpa only [forward, RingHom.comp_apply, mkPoint_x] using h

private def backward : LaurentPolynomial (R k n) →+* B k n true :=
  LaurentPolynomial.eval₂ ((restriction k n true).comp (base k n)) (xUnit k n)

omit [CharZero k] in
private lemma backward_C (a : R k n) :
    backward k n (LaurentPolynomial.C a) = restriction k n true (base k n a) :=
  LaurentPolynomial.eval₂_C _ _ _

private lemma backward_T : backward k n (LaurentPolynomial.T 1) =
    restriction k n true (coordX k n) := by
  simpa [backward] using xUnit_val k n

private lemma backward_forward : (backward k n).comp (forward k n) =
    RingHom.id (B k n true) := by
  apply open_hom_ext k n
  · apply RingHom.ext
    intro a
    change backward k n (forward k n (restriction k n true (base k n a))) = _
    rw [forward_base_apply, backward_C]
    rfl
  · change backward k n (forward k n (restriction k n true (coordX k n))) = _
    rw [forward_x, backward_T]
    rfl

private lemma forward_backward : (forward k n).comp (backward k n) =
    RingHom.id (LaurentPolynomial (R k n)) := by
  apply laurent_hom_ext
  · intro a
    change forward k n (backward k n (LaurentPolynomial.C a)) = _
    rw [backward_C, forward_base_apply]
    rfl
  · change forward k n (backward k n (LaurentPolynomial.T 1)) = _
    rw [backward_T, forward_x]
    rfl

private def presentation : B k n true ≃+* LaurentPolynomial (R k n) :=
  { forward k n with
    invFun := backward k n
    left_inv := fun a => RingHom.congr_fun (backward_forward k n) a
    right_inv := fun a => RingHom.congr_fun (forward_backward k n) a }

end TruncatedLaurentPresentationR0131

open ArithmeticThetaInfinitesimalPolygonR0129 TruncatedLaurentPresentationR0131

/-- The unique presentation preserving the actual structural base map and x coordinate. -/
theorem truncated_laurent_presentation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ n : ℕ,
      ∃! L : B k n true ≃+* LaurentPolynomial (R k n), LaurentPresentation k n L := by
  intro k _ _ n
  refine ⟨presentation k n, ⟨forward_base k n, forward_x k n⟩, ?_⟩
  intro L hL
  apply RingEquiv.toRingHom_injective
  apply open_hom_ext k n
  · exact hL.1.trans (forward_base k n).symm
  · exact hL.2.trans (forward_x k n).symm

end ArithmeticThetaPolygonCohomologyR0131
