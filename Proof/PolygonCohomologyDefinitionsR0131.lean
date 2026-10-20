module

public import ProperFlatPolygonTowerR0130
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-! Concrete finite-stage Cech maps and marked sections. No geometric existence,
exactness, regularity, or algebraization conclusion is stored as an input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

variable (k : Type u) [Field k] [CharZero k]

def LaurentPresentation (n : ℕ)
    (L : B k n true ≃+* LaurentPolynomial (R k n)) : Prop :=
  L.toRingHom.comp ((restriction k n true).comp (base k n)) =
    LaurentPolynomial.C ∧
  L (restriction k n true (coordX k n)) = LaurentPolynomial.T 1

def difference (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (a : Fin r → A k n) : Fin r → B k n true :=
  fun i => E (restriction k n false (a i)) -
    restriction k n true (a (next r hr i))

def constants (r n : ℕ) (c : R k n) : Fin r → A k n :=
  fun _ => base k n c

def residue (r n : ℕ) (L : B k n true ≃+* LaurentPolynomial (R k n))
    (b : Fin r → B k n true) : R k n :=
  ∑ i : Fin r, (L (b i)).coeff 0

def globalBase (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E) :
    R k n →+* D.X.presheaf.obj (Opposite.op ⊤) :=
  D.p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv.hom

def markedUnit (n : ℕ) (a : kˣ) : (R k n)ˣ :=
  Units.map ((trunc (PowerSeries k) PowerSeries.X n).comp PowerSeries.C) a

def markedPoint (n : ℕ) (a : kˣ) : A k n →+* R k n :=
  mkPoint (RingHom.id (R k n)) (markedUnit k n a : R k n)
    (parameter k n * ↑((markedUnit k n a)⁻¹)) (by
      simp [mul_left_comm])

def markedEquation (n : ℕ) (a : kˣ) : A k n :=
  coordX k n - base k n (markedUnit k n a : R k n)

def markedSection (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (i : Fin r) (a : kˣ) : specR k n ⟶ D.X :=
  Spec.map (CommRingCat.ofHom (markedPoint k n a)) ≫ D.chart i

end ArithmeticThetaPolygonCohomologyR0131
