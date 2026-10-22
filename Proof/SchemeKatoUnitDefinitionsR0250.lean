module

public import ArbitraryKatoUnitNaturalityR0249
public import ArbitraryKatoCartierDivisorR0249
public import SchemeDiscriminantExistenceR0244
public import SchemeDiscriminantDefinitionsR0244
public import ArbitraryKatoUnitDefinitionsR0249

@[expose] public section

/-! Units on the actual torsion complement of an arbitrary elliptic family.
The test normalization uses accepted affine Kato units, with actual maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoUnitR0250
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244

variable {S : Scheme.{u}} (E : Family S)

/-- Multiplication evaluated on the identity point of the represented functor. -/
def multiplication (n : ℕ) : E.curve ⟶ E.curve :=
  (ArithmeticThetaSchemeLevelR0204.multiple E E.p n
    ⟨𝟙 E.curve, Category.id_comp E.p⟩).val

def identityIdeal : E.curve.IdealSheafData := E.zero.ker

def torsionIdeal (c : ℕ) : E.curve.IdealSheafData :=
  (identityIdeal E).comap (multiplication E c)

def complement (c : ℕ) : E.curve.Opens := (torsionIdeal E c).support.compl

abbrev UnitSection (c : ℕ) :=
  (E.curve.presheaf.obj (Opposite.op (complement E c)))ˣ

/-- Test every affine equation and every pointed Cartesian comparison, including
nonflat and nonreduced tests. Neither existence nor uniqueness is assumed. -/
def IsKatoUnit (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (c : ℕ) (v : UnitSection E c) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    (b : Base R ⟶ S), b ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    ∀ C : Comparison E (weierstrassFamily R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      ∃ w : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection R W G c,
        ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit R W G c w ∧
        ∃ e : ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c ≤
            C.map ⁻¹ᵁ complement E c,
          (w : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj
            (Opposite.op (ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c))) =
            C.map.appLE _ _ e (v : _)

/-- Exact Cartier divisor, stated without a function field on the base or curve.
The correcting unit is on the entire affine open, not only its complement. -/
def HasCartierDivisor (c : ℕ) (v : UnitSection E c) : Prop :=
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (identityIdeal E) ∧
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (torsionIdeal E c) ∧
  ∀ (U : E.curve.affineOpens)
    (a b : E.curve.presheaf.obj (Opposite.op U.1)),
    IsRegular a → IsRegular b →
    (identityIdeal E).ideal U = Ideal.span ({a} : Set _) →
    (torsionIdeal E c).ideal U = Ideal.span ({b} : Set _) →
    ∃ ε : (E.curve.presheaf.obj (Opposite.op U.1))ˣ,
      ArithmeticThetaArbitraryKatoUnitR0249.restrict (complement E c)
          (U.1 ⊓ complement E c) inf_le_right (v : _) *
        ArithmeticThetaArbitraryKatoUnitR0249.restrict U.1
          (U.1 ⊓ complement E c) inf_le_left b =
      ArithmeticThetaArbitraryKatoUnitR0249.restrict U.1
        (U.1 ⊓ complement E c) inf_le_left ((ε : _) * a ^ (c ^ 2))

end ArithmeticThetaSchemeKatoUnitR0250
