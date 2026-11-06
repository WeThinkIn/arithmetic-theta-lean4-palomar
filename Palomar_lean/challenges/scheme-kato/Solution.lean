module
public import Mathlib
public import SchemeKatoUnitNaturalityR0250
public import SchemeKatoIntrinsicCharacterizationR0254
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaPalomarWeierstrass373
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
theorem projectiveGeometry (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    IsProper (structureMap R W) ∧ SmoothOfRelativeDimension 1 (structureMap R W) ∧
      GeometricallyConnected (structureMap R W) := by
  refine ⟨WeierstrassProjModel.projModelStrCR_isProper W.toProjective,
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective, ?_⟩
  letI : GeometricallyIntegral (structureMap R W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  exact GeometricallyIrreducible.geometricallyConnected (structureMap R W)
def family (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) : Family (ArithmeticThetaLocalWeierstrassR0203.Base R) where
  curve := Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul
           mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel
           mul_natural := G.mul_natural, mul_comm := hG.2 }
  proper := (projectiveGeometry R W).1
  dimension := (projectiveGeometry R W).2.1
  connected := (projectiveGeometry R W).2.2

end ArithmeticThetaPalomarWeierstrass373
namespace ArithmeticThetaPalomarNormalized394
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (G : Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
variable [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
def Normalized (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G c g ∧ ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)
end ArithmeticThetaPalomarNormalized394
namespace ArithmeticThetaPalomarAffineKato394
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaPalomarNormalized394
open ArithmeticThetaArbitraryDiscriminantR0243

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

def identityIdeal : (Curve R W).IdealSheafData := (origin R W).ker
def torsionIdeal (c : ℕ) : (Curve R W).IdealSheafData :=
  (identityIdeal R W).comap (G.schemeNsmul c)
def complement (c : ℕ) : (Curve R W).Opens :=
  (torsionIdeal R W G c).support.compl
abbrev UnitSection (c : ℕ) :=
  ((Curve R W).presheaf.obj (Opposite.op (complement R W G c)))ˣ

def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : X.presheaf.obj (Opposite.op U)) : X.presheaf.obj (Opposite.op V) :=
  X.presheaf.map (homOfLE h).op a

variable [Algebra ℚ R]

/-- The value is pulled through M's specific pointed Cartesian map. Existence
of a normalized source representative and of the inclusion is required in the
conclusion, not postulated as target geometric data. -/
def FromModel (M : NormalModel R W) (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∃ hU : Nonempty (complement M.ring M.equation M.law c),
  ∃ g : (Curve M.ring M.equation).functionField,
    Normalized M.ring M.equation M.law c g ∧
    ∃ a : (Curve M.ring M.equation).presheaf.obj
        (Opposite.op (complement M.ring M.equation M.law c)),
      IsUnit a ∧
      @Scheme.germToFunctionField (Curve M.ring M.equation) _
        (complement M.ring M.equation M.law c) hU a = g ∧
      ∃ e : complement R W G c ≤
          M.comparison.map ⁻¹ᵁ complement M.ring M.equation M.law c,
        (v : _) = M.comparison.map.appLE _ _ e a

/-- Normal-source normalization is tested against every actual model. The
accepted normal_discriminant_model supplies models for every elliptic target. -/
def IsKatoUnit (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∀ M : NormalModel R W, FromModel R W G M c v

end ArithmeticThetaPalomarAffineKato394
namespace ArithmeticThetaPalomarSchemeKato394
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
    ∀ C : Comparison E (ArithmeticThetaPalomarWeierstrass373.family R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      ∃ w : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c,
        ArithmeticThetaPalomarAffineKato394.IsKatoUnit R W G c w ∧
        ∃ e : ArithmeticThetaPalomarAffineKato394.complement R W G c ≤
            C.map ⁻¹ᵁ complement E c,
          (w : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj
            (Opposite.op (ArithmeticThetaPalomarAffineKato394.complement R W G c))) =
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
      ArithmeticThetaPalomarAffineKato394.restrict (complement E c)
          (U.1 ⊓ complement E c) inf_le_right (v : _) *
        ArithmeticThetaPalomarAffineKato394.restrict U.1
          (U.1 ⊓ complement E c) inf_le_left b =
      ArithmeticThetaPalomarAffineKato394.restrict U.1
        (U.1 ⊓ complement E c) inf_le_left ((ε : _) * a ^ (c ^ 2))

end ArithmeticThetaPalomarSchemeKato394
namespace ArithmeticThetaPalomarSchemeNorm394
open CategoryTheory AlgebraicGeometry

abbrev Sections (X : Scheme.{u}) (U : X.Opens) :=
  X.presheaf.obj (Opposite.op U)

abbrev restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : Sections X U) : Sections X V :=
  ArithmeticThetaPalomarAffineKato394.restrict U V h a

/-- Every free affine restriction is tested with the algebra induced by f.app.
The accepted affineNorm definition elaborates its scalar action from that map.
This avoids the totalized norm on a nonfree global section algebra. -/
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U),
    ArithmeticThetaGeometricNormR0150.AffineFree f V.1 →
    ArithmeticThetaGeometricNormR0150.affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) =
      restrict U V.1 e b

abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U

/-- Actual multiplicative maps on the section rings, with their determinant
normalization and restriction compatibility on all opens. -/
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)

/-- The original section restricts to the inverse image of its domain and its
local determinant is the same original section. The inclusion is constructed. -/
def LocallyNormFixed {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens)
    (v : Sections X U) : Prop :=
  ∃ e : f ⁻¹ᵁ U ≤ U, IsNormSection f U (restrict U (f ⁻¹ᵁ U) e v) v

/-- Construct the actual norm family and the restriction used in its fixed-point
equation. This includes the norm operator, not only a conditional equation. -/
def NormInvariant {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens)
    (v : Sections X U) : Prop :=
  ∃ N : NormFamily f, IsNormFamily f N ∧
    ∃ e : f ⁻¹ᵁ U ≤ U, N U (restrict U (f ⁻¹ᵁ U) e v) = v

end ArithmeticThetaPalomarSchemeNorm394
namespace ArithmeticThetaPalomarKatoSupport394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
theorem normalModelExists (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    Nonempty (ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W) := by
  exact ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model R W
theorem schemeUnitExists :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∃ v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c, ArithmeticThetaPalomarSchemeKato394.IsKatoUnit E k σ c v := by
  exact ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_existence
end ArithmeticThetaPalomarKatoSupport394
namespace ArithmeticThetaPalomarKato394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaPalomarSchemeKato394 ArithmeticThetaPalomarSchemeNorm394
theorem normalized_iff (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    [IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)]
    [IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)]
    [IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)]
    [IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)]
    (c : ℕ) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) :
    ArithmeticThetaPalomarNormalized394.Normalized R W G c g ↔
      ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g := Iff.rfl
theorem affine_FromModel_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (G : ArithmeticThetaRelativeKatoR0169.Law R W) (M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W) (c : ℕ)
    (v : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c) :
    ArithmeticThetaPalomarAffineKato394.FromModel R W G M c v ↔
      ArithmeticThetaArbitraryKatoUnitR0249.FromModel R W G M c v := Iff.rfl
theorem affine_IsKatoUnit_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (G : ArithmeticThetaRelativeKatoR0169.Law R W) (c : ℕ)
    (v : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c) :
    ArithmeticThetaPalomarAffineKato394.IsKatoUnit R W G c v ↔
      ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit R W G c v := Iff.rfl
theorem scheme_iff {S : Scheme.{u}} (E : Family S) (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ Base k) (c : ℕ) (v : UnitSection E c) :
    IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v := Iff.rfl
theorem cartier_iff {S : Scheme.{u}} (E : Family S) (c : ℕ) (v : UnitSection E c) :
    HasCartierDivisor E c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v := Iff.rfl
theorem normFamily_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) :
    IsNormFamily f N ↔ ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N := Iff.rfl
theorem normInvariant_iff {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) :
    NormInvariant f U v ↔ ArithmeticThetaSchemeKatoNormR0251.NormInvariant f U v := Iff.rfl
theorem schemeUnitNaturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S),
    ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S),
      b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ,
      1 < c → Nat.Coprime c 6 → ∀ (v : UnitSection E c) (w : UnitSection H c),
      IsKatoUnit E k σ c v → IsKatoUnit H k τ c w →
      ∃ e : complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (complement E c),
        (w : H.curve.presheaf.obj (Opposite.op (complement H c))) =
          C.map.appLE _ _ e (v : _) := by
  exact ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality
theorem schemeIntrinsicCharacterization :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (Base k)) (E : Family S),
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : UnitSection E c,
      IsKatoUnit E k σ c v ↔ HasCartierDivisor E c v ∧
        NormInvariant (multiplication E 2) (complement E c) (v : _) ∧
        NormInvariant (multiplication E 3) (complement E c) (v : _) := by
  exact ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization
theorem recover_original_083 :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S),
    ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S),
      b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ,
      1 < c → Nat.Coprime c 6 → ∀ (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c) (w : ArithmeticThetaSchemeKatoUnitR0250.UnitSection H c),
      ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v → ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit H k τ c w →
      ∃ e : ArithmeticThetaSchemeKatoUnitR0250.complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (ArithmeticThetaSchemeKatoUnitR0250.complement E c),
        (w : H.curve.presheaf.obj (Opposite.op (ArithmeticThetaSchemeKatoUnitR0250.complement H c))) =
          C.map.appLE _ _ e (v : _) := by
  exact schemeUnitNaturality
theorem recover_original_086 :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (Base k)) (E : Family S),
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c,
      ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧
        ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 2) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) ∧
        ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 3) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) := by
  exact schemeIntrinsicCharacterization
end ArithmeticThetaPalomarKato394
