module
public import Mathlib
public import SchemeKatoUnitNaturalityR0250
public import SchemeKatoFullTateExpansionR0252
public import LaurentGammaExistenceR0064
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
theorem projectiveGeometry (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] : IsProper (structureMap R W) ∧ SmoothOfRelativeDimension 1 (structureMap R W) ∧ GeometricallyConnected (structureMap R W) := by
  refine ⟨WeierstrassProjModel.projModelStrCR_isProper W.toProjective,
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective, ?_⟩
  letI : GeometricallyIntegral (structureMap R W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  exact GeometricallyIrreducible.geometricallyConnected (structureMap R W)
def family (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : Family (ArithmeticThetaLocalWeierstrassR0203.Base R) where
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
def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : X.presheaf.obj (Opposite.op U)) : X.presheaf.obj (Opposite.op V) :=
  X.presheaf.map (homOfLE h).op a
variable [Algebra ℚ R]
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
def IsKatoUnit (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∀ M : NormalModel R W, FromModel R W G M c v
end ArithmeticThetaPalomarAffineKato394
namespace ArithmeticThetaPalomarSchemeKato394
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
variable {S : Scheme.{u}} (E : Family S)
def multiplication (n : ℕ) : E.curve ⟶ E.curve :=
  (ArithmeticThetaSchemeLevelR0204.multiple E E.p n
    ⟨𝟙 E.curve, Category.id_comp E.p⟩).val
def identityIdeal : E.curve.IdealSheafData := E.zero.ker
def torsionIdeal (c : ℕ) : E.curve.IdealSheafData :=
  (identityIdeal E).comap (multiplication E c)
def complement (c : ℕ) : E.curve.Opens := (torsionIdeal E c).support.compl
abbrev UnitSection (c : ℕ) :=
  (E.curve.presheaf.obj (Opposite.op (complement E c)))ˣ
def IsKatoUnit (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) (c : ℕ) (v : UnitSection E c) : Prop :=
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
abbrev restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : Sections X U) : Sections X V :=
  ArithmeticThetaPalomarAffineKato394.restrict U V h a
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U),
    ArithmeticThetaGeometricNormR0150.AffineFree f V.1 →
    ArithmeticThetaGeometricNormR0150.affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) =
      restrict U V.1 e b
abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)
def LocallyNormFixed {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) : Prop :=
  ∃ e : f ⁻¹ᵁ U ≤ U, IsNormSection f U (restrict U (f ⁻¹ᵁ U) e v) v
def NormInvariant {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) : Prop :=
  ∃ N : NormFamily f, IsNormFamily f N ∧
    ∃ e : f ⁻¹ᵁ U ≤ U, N U (restrict U (f ⁻¹ᵁ U) e v) = v
end ArithmeticThetaPalomarSchemeNorm394
namespace ArithmeticThetaPalomarKatoSupport394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
theorem normalModelExists (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] : Nonempty (ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W) := by
  exact ArithmeticThetaArbitraryDiscriminantR0243.normal_discriminant_model R W
theorem schemeUnitExists : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃ v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c, ArithmeticThetaPalomarSchemeKato394.IsKatoUnit E k σ c v := by
  exact ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_existence
end ArithmeticThetaPalomarKatoSupport394
namespace ArithmeticThetaPalomarKato394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaPalomarSchemeKato394 ArithmeticThetaPalomarSchemeNorm394
theorem normalized_iff (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W) [IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (c : ℕ) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) : ArithmeticThetaPalomarNormalized394.Normalized R W G c g ↔ ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g := Iff.rfl
theorem affine_FromModel_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W) (M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W) (c : ℕ) (v : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c) : ArithmeticThetaPalomarAffineKato394.FromModel R W G M c v ↔ ArithmeticThetaArbitraryKatoUnitR0249.FromModel R W G M c v := Iff.rfl
theorem affine_IsKatoUnit_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W) (c : ℕ) (v : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c) : ArithmeticThetaPalomarAffineKato394.IsKatoUnit R W G c v ↔ ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit R W G c v := Iff.rfl
theorem scheme_iff {S : Scheme.{u}} (E : Family S) (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) (c : ℕ) (v : UnitSection E c) : IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v := Iff.rfl
theorem cartier_iff {S : Scheme.{u}} (E : Family S) (c : ℕ) (v : UnitSection E c) : HasCartierDivisor E c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v := Iff.rfl
theorem normFamily_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : IsNormFamily f N ↔ ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N := Iff.rfl
theorem normInvariant_iff {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) : NormInvariant f U v ↔ ArithmeticThetaSchemeKatoNormR0251.NormInvariant f U v := Iff.rfl
theorem schemeUnitNaturality : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S), ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S), b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ (v : UnitSection E c) (w : UnitSection H c), IsKatoUnit E k σ c v → IsKatoUnit H k τ c w → ∃ e : complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (complement E c), (w : H.curve.presheaf.obj (Opposite.op (complement H c))) = C.map.appLE _ _ e (v : _) := by
  exact ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality
theorem schemeIntrinsicCharacterization : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : Quiver.Hom S (Base k)) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : UnitSection E c, IsKatoUnit E k σ c v ↔ HasCartierDivisor E c v ∧ NormInvariant (multiplication E 2) (complement E c) (v : _) ∧ NormInvariant (multiplication E 3) (complement E c) (v : _) := by
  exact ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization
theorem recover_original_083 : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S), ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S), b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c) (w : ArithmeticThetaSchemeKatoUnitR0250.UnitSection H c), ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v → ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit H k τ c w → ∃ e : ArithmeticThetaSchemeKatoUnitR0250.complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (ArithmeticThetaSchemeKatoUnitR0250.complement E c), (w : H.curve.presheaf.obj (Opposite.op (ArithmeticThetaSchemeKatoUnitR0250.complement H c))) = C.map.appLE _ _ e (v : _) := by
  exact schemeUnitNaturality
theorem recover_original_086 : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : Quiver.Hom S (Base k)) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 2) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 3) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) := by
  exact schemeIntrinsicCharacterization
end ArithmeticThetaPalomarKato394
namespace ArithmeticThetaPalomarSchemeTate422
open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203
def TateExpansion (k : Type) [Field k] [CharZero k] {B : Scheme.{0}} (σ : B ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) (E : ArithmeticThetaLocalWeierstrassR0203.Family B) (c : ℕ) (v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] [Algebra k l],
  ∃ hE : (ArithmeticThetaPeriodOneNormR0248.periodCurve l).IsElliptic,
  ∃ hI : IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  ∃ hN : IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  letI := hE
  letI := hI
  letI := hN
  ∃ ev : (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)).functionField →+*
      ArithmeticThetaPeriodOneNormR0248.Series l,
    ArithmeticThetaPeriodOneNormR0248.IsEvaluation l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l) 1 ev ∧
    Function.Injective ev ∧
    ∀ (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l))
      (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G)
      (b : ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries l) ⟶ B),
      b ≫ σ = Spec.map (CommRingCat.ofHom
        ((algebraMap l (LaurentSeries l)).comp (algebraMap k l))) →
      ∀ C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E
        (ArithmeticThetaPalomarWeierstrass373.family (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G hG) b,
      ∃ e : ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c ≤
          C.map ⁻¹ᵁ ArithmeticThetaPalomarSchemeKato394.complement E c,
      ∃ hU : Nonempty (ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c),
        ArithmeticThetaUnsplitExpansionR0158.HasExpansion l 1 c 0
          (ev (@Scheme.germToFunctionField (ArithmeticThetaPeriodOneNormR0248.Curve l
            (ArithmeticThetaPeriodOneNormR0248.periodCurve l)) _
            (ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
              (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c) hU
            (C.map.appLE _ _ e (v : _))))
theorem expansion_iff {k : Type} [Field k] [CharZero k] {B : Scheme.{0}} (σ : B ⟶ Base k) (E : Family B) (c : ℕ) (v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c) : TateExpansion k σ E c v ↔ ArithmeticThetaSchemeKatoExpansionR0252.TateExpansion k σ E c v := Iff.rfl
theorem gammaPair (k : Type) [Field k] [CharZero k] (c : ℕ) : (∃! g : ArithmeticThetaLaurentNormR0064.Series k, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) 1 0 (ArithmeticThetaLaurentNormR0064.w k) g) ∧ (∃! h : ArithmeticThetaLaurentNormR0064.Series k, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) 1 0 (ArithmeticThetaLaurentNormR0064.w k ^ c) h) := by
  have hw : ArithmeticThetaLaurentNormR0064.w k ≠ 0 := by
    simpa [ArithmeticThetaLaurentNormR0064.w] using
      (IsFractionRing.injective (LaurentPolynomial k) (ArithmeticThetaLaurentNormR0064.Coeff k)).ne
        (LaurentPolynomial.isUnit_T (1 : ℤ) (R := k)).ne_zero
  exact ⟨ArithmeticThetaLaurentNormR0064.gamma_exists_unique _ 1 0 _ (by decide) hw,
    ArithmeticThetaLaurentNormR0064.gamma_exists_unique _ 1 0 _ (by decide) (pow_ne_zero _ hw)⟩
theorem schemeKatoFullTateExpansion :
∀ (k : Type) [Field k] [CharZero k] (B : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom B (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family B), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃! v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c, ArithmeticThetaPalomarSchemeKato394.IsKatoUnit E k σ c v ∧ ArithmeticThetaPalomarSchemeKato394.HasCartierDivisor E c v ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ArithmeticThetaPalomarSchemeNorm394.NormInvariant (ArithmeticThetaPalomarSchemeKato394.multiplication E d) (ArithmeticThetaPalomarSchemeKato394.complement E c) (v : _)) ∧ TateExpansion k σ E c v := by
  exact ArithmeticThetaSchemeKatoExpansionR0252.scheme_kato_full_tate_expansion
theorem recover_original_084 :
∀ (k : Type) [Field k] [CharZero k] (B : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom B (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family B), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃! v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ∧ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E d) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _)) ∧ ArithmeticThetaSchemeKatoExpansionR0252.TateExpansion k σ E c v := by
  exact schemeKatoFullTateExpansion
end ArithmeticThetaPalomarSchemeTate422
