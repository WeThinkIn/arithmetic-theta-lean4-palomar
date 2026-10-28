module
public import ArithmeticCommonUnaryFamilyR0238
public import SchemeDiscriminantExistenceR0244
import all Lean.Meta.Match.Match
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
namespace P458
open ArithmeticThetaSheafTensor
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) =
      tensorSection X M N (f ⁻¹ᵁ U)
        (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) : ∃! q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N, Compatible f H K M N e d q := by
  let q := ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
    ArithmeticThetaPullback.sheafTensorCongr X e d
  have hq : Compatible f H K M N e d q := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (pullSection f (tensorSection Y H K U s t))) = _
    rw [show pullSection f (tensorSection Y H K U s t) =
      Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t) from rfl]
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ArithmeticThetaSheafTensor.tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change q'.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t)) =
    q.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t))
  exact (hq' U.unop s t).trans (hq U.unop s t).symm
theorem compatible_iff_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Compatible f H K M N e d q ↔ q = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫ ArithmeticThetaPullback.sheafTensorCongr X e d := by
  have h : Compatible f H K M N e d (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
      ArithmeticThetaPullback.sheafTensorCongr X e d) := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t))) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  constructor
  · intro hq
    exact (canonicalBinaryTensor f H K M N e d).unique hq h
  · rintro rfl
    exact h
end P458
namespace P505
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) :=
  Classical.choose (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
end P505
namespace P505
open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end P505
namespace P485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end P485
namespace P505
theorem binary_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : binary f H K = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K := by
  have h := Classical.choose_spec (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
  have hq : P458.Compatible f H K _ _ (Iso.refl _) (Iso.refl _) (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K) := by
    intro U s t
    change (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _ (Scheme.Modules.pullbackLocalSection f (ArithmeticThetaSheafTensor.tensorSection Y H K U s t)) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section]
    rfl
  exact (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).unique h hq
theorem powerComparison_eq_original (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) (n : ℕ) : powerComparison X Y f H n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerComparison, ArithmeticThetaPullback.pullback_tensorPower_iso, binary_eq_original, ih]
end P505
namespace P509.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
def tensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X K n :=
  P505.powerComparison X Y p H n ≪≫ powerCongr X e n
end P509.HodgeBaseChange
namespace P509.OpenHodge
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower ArithmeticThetaOpenHodgeR0180
def powerComparison {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) : (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n :=
  P509.HodgeBaseChange.tensorComparison (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n
def pullSection {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤)) : Γ(HodgePower R W n, ⊤) :=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))
def IsD2 {S : Type u} [CommRing S] (E : EllipticFamily S) (d : Γ(power E 24, ⊤)) : Prop :=
  IsFrame (power E 24) ⊤ d ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G →
    ∀ (C : Test S E R W G) (g : (Curve R W).functionField),
    Normalized R W G 5 g → RepresentsInitial R W G 5 g (pullSection C 24 d)
end P509.OpenHodge
namespace P509.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def pullToOpen {D : LevelData k L} (n : ℕ) (s : Γ(power D.atlas.descent.family n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((P505.powerComparison _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (Scheme.Modules.pullbackLocalSection D.quotient.inclusion s))
def restrictPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((P509.HodgeBaseChange.tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))
end P509.BoundaryHodge
namespace P509
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaTensorPower
theorem tensorComparison_eq_original {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : HodgeBaseChange.tensorComparison p H K e n = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison p H K e n := by
  simp only [HodgeBaseChange.tensorComparison, ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison, P505.powerComparison_eq_original]
theorem isD2_iff_original {S : Type u} [CommRing S] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (d : Γ(ArithmeticThetaOpenHodgeR0180.power E 24, ⊤)) : OpenHodge.IsD2 E d ↔ ArithmeticThetaOpenHodgeR0180.IsD2 E d := by
  simp only [OpenHodge.IsD2, ArithmeticThetaOpenHodgeR0180.IsD2, OpenHodge.pullSection, ArithmeticThetaOpenHodgeR0180.pullSection, OpenHodge.powerComparison, ArithmeticThetaOpenHodgeR0180.powerComparison, tensorComparison_eq_original]
end P509
namespace P514.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def diskPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (T : DiskTest k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(tensorPower (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) n, ⊤) :=
  res _ (by simp) ((P505.powerComparison _ _
    T.disk H.line n).hom.app _ (Scheme.Modules.pullbackLocalSection T.disk s))
end P514.BoundaryHodge
namespace P514
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (m N : ℕ)
structure OpenPower (D : LevelData k (level N)) (a b : Fin N) where
  quotient : ArithmeticThetaOpenHodgeR0180.Quotient D.atlas.quotient.ring
    (ArithmeticThetaOpenHodgeR0180.levelFamily k (level N) D.atlas) m
    (ArithmeticThetaOpenHodgeR0180.kernelPoint k (level N) D.atlas m)
  discriminant : Γ(ArithmeticThetaOpenHodgeR0180.power quotient.target 24, ⊤)
  intrinsic : P509.OpenHodge.IsD2 quotient.target discriminant
  value : D.atlas.quotient.ring
  value_spec : ArithmeticThetaOpenHodgeR0180.IsKatoValue quotient.target (1+12*N)
    (ArithmeticThetaOpenHodgeR0180.liftPoint k (level N) D.atlas m N a.val b.val ≫ quotient.arrow.map) value
  section_ : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (weight N), ⊤)
  normalized : ArithmeticThetaOpenHodgeR0180.IsNormalizedPower k (level N) D.atlas
    m N quotient discriminant value section_
def DiskCoefficient {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) (f : PowerSeries k) : Prop :=
  ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤),
    ExtendsGenerator k (level N) H V η →
    BoundaryHodge.diskPower k (level N) H V (weight N) s =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) f •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line) (weight N) ⊤ η
def RealizesUnary {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : Prop :=
  P509.BoundaryHodge.restrictPower k (level N) H (weight N) s = P509.BoundaryHodge.pullToOpen k (level N) (weight N) A.section_ ∧
  IsFrame (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (weight N)) ⊤ A.section_ ∧
  (∀ V : DiskTest k (level N) D X, ∃ f : PowerSeries k,
    f ≠ 0 ∧ DiskCoefficient k N H V s f) ∧
  (∀ (V : DiskTest k (level N) D X) (ζ : k), IsPrimitiveRoot ζ (level N) →
    CanonicalMarking k (level N) ζ V.level →
    ∃ f : PowerSeries k,
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N ∧
      DiskCoefficient k N H V s f)
end P514
namespace P514
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (m N : ℕ)
def toOriginal {D : LevelData k (level N)} {a b : Fin N} (A : OpenPower k m N D a b) : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b where
  quotient := A.quotient
  discriminant := A.discriminant
  value := A.value
  value_spec := A.value_spec
  section_ := A.section_
  normalized := A.normalized
  intrinsic := (P509.isD2_iff_original _ _).mp A.intrinsic
def ofOriginal {D : LevelData k (level N)} {a b : Fin N} (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) : OpenPower k m N D a b where
  quotient := A.quotient
  discriminant := A.discriminant
  value := A.value
  value_spec := A.value_spec
  section_ := A.section_
  normalized := A.normalized
  intrinsic := (P509.isD2_iff_original _ _).mpr A.intrinsic
theorem diskCoefficient_iff_original {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) (f : PowerSeries k) : DiskCoefficient k N H V s f ↔ ArithmeticThetaCompactUnaryR0183.DiskCoefficient k N H V s f := by
  simp only [DiskCoefficient, ArithmeticThetaCompactUnaryR0183.DiskCoefficient, BoundaryHodge.diskPower, ArithmeticThetaBoundaryHodgeR0182.diskPower, P505.powerComparison_eq_original]
theorem realizes_toOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν A s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν (toOriginal k m N A) s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, toOriginal, diskCoefficient_iff_original, P509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, P509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, P509.tensorComparison_eq_original, P505.powerComparison_eq_original]
theorem realizes_ofOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν (ofOriginal k m N A) s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, ofOriginal, diskCoefficient_iff_original, P509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, P509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, P509.tensorComparison_eq_original, P505.powerComparison_eq_original]
end P514
namespace P365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens} (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s
section Differentials
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) :=
  ((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (kaehlerPresheaf f)
def kaehlerToSections (U : X.Opens) : ((kaehlerPresheaf f).obj (op U) : Type u) → (Γ(kaehler f, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (kaehlerPresheaf f)).app (op U)).hom s
def relativeD (U : X.Opens) (a : Γ(X, U)) : Γ(kaehler f, U) :=
  letI : Algebra R Γ(X, U) := sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X, U) a)
end Differentials
end P365
namespace P436
open P365
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (e : S ⟶ X)
def Normalized (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Prop :=
  ∀ (U : X.Opens) (x : Γ(idealModule e.ker,U)),
    m.app (e ⁻¹ᵁ U) (pullSection e x) =
      pullSection e (relativeD c U ((idealInclusion e.ker).app U x))
theorem canonicalConormalMap : ∃! m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c), Normalized c e m := by
  let m := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e
  refine ⟨m, ?_, ?_⟩
  · intro U x
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x
  · intro n hn
    apply Scheme.Modules.pullback_hom_ext e
    intro U x
    exact (hn U x).trans
      (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x).symm
def conormalMap : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c) :=
  (canonicalConormalMap c e).exists.choose
theorem normalized_iff_original (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Normalized c e m ↔ m = ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e := by
  constructor
  · intro h
    apply Scheme.Modules.pullback_hom_ext e
    intro U x
    exact (h U x).trans
      (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x).symm
  · rintro rfl
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e
theorem conormalMap_eq_original : conormalMap c e = ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e :=
  (normalized_iff_original c e _).mp (canonicalConormalMap c e).exists.choose_spec
end P436
namespace P544
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
variable {X Y : Scheme.{u}}
abbrev unitMap (f : X ⟶ Y) : SheafOfModules.unit Y.ringCatSheaf ⟶ (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
def idealModule (I : X.IdealSheafData) : X.Modules := (kernel (unitMap I.subschemeι) : SheafOfModules X.ringCatSheaf)
def idealInclusion (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf := kernel.ι (unitMap I.subschemeι)
end P544
namespace P519.Hodge
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (P544.idealModule E.zero.ker)
def IdealCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (f : F.curve ⟶ E.curve) (i : (Scheme.Modules.pullback f).obj (P544.idealModule E.zero.ker) ≅ (P544.idealModule F.zero.ker)) : Prop :=
  i.hom ≫ (P544.idealInclusion F.zero.ker) =
    (Scheme.Modules.pullback f).map (P544.idealInclusion E.zero.ker) ≫
      (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (i : (Scheme.Modules.pullback f).obj (P544.idealModule E.zero.ker) ≅ (P544.idealModule F.zero.ker)) : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F :=
  squarePullbackIso b E.zero F.zero f hz.symm (P544.idealModule E.zero.ker) ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F) : Prop :=
  ∃ i, IdealCompatible E F f i ∧ e = cotangentComparison E F b f hz i
abbrev affineDifferential {R : Type u} [CommRing R] (E : Family (Base R)) : Cotangent E ⟶ (Scheme.Modules.pullback E.zero).obj E.p.kaehler :=
  P436.conormalMap E.p E.zero
variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
abbrev universalFamily := ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily L A
abbrev ModularHodge : (Base Q.quotient.ring).Modules :=
  (Scheme.Modules.pullback Q.inclusion).obj
    ((Scheme.Modules.pullback (universalFamily k L A).zero).obj
      (universalFamily k L A).p.kaehler)
def ClassifierHodge {S : Scheme.{u}} (E : Family S) (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) (e : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E) : Prop :=
  ∃ (hz : E.zero ≫ f = (b ≫ Q.inclusion) ≫ (universalFamily k L A).zero)
    (i : (Scheme.Modules.pullback f).obj (P544.idealModule (universalFamily k L A).zero.ker) ≅ (P544.idealModule E.zero.ker)),
    IdealCompatible (universalFamily k L A) E f i ∧
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pullback Q.inclusion).map (affineDifferential (universalFamily k L A))) ≫
        e.hom =
      ((Scheme.Modules.pullbackComp b Q.inclusion).app (Cotangent (universalFamily k L A))).hom ≫
        (cotangentComparison (universalFamily k L A) E (b ≫ Q.inclusion) f hz i).hom
end P519.Hodge
namespace P519.Level
open CategoryTheory.Limits ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 P519.Hodge
abbrev constants {k l : Type} [Field k] [Field l] (ι : k →+* l) : Base l ⟶ Base k := Spec.map (CommRingCat.ofHom ι)
abbrev Classifies {k : Type} [Field k] [CharZero k] {L : ℕ} (D : LevelData k L) {S : Scheme.{0}} (σ : S ⟶ Base k) (F : Family S) (M : FullLevel F L) (b : S ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve) :=
  ArithmeticThetaSchemeLevelR0204.Classifies k L D.atlas D.two D.cover D.quotient σ F M b f
def RespectsClassifiers {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (f : OpenBase l L E ⟶ OpenBase k L D) : Prop :=
  f ≫ openStructure k L D = openStructure l L E ≫ constants ι ∧
  ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L)
    (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve),
    Classifies E σ F M b g →
    ∃ a : F.curve ⟶ D.atlas.descent.family.curve,
      Classifies D (σ ≫ constants ι) F M (b ≫ f) a
abbrev weight {k : Type} [Field k] [CharZero k] {L : ℕ} (D : LevelData k L) :=
  ModularHodge k L D.atlas D.two D.cover D.quotient
def HodgeCompatible {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (f : OpenBase l L E ⟶ OpenBase k L D) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) : Prop :=
  ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L)
    (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve)
    (a : F.curve ⟶ D.atlas.descent.family.curve),
    Classifies E σ F M b g → Classifies D (σ ≫ constants ι) F M (b ≫ f) a →
    ∀ (el : (Scheme.Modules.pullback b).obj (weight E) ≅ Cotangent F)
      (ek : (Scheme.Modules.pullback (b ≫ f)).obj (weight D) ≅ Cotangent F),
    ClassifierHodge l L E.atlas E.two E.cover E.quotient F b g el →
    ClassifierHodge k L D.atlas D.two D.cover D.quotient F (b ≫ f) a ek →
    (Scheme.Modules.pullback b).map e.hom ≫ el.hom =
      ((Scheme.Modules.pullbackComp b f).app (weight D)).hom ≫ ek.hom
def Extends {k l : Type} [Field k] [Field l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (X : Compactification k L D) (Y : Compactification l L E) (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) : Prop :=
  F ≫ X.projection = Y.projection ≫ constants ι ∧ Y.inclusion ≫ F = f ≫ X.inclusion
end P519.Level
namespace P519.Boundary
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange P519.Level
variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
def CompactCompatible (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L} {X : Compactification k L D} {Y : Compactification l L E} (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) (hF : P519.Level.Extends ι D E X Y f F) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) (H : Extension k L D X) (J : Extension l L E Y) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) : Prop :=
  (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom =
    ((Scheme.Modules.pullbackComp Y.inclusion F).app H.line).hom ≫
    (pullbackEqIso hF.2 H.line).hom ≫
    ((Scheme.Modules.pullbackComp f X.inclusion).app H.line).inv ≫
    (Scheme.Modules.pullback f).map H.onOpen.hom ≫ e.hom
def GeometricallyCanonical {L : ℕ} {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] [IsAlgClosed l] (ι : k →+* l)
    (E : LevelData l L) (Y : Compactification l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hf : RespectsClassifiers ι D E f)
    (hF : P519.Level.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E),
    HodgeCompatible ι D E f e → ∀ J : Extension l L E Y,
    Canonical l L J → ∃! a : (Scheme.Modules.pullback F).obj H.line ≅ J.line,
      CompactCompatible ι f F hF e H J a
end P519.Boundary
namespace P519
theorem classifierHodge_iff_original {k : Type u} [Field k] [CharZero k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) {S : Scheme.{u}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (b : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) (e : (Scheme.Modules.pullback b).obj (Hodge.ModularHodge k L A B C Q) ≅ Hodge.Cotangent E) : Hodge.ClassifierHodge k L A B C Q E b f e ↔ ArithmeticThetaSchemeHodgeR0205.ClassifierHodge k L A B C Q E b f e := by
  simp only [Hodge.ClassifierHodge, ArithmeticThetaSchemeHodgeR0205.ClassifierHodge, Hodge.affineDifferential, ArithmeticThetaSchemeHodgeR0205.affineDifferential, P436.conormalMap_eq_original]
  rfl
theorem hodgeCompatible_iff_original {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (f : ArithmeticThetaLevelCompactificationR0179.OpenBase l L E ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D) (e : (Scheme.Modules.pullback f).obj (Level.weight D) ≅ Level.weight E) : Level.HodgeCompatible ι D E f e ↔ ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e := by
  simp only [Level.HodgeCompatible, ArithmeticThetaLevelConstantsR0234.HodgeCompatible, classifierHodge_iff_original]
  rfl
theorem geometric_iff_original {k : Type} [Field k] [CharZero k] {L : ℕ} {D : ArithmeticThetaLevelCompactificationR0179.LevelData k L} {X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D} (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) : Boundary.GeometricallyCanonical H ↔ ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H := by
  simp only [Boundary.GeometricallyCanonical, ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical, hodgeCompatible_iff_original]
  rfl
end P519
namespace P506
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
variable (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
def HalfBranch (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (Component k L D X x)) (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H) : Prop :=
  ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    CanonicalMarking k L ζ V.level →
    ∀ (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk)
      (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)),
      ExtendsGenerator k L H V η →
      ∃ h : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
        IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ h ∧
        pullbackGlobalSection f A.line A.section_ =
          scalar (PowerSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m)) • h ∧
        (ArithmeticThetaCommonHalfHodgeR0185.diskHodgeIso k L D X x H V f hf).hom.app ⊤
          (((P505.powerComparison _ _ f A.line 2).symm ≪≫
            (Scheme.Modules.pullback f).mapIso β).hom.app ⊤
            (tensorPowerSection _ ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ h)) = η
end P506
namespace P506
theorem branch_iff_original (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (β : ArithmeticThetaTensorPower.tensorPower _ A.line 2 ≅ ArithmeticThetaComponentDegreeR0184.hodge k L D X x H) : HalfBranch k L m D X H x A β ↔ ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch k L m D X H x A β := by
  simp only [HalfBranch, ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch, P505.powerComparison_eq_original]
end P506
namespace P529
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185
def squarePull {Z Y : Scheme} {W : Z.Modules} (f : Y ⟶ Z) (A : SquareLine Z W) : tensorPower Y ((Scheme.Modules.pullback f).obj A.line) 2 ≅ (Scheme.Modules.pullback f).obj W :=
  (P505.powerComparison Y Z f A.line 2).symm ≪≫
    (Scheme.Modules.pullback f).mapIso A.square
def squareOnDisk (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : tensorPower (Disk k) ((Scheme.Modules.pullback f).obj J) 2 ≅ (Scheme.Modules.pullback d).obj H :=
  (P505.powerComparison (Disk k) B f J 2).symm ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ along f p d hf H
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) :=
  (P505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens))
    (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
end P529
namespace P529
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185
structure CoverFrame (k : Type) [Field k] [CharZero k] (N : ℕ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k))) (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ) (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k))) (projection k (level N) D X (V.disk (closedPoint k))) b) where
  disk : Disk k ⟶ C.space
  triangle : disk ≫ (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k))) = V.disk
  dominant : IsDominant (genericInclusion k ≫ disk)
  frame : Sections (Disk k) ((Scheme.Modules.pullback disk).obj ((Scheme.Modules.pullback C.map).obj J.line))
  isFrame : ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ frame
  generator : Sections (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line)
  extendsGenerator : ExtendsGenerator k (level N) H V generator
  square_eq : (squareOnDisk k (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
    ((Scheme.Modules.pullback C.map).obj J.line) H.line
    (squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
      (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
    disk V.disk triangle).hom.app ⊤ (tensorPowerSection _ _ 2 ⊤ frame) = generator
end P529
namespace P529
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185
theorem squarePull_eq_original {Z Y : Scheme} {W : Z.Modules} (f : Y ⟶ Z) (A : SquareLine Z W) : squarePull f A = ArithmeticThetaSquareLinesR0192.squarePull f A := by
  simp only [squarePull, ArithmeticThetaSquareLinesR0192.squarePull, P505.powerComparison_eq_original]
theorem squareOnDisk_eq_original (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : squareOnDisk k p J H β f d hf = ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H β f d hf := by
  simp only [squareOnDisk, ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk, P505.powerComparison_eq_original]
theorem pullbackPowerSection_eq_original {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : pullbackPowerSection p H n F = ArithmeticThetaNormalizedSections.pullbackPowerSection p H n F := by
  simp only [pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, P505.powerComparison_eq_original]
variable (k : Type) [Field k] [CharZero k] (N : ℕ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k))) (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ) (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k))) (projection k (level N) D X (V.disk (closedPoint k))) b)
def frameToOriginal (F : CoverFrame k N H V J b C) : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C where
  disk := F.disk
  triangle := F.triangle
  dominant := F.dominant
  frame := F.frame
  isFrame := F.isFrame
  generator := F.generator
  extendsGenerator := F.extendsGenerator
  square_eq := by simpa only [squareOnDisk_eq_original, squarePull_eq_original] using F.square_eq
def frameOfOriginal (F : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C) : CoverFrame k N H V J b C where
  disk := F.disk
  triangle := F.triangle
  dominant := F.dominant
  frame := F.frame
  isFrame := F.isFrame
  generator := F.generator
  extendsGenerator := F.extendsGenerator
  square_eq := by simpa only [squareOnDisk_eq_original, squarePull_eq_original] using F.square_eq
end P529
namespace P534
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder P529
structure CanonicalHalf (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X) (x : X.space) where
  openData : OpenAlpha k L m D
  alpha : Γ(H.line, ⊤)
  realizes : CompactRealizes k L m D X H openData alpha
  divisor : Component k L D X x →₀ ℤ
  effective : ∀ y, 0 ≤ divisor y
  normal : NormalAffine (Component k L D X x)
  half : HalfDivisor k L D X H x alpha divisor
  invertible : Scheme.Modules.IsInvertible
    (canonicalDivisorData k L D X x divisor effective normal).line
  square : tensorPower (Component k L D X x)
    (canonicalDivisorData k L D X x divisor effective normal).line 2 ≅ hodge k L D X x H
  square_section : square.hom.app ⊤ (tensorPowerSection _
    (canonicalDivisorData k L D X x divisor effective normal).line 2 ⊤
    (canonicalDivisorData k L D X x divisor effective normal).section_) =
      componentAlpha k L D X H x alpha
  branch : P506.HalfBranch k L m D X H x
    (canonicalDivisorData k L D X x divisor effective normal) square
variable {k : Type} [Field k] [CharZero k] {L m : ℕ} {D : LevelData k L}
    {X : Compactification k L D} {H : Extension k L D X} {x : X.space}
def CanonicalHalf.data (A : CanonicalHalf k L m D X H x) : DivisorLine (Component k L D X x) :=
  canonicalDivisorData k L D X x A.divisor A.effective A.normal
def CanonicalHalf.squareLine (A : CanonicalHalf k L m D X H x) : SquareLine (Component k L D X x) (hodge k L D X x H) :=
  ⟨A.data.line, A.invertible, A.square⟩
end P534
namespace P534
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder P529
def IsSquarePower {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (N : ℕ) (e : tensorPower B J (exponent N) ≅ tensorPower B ((Scheme.Modules.pullback p).obj H) (weight N)) : Prop :=
  ∀ (U : B.Opens) (v : J.presheaf.obj (Opposite.op U)),
    e.hom.app U (tensorPowerSection B J (exponent N) U v) =
      tensorPowerSection B ((Scheme.Modules.pullback p).obj H) (weight N) U
        (β.hom.app U (tensorPowerSection B J 2 U v))
def UnaryPowers (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) {B : Scheme} (p : B ⟶ X.space) (J : B.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H.line) (F : Fin s → Sections B (tensorPower B J (exponent N))) : Prop :=
  ∃ e : tensorPower B J (exponent N) ≅
      tensorPower B ((Scheme.Modules.pullback p).obj H.line) (weight N),
    IsSquarePower p J H.line β N e ∧ ∀ j,
      F j ≠ 0 ∧ ∃ (a b : Fin N),
        a.val = unaryResidue (m j) N (ν j) ∧ b.val = N/2 ∧
        ∃ (A : P514.OpenPower k (m j) N D a b)
          (t : Sections X.space (tensorPower X.space H.line (weight N))),
          P514.RealizesUnary k (m j) N H (ν j) A t ∧
          e.hom.app ⊤ (F j) = P529.pullbackPowerSection p H.line (weight N) t
end P534
namespace P534
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder P529
def RatioMultiple {B Y : Scheme} [IsIntegral B] (p : Y ⟶ B) (J : Y.Modules) (t t₀ : Sections Y J) (r : B.functionField) : Prop :=
  ∃ (U : B.Opens) (hU : Nonempty U), letI := hU
    ∃ v : B.presheaf.obj (Opposite.op U), B.germToFunctionField U v = r ∧
      J.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op t =
        p.app U v • J.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op t₀
def RegularUnary (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k))) (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ) (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k))) (projection k (level N) D X (V.disk (closedPoint k))) b) (F : CoverFrame k N H V J b C) (t₀ : Fin s → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line)) : Prop :=
  ∃ t : Fin s → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line),
    UnaryPowers k N s m ν H (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
      ((Scheme.Modules.pullback C.map).obj J.line)
      (P529.squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
        (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
      (fun i => tensorPowerSection _ _ (exponent N) ⊤ (t i)) ∧
    ∀ i, t i ≠ 0 ∧
      pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) (t i) =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (unarySeries k N (m i) (ν i)) • F.frame ∧
      ∃ r : (Component k (level N) D X (V.disk (closedPoint k))).functionField,
        RationalExpansion k _ (genericInclusion k ≫ (F.disk ≫ C.map)) r
          (algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N (m i) (ν i)) /
            algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N (m i) 0)) ∧
        RatioMultiple C.map ((Scheme.Modules.pullback C.map).obj J.line) (t i) (t₀ i) r
end P534
namespace P534
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder P529
def CommonUnary (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ) (D : LevelData k (level N)) (X : Compactification k (level N) D) (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ A : ∀ i, CanonicalHalf k (level N) (m i) D X H x,
    ∃ C : RootCover k (Component k (level N) D X x)
      (projection k (level N) D X x) (2^s),
      Etale C.map ∧ (s = 0 → IsIso C.map) ∧
      ∃ F : CoverFrame k N H V (A 0).squareLine (2^s) C,
        ∃ t₀ : Fin (s+1) → Sections C.space
          ((Scheme.Modules.pullback C.map).obj (A 0).data.line),
          (∀ i, t₀ i ≠ 0 ∧
            pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj (A 0).data.line)
              (t₀ i) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
                (unarySeries k N (m i) 0) • F.frame) ∧
          RegularUnary k N (s+1) m ν H V (A 0).squareLine (2^s) C F t₀
end P534
namespace P534
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder P529
def halfToOriginal {k : Type} [Field k] [CharZero k] {L m : ℕ} {D : LevelData k L} {X : Compactification k L D} {H : Extension k L D X} {x : X.space} (A : CanonicalHalf k L m D X H x) : ArithmeticThetaSharpCoverR0194.CanonicalHalf k L m D X H x where
  openData := A.openData
  alpha := A.alpha
  realizes := A.realizes
  divisor := A.divisor
  effective := A.effective
  normal := A.normal
  half := A.half
  invertible := A.invertible
  square := A.square
  square_section := A.square_section
  branch := (P506.branch_iff_original _ _ _ _ _ _ _ _ _).mp A.branch
def halfOfOriginal {k : Type} [Field k] [CharZero k] {L m : ℕ} {D : LevelData k L} {X : Compactification k L D} {H : Extension k L D X} {x : X.space} (A : ArithmeticThetaSharpCoverR0194.CanonicalHalf k L m D X H x) : CanonicalHalf k L m D X H x where
  openData := A.openData
  alpha := A.alpha
  realizes := A.realizes
  divisor := A.divisor
  effective := A.effective
  normal := A.normal
  half := A.half
  invertible := A.invertible
  square := A.square
  square_section := A.square_section
  branch := (P506.branch_iff_original _ _ _ _ _ _ _ _ _).mpr A.branch
theorem unaryPowers_iff_original (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) {B : Scheme} (p : B ⟶ X.space) (J : B.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H.line) (F : Fin s → Sections B (tensorPower B J (exponent N))) : UnaryPowers k N s m ν H p J β F ↔ ArithmeticThetaSimultaneousUnaryR0187.UnaryPowers k N s m ν H p J β F := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun j => ?_⟩
    obtain ⟨hn, a, b, ha, hb, A, t, ht, heq⟩ := h j
    refine ⟨hn, a, b, ha, hb, P514.toOriginal k (m j) N A, t, ?_, ?_⟩
    · exact (P514.realizes_toOriginal k (m j) N H (ν j) A t).mp ht
    · simpa only [P529.pullbackPowerSection_eq_original] using heq
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun j => ?_⟩
    obtain ⟨hn, a, b, ha, hb, A, t, ht, heq⟩ := h j
    refine ⟨hn, a, b, ha, hb, P514.ofOriginal k (m j) N A, t, ?_, ?_⟩
    · exact (P514.realizes_ofOriginal k (m j) N H (ν j) A t).mpr ht
    · simpa only [P529.pullbackPowerSection_eq_original] using heq
theorem regularUnary_iff_original (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k))) (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ) (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k))) (projection k (level N) D X (V.disk (closedPoint k))) b) (F : CoverFrame k N H V J b C) (t₀ : Fin s → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line)) : RegularUnary k N s m ν H V J b C F t₀ ↔ ArithmeticThetaSharpKernelR0195.RegularUnary k N s m ν H V J b C (P529.frameToOriginal k N H V J b C F) t₀ := by
  simp only [RegularUnary, ArithmeticThetaSharpKernelR0195.RegularUnary, unaryPowers_iff_original, P529.squarePull_eq_original]
  rfl
theorem commonUnary_iff_original (k : Type) [Field k] [CharZero k] (N s : ℕ) (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ) (D : LevelData k (level N)) (X : Compactification k (level N) D) (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) : CommonUnary k N s m ν D X H V ↔ ArithmeticThetaArithmeticCommonCoverR0238.CommonUnary k N s m ν D X H V := by
  constructor
  · rintro ⟨A, C, het, hiso, F, t₀, hbasic, hregular⟩
    refine ⟨fun i => halfToOriginal (A i), C, het, hiso, P529.frameToOriginal k N H V (A 0).squareLine (2^s) C F, t₀, hbasic, ?_⟩
    exact (regularUnary_iff_original k N (s+1) m ν H V (A 0).squareLine (2^s) C F t₀).mp hregular
  · rintro ⟨A, C, het, hiso, F, t₀, hbasic, hregular⟩
    let F' := P529.frameOfOriginal k N H V (A 0).squareLine (2^s) C F
    refine ⟨fun i => halfOfOriginal (A i), C, het, hiso, F', t₀, hbasic, ?_⟩
    exact (regularUnary_iff_original k N (s+1) m ν H V (A 0).squareLine (2^s) C F' t₀).mpr hregular
theorem arithmeticCommonUnary : ∀ (k : Type) [Field k] [CharZero k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ), (∀ i, 0 < m i ∧ Even (m i) ∧ m i ∣ N ∧ (-(m i : ℤ) ≤ 2*ν i ∧ 2*ν i < (m i : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → P519.Boundary.GeometricallyCanonical H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → P534.CommonUnary k N s m ν D X H V := by
  simpa only [P519.geometric_iff_original, commonUnary_iff_original] using ArithmeticThetaArithmeticCommonCoverR0238.arithmetic_common_unary_family
theorem recover_original_071 : ∀ (k : Type) [Field k] [CharZero k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin (s+1) → ℕ) (ν : Fin (s+1) → ℤ), (∀ i, 0 < m i ∧ Even (m i) ∧ m i ∣ N ∧ (-(m i : ℤ) ≤ 2*ν i ∧ 2*ν i < (m i : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ArithmeticThetaArithmeticCommonCoverR0238.CommonUnary k N s m ν D X H V := by
  simpa only [P519.geometric_iff_original, commonUnary_iff_original] using arithmeticCommonUnary
end P534

namespace P544
example {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I = I.module := by rfl
example {X : Scheme.{u}} (I : X.IdealSheafData) : idealInclusion I = I.moduleι := by rfl
end P544
