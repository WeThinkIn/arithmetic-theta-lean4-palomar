module
public import FieldCompactUnaryR0236
public import SchemeDiscriminantExistenceR0244
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
namespace ArithmeticThetaPalomarBinaryTensor458
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
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) :=
  Classical.choose (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end ArithmeticThetaPalomarComponent485
namespace ArithmeticThetaPalomarHalf505
theorem binary_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : binary f H K = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K := by
  have h := Classical.choose_spec (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
  have hq : ArithmeticThetaPalomarBinaryTensor458.Compatible f H K _ _ (Iso.refl _) (Iso.refl _) (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K) := by
    intro U s t
    change (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _ (Scheme.Modules.pullbackLocalSection f (ArithmeticThetaSheafTensor.tensorSection Y H K U s t)) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section]
    rfl
  exact (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).unique h hq
theorem powerComparison_eq_original (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) (n : ℕ) : powerComparison X Y f H n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerComparison, ArithmeticThetaPullback.pullback_tensorPower_iso, binary_eq_original, ih]
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPalomarD2_509.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
def tensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X K n :=
  ArithmeticThetaPalomarHalf505.powerComparison X Y p H n ≪≫ powerCongr X e n
end ArithmeticThetaPalomarD2_509.HodgeBaseChange
namespace ArithmeticThetaPalomarD2_509.OpenHodge
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower ArithmeticThetaOpenHodgeR0180
def powerComparison {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) : (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n :=
  ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n
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
end ArithmeticThetaPalomarD2_509.OpenHodge
namespace ArithmeticThetaPalomarD2_509.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def pullToOpen {D : LevelData k L} (n : ℕ) (s : Γ(power D.atlas.descent.family n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarHalf505.powerComparison _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (Scheme.Modules.pullbackLocalSection D.quotient.inclusion s))
def restrictPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))
end ArithmeticThetaPalomarD2_509.BoundaryHodge
namespace ArithmeticThetaPalomarD2_509
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaTensorPower
theorem tensorComparison_eq_original {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : HodgeBaseChange.tensorComparison p H K e n = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison p H K e n := by
  simp only [HodgeBaseChange.tensorComparison, ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem isD2_iff_original {S : Type u} [CommRing S] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (d : Γ(ArithmeticThetaOpenHodgeR0180.power E 24, ⊤)) : OpenHodge.IsD2 E d ↔ ArithmeticThetaOpenHodgeR0180.IsD2 E d := by
  simp only [OpenHodge.IsD2, ArithmeticThetaOpenHodgeR0180.IsD2, OpenHodge.pullSection, ArithmeticThetaOpenHodgeR0180.pullSection, OpenHodge.powerComparison, ArithmeticThetaOpenHodgeR0180.powerComparison, tensorComparison_eq_original]
end ArithmeticThetaPalomarD2_509
namespace ArithmeticThetaPalomarUnary514.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def diskPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (T : DiskTest k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(tensorPower (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarHalf505.powerComparison _ _
    T.disk H.line n).hom.app _ (Scheme.Modules.pullbackLocalSection T.disk s))
end ArithmeticThetaPalomarUnary514.BoundaryHodge
namespace ArithmeticThetaPalomarUnary514
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (m N : ℕ)
structure OpenPower (D : LevelData k (level N)) (a b : Fin N) where
  quotient : ArithmeticThetaOpenHodgeR0180.Quotient D.atlas.quotient.ring
    (ArithmeticThetaOpenHodgeR0180.levelFamily k (level N) D.atlas) m
    (ArithmeticThetaOpenHodgeR0180.kernelPoint k (level N) D.atlas m)
  discriminant : Γ(ArithmeticThetaOpenHodgeR0180.power quotient.target 24, ⊤)
  intrinsic : ArithmeticThetaPalomarD2_509.OpenHodge.IsD2 quotient.target discriminant
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
  ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k (level N) H (weight N) s = ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k (level N) (weight N) A.section_ ∧
  IsFrame (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (weight N)) ⊤ A.section_ ∧
  (∀ V : DiskTest k (level N) D X, ∃ f : PowerSeries k,
    f ≠ 0 ∧ DiskCoefficient k N H V s f) ∧
  (∀ (V : DiskTest k (level N) D X) (ζ : k), IsPrimitiveRoot ζ (level N) →
    CanonicalMarking k (level N) ζ V.level →
    ∃ f : PowerSeries k,
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N ∧
      DiskCoefficient k N H V s f)
end ArithmeticThetaPalomarUnary514
namespace ArithmeticThetaPalomarUnary514
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (m N : ℕ)
def toOriginal {D : LevelData k (level N)} {a b : Fin N} (A : OpenPower k m N D a b) : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b where
  quotient := A.quotient
  discriminant := A.discriminant
  value := A.value
  value_spec := A.value_spec
  section_ := A.section_
  normalized := A.normalized
  intrinsic := (ArithmeticThetaPalomarD2_509.isD2_iff_original _ _).mp A.intrinsic
def ofOriginal {D : LevelData k (level N)} {a b : Fin N} (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) : OpenPower k m N D a b where
  quotient := A.quotient
  discriminant := A.discriminant
  value := A.value
  value_spec := A.value_spec
  section_ := A.section_
  normalized := A.normalized
  intrinsic := (ArithmeticThetaPalomarD2_509.isD2_iff_original _ _).mpr A.intrinsic
theorem diskCoefficient_iff_original {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) (f : PowerSeries k) : DiskCoefficient k N H V s f ↔ ArithmeticThetaCompactUnaryR0183.DiskCoefficient k N H V s f := by
  simp only [DiskCoefficient, ArithmeticThetaCompactUnaryR0183.DiskCoefficient, BoundaryHodge.diskPower, ArithmeticThetaBoundaryHodgeR0182.diskPower, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem realizes_toOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν A s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν (toOriginal k m N A) s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, toOriginal, diskCoefficient_iff_original, ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem realizes_ofOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν (ofOriginal k m N A) s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, ofOriginal, diskCoefficient_iff_original, ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
end ArithmeticThetaPalomarUnary514
namespace ArithmeticThetaPalomarDifferential365
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
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarConormal436
open ArithmeticThetaPalomarDifferential365
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
end ArithmeticThetaPalomarConormal436
namespace ArithmeticThetaPalomarField519.Hodge
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj E.zero.ker.module
def IdealCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (f : F.curve ⟶ E.curve) (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) : Prop :=
  i.hom ≫ F.zero.ker.moduleι =
    (Scheme.Modules.pullback f).map E.zero.ker.moduleι ≫
      (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F :=
  squarePullbackIso b E.zero F.zero f hz.symm E.zero.ker.module ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F) : Prop :=
  ∃ i, IdealCompatible E F f i ∧ e = cotangentComparison E F b f hz i
abbrev affineDifferential {R : Type u} [CommRing R] (E : Family (Base R)) : Cotangent E ⟶ (Scheme.Modules.pullback E.zero).obj E.p.kaehler :=
  ArithmeticThetaPalomarConormal436.conormalMap E.p E.zero
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
    (i : (Scheme.Modules.pullback f).obj (universalFamily k L A).zero.ker.module ≅ E.zero.ker.module),
    IdealCompatible (universalFamily k L A) E f i ∧
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pullback Q.inclusion).map (affineDifferential (universalFamily k L A))) ≫
        e.hom =
      ((Scheme.Modules.pullbackComp b Q.inclusion).app (Cotangent (universalFamily k L A))).hom ≫
        (cotangentComparison (universalFamily k L A) E (b ≫ Q.inclusion) f hz i).hom
end ArithmeticThetaPalomarField519.Hodge
namespace ArithmeticThetaPalomarField519.Level
open CategoryTheory.Limits ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaPalomarField519.Hodge
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
end ArithmeticThetaPalomarField519.Level
namespace ArithmeticThetaPalomarField519.Boundary
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaPalomarField519.Level
variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
def CompactCompatible (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L} {X : Compactification k L D} {Y : Compactification l L E} (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) (hF : ArithmeticThetaPalomarField519.Level.Extends ι D E X Y f F) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) (H : Extension k L D X) (J : Extension l L E Y) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) : Prop :=
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
    (hF : ArithmeticThetaPalomarField519.Level.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E),
    HodgeCompatible ι D E f e → ∀ J : Extension l L E Y,
    Canonical l L J → ∃! a : (Scheme.Modules.pullback F).obj H.line ≅ J.line,
      CompactCompatible ι f F hF e H J a
end ArithmeticThetaPalomarField519.Boundary
namespace ArithmeticThetaPalomarField519
theorem classifierHodge_iff_original {k : Type u} [Field k] [CharZero k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) {S : Scheme.{u}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (b : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) (e : (Scheme.Modules.pullback b).obj (Hodge.ModularHodge k L A B C Q) ≅ Hodge.Cotangent E) : Hodge.ClassifierHodge k L A B C Q E b f e ↔ ArithmeticThetaSchemeHodgeR0205.ClassifierHodge k L A B C Q E b f e := by
  simp only [Hodge.ClassifierHodge, ArithmeticThetaSchemeHodgeR0205.ClassifierHodge, Hodge.affineDifferential, ArithmeticThetaSchemeHodgeR0205.affineDifferential, ArithmeticThetaPalomarConormal436.conormalMap_eq_original]
  rfl
theorem hodgeCompatible_iff_original {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (f : ArithmeticThetaLevelCompactificationR0179.OpenBase l L E ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D) (e : (Scheme.Modules.pullback f).obj (Level.weight D) ≅ Level.weight E) : Level.HodgeCompatible ι D E f e ↔ ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e := by
  simp only [Level.HodgeCompatible, ArithmeticThetaLevelConstantsR0234.HodgeCompatible, classifierHodge_iff_original]
theorem geometric_iff_original {k : Type} [Field k] [CharZero k] {L : ℕ} {D : ArithmeticThetaLevelCompactificationR0179.LevelData k L} {X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D} (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) : Boundary.GeometricallyCanonical H ↔ ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H := by
  simp only [Boundary.GeometricallyCanonical, ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical, hodgeCompatible_iff_original]
  rfl
end ArithmeticThetaPalomarField519
namespace ArithmeticThetaPalomarField519
theorem fieldCompactUnary : ∀ (k : Type) [Field k] [CharZero k] (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaPalomarField519.Boundary.GeometricallyCanonical H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaPalomarUnary514.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPalomarUnary514.RealizesUnary k m N H ν A s := by
  intro k _ _ m N hm hmeven hN hNeven hmN D X H hH hgH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := ArithmeticThetaArithmeticSectionsR0236.field_compact_unary k m N hm hmeven hN hNeven hmN D X H hH ((geometric_iff_original H).mp hgH) ν hν
  refine ⟨a,b,ha,hb,ArithmeticThetaPalomarUnary514.ofOriginal k m N A, ?_⟩
  simpa only [ArithmeticThetaPalomarUnary514.realizes_ofOriginal] using hA
theorem recover_original_069 : ∀ (k : Type) [Field k] [CharZero k] (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  intro k _ _ m N hm hmeven hN hNeven hmN D X H hH hgH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := fieldCompactUnary k m N hm hmeven hN hNeven hmN D X H hH ((geometric_iff_original H).mpr hgH) ν hν
  refine ⟨a,b,ha,hb,ArithmeticThetaPalomarUnary514.toOriginal k m N A, ?_⟩
  simpa only [ArithmeticThetaPalomarUnary514.realizes_toOriginal] using hA
end ArithmeticThetaPalomarField519
