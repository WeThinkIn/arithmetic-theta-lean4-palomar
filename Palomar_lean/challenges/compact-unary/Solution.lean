module
public import CompactUnaryHodgeRealizationR0183
public import SchemeDiscriminantExistenceR0244
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
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
namespace ArithmeticThetaPalomarUnary514
theorem compactUnaryHodgeRealization :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaPalomarUnary514.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPalomarUnary514.RealizesUnary k m N H ν A s := by
  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := ArithmeticThetaCompactUnaryR0183.compact_unary_hodge_realization k m N hm hmeven hN hNeven hmN D X H hH ν hν
  refine ⟨a,b,ha,hb,ofOriginal k m N A, ?_⟩
  simpa only [realizes_ofOriginal] using hA
theorem recover_original_028 :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := compactUnaryHodgeRealization k m N hm hmeven hN hNeven hmN D X H hH ν hν
  refine ⟨a,b,ha,hb,toOriginal k m N A, ?_⟩
  simpa only [realizes_toOriginal] using hA
end ArithmeticThetaPalomarUnary514
