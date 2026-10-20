module

public import ConservativeMatrixKernelR0189
public import TwoTorsionAffineCoordinatesR0177
public import TwoTorsionSplitCubicR0177
public import TateMarkedRootIdentity

@[expose] public section

/-! Relative and compact four-torsion Hodge sections. These are ordinary
geometric definitions; no existence or expansion assertion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaGlobalFourTorsionR0190
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaTensorPower ArithmeticThetaPullback

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)
  (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))

def twoLabel (i : Fin 3) : Base R ⟶ Curve R W :=
  ![(G.nsmul (𝟙 _) (L/2) M.x).val,
    (G.nsmul (𝟙 _) (L/2) M.y).val,
    (G.mul (𝟙 _) (G.nsmul (𝟙 _) (L/2) M.x)
      (G.nsmul (𝟙 _) (L/2) M.y)).val] i

def quarterPoint : Base R ⟶ Curve R W := (G.nsmul (𝟙 _) (L/4) M.y).val

def completedY [Algebra ℚ R] (x y : R) : R :=
  y + algebraMap ℚ R (1/2) * (W.a₁ * x + W.a₃)

def Labels [Algebra ℚ R] (e : Fin 3 → R) : Prop :=
  ∀ i, HasCoordinates R W (twoLabel R W G L M i) (e i)
    (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i + W.a₃))

/-- The section is the actual quarter of the second full-level label.
The denominator is required to be a unit over the entire base. -/
def RootData [Algebra ℚ R] (e : Fin 3 → R) (x y g : R) : Prop :=
  Labels R W G L M e ∧ SplitCubic R W e ∧
  HasCoordinates R W (quarterPoint R W G L M) x y ∧
  IsUnit (completedY R W x y) ∧ IsUnit g ∧
  2 * completedY R W x y * g = (x-e 0)^2 - (e 0-e 1)*(e 0-e 2) ∧
  g^2 = e 1-e 0

abbrev CurveFrame :=
  (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules) ≅
    (structureMap R W).kaehler

def differentialSection (δ : CurveFrame R W) : Γ((structureMap R W).kaehler, ⊤) :=
  Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve R W, ⊤))

/-- Normalization through the actual affine chart and its universal derivation:
dx=(2y+a1*x+a3) delta. -/
def NormalizedFrame (δ : CurveFrame R W) : Prop :=
  let j := chartInclusion R W
  let p := j ≫ structureMap R W
  let x := WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective
  let y := WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective
  let toGlobal := (Scheme.ΓSpecIso (CommRingCat.of (ChartRing R W))).inv
  ArithmeticThetaCompactifiedDifferentialR0145.relativeD p ⊤ (toGlobal x) =
    toGlobal (2*y + chartScalar R W W.a₁*x + chartScalar R W W.a₃) •
      (differentialMap (structureMap R W) p j (by simp [p])).app ⊤
        (pullbackGlobalSection j (structureMap R W).kaehler (differentialSection R W δ))

def hodgeGenerator (δ : CurveFrame R W) : Γ(Hodge R W, ⊤) :=
  pullbackGlobalSection (origin R W) (structureMap R W).kaehler
    (differentialSection R W δ)

/-- A specified algebraic formula in the genuine Hodge sheaf. Existence of
coordinates, unit coefficient and normalized differential are part of this
predicate, so it cannot hold vacuously because of missing test objects. -/
def RealizesAlpha [Algebra ℚ R] (a : Γ(Hodge R W, ⊤)) : Prop :=
  ∃ (e : Fin 3 → R) (x y g : R) (δ : CurveFrame R W),
    RootData R W G L M e x y g ∧ NormalizedFrame R W δ ∧
    a = ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • hodgeGenerator R W δ

section BaseChange
variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
  [W.IsElliptic]
  (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)
  (Gs : Law S Ws) (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b)

def hodgeComparison :
    (Scheme.Modules.pullback (baseMap R S ι)).obj (Hodge R W) ≅ Hodge S Ws := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (relative_curve_geometry R W).2.2.2.2.2.1
  exact pointedDifferentialIso (structureMap R W) (structureMap S Ws) b hb.1
    (origin R W) (origin S Ws) hb.2.1

def pullAlpha (a : Γ(Hodge R W, ⊤)) : Γ(Hodge S Ws, ⊤) :=
  (hodgeComparison R W G S Ws Gs ι b hb).hom.app ⊤
    (pullbackGlobalSection (baseMap R S ι) (Hodge R W) a)
end BaseChange

section LevelBase
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
variable (k : Type) [Field k] [CharZero k] (D : LevelData k L)

/-- The actual pointed Cartesian comparison for every classifying chart. -/
def openComparison (R : Type) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (b : Base R ⟶ OpenBase k L D) (f : Curve R W ⟶ D.atlas.descent.family.curve)
    (hf : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two
      D.cover D.quotient R W G M b f) :
    (Scheme.Modules.pullback b).obj (openHodge k L D) ≅ Hodge R W := by
  let ι : D.atlas.quotient.ring →+* R := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have he : baseMap D.atlas.quotient.ring R ι = b ≫ D.quotient.inclusion := Spec.map_preimage _
  letI : Algebra D.atlas.quotient.ring R := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 D.atlas.descent.family.projection := D.atlas.descent.family.smooth
  let e := pointedDifferentialIso D.atlas.descent.family.projection (structureMap R W) f
    (by rw [show Spec.map (CommRingCat.ofHom (algebraMap D.atlas.quotient.ring R)) = b ≫ D.quotient.inclusion from he]; exact hf.2.1)
    (ArithmeticThetaOpenHodgeR0180.zero D.atlas.descent.family) (origin R W)
    (by rw [show Spec.map (CommRingCat.ofHom (algebraMap D.atlas.quotient.ring R)) = b ≫ D.quotient.inclusion from he]; exact hf.2.2.1)
  exact (Scheme.Modules.pullbackComp b D.quotient.inclusion).app _ ≪≫
    pullbackEqIso he.symm _ ≪≫ e

def pullOpenAlpha (R : Type) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R)))
    (b : Base R ⟶ OpenBase k L D) (f : Curve R W ⟶ D.atlas.descent.family.curve)
    (hf : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two
      D.cover D.quotient R W G M b f) (a : Γ(openHodge k L D, ⊤)) : Γ(Hodge R W, ⊤) :=
  (openComparison L k D R W G M b f hf).hom.app ⊤
    (pullbackGlobalSection b (openHodge k L D) a)

def IsOpenAlpha (a : Γ(openHodge k L D, ⊤)) : Prop :=
  IsFrame (openHodge k L D) ⊤ a ∧
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
    ∀ (M : FullLevel R W G L (𝟙 (Base R)))
    (b : Base R ⟶ OpenBase k L D) (f : Curve R W ⟶ D.atlas.descent.family.curve)
    (hf : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two
      D.cover D.quotient R W G M b f),
    RealizesAlpha R W G L M (pullOpenAlpha L k D R W G M b f hf a)

variable (X : Compactification k L D) (H : Extension k L D X)
def restrictAlpha (a : Γ(H.line, ⊤)) : Γ(openHodge k L D, ⊤) :=
  H.onOpen.hom.app ⊤ (pullbackGlobalSection X.inclusion H.line a)

/-- Full series at every actual marked cusp, with exact allowed orders.
The unit and order are outputs, not presumed expansion data. -/
def CuspOrders (a : Γ(H.line, ⊤)) : Prop :=
  ∀ T : DiskTest k L D X, ∀ η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
    ExtendsGenerator k L H T η →
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧ Even j ∧
      pullbackGlobalSection T.disk H.line a =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (PowerSeries.X^j * (v : PowerSeries k)) • η

/-- The theta here has q=Q^(1/2)=t^(L/2), with complete coefficients. -/
def thetaAt (L : ℕ) : PowerSeries k :=
  PowerSeries.mk (fun n => if L/2 ∣ n then PowerSeries.coeff (n/(L/2))
    (ArithmeticThetaTateSeries.theta k) else 0)

def ExactTateAlpha (a : Γ(H.line, ⊤)) : Prop :=
  ∀ (T : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ T.level →
    ∀ η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤),
    ExtendsGenerator k L H T η →
      pullbackGlobalSection T.disk H.line a =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L ^ 2) • η
end LevelBase
end ArithmeticThetaGlobalFourTorsionR0190
