module

public import SharpMatrixGeometricFamilyR0195
public import SquareIsometryInterfaceAdapterR0192

@[expose] public section

/-! Test objects of the square-root moduli problem and their actual scheme fibers.
All assertions of representability, naturality and degree are future obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaCoverComparison

/-- A root object over a test scheme, including its actual map to the base. -/
structure RootObject (B : Scheme.{0}) (W : B.Modules) (T : Scheme.{0}) where
  map : T ⟶ B
  root : SquareLine T ((Scheme.Modules.pullback map).obj W)

/-- Pullback of the weight line with its specified square identification. -/
def pullRoot {B Y : Scheme.{0}} {W : B.Modules} (p : Y ⟶ B)
    (J : SquareLine B W) : SquareLine Y ((Scheme.Modules.pullback p).obj W) :=
  ⟨(Scheme.Modules.pullback p).obj J.line, J.invertible.pullback p, squarePull p J⟩

/-- A candidate point of Y times the root object T over the root moduli problem.
The line isomorphism is actual sheaf data; compatibility is imposed separately. -/
structure Lift {B Y T : Scheme.{0}} {W : B.Modules} (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W))
    (R : RootObject B W T) (S : Scheme.{0}) where
  toLevel : S ⟶ Y
  toTest : S ⟶ T
  triangle : toLevel ≫ p = toTest ≫ R.map
  iso : (Scheme.Modules.pullback toTest).obj R.root.line ≅
    (Scheme.Modules.pullback toLevel).obj H.line

/-- Both routes end in the same pullback of the original W. -/
def Compatible {B Y T S : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d : Lift p H R S) : Prop :=
  tensorPowerMap d.iso.hom 2 ≫ (squarePull d.toLevel H).hom ≫
    ((Scheme.Modules.pullbackComp d.toLevel p).app W).hom ≫
    ((Scheme.Modules.pullbackCongr d.triangle).app W).hom =
      (squarePull d.toTest R.root).hom ≫
        ((Scheme.Modules.pullbackComp d.toTest R.map).app W).hom

/-- Reindexing uses only the canonical sheaf pullback comparison. -/
def reindex {B Y T S S' : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d : Lift p H R S) (a : S' ⟶ S) : Lift p H R S' where
  toLevel := a ≫ d.toLevel
  toTest := a ≫ d.toTest
  triangle := by simp only [Category.assoc, d.triangle]
  iso := ((Scheme.Modules.pullbackComp a d.toTest).app R.root.line).symm ≪≫
    (Scheme.Modules.pullback a).mapIso d.iso ≪≫
      (Scheme.Modules.pullbackComp a d.toLevel).app H.line

/-- Equality of geometric lifts after transport through their map equalities. -/
def SameLift {B Y T S : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (d e : Lift p H R S) : Prop :=
  ∃ (hy : d.toLevel = e.toLevel) (ht : d.toTest = e.toTest),
    d.iso ≪≫ (Scheme.Modules.pullbackCongr hy).app H.line =
      (Scheme.Modules.pullbackCongr ht).app R.root.line ≪≫ e.iso

/-- A scheme representing the full fiber, with a universal square isomorphism. -/
structure Fiber {B Y T : Scheme.{0}} {W : B.Modules} (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W))
    (R : RootObject B W T) where
  space : Scheme.{0}
  universal : Lift p H R space

/-- The natural Yoneda universal property retains the universal isomorphism,
not just the two underlying maps or a bijection on geometric points. -/
def Represents {B Y T : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (F : Fiber p H R) : Prop :=
  Compatible F.universal ∧
    ∀ (S : Scheme.{0}) (d : Lift p H R S), Compatible d →
      ∃! g : S ⟶ F.space, SameLift (reindex F.universal g) d

/-- The representing scheme lies over the actual base product. -/
def PairTorsor {B Y T : Scheme.{0}} {W : B.Modules} {p : Y ⟶ B}
    {H : SquareLine Y ((Scheme.Modules.pullback p).obj W)}
    {R : RootObject B W T} (F : Fiber p H R) : Prop :=
  ∃ a : F.space ⟶ Limits.pullback p R.map,
    a ≫ Limits.pullback.fst p R.map = F.universal.toLevel ∧
    a ≫ Limits.pullback.snd p R.map = F.universal.toTest ∧
    IsFinite a ∧ Etale a ∧ Surjective a ∧
      ∀ z : ↥(Limits.pullback p R.map), Scheme.Hom.finrank a z = 2

/-- Finite representability at every test root, with pointwise degree relative
 to the ORIGINAL structural map p, even on disconnected or empty tests. -/
def FiniteRootLevel {B Y : Scheme.{0}} {W : B.Modules} (p : Y ⟶ B)
    (H : SquareLine Y ((Scheme.Modules.pullback p).obj W)) : Prop :=
  ∀ (T : Scheme.{0}) (R : RootObject B W T),
    ∃ F : Fiber p H R, Represents F ∧ PairTorsor F ∧
      IsFinite F.universal.toTest ∧ Etale F.universal.toTest ∧
      Surjective F.universal.toTest ∧
      ∀ t : T, Scheme.Hom.finrank F.universal.toTest t =
        2 * Scheme.Hom.finrank p (R.map t)

/-- Actual square-compatible isomorphisms on a fixed scheme. -/
def SquareIso {Z : Scheme.{0}} {W : Z.Modules} (A B : SquareLine Z W) :=
  {e : A.line ≅ B.line // tensorPowerMap e.hom 2 ≫ B.square.hom = A.square.hom}

/-- The functor of points of mu_2; all global units with square one, including
independent signs on disconnected tests. -/
def MuTwo (Z : Scheme.{0}) := {u : (Z.presheaf.obj (Opposite.op ⊤))ˣ // u ^ 2 = 1}

/-- The specified mu_2 action is multiplication on actual local sections. -/
def Scales {Z : Scheme.{0}} {W : Z.Modules} {A B : SquareLine Z W}
    (u : MuTwo Z) (e e' : SquareIso A B) : Prop :=
  ∀ (U : Z.Opens) (v : Γ(A.line, U)),
    e'.val.hom.app U v =
      Z.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (u.val : Z.presheaf.obj (Opposite.op ⊤)) •
        e.val.hom.app U v

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaSharpKernelR0195

/-- The accepted sharp geometric family strengthened by actual representability
at every square-root test object on its compact component. -/
def MetaplecticFamily {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D}
    (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : Prop :=
  let N := commonN A
  let L := level N
  let x := V.disk (closedPoint ℂ)
  ∃ J : SquareLine (Component ℂ L D X x) (hodge ℂ L D X x H),
    ∃ C : RootCover ℂ (Component ℂ L D X x) (projection ℂ L D X x) (2^(normCount A-1)),
      FiniteRootLevel C.map (pullRoot C.map J) ∧
      Etale C.map ∧ (normCount A = 1 → IsIso C.map) ∧
      SquareCoverDegree ℂ L D X H x J (2^(normCount A-1)) n C ∧
      ∃ F : CoverFrame ℂ N H V J (2^(normCount A-1)) C,
        ∃ (t : Fin U.count → Sections C.space ((Scheme.Modules.pullback C.map).obj J.line))
          (σ : Fin h → Sections C.space (tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n)),
          (∀ j, t j ≠ 0 ∧ pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) (t j) =
            ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (unarySeries ℂ N (U.pair j).1 (U.pair j).2) • F.frame) ∧
          (∀ i, σ i = ∑ a : Cosets A i, tensorProductSection C.space ((Scheme.Modules.pullback C.map).obj J.line)
            n ⊤ (fun j => t (U.index i a j))) ∧
          ∀ c : Fin h → ℂ,
            pullbackPowerSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) n
              (∑ i : Fin h, baseScalar ℂ (C.map ≫ projection ℂ L D X x) (c i) • σ i) =
                ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries ℂ) (expanded A c) •
                  tensorPowerSection (Disk ℂ) ((Scheme.Modules.pullback F.disk).obj
                    ((Scheme.Modules.pullback C.map).obj J.line)) n ⊤ F.frame

end ArithmeticThetaMetaplecticTestsR0196
