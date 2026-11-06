module

public import ProjectiveCoreRecovery

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace PalomarProjective969
open ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaInvariantRatiosR0265
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
open ArithmeticThetaGlobalProjectiveRatiosR0266.GlobalArithmeticProjectiveRatios
open Arithmetic


open PalomarProjective956
open InvariantRatioFieldDescent ArithmeticInvariantRatioRealization SchemeDoubledTorsionLift

def Geometry : Prop :=
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
    ∃ (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
      (Vd : DiskTest k (2*m) D X), CanonicalMarking k (2*m) (ζ : k) Vd.level

theorem geometry : Geometry := @ArithmeticThetaGlobalProjectiveRatiosR0266.GlobalArithmeticProjectiveRatios.geometric_data

def PointedGroup : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S T : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (E : ArithmeticThetaLocalWeierstrassR0203.Family.{0} S) (F : ArithmeticThetaLocalWeierstrassR0203.Family.{0} T)
  (b : Quiver.Hom.{0, 0 + 1} T S)
  (f :
    Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E)),
  CategoryTheory.IsPullback.{0, 0 + 1} f (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} E) b →
    Eq.{0 + 1}
        (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} F) f)
        (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} b (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} E)) →
      ArithmeticThetaSchemeLevelR0204.Multiplicative.{0} E F b f

theorem pointedgroup : PointedGroup := @ArithmeticThetaSchemeLevelR0204.pointed_cartesian_group_law.{0}

def GlobalMarking : Prop :=
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (V : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) V → ∃ (Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm V ζ) (a : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointX k V))) (b : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointY k V))), ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k V Q he hζ a ∧ ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k V Q he b ∧ ∀ (S : AlgebraicGeometry.Scheme) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m)) (t : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Puncture k) S) (f : Quiver.Hom (ArithmeticThetaTateSchemeMarkingR0263.family k V).curve E.curve) (hc : CategoryTheory.IsPullback f (ArithmeticThetaTateSchemeMarkingR0263.family k V).p E.p t) (hz : CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.family k V).zero f = CategoryTheory.CategoryStruct.comp t E.zero), ArithmeticThetaSchemeLevelR0204.Multiplicative E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f → CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.pointX k V).val f = CategoryTheory.CategoryStruct.comp t M.x.val → CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.pointY k V).val f = CategoryTheory.CategoryStruct.comp t M.y.val → ∃ (I : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.inverse E)) (A : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x)) (B : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y)), ArithmeticThetaSchemeThetaMarkingR0259.NormalizedInversion E m I ∧ ArithmeticThetaSchemeThetaMarkingR0259.MidpointNormalized E m M.x I A ∧ ArithmeticThetaSchemeThetaMarkingR0259.MidpointNormalized E m M.y I B ∧ ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.x I A ∧ ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.y I B ∧ (∃! signs : Bool × Bool, ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x) (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointX k V)) (ArithmeticThetaSchemeThetaMarkingR0259.scaled E m (ArithmeticThetaSchemeThetaNaturalityR0262.signUnit S signs.1) A) a ∧ ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y) (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointY k V)) (ArithmeticThetaSchemeThetaMarkingR0259.scaled E m (ArithmeticThetaSchemeThetaNaturalityR0262.signUnit S signs.2) B) b)

theorem globalmarking : GlobalMarking := by
 intro k _ _ m hm he V ζ hζ hmark
 obtain ⟨Q, N, hNx, hNy, i, a, b, hi, ha, hb, hv, hc, hglobal⟩ :=
   ArithmeticThetaTateSchemeMarkingR0263.global_literal_tate_marking k m hm he V ζ hζ hmark
 exact ⟨Q, a, b, ha, hb, hglobal⟩

def Commutator : Prop :=
∀ (k : Type 0) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{0})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
      ∀ (m : ℕ), 0 < m → Even m →
      ∀ M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m),
      ∀ (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m
        (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x))
        (β : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m
        (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y)),
      ∃! c : (S.presheaf.obj (Opposite.op ⊤))ˣ,
        ArithmeticThetaSchemeThetaMarkingR0259.Commutator E m M.x M.y α β c ∧
        ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c

theorem commutator : Commutator := @ArithmeticThetaSchemeThetaMarkingR0259.scheme_primitive_theta_commutator.{0}

def InvariantLine : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (E : ArithmeticThetaLocalWeierstrassR0203.Family.{0} S) (m : ℕ),
  LT.lt.{0} 0 m →
    ∀ (A B : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} E m))
      (c :
        Units.{0}
          ↑(CategoryTheory.Functor.obj.{0, 0, 0, 0 + 1}
              (AlgebraicGeometry.PresheafedSpace.presheaf.{0, 0 + 1, 0}
                (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{0 + 1, 0, 0}
                  (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0}
                    (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} S))))
              (Opposite.op.{0 + 1} Top.top.{0}))),
      ArithmeticThetaSchemeSchrodingerR0261.Relations.{0} m A B c →
        ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit.{0} m c →
          AlgebraicGeometry.Scheme.Modules.IsInvertible.{0} (ArithmeticThetaSchemeSchrodingerR0261.fixed.{0} A)

theorem invariantline : InvariantLine := @ArithmeticThetaSchemeSchrodingerR0261.scheme_invariant_theta_line.{0}

def Orbit : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (W : AlgebraicGeometry.Scheme.Modules.{0} S) (m : ℕ),
  LT.lt.{0} 0 m →
    ∀ (A B : CategoryTheory.End.{0, 0 + 1} W)
      (c :
        Units.{0}
          ↑(CategoryTheory.Functor.obj.{0, 0, 0, 0 + 1}
              (AlgebraicGeometry.PresheafedSpace.presheaf.{0, 0 + 1, 0}
                (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{0 + 1, 0, 0}
                  (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0}
                    (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} S))))
              (Opposite.op.{0 + 1} Top.top.{0}))),
      ArithmeticThetaSchemeSchrodingerR0261.Relations.{0} m A B c →
        ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit.{0} m c →
          ArithmeticThetaSchemeSchrodingerR0261.Orbit.{0} m A B c

theorem orbit : Orbit := @ArithmeticThetaSchemeSchrodingerR0261.scheme_schrodinger_orbit.{0}

def Intertwining : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (E : ArithmeticThetaLocalWeierstrassR0203.Family.{0} S) (T : AlgebraicGeometry.Scheme.{0})
  (F : ArithmeticThetaLocalWeierstrassR0203.Family.{0} T) (b : Quiver.Hom.{0, 0 + 1} T S)
  (f :
    Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E))
  (hc :
    CategoryTheory.IsPullback.{0, 0 + 1} f (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} E) b)
  (hz :
    Eq.{0 + 1}
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} F) f)
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} b (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} E)))
  (m : ℕ),
  LT.lt.{0} 0 m →
    CategoryTheory.IsIso.{0, 0 + 1} (ArithmeticThetaSchemeThetaNaturalityR0262.pushforwardMap.{0} E F b f hc hz m) ∧
      ∀
        (g :
          Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E)
            (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E))
        (g' :
          Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
            (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F))
        (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} E m g)
        (α' : ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} F m g')
        (A : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} E m))
        (A' : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} F m)),
        ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds.{0} E F b f hc hz m g g' α α' →
          ArithmeticThetaSchemeSchrodingerR0261.IsAction.{0} E m g α A →
            ArithmeticThetaSchemeSchrodingerR0261.IsAction.{0} F m g' α' A' →
              ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines.{0} E F b f hc hz m A A'

theorem intertwining : Intertwining := @ArithmeticThetaSchemeThetaNaturalityR0262.scheme_pushforward_intertwining.{0}

def Naturality : Prop :=
∀ (k : Type 0) [inst : Field.{0} k] [CharZero.{0} k] (S : AlgebraicGeometry.Scheme.{0})
  (σ : Quiver.Hom.{0, 0 + 1} S (ArithmeticThetaLocalWeierstrassR0203.Base.{0} k))
  (E : ArithmeticThetaLocalWeierstrassR0203.Family.{0} S) (T : AlgebraicGeometry.Scheme.{0})
  (F : ArithmeticThetaLocalWeierstrassR0203.Family.{0} T) (b : Quiver.Hom.{0, 0 + 1} T S)
  (f :
    Quiver.Hom.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.curve.{0} E))
  (hc :
    CategoryTheory.IsPullback.{0, 0 + 1} f (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} F)
      (ArithmeticThetaLocalWeierstrassR0203.Family.p.{0} E) b)
  (hz :
    Eq.{0 + 1}
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} F) f)
      (CategoryTheory.CategoryStruct.comp.{0, 0 + 1} b (ArithmeticThetaLocalWeierstrassR0203.Family.zero.{0} E)))
  (m : ℕ),
  LT.lt.{0} 0 m →
    ∀ (A B : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} E m))
      (A' B' : CategoryTheory.End.{0, 0 + 1} (ArithmeticThetaSchemeSchrodingerR0261.V.{0} F m)),
      Eq.{0 + 1} (HPow.hPow.{0, 0, 0} A m) 1 →
        ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines.{0} E F b f hc hz m A A' →
          ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines.{0} E F b f hc hz m B B' →
            ArithmeticThetaSchemeThetaNaturalityR0262.InvariantComponents.{0} E F b f hc hz m A B A' B'

theorem naturality : Naturality := @ArithmeticThetaSchemeThetaNaturalityR0262.scheme_invariant_component_naturality.{0}

def TateRatios : Prop :=
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (Vd : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) (Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd ζ), ∀ (a : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd))) (b : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd))), ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd Q he hζ a → ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd Q he b → ∀ (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m)), ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd)) a A → ArithmeticThetaSchemeSchrodingerR0261.IsAction (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd)) b B → ArithmeticThetaInvariantRatiosR0265.ComponentRatios (ArithmeticThetaTateSchemeMarkingR0263.family k Vd) m hm A B (ArithmeticThetaInvariantRatiosR0265.unaryRatio k m hm)

theorem tateratios : TateRatios := @ArithmeticThetaInvariantRatiosR0265.tate_invariant_component_ratios

def TestExists : Prop :=
∀ (k : Type) [Field k] [CharZero k] (m : ℕ)
 (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (Vd : DiskTest k (2*m) D X),
 Nonempty (ArithmeticThetaInvariantRatiosR0265.Arithmetic.Test k m D X Vd)
theorem testexists : TestExists := ArithmeticThetaInvariantRatiosR0265.ArithmeticInvariantRatioRealization.test_exists

theorem core_from_providers (hPointedGroup : PointedGroup) (hGlobalMarking : GlobalMarking) (hCommutator : Commutator) (hInvariantLine : InvariantLine) (hOrbit : Orbit) (hIntertwining : Intertwining) (hNaturality : Naturality) (hTateRatios : TateRatios) : GlobalThetaCore := by
  intro k _ _ m D X Vd hm he ζ hζ hmark
  let E := globalFamily k m D
  let F := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let M := globalLevel k m D
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := tateBase k m D X Vd
  have hc : IsPullback Vd.map F.p E.p t := Vd.classifies.2.1
  have hz : F.zero ≫ Vd.map = t ≫ E.zero := tate_pointed k m D X Vd
  have hmul : Multiplicative E F t Vd.map :=
    hPointedGroup k _ _ σ E F t Vd.map hc hz
  obtain ⟨Q, a, b, ha, hb, hglobal⟩ :=
    hGlobalMarking k m hm he Vd.level ζ hζ hmark
  obtain ⟨I, α₀, β₀, hI, hα₀, hβ₀, hsα₀, hsβ₀, signs, hsigns, _⟩ :=
    hglobal _ σ E M t Vd.map hc hz hmul Vd.classifies.2.2.2.1 Vd.classifies.2.2.2.2
  let α := scaled E m (signUnit _ signs.1) α₀
  let β := scaled E m (signUnit _ signs.2) β₀
  let A := ActionRelations.thetaAction E m M.x α
  let B := ActionRelations.thetaAction E m M.y β
  let A' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level) a
  let B' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level) b
  have hA : IsAction E m (translation E M.x) α A :=
    ⟨translation_over E M.x, PushforwardAction.formula _ _ _ _ _⟩
  have hB : IsAction E m (translation E M.y) β B :=
    ⟨translation_over E M.y, PushforwardAction.formula _ _ _ _ _⟩
  have hA' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hB' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hpA : A ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_x α₀ hα₀ signs.1
  have hpB : B ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_y β₀ hβ₀ signs.2
  obtain ⟨c, hcmt, _⟩ := hCommutator k _ σ E m hm he M α β
  have hrel : Relations m A B c := ⟨hpA, hpB, action_commutator E m _ _ α β c hcmt.1⟩
  have hline := hInvariantLine k _ σ E m hm A B c hrel hcmt.2
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  have horbit := hOrbit k _ σ (V E m) m hm A B c hrel hcmt.2
  have hvalue : Scheme.Modules.IsInvertible (commonValueLine E m A) :=
    hline.dual.1.tensor_monoidalV2 hfiber
  have hpush := hIntertwining k _ σ E _ F t Vd.map hc hz m hm
  have hAA := hpush.2 _ _ α a A A' hsigns.1 hA hA'
  have hBB := hpush.2 _ _ β b B B' hsigns.2 hB hB'
  have hcmp := hNaturality k _ σ E _ F t Vd.map hc hz
    m hm A B A' B' hpA hAA hBB
  have hrat := hTateRatios k m hm he Vd.level ζ hζ Q a b ha hb A' B' hA' hB'
  exact ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsigns.1, hsigns.2, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hcmt.2, hline, horbit, hvalue, hcmp, hrat⟩


variable (k : Type) [Field k] [CharZero k] (m : ℕ)
 (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (Vd : DiskTest k (2*m) D X)
theorem realization_from_components (htest : TestExists) (hcore : GlobalThetaCore) (hq : PalomarProjective954.QuotientTransfer) (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) Vd.level) :
    GlobalRealization k m D X Vd hm he ζ hζ := by
  let E := globalFamily k m D
  let F := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let M := globalLevel k m D
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := tateBase k m D X Vd
  obtain ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsignα, hsignβ, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hprim, hline, horbit, hvalue, hcmp, hrat⟩ := hcore k m D X Vd hm he ζ hζ hmark
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  obtain ⟨test⟩ := htest k m D X Vd
  let g := genericBase k m D X Vd
  have ht : Spec.map (CommRingCat.ofHom test.scalar) ≫ g = t := by
    change Spec.map (CommRingCat.ofHom test.scalar) ≫
      (GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X (Vd.disk (closedPoint k)) ≫
        D.quotient.inclusion) = _
    rw [← Category.assoc, test.base_eq]
  let P := Scheme.Modules.pullback t
  let z : Fin m := ⟨0, hm⟩
  let d := component E m A B z
  let d' := component F m A' B' z
  let eN := fiberComparison E F t Vd.map hc hz m
  have hcomparison := hcmp
  obtain ⟨e, heq, _⟩ := hcomparison
  have H (j : Fin m) : P.map (component E m A B j) ≫ eN.hom =
      e.hom ≫ component F m A' B' j := heq.2.2 j
  have hdT : IsIso (P.map d) := by
    letI : IsIso d' := hrat.1
    have hdEq : P.map d = e.hom ≫ d' ≫ eN.inv := by
      rw [← Category.assoc, ← H z, Category.assoc, eN.hom_inv_id, Category.comp_id]
    rw [hdEq]
    infer_instance
  have hsT (j : Fin m) : P.map (component E m A B j) =
      P.map d ≫ scalarEnd (P.obj ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)))
        (unaryRatio k m hm j) := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, scalar_natural, ← Category.assoc, H z, Category.assoc, ← hrat.2 j]
    exact H j
  obtain ⟨C, hC⟩ := interior_chart k m D X Vd
  obtain ⟨r, C', hr, hCC', hreg, himage⟩ := hq
    (compactComponent k m D X Vd) (globalBase k m D) g C
    (LaurentSeries k) test.scalar t ht
    (fixed A) ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)) hline hfiber
    d m (fun j => component E m A B j) (unaryRatio k m hm) hdT hsT
  refine ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsignα, hsignβ, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hprim, hline, horbit, hvalue, hcmp, hrat,
    C', r, test, interior_refines k m D X Vd hC hCC', hr, hreg, himage, ?_⟩
  intro j
  exact (rationalExpansion_iff k (compactComponent k m D X Vd) (genericInclusion k ≫ test.disk)
    test.scalar test.generic_eq (r j) (unaryRatio k m hm j)).mpr (himage j)

theorem recover_from_providers (hTest : TestExists) (hGeometry : Geometry) (hPointedGroup : PointedGroup) (hGlobalMarking : GlobalMarking) (hCommutator : Commutator) (hInvariantLine : InvariantLine) (hOrbit : Orbit) (hIntertwining : Intertwining) (hNaturality : Naturality) (hTateRatios : TateRatios) (hq : PalomarProjective954.QuotientTransfer) :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := by
  intro k _ _ m hm he ζ hζ
  obtain ⟨D, X, Vd, hmark⟩ := hGeometry k m hm he ζ hζ
  exact ⟨D, X, Vd, hmark, realization_from_components k m D X Vd hTest (core_from_providers hPointedGroup hGlobalMarking hCommutator hInvariantLine hOrbit hIntertwining hNaturality hTateRatios) hq hm he ζ hζ hmark⟩



theorem original_global_arithmetic_projective_ratios :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := recover_from_providers testexists geometry pointedgroup globalmarking commutator invariantline orbit intertwining naturality tateratios PalomarProjective954.quotient_transfer
end PalomarProjective969
