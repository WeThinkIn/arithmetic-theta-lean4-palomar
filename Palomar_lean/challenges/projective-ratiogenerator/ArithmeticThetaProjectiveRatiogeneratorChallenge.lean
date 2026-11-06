module
public import Mathlib
import all Lean.Meta.Match.Match
macro "eu1382":command=> `(@[expose] public section)
macro "au1382":command=> `(set_option autoImplicit false)
macro "ru1382":command=> `(set_option backward.isDefEq.respectTransparency false)
macro "nu1382":command=> `(noncomputable section)
elab "ec979" n:num:command=> do
  for _ in [:n.getNat] do
    let ss ← Lean.Elab.Command.getScopes
    let h := ss.head!.header
    if h.isEmpty then Lean.Elab.Command.elabCommand (← `(end))
    else Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent (Lean.Name.str Lean.Name.anonymous h))))
eu1382 au1382 open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z7, SheafOfModules → z8, CommRingCat → z9, LinearMap → z10, ModuleCat → z11, AddMonoidHom → z12, RingHom → z13, IsDomain → z14, IsIntegrallyClosed → z15, Finsupp → z18, SetLike → z19, Submodule → z20, HomogeneousIdeal → z22, HomogeneousLocalization → z23, IsScalarTower → z25, AddSubgroupClass → z26, AddSubmonoidClass → z27, Algebra → z28, Nonempty → z29 open AlgebraicGeometry renaming Scheme → zS set_option maxHeartbeats 2000000 set_option maxRecDepth 8192 set_option backward.privateInPublic true macro "rc590":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}) set_option hygiene false set_option quotPrecheck false set_option quotPrecheck true set_option hygiene true eu1382
open Lean Elab Command in
meta def p2mOpenCore (s : String) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue
    let parts := w.splitOn "~"
    let ns := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (fun h => h.toName)
    modifyScope fun sc => { sc with openDecls := OpenDecl.simple ns hidden :: sc.openDecls }
    activateScoped ns
open Lean Elab Command in elab "p2m_open " s:str : command => p2mOpenCore s.getString
open Lean Elab Command in
elab "p2m_open_scoped " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    activateScoped ((w.splitOn "~").head!).toName
syntax (name:= p2mOpenIn) "p2m_open " str " in" ppLine command: command open Lean in macro_rules | `(p2m_open $s:str in $c:command) => return mkNullNode #[← `(section), ← `(p2m_open $s:str), c, ← `(end)]
open Lean Elab Command in
elab "p2m_export " n:str m:str : command => do
  let env ← getEnv
  let ns := n.getString.toName
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for w in m.getString.splitOn " " do
    if w.isEmpty then continue
    let full := ns ++ w.toName
    if env.contains full then al := al.push (cur ++ w.toName, full)
    else
      let prv := mkPrivateName env full
      if env.contains prv then al := al.push (cur ++ w.toName, prv)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env
macro "p2m_open_scoped " s:str " in " c:command : command => `(section p2m_open_scoped $s $c end)    namespace AlgebraicGeometry ec979 1               namespace AlgebraicGeometry.Scheme ec979 2     namespace AlgebraicGeometry.Scheme.Modules ec979 3   
     namespace ArithmeticThetaAlgebraizedMarkedLineR0136 ec979 1  namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion ec979 3      namespace ArithmeticThetaBoundaryHodgeR0182 ec979 1    namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1 
  namespace ArithmeticThetaComponentDegreeR0184 ec979 1               
            
           
     namespace ArithmeticThetaGeneralEllipticKatoR0168 ec979 1            
             namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1     namespace ArithmeticThetaIdentitySectionsR0138 ec979 1
     namespace ArithmeticThetaInvariantRatiosR0265 ec979 1      namespace ArithmeticThetaLevelCompactificationR0179 ec979 1  namespace ArithmeticThetaLocalWeierstrassR0203 ec979 1       namespace ArithmeticThetaNodeCharts ec979 1    namespace ArithmeticThetaPolygonCartierR0133 ec979 1
                namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1  namespace ArithmeticThetaSchemeHodgeR0205 ec979 1   namespace ArithmeticThetaSchemeLevelR0204 ec979 1  
 namespace ArithmeticThetaSchemeSchrodingerR0261 ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259 ec979 1   namespace ArithmeticThetaSchemeThetaNaturalityR0262 ec979 1   namespace ArithmeticThetaSharpCoverR0194 ec979 1  namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3    namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4   namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.Midpoint
ec979 4       namespace ArithmeticThetaTateCuspsR0181 ec979 1    namespace CategoryTheory ec979 1 namespace CategoryTheory.Limits ec979 2    namespace GoodReductionJacobian ec979 1   namespace HomogeneousIdealQuotientGrading ec979 1 namespace NeronModelInfra ec979 1   namespace P2MW ec979 1 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso ec979 2 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry ec979 3 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme ec979 4 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules ec979 5
namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2 ec979 6   namespace PresheafOfModules ec979 1                namespace ProjWeierstrassCubicPrime ec979 1 namespace SheafOfModules ec979 1 namespace WeierstrassCurve ec979 1  namespace WeierstrassProjModel ec979 1  namespace HomogeneousIdealQuotientGrading ec979 1 namespace NeronModelInfra ec979 1 section rc590 eu1382 au1382 namespace WeierstrassProjModel  ec979 1
au1382 universe u namespace WeierstrassProjModel  ec979 1 nu1382 open AlgebraicGeometry CategoryTheory MvPolynomial open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime open NeronModelInfra namespace WeierstrassProjModel attribute [local instance] z6.gradedAlgebra section Carrier variable {R: Type*} [z0 R] theorem span_polynomial_isHomogeneousCR (V: z3.Projective R): (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R):= by sorry def projModelHomogeneousIdealCR (V: z3.Projective R): z22 (homogeneousSubmodule (Fin 3) R):= ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩ @[simp] theorem projModelHomogeneousIdealCR_toIdeal (V: z3.Projective R): (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial}:= by sorry ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 section rc590 eu1382 au1382 ru1382 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u v' u' open CategoryTheory MonoidalCategory Limits Opposite namespace PresheafOfModules section general variable {C: Type u'} [Category.{v'} C] {R: Cᵒᵖ ⥤ z9.{u}} (F N: z7.{u} (R ⋙ forget₂ _ _)) namespace InternalHom abbrev PiFamily (X: Cᵒᵖ): Type (max u u' v'):= ∀ ⦃Y: Cᵒᵖ⦄ (_: X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y) variable {F N} in def IsNatural {X: Cᵒᵖ} (φ: PiFamily F N X): Prop:= ∀ ⦃Y Z: Cᵒᵖ⦄ (f: X ⟶ Y) (g: Y ⟶ Z) (x: F.obj Y), N.map g (φ f x) = φ (f ≫ g) (F.map g x)
def naturalFamilies (X : Cᵒᵖ) : AddSubgroup (PiFamily F N X) where
  carrier := {φ | IsNatural φ}
  zero_mem' := by
    intro Y Z f g x
    simp only [Pi.zero_apply, LinearMap.zero_apply]
    exact (N.map g).hom.map_zero
  add_mem' := by
    intro φ ψ hφ hψ Y Z f g x
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hφ f g x, hψ f g x]
  neg_mem' := by
    intro φ hφ Y Z f g x
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hφ f g x]
variable {F N} @[ext] lemma naturalFamilies_ext {X: Cᵒᵖ} {φ ψ: naturalFamilies F N X} (h: ∀ ⦃Y: Cᵒᵖ⦄ (f: X ⟶ Y) (x: F.obj Y), φ.1 f x = ψ.1 f x): φ = ψ:= by sorry lemma congr_app {X: Cᵒᵖ} (φ: naturalFamilies F N X) {Y: Cᵒᵖ} {f g: X ⟶ Y} (h: f = g) (x: F.obj Y): φ.1 f x = φ.1 g x:= by sorry
instance instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩
@[simp] lemma smul_app {X: Cᵒᵖ} (r: R.obj X) (φ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (r • φ).1 f x = R.map f r • φ.1 f x:= by sorry @[simp] lemma add_app {X: Cᵒᵖ} (φ ψ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (φ + ψ).1 f x = φ.1 f x + ψ.1 f x:= by sorry
set_option hygiene false
set_option quotPrecheck false
local notation "Hg1" => (@CategoryTheory.Functor.comp.{u_3, u_1, u_1, u_2, u_1 + 1, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} R (@CategoryTheory.forget₂.{u_1, u_1, u_1 + 1, u_1, u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (fun (R S : CommRingCat.{u_1}) => @RingHom.{u_1, u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.commRing.{u_1} R)))) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (CommRingCat.commRing.{u_1} S))))) CommRingCat.carrier.{u_1} (fun (X Y : CommRingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} X) ((fun (X : CommRingCat.{u_1}) => @CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.commRing.{u_1} X))) X)) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (CommRingCat.commRing.{u_1} Y))))) CommRingCat.instConcreteCategoryRingHomCarrier.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} (fun (R S : RingCat.{u_1}) => @RingHom.{u_1, u_1} (RingCat.carrier.{u_1} R) (RingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} R) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} R) (RingCat.ring.{u_1} R))) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} S) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} S) (RingCat.ring.{u_1} S)))) RingCat.carrier.{u_1} (fun (X Y : RingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (RingCat.carrier.{u_1} X) (RingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} X) ((fun (X : RingCat.{u_1}) => @Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} X) (RingCat.ring.{u_1} X)) X)) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} Y) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} Y) (RingCat.ring.{u_1} Y)))) RingCat.instConcreteCategoryRingHomCarrier.{u_1} CommRingCat.hasForgetToRingCat.{u_1}))
local notation "Hg5" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 i)
local notation "Hg38" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F i)
local notation "Hg21" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38)
local notation "Hg39" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N i)
local notation "Hg4" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R i)
local notation "Hg33" => (@CommRing.toRing.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4))
local notation "Hg52" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg39)
local notation "Hg51" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg38)
local notation "Hg17" => (@AddCommGroup.toAddCommMonoid.{u_1} Hg21 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38))
local notation "Hg12" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4)))
local notation "Hg27" => (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) Hg12))
local notation "Hg23" => (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg32" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg31" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38)
local notation "Hg19" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39)
local notation "Hg11" => (@LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32)
local notation "Hg22" => (@Quiver.opposite.{u_2, u_3} C (@CategoryTheory.ReflQuiver.toQuiver.{u_3, u_2} C (@CategoryTheory.catToReflQuiver.{u_3, u_2} C inst)))
local notation "Hg48" => (@Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i)
local notation "Hg14" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R Y)
local notation "Hg30" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg14)))
local notation "Hg47" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N Y)
local notation "Hg46" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F Y)
local notation "Hg15" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 Y)
local notation "Hg42" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)
local notation "Hg41" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)
local notation "Hg6" => (fun (Y : Opposite.{u_2 + 1} C) => @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X Y → @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (CommRingCat.carrier.{u_1} Hg14) Hg30 Hg30 (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) Hg30)) Hg41 Hg42 (@AddCommGroup.toAddCommMonoid.{u_1} Hg41 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)) (@AddCommGroup.toAddCommMonoid.{u_1} Hg42 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47))
local notation "Hg10" => (fun (x : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32)
local notation "Hg0" => (@Pi.addGroup.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addGroup.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg51 Hg52 Hg27)) i)
local notation "Hg13" => (@PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X)
local notation "Hg45" => (@AddSubgroup.instSetLike.{max (max u_1 u_2) u_3} Hg13 Hg0)
local notation "Hg29" => (@PresheafOfModules.InternalHom.naturalFamilies.{u_1, u_3, u_2} C inst R F N X)
local notation "Hg2" => (@AddSubmonoidClass.toAddCommMonoid.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@Pi.addCommMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addCommMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @LinearMap.addCommMonoid.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg51 Hg52 Hg27) i) (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg45 (@AddSubgroupClass.toAddSubmonoidClass.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 (@Pi.subNegMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.subNegMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddGroup.toSubNegMonoid.{u_1} Hg11 (@AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg31 Hg32 Hg27))) i) Hg45 (@AddSubgroup.instAddSubgroupClass.{max (max u_1 u_2) u_3} Hg13 Hg0)) Hg29)
local notation "Hg20" => (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 Hg45)
local notation "Hg3" => (@Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x)
local notation "Hg18" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R X)
local notation "Hg7" => (CommRingCat.carrier.{u_1} Hg18)
local notation "Hg16" => (@instHSMul.{u_1, max (max u_1 u_2) u_3} Hg7 Hg3 (@PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies.{u_1, u_3, u_2} C inst R F N X))
local notation "Hg26" => (@OfNat.ofNat.{max (max u_1 u_2) u_3} Hg3 (nat_lit 0) (@Zero.toOfNat0.{max (max u_1 u_2) u_3} Hg3 (@AddZero.toZero.{max (max u_1 u_2) u_3} Hg3 (@AddZeroClass.toAddZero.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddZeroClass.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2))))))
local notation "Hg28" => (@CommSemiring.toSemiring.{u_1} Hg7 (@CommRing.toCommSemiring.{u_1} Hg7 (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg18)))
local notation "Hg40" => (@instHAdd.{max (max u_1 u_2) u_3} Hg3 (@AddSemigroup.toAdd.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddSemigroup.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2))))
local notation "Hg49" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 s φ)
local notation "Hg50" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r φ)
set_option quotPrecheck true
set_option hygiene true
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_1.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r s : CommRingCat.carrier.{u_1} Hg18) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@HMul.hMul.{u_1, u_1, u_1} Hg7 Hg7 Hg7 (@instHMul.{u_1} Hg7 (@Semigroup.toMul.{u_1} Hg7 (@Monoid.toSemigroup.{u_1} Hg7 (@Semiring.toMonoid.{u_1} Hg7 Hg28)))) r s) φ) (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r Hg49) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_2.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@OfNat.ofNat.{u_1} Hg7 (nat_lit 1) (@One.toOfNat1.{u_1} Hg7 (@MulOne.toOne.{u_1} Hg7 (@MulOneClass.toMulOne.{u_1} Hg7 (@Monoid.toMulOneClass.{u_1} Hg7 (@Semiring.toMonoid.{u_1} Hg7 Hg28)))))) φ) φ := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_3.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r : CommRingCat.carrier.{u_1} Hg18), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r Hg26) Hg26 := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_4.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r : CommRingCat.carrier.{u_1} Hg18) (φ ψ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 Hg40 φ ψ)) (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 Hg40 Hg50 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r ψ)) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_5.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r s : CommRingCat.carrier.{u_1} Hg18) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@HAdd.hAdd.{u_1, u_1, u_1} Hg7 Hg7 Hg7 (@instHAdd.{u_1} Hg7 (@Distrib.toAdd.{u_1} Hg7 (@instDistribOfSemiring.{u_1} Hg7 Hg28))) r s) φ) (@HAdd.hAdd.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg3 Hg3 Hg3 (@instHAdd.{max (max u_1 u_2) u_3} Hg3 (@AddCommMagma.toAdd.{max (max u_1 u_2) u_3} Hg3 (@AddCommSemigroup.toAddCommMagma.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddCommSemigroup.{max (max u_1 u_2) u_3} Hg3 Hg2)))) Hg50 Hg49) := by sorry
theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_6.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@OfNat.ofNat.{u_1} Hg7 (nat_lit 0) (@Zero.toOfNat0.{u_1} Hg7 (@MulZeroClass.toZero.{u_1} Hg7 (@instMulZeroClassOfSemiring.{u_1} Hg7 Hg28)))) φ) Hg26 := by sorry
run_cmd do
  for i in [1:7] do
    let n := ("PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_" ++ toString i).toName
    let ci ← Lean.getConstInfo n
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
instance instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp
variable (F N)
def restrict {X X' : Cᵒᵖ} (h : X ⟶ X') : naturalFamilies F N X →+ naturalFamilies F N X' where
  toFun φ := ⟨fun Y f => φ.1 (h ≫ f), fun Y Z f g x => by
    rw [φ.2 (h ≫ f) g x, Category.assoc]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
@[simps obj] def presheaf : Cᵒᵖ ⥤ Ab.{max u u' v'} where
  obj X := AddCommGrpCat.of (naturalFamilies F N X)
  map h := AddCommGrpCat.ofHom (restrict F N h)
  map_id X := by
    ext φ Y f x
    change φ.1 (𝟙 X ≫ f) x = φ.1 f x
    rw [Category.id_comp]
  map_comp h h' := by
    ext φ Y f x
    change φ.1 ((h ≫ h') ≫ f) x = φ.1 (h ≫ (h' ≫ f)) x
    rw [Category.assoc]
instance instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf (X: Cᵒᵖ): Module ((R ⋙ forget₂ z9 RingCat).obj X) ((presheaf F N).obj X):= inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))
variable {N} in
def postcomp {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') (X : Cᵒᵖ) : naturalFamilies F N X →+ naturalFamilies F N' X where
  toFun φ := ⟨fun Y f =>
    { toFun := fun x => ψ.app Y (φ.1 f x)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by
        rw [(φ.1 f).map_smul]
        exact (ψ.app Y).hom.map_smul r _ }, by
    intro Y Z f g x
    change N'.map g (ψ.app Y (φ.1 f x)) = ψ.app Z (φ.1 (f ≫ g) (F.map g x))
    rw [← naturality_apply, φ.2 f g x]⟩
  map_zero' := by ext Y f x; exact (ψ.app Y).hom.map_zero
  map_add' φ φ' := by ext Y f x; exact (ψ.app Y).hom.map_add _ _
ec979 1 open InternalHom
@[simps! obj] noncomputable def ihomObj : PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) :=
  ofPresheaf (InternalHom.presheaf F N) (by
    intro X X' h r φ
    apply naturalFamilies_ext
    intro Y f x
    change (R.map (h ≫ f) r) • φ.1 (h ≫ f) x = R.map f (R.map h r) • φ.1 (h ≫ f) x
    rw [Functor.map_comp]
    rfl)
@[simp] lemma ihomObj_map_val {X X': Cᵒᵖ} (h: X ⟶ X') (φ: (ihomObj F N).obj X) {Y: Cᵒᵖ} (f: X' ⟶ Y) (x: F.obj Y): ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x:= by sorry
variable {N} in
noncomputable def ihomMap {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') : ihomObj F N ⟶ ihomObj F N' :=
  homMk { app := fun X => AddCommGrpCat.ofHom (postcomp F ψ X)
          naturality := fun {X X'} h => by ext φ; rfl } (by
    intro X r φ
    apply naturalFamilies_ext
    intro Y f x
    exact (ψ.app Y).hom.map_smul _ _)
noncomputable def ihomFunctor : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) where
  obj N := ihomObj F N
  map ψ := ihomMap F ψ
  map_id N := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
  map_comp ψ ψ' := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
ec979 1 section closed variable {C: Type u} [Category.{u} C] {R: Cᵒᵖ ⥤ z9.{u}} (F: z7.{u} (R ⋙ forget₂ _ _)) {G N: z7.{u} (R ⋙ forget₂ _ _)} namespace InternalHom
noncomputable def curryFamily (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      map_add' := fun x x' => by rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← (θ.app Y).hom.map_smul]
        rfl }, by
    intro Y Z f g x
    change N.map g (θ.app Y _) = θ.app Z _
    rw [← naturality_apply]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    change θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map g (G.map f y)) =
      θ.app Z (F.map g x ⊗ₜ[R.obj Z] G.map (f ≫ g) y)
    rw [← PresheafOfModules.map_comp_apply]⟩
@[simp] lemma curryFamily_app (θ: F ⊗ G ⟶ N) {X: Cᵒᵖ} (y: G.obj X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y):= by sorry ec979 1 open InternalHom
noncomputable def curry' (θ : F ⊗ G ⟶ N) : G ⟶ ihomObj F N :=
  homMk
    { app := fun X => AddCommGrpCat.ofHom
        { toFun := fun y => curryFamily F θ y
          map_zero' := by
            apply naturalFamilies_ext; intro Y f x
            have h0 : G.map f (0 : G.obj X) = 0 := (G.map f).hom.map_zero
            rw [curryFamily_app, h0, TensorProduct.tmul_zero]
            exact (θ.app Y).hom.map_zero
          map_add' := fun y y' => by
            apply naturalFamilies_ext; intro Y f x
            have h1 : G.map f (y + y') = G.map f y + G.map f y' := (G.map f).hom.map_add _ _
            rw [InternalHom.add_app, curryFamily_app, curryFamily_app, curryFamily_app, h1,
              TensorProduct.tmul_add]
            exact (θ.app Y).hom.map_add _ _ }
      naturality := fun {X X'} h => by
        ext y
        apply naturalFamilies_ext; intro Y f x
        change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (G.map h y)) = θ.app Y (x ⊗ₜ[R.obj Y] G.map (h ≫ f) y)
        rw [PresheafOfModules.map_comp_apply] }
    (by
      intro X r y
      apply naturalFamilies_ext; intro Y f x
      change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (r • y)) = R.map f r • θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      rw [G.map_smul]
      change θ.app Y (x ⊗ₜ[R.obj Y] ((R.map f r : R.obj Y) • G.map f y)) = _
      rw [TensorProduct.tmul_smul]
      exact (θ.app Y).hom.map_smul _ _)
noncomputable def uncurryApp (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) : (F ⊗ G).obj X ⟶ N.obj X :=
  ModuleCat.MonoidalCategory.tensorLift (fun (x : F.obj X) (y : G.obj X) => (κ.app X y).1 (𝟙 X) x)
    (fun x x' y => by simp)
    (fun r x y => by simp)
    (fun x y y' => by
      have h1 : κ.app X (y + y') = κ.app X y + κ.app X y' := (κ.app X).hom.map_add _ _
      simp only [h1]; rfl)
    (fun r x y => by
      have h1 : κ.app X (r • y) = r • κ.app X y := (κ.app X).hom.map_smul _ _
      simp only [h1]
      change R.map (𝟙 X) r • (κ.app X y).1 (𝟙 X) x = _
      rw [R.map_id]
      rfl)
lemma tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := by sorry
lemma uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by sorry
noncomputable def uncurry' (κ : G ⟶ ihomObj F N) : F ⊗ G ⟶ N where
  app X := uncurryApp F κ X
  naturality {X Y} g := ModuleCat.MonoidalCategory.tensor_ext (fun x y => by
    dsimp
    erw [tensorObj_map_tmul' F (G := G) g x y]
    erw [uncurryApp_tmul, uncurryApp_tmul]
    rw [naturality_apply κ g y]
    erw [ihomObj_map_val]
    erw [(κ.app X y).2 (𝟙 X) g x]
    exact congr_app _ (by simp) _)
lemma uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) : DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by sorry
lemma uncurry'_curry' (θ: F ⊗ G ⟶ N): uncurry' F (curry' F θ) = θ:= by sorry lemma curry'_uncurry' (κ: G ⟶ ihomObj F N): curry' F (uncurry' F κ) = κ:= by sorry
noncomputable def tensorIhomAdj : tensorLeft F ⊣ ihomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G N =>
        { toFun := curry' F
          invFun := uncurry' F
          left_inv := uncurry'_curry' F
          right_inv := curry'_uncurry' F }
      homEquiv_naturality_left_symm := fun {G G' N} γ κ => by
        ext X : 1
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        change (uncurry' F (γ ≫ κ)).app X (x ⊗ₜ[R.obj X] y) =
          (uncurry' F κ).app X ((F ◁ γ).app X (x ⊗ₜ[R.obj X] y))
        erw [uncurry'_app_tmul, uncurry'_app_tmul]
      homEquiv_naturality_right := fun {G N N'} θ ν => by
        ext X y
        apply naturalFamilies_ext; intro Y f x
        rfl }
noncomputable instance instMonoidalClosed : MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }
ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1382 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false au1382 universe u open CategoryTheory MonoidalCategory Limits nu1382 namespace SheafOfModules variable {C: Type u} [Category.{u} C] {J: GrothendieckTopology C} (𝒪: Cᵒᵖ ⥤ z9.{u}) (h𝒪: Presheaf.IsSheaf J (𝒪 ⋙ forget₂ z9 RingCat)) [originalWEquals: J.WEqualsLocallyBijective AddCommGrpCat.{u}] [originalWeakSheafify: HasWeakSheafify J AddCommGrpCat.{u}] abbrev ringSheaf: Sheaf J RingCat.{u}:= ⟨𝒪 ⋙ forget₂ z9 RingCat, h𝒪⟩ abbrev PMod:= z7.{u} (𝒪 ⋙ forget₂ z9 RingCat)
abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev toPMod: z8.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪:= z8.forget (ringSheaf 𝒪 h𝒪) ⋙ z7.restrictScalars (𝟙 (𝒪 ⋙ forget₂ z9 RingCat))
abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
instance instFaithfulRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Faithful:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instFullRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Full:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instIsLocalizationPModRingSheafSheafifyFunctorPresheafW: (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪):= by sorry include h𝒪 in theorem presheafW_isMonoidal: (presheafW J 𝒪).IsMonoidal:= by sorry def sheafifyCounitIso (M: z8.{u} (ringSheaf 𝒪 h𝒪)): (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M:= (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] ru1382 in def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅ (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) := sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))
instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal
instance monoidalClosed: MonoidalClosed (z8.{u} (ringSheaf 𝒪 h𝒪)):= Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪) ec979 1 namespace AlgebraicGeometry ec979 1 ec979 1 ec979 1 ec979 1 namespace AlgebraicGeometry.Scheme.Modules ec979 3 section rc590 eu1382 set_option backward.isDefEq.respectTransparency.types false au1382 ru1382 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false universe v u v₁ u₁ v₂ u₂ open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal namespace PresheafOfModules section restrictScalars variable {C: Type u₁} [Category.{v₁} C] {R S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ R) abbrev ringCatHom: S ⋙ forget₂ z9 RingCat ⟶ R ⋙ forget₂ z9 RingCat:= Functor.whiskerRight φ (forget₂ z9 RingCat) noncomputable abbrev restrictScalarsAt (U: Cᵒᵖ): z11.{u} (R.obj U) ⥤ z11.{u} (S.obj U):= z11.restrictScalars (φ.app U).hom
noncomputable def restrictScalarsε : 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶ (restrictScalars (ringCatHom φ)).obj (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ _))) where
  app U := ε (restrictScalarsAt φ U)
  naturality {U V} i := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : S.obj U) => ?_)
    change ε (restrictScalarsAt φ V) (S.map i s) = R.map i (ε (restrictScalarsAt φ U) s)
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    exact ConcreteCategory.congr_hom (φ.naturality i) s
noncomputable def restrictScalarsμ (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) : (restrictScalars (ringCatHom φ)).obj M ⊗ (restrictScalars (ringCatHom φ)).obj N ⟶ (restrictScalars (ringCatHom φ)).obj (M ⊗ N) where
  app U := μ (restrictScalarsAt φ U) (M.obj U) (N.obj U)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    rfl
noncomputable instance restrictScalars_laxMonoidal : (restrictScalars (ringCatHom φ)).LaxMonoidal where
  ε := restrictScalarsε φ
  μ M N := restrictScalarsμ φ M N
  μ_natural_left f N := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app]
    exact μ_natural_left (restrictScalarsAt φ U) (f.app U) (N.obj U)
  μ_natural_right M f := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app]
    exact μ_natural_right (restrictScalarsAt φ U) (M.obj U) (f.app U)
  associativity M N P := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app,
      PresheafOfModulesOfCommRing.associator_hom_app]
    exact associativity (restrictScalarsAt φ U) (M.obj U) (N.obj U) (P.obj U)
  left_unitality M := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.leftUnitor_hom_app]
    exact left_unitality (restrictScalarsAt φ U) (M.obj U)
  right_unitality M := by
    ext1 U
    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.rightUnitor_hom_app]
    exact right_unitality (restrictScalarsAt φ U) (M.obj U)
ec979 1 section pushforward variable {C: Type u₁} [Category.{v₁} C] {D: Type u₂} [Category.{v₂} D] (F: C ⥤ D) {R: Dᵒᵖ ⥤ z9.{u}} {S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ F.op ⋙ R)
noncomputable instance pushforward_laxMonoidal : (pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).LaxMonoidal :=
  inferInstanceAs (pushforward₀OfCommRingCat F R ⋙
    restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).LaxMonoidal
noncomputable instance pullback_oplaxMonoidal [(pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).IsRightAdjoint] :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction (R := R ⋙ forget₂ _ _) (ringCatHom φ)).leftAdjointOplaxMonoidal
ec979 1 ec979 1 namespace PresheafOfModules namespace PullbackMonoidal open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal variable {C D: Type u} [SmallCategory C] [SmallCategory D] [originalProductsC: HasFiniteProducts C] [originalProductsD: HasFiniteProducts D] (F: C ⥤ D) [originalPreservesProducts: PreservesFiniteProducts F] {R: Dᵒᵖ ⥤ z9.{u}} {S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ F.op ⋙ R) local notation "R'" => R ⋙ forget₂ z9 RingCat local notation "S'" => S ⋙ forget₂ z9 RingCat
noncomputable abbrev pb : PresheafOfModules.{u} S' ⥤ PresheafOfModules.{u} R' :=
  pullback (R := R') (ringCatHom φ)
instance isIso_δ (A B: z7.{u} S'): IsIso (δ (pb F φ) A B):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts instance isIso_η: IsIso (η (pb F φ)):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts noncomputable instance pullback_monoidal: (pb F φ).Monoidal:= Functor.Monoidal.ofOplaxMonoidal _ ec979 1 ec979 1 ec979 1 ec979 1 namespace AlgebraicGeometry.Scheme.Modules ec979 3 namespace AlgebraicGeometry.Scheme.Modules ec979 3 namespace AlgebraicGeometry ec979 1 namespace AlgebraicGeometry.Scheme.Modules ec979 3 namespace GoodReductionJacobian  ec979 1 namespace GoodReductionJacobian  ec979 1 namespace AlgebraicGeometry  ec979 1 namespace AlgebraicGeometry  ec979 1  namespace AlgebraicGeometry  namespace OModulePresheaf ec979 1 ec979 1 namespace AlgebraicGeometry  namespace OModulePresheaf namespace Hom ec979 1  ec979 1 ec979 1    namespace ArithmeticThetaNodeCharts
ec979 1 namespace ArithmeticThetaNodeCharts ec979 1            namespace ArithmeticThetaPolygonCartierR0133 ec979 1 namespace ArithmeticThetaPolygonCartierR0133  ec979 1 namespace ArithmeticThetaPolygonCartierR0133  ec979 1  namespace ArithmeticThetaAlgebraizedMarkedLineR0136 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136  ec979 1 namespace AlgebraicGeometry namespace OModulePresheaf ec979 1 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion namespace HomCompleteAux   ec979 1 ec979 3 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2       namespace ArithmeticThetaIdentitySectionsR0138 ec979 1 namespace ArithmeticThetaIdentitySectionsR0138  ec979 1        namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145  ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145  ec979 1
namespace ArithmeticThetaGeneralEllipticKatoR0168  ec979 1  namespace GoodReductionJacobian  ec979 1    section rc590 eu1382 au1382 ru1382 nu1382 universe u namespace ArithmeticThetaLocalWeierstrassR0203 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra open scoped TensorProduct abbrev Base (R: Type u) [z0 R]:= Spec (z9.of R) ec979 1 ec979 1 ec979 1 ec979 1      namespace ArithmeticThetaSchemeLevelR0204 ec979 1 namespace ArithmeticThetaSchemeLevelR0204  ec979 1 namespace ArithmeticThetaSchemeLevelR0204  ec979 1 namespace ArithmeticThetaSchemeHodgeR0205 ec979 1 namespace ArithmeticThetaSchemeHodgeR0205  ec979 1 namespace ArithmeticThetaLevelCompactificationR0179 ec979 1
 namespace ArithmeticThetaTateCuspsR0181 ec979 1 namespace ArithmeticThetaBoundaryHodgeR0182 ec979 1 namespace ArithmeticThetaSchemeHodgeR0205  ec979 1  namespace ArithmeticThetaComponentDegreeR0184 ec979 1 namespace ArithmeticThetaComponentDegreeR0184  ec979 1    namespace ArithmeticThetaSharpCoverR0194 ec979 1 section rc590 eu1382 ru1382 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso au1382 universe u p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry Opposite" namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.appTop Scheme.Hom.comp_appTop Scheme.Hom.naturality Scheme.Modules Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.existsUnique_app_eq_smul" namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom.id_app Hom Γ Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.appTop Hom.comp_appTop Hom.naturality Modules Opens Modules.map_smul PresheafOfModules ΓSpecIso Modules.IsInvertible Modules.IsInvertible.existsUnique_app_eq_smul" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom mapPresheaf_app Hom.id_app Hom.app pullbackPushforwardAdjunction map_smul IsInvertible unitOne IsInvertible.existsUnique_app_eq_smul" namespace P2K2 p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry" variable {X Y: Scheme.{u}} noncomputable abbrev resTop (s: Γ(X, ⊤)) (U: X.Opens): Γ(X, U):= X.presheaf.map (homOfLE le_top: U ⟶ ⊤).op s lemma smul_res_comm (s: Γ(X, ⊤)) (M: X.Modules) (U: X.Opens) (r: Γ(X, U)) (m: Γ(M, U)): resTop s U • r • m = r • resTop s U • m:= by sorry lemma map_resTop_smul (s: Γ(X, ⊤)) (M: X.Modules) {U V: X.Opens} (i: U ⟶ V) (x: Γ(M, V)): M.presheaf.map i.op (resTop s V • x) = resTop s U • M.presheaf.map i.op x:= by sorry
noncomputable def smulHom (s : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(M, U.unop) (resTop s U.unop))
      naturality := fun {U V} i => by
        ext x
        exact (map_resTop_smul s M i.unop (x : Γ(M, U.unop))).symm }
    (fun U r m => smul_res_comm s M U.unop r m)⟩
ec979 4 ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 namespace ArithmeticFamily ec979 1 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4   namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta  ec979 4 namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244  ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259 ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259  ec979 1 namespace ArithmeticThetaSchemeSchrodingerR0261 ec979 1 namespace ArithmeticThetaSchemeThetaNaturalityR0262 ec979 1  section rc590 eu1382 au1382 ru1382
set_option backward.isDefEq.respectTransparency.types false set_option maxHeartbeats 1600000 set_option maxRecDepth 4096 nu1382 universe u namespace ArithmeticThetaInvariantRatiosR0265 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra open ArithmeticThetaLocalWeierstrassR0203 open ArithmeticThetaSchemeThetaMarkingR0259 open ArithmeticThetaSchemeSchrodingerR0261 open ArithmeticThetaSchemeThetaNaturalityR0262 open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184 def scalarEnd {F: Type u} [z1 F] (M: (Base F).Modules) (a: F): End M:= P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom ((Scheme.ΓSpecIso (z9.of F)).inv.hom a) M  ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266  ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1 eu1382 nu1382 open CategoryTheory AlgebraicGeometry open ArithmeticThetaLocalWeierstrassR0203 namespace ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios
def frameValue {F : Type} [Field F] {N : (Base F).Modules}
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules))
    (x : Γ(N, ⊤)) : F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom (e.hom.app ⊤ x)
end ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios set_option hygiene false set_option quotPrecheck false local notation "RG1366x10" => (@ArithmeticThetaLocalWeierstrassR0203.Base.{0} F (@Field.toCommRing.{0} F inst)) local notation "RG1366x30" => (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} RG1366x10)) local notation "RG1366x0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0} CommRingCat.instCategory.{0} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x30)) local notation "RG1366x29" => (AlgebraicGeometry.Spec.{0} (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst))) local notation "RG1366x20" => (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} RG1366x29)) local notation "RG1366x31" => (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x20) local notation "RG1366x6" => (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x31) local notation "RG1366x24" => (@TopologicalSpace.Opens.{0} (TopCat.carrier.{0} RG1366x6) (TopCat.str.{0} RG1366x6)) local notation "RG1366x12" => (AlgebraicGeometry.Scheme.Opens.{0} RG1366x29)
local notation "RG1366x13" => (@TopologicalSpace.Opens.instCompleteLattice.{0} (TopCat.carrier.{0} RG1366x6) (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x20)) local notation "RG1366x9" => (@Preorder.toLE.{0} RG1366x12 (@PartialOrder.toPreorder.{0} RG1366x12 (@SemilatticeSup.toPartialOrder.{0} RG1366x12 (@Lattice.toSemilatticeSup.{0} RG1366x12 (@CompleteLattice.toLattice.{0} RG1366x12 RG1366x13))))) local notation "RG1366x26" => (@Top.top.{0} RG1366x12 (@OrderTop.toTop.{0} RG1366x12 RG1366x9 (@BoundedOrder.toOrderTop.{0} RG1366x12 RG1366x9 (@CompleteLattice.toBoundedOrder.{0} RG1366x12 RG1366x13)))) local notation "RG1366x1" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} RG1366x24) (@CategoryTheory.Category.opposite.{0, 0} RG1366x24 (@Preorder.smallCategory.{0} RG1366x24 (@PartialOrder.toPreorder.{0} RG1366x24 (@TopologicalSpace.Opens.instPartialOrder.{0} (TopCat.carrier.{0} RG1366x6) (TopCat.str.{0} RG1366x6))))) CommRingCat.{0} CommRingCat.instCategory.{0} (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x31) (@Opposite.op.{1} RG1366x12 RG1366x26)) local notation "RG1366x21" => (@TopologicalSpace.Opens.instCompleteLattice.{0} (TopCat.carrier.{0} RG1366x0) (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x30))
local notation "RG1366x14" => (@Preorder.toLE.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) (@PartialOrder.toPreorder.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) (@SemilatticeSup.toPartialOrder.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) (@Lattice.toSemilatticeSup.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) (@CompleteLattice.toLattice.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) RG1366x21))))) local notation "RG1366x2" => (@Top.top.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) (@OrderTop.toTop.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) RG1366x14 (@BoundedOrder.toOrderTop.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) RG1366x14 (@CompleteLattice.toBoundedOrder.{0} (AlgebraicGeometry.Scheme.Opens.{0} RG1366x10) RG1366x21)))) local notation "RG1366x11" => (@TopologicalSpace.Opens.{0} (TopCat.carrier.{0} RG1366x0) (TopCat.str.{0} RG1366x0)) local notation "RG1366x17" => (@Preorder.smallCategory.{0} RG1366x11 (@PartialOrder.toPreorder.{0} RG1366x11 (@TopologicalSpace.Opens.instPartialOrder.{0} (TopCat.carrier.{0} RG1366x0) (TopCat.str.{0} RG1366x0)))) local notation "RG1366x32" => (@CategoryTheory.Category.opposite.{0, 0} RG1366x11 RG1366x17) local notation "RG1366x33" => (@TopologicalSpace.Opens.instCompleteLattice.{0} (TopCat.carrier.{0} RG1366x0) (TopCat.str.{0} RG1366x0)) local notation "RG1366x22" => (@Preorder.toLE.{0} RG1366x11 (@PartialOrder.toPreorder.{0} RG1366x11 (@SemilatticeSup.toPartialOrder.{0} RG1366x11 (@Lattice.toSemilatticeSup.{0} RG1366x11 (@CompleteLattice.toLattice.{0} RG1366x11 RG1366x33)))))
local notation "RG1366x3" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} RG1366x11) RG1366x32 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} RG1366x10 M) (@Opposite.op.{1} RG1366x11 (@Top.top.{0} RG1366x11 (@OrderTop.toTop.{0} RG1366x11 RG1366x22 (@BoundedOrder.toOrderTop.{0} RG1366x11 RG1366x22 (@CompleteLattice.toBoundedOrder.{0} RG1366x11 RG1366x33)))))) local notation "RG1366x4" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} RG1366x11) RG1366x32 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} RG1366x10 M) (@Opposite.op.{1} RG1366x11 RG1366x2)) local notation "RG1366x5" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} RG1366x11) RG1366x32 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} RG1366x10 N) (@Opposite.op.{1} RG1366x11 RG1366x2))
local notation "RG1366x7" => (fun (X Y : AddCommGrpCat.{0}) => @AddMonoidHom.instFunLike.{0, 0} (AddCommGrpCat.carrier.{0} X) (AddCommGrpCat.carrier.{0} Y) (@AddZeroClass.toAddZero.{0} (AddCommGrpCat.carrier.{0} X) ((fun (X : AddCommGrpCat.{0}) => @AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} X) (@SubNegMonoid.toAddMonoid.{0} (AddCommGrpCat.carrier.{0} X) (@AddGroup.toSubNegMonoid.{0} (AddCommGrpCat.carrier.{0} X) (@AddCommGroup.toAddGroup.{0} (AddCommGrpCat.carrier.{0} X) (AddCommGrpCat.str.{0} X))))) X)) (@AddZeroClass.toAddZero.{0} (AddCommGrpCat.carrier.{0} Y) (@AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} Y) (@SubNegMonoid.toAddMonoid.{0} (AddCommGrpCat.carrier.{0} Y) (@AddGroup.toSubNegMonoid.{0} (AddCommGrpCat.carrier.{0} Y) (@AddCommGroup.toAddGroup.{0} (AddCommGrpCat.carrier.{0} Y) (AddCommGrpCat.str.{0} Y)))))))
local notation "RG1366x8" => (fun (x1 x2 : AddCommGrpCat.{0}) => @AddMonoidHom.{0, 0} (AddCommGrpCat.carrier.{0} x1) (AddCommGrpCat.carrier.{0} x2) (@AddZeroClass.toAddZero.{0} (AddCommGrpCat.carrier.{0} x1) (@AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} x1) (@SubNegMonoid.toAddMonoid.{0} (AddCommGrpCat.carrier.{0} x1) (@AddGroup.toSubNegMonoid.{0} (AddCommGrpCat.carrier.{0} x1) (@AddCommGroup.toAddGroup.{0} (AddCommGrpCat.carrier.{0} x1) (AddCommGrpCat.str.{0} x1)))))) (@AddZeroClass.toAddZero.{0} (AddCommGrpCat.carrier.{0} x2) (@AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} x2) (@SubNegMonoid.toAddMonoid.{0} (AddCommGrpCat.carrier.{0} x2) (@AddGroup.toSubNegMonoid.{0} (AddCommGrpCat.carrier.{0} x2) (@AddCommGroup.toAddGroup.{0} (AddCommGrpCat.carrier.{0} x2) (AddCommGrpCat.str.{0} x2))))))) local notation "RG1366x28" => (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) local notation "RG1366x15" => (@ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios.frameValue F inst N e (@DFunLike.coe.{1, 1, 1} (RG1366x8 RG1366x4 RG1366x5) (AddCommGrpCat.carrier.{0} RG1366x4) (fun (x : AddCommGrpCat.carrier.{0} RG1366x4) => AddCommGrpCat.carrier.{0} RG1366x5) (RG1366x7 RG1366x4 RG1366x5) (@CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} Ab.{0} AddCommGrpCat.instCategory.{0} RG1366x8 AddCommGrpCat.carrier.{0} RG1366x7 AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{0} RG1366x4 RG1366x5 (@AlgebraicGeometry.Scheme.Modules.Hom.app.{0} RG1366x10 M N (f (@Fin.mk n RG1366x28 hn)) RG1366x2)) x₀))
local notation "RG1366x16" => (fun (X Y : CommRingCat.{0}) => @RingHom.instFunLike.{0, 0} (CommRingCat.carrier.{0} X) (CommRingCat.carrier.{0} Y) (@Semiring.toNonAssocSemiring.{0} (CommRingCat.carrier.{0} X) ((fun (X : CommRingCat.{0}) => @CommSemiring.toSemiring.{0} (CommRingCat.carrier.{0} X) (@CommRing.toCommSemiring.{0} (CommRingCat.carrier.{0} X) (CommRingCat.commRing.{0} X))) X)) (@Semiring.toNonAssocSemiring.{0} (CommRingCat.carrier.{0} Y) (@CommSemiring.toSemiring.{0} (CommRingCat.carrier.{0} Y) (@CommRing.toCommSemiring.{0} (CommRingCat.carrier.{0} Y) (CommRingCat.commRing.{0} Y))))) local notation "RG1366x18" => (fun (R S : CommRingCat.{0}) => @RingHom.{0, 0} (CommRingCat.carrier.{0} R) (CommRingCat.carrier.{0} S) (@Semiring.toNonAssocSemiring.{0} (CommRingCat.carrier.{0} R) (@CommSemiring.toSemiring.{0} (CommRingCat.carrier.{0} R) (@CommRing.toCommSemiring.{0} (CommRingCat.carrier.{0} R) (CommRingCat.commRing.{0} R)))) (@Semiring.toNonAssocSemiring.{0} (CommRingCat.carrier.{0} S) (@CommSemiring.toSemiring.{0} (CommRingCat.carrier.{0} S) (@CommRing.toCommSemiring.{0} (CommRingCat.carrier.{0} S) (CommRingCat.commRing.{0} S))))) local notation "RG1366x19" => (@SubNegMonoid.toAddMonoid.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (@AddGroup.toSubNegMonoid.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (@AddCommGroup.toAddGroup.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (AddCommGrpCat.str.{0} RG1366x3)))) local notation "RG1366x27" => (@AlgebraicGeometry.Scheme.Modules.instCategory.{0} RG1366x10)
local notation "RG1366x23" => (@CategoryTheory.ReflQuiver.toQuiver.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) (@CategoryTheory.catToReflQuiver.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x27)) local notation "RG1366x25" => (@CommSemiring.toSemiring.{0} (CommRingCat.carrier.{0} RG1366x1) (@CommRing.toCommSemiring.{0} (CommRingCat.carrier.{0} RG1366x1) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{0} RG1366x1))) local notation "RG1366x34" => (@CommSemiring.toSemiring.{0} F (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst))) set_option quotPrecheck true set_option hygiene true
theorem _root_.ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios.ratios_of_generator : ∀ {F : Type} [inst : Field.{0} F] {M N : AlgebraicGeometry.Scheme.Modules.{0} RG1366x10} {n : Nat} (hn : @LT.lt.{0} Nat instLTNat RG1366x28 n) (f : Fin n → @Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x23 M N) (r : Fin n → F) (e : @CategoryTheory.Iso.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x27 N (@SheafOfModules.unit.{0, 0, 0} RG1366x11 RG1366x17 (@Opens.grothendieckTopology.{0} (TopCat.carrier.{0} RG1366x0) (TopCat.str.{0} RG1366x0)) (AlgebraicGeometry.Scheme.ringCatSheaf.{0} RG1366x10))) (x₀ : AddCommGrpCat.carrier.{0} RG1366x3) (hspan : ∀ (x : AddCommGrpCat.carrier.{0} RG1366x3), @Exists.{1} F fun (c : F) => @Eq.{1} (AddCommGrpCat.carrier.{0} RG1366x3) x (@HSMul.hSMul.{0, 0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) (AddCommGrpCat.carrier.{0} RG1366x3) (@instHSMul.{0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) (@SMulZeroClass.toSMul.{0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) (@AddZero.toZero.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (@AddZeroClass.toAddZero.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (@AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} RG1366x3) RG1366x19))) (@DistribSMul.toSMulZeroClass.{0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) (@AddMonoid.toAddZeroClass.{0} (AddCommGrpCat.carrier.{0} RG1366x3) RG1366x19) (@DistribMulAction.toDistribSMul.{0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) (@Semiring.toMonoid.{0} (CommRingCat.carrier.{0} RG1366x1) RG1366x25) RG1366x19 (@Module.toDistribMulAction.{0, 0} (CommRingCat.carrier.{0} RG1366x1) (AddCommGrpCat.carrier.{0} RG1366x3) RG1366x25 (@AddCommGroup.toAddCommMonoid.{0} (AddCommGrpCat.carrier.{0} RG1366x3) (AddCommGrpCat.str.{0} RG1366x3)) (@AlgebraicGeometry.Scheme.Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf.{0} RG1366x29 M RG1366x26)))))) (@DFunLike.coe.{1, 1, 1} (RG1366x18 (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst)) RG1366x1) (CommRingCat.carrier.{0} (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst))) (fun (x : CommRingCat.carrier.{0} (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst))) => CommRingCat.carrier.{0} RG1366x1) (RG1366x16 (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst)) RG1366x1) (@CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x18 CommRingCat.carrier.{0} RG1366x16 CommRingCat.instConcreteCategoryRingHomCarrier.{0} (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst)) RG1366x1 (@CategoryTheory.Iso.inv.{0, 1} CommRingCat.{0} CommRingCat.instCategory.{0} RG1366x1 (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst)) (AlgebraicGeometry.Scheme.ΓSpecIso.{0} (@CommRingCat.of.{0} F (@Field.toCommRing.{0} F inst))))) c) x₀)) (hne : @Ne.{1} F RG1366x15 (@OfNat.ofNat.{0} F (nat_lit 0) (@Zero.toOfNat0.{0} F (@MulZeroClass.toZero.{0} F (@instMulZeroClassOfSemiring.{0} F RG1366x34))))) (hr : ∀ (i : Fin n), @Eq.{1} F (@ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios.frameValue F inst N e (@DFunLike.coe.{1, 1, 1} (RG1366x8 RG1366x4 RG1366x5) (AddCommGrpCat.carrier.{0} RG1366x4) (fun (x : AddCommGrpCat.carrier.{0} RG1366x4) => AddCommGrpCat.carrier.{0} RG1366x5) (RG1366x7 RG1366x4 RG1366x5) (@CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} Ab.{0} AddCommGrpCat.instCategory.{0} RG1366x8 AddCommGrpCat.carrier.{0} RG1366x7 AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{0} RG1366x4 RG1366x5 (@AlgebraicGeometry.Scheme.Modules.Hom.app.{0} RG1366x10 M N (f i) RG1366x2)) x₀)) (@HMul.hMul.{0, 0, 0} F F F (@instHMul.{0} F (@Distrib.toMul.{0} F (@instDistribOfSemiring.{0} F RG1366x34))) RG1366x15 (r i))), And (@CategoryTheory.IsIso.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x27 M N (f (@Fin.mk n RG1366x28 hn))) (∀ (i : Fin n), @Eq.{1} (@Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x23 M N) (f i) (@CategoryTheory.CategoryStruct.comp.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) (@CategoryTheory.Category.toCategoryStruct.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} RG1366x10) RG1366x27) M N N (f (@Fin.mk n RG1366x28 hn)) (@ArithmeticThetaInvariantRatiosR0265.scalarEnd.{0} F inst N (r i)))) := by sorry
end
